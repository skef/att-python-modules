#!/usr/bin/env python3

'''
This tool exports the kerning and groups data within a UFO to a
`makeotf`-compatible GPOS kern feature file.

#### Default functionality:

-   writing of a sorted kern.fea file, which organizes pairs in order of
    specificity (exceptions first, then glyph-to-glyph, then group pairs)
-   filtering of small pairs (often results of interpolation).
    Exceptions (even though they may be small) are not filtered.
-   processing of right-to-left pairs (given that kerning groups containing
    those glyphs are suffixed with `_ARA`, `_HEB`, or `_RTL`)

#### Optional functionality:

-   dissolving single-element groups into glyph pairs – this helps with
    subtable optimization, and can be seen as a means to avoid kerning overflow
-   subtable measuring and automatic insertion of subtable breaks
-   specifying a maximum subtable size
-   identification of glyph-to-glyph RTL pairs by way of a global `RTL_KERNING`
    reference group
-   specifying a glyph name suffix for glyphs to be ignored when writing the
    kern feature

#### Usage:
```zsh

    # write a basic kern feature file
    python kernFeatureWriter.py font.ufo

    # write a kern feature file with minimum absolute kerning value of 5
    python kernFeatureWriter.py -min 5 font.ufo

    # write a kern feature with subtable breaks
    python kernFeatureWriter.py -s font.ufo

    # further usage information
    python kernFeatureWriter.py -h

```
'''

import argparse
import itertools
import time
from abc import abstractmethod
from collections import defaultdict
from graphlib import TopologicalSorter, CycleError
from pathlib import Path

import defcon
from fontTools.designspaceLib import (
    DesignSpaceDocument,
    DesignSpaceDocumentError,
)

# constants
RTL_GROUP = 'RTL_KERNING'
RTL_TAGS = ['_ARA', '_HEB', '_RTL']
SHORTINSTNAMEKEY = 'adobe.shortInstanceName'
GROUPSPLITSUFFIX = '_split'


# helpers
def is_group(item_name):
    '''
    Check if an item name implies a group.
    '''

    return any([
        item_name.startswith('@'),
        item_name.startswith('public.')])


def is_kerning_group(grp_name):
    '''
    Check if a group name implies a kerning group.
    '''

    return any([
        grp_name.startswith('@MMK_'),
        grp_name.startswith('public.kern')])


def is_rtl_group(grp_name):
    '''
    Check if a given group is a RTL group
    '''
    return any([tag in grp_name for tag in RTL_TAGS])


class Defaults(object):
    '''
    default values
    These can later be overridden by argparse.
    '''

    def __init__(self):

        # The default output filename
        self.output_name = 'kern.fea'

        # The default name for the locations file
        self.locations_name = 'locations.fea'

        # Default mimimum kerning value. This value is _inclusive_, which
        # means that pairs that equal this absolute value will not be
        # ignored/trimmed. Pairs in range of +/- value will be trimmed.
        # Exceptions within the value range will not be trimmed.
        self.min_value = 3

        # The maximum possible subtable size is 2 ** 16 = 65536.
        # Every other GPOS feature counts against that size, so the
        # subtable size chosen needs to be quite a bit smaller.
        self.subtable_size = 2 ** 13

        # Write trimmed pairs to the output file (as comments).
        self.write_trimmed_pairs = False

        # If variable, output user location values
        # (default is design values)
        self.user_values = False

        # Write subtables?
        self.write_subtables = False

        # Write time stamp in .fea file header?
        self.write_timestamp = False

        # Do not write the locations file?
        self.no_locations = False

        # Write single-element groups as glyphs?
        # (This has no influence on the output kerning data, but helps with
        # balancing subtables, and potentially makes the number of kerning
        # pairs involving groups a bit smaller).
        self.dissolve_single = False

        # ignore pairs which contain glyphs using the following suffix
        self.ignore_suffix = None


class KernAdapter(object):
    '''
    Interface layer between underlying font source and the KerningSanitizer
    '''

    def has_data(self):
        return self._has_data

    def has_locations(self):
        '''
        Returns true when the source is variable and false otherwise
        '''
        return False

    def get_locations(self, userUnits = False):
        '''
        Returns a dictionary of location name to axis coordinates
        '''
        assert False
        return {}

    @abstractmethod
    def all_glyphs(self):
        '''
        Returns a set of the names of all glyphs in the sources
        '''
        pass

    @abstractmethod
    def glyph_order(self):
        '''
        Returns a dictionary of all the glyphs in the source font where
        the key is the name and the value is the order of the glyph in
        the font.
        '''
        pass

    @abstractmethod
    def groups(self):
        '''
        Returns a dict of all groups in the sources, with the name as a
        key and a list of glyphs in the group as the value
        '''
        pass

    @abstractmethod
    def kerning(self):
        '''
        Returns a dict of all kerning pairs in the sources, with the
        key being a tuple of (left, right) and the value being the kerning
        value. The elements of the tuple can be glyph names or group names
        '''
        pass

    @abstractmethod
    def postscript_font_name(self):
        '''
        Returns the postscriptFontName stored in the sources, or None if
        there is no name
        '''
        pass

    @abstractmethod
    def path(self):
        '''
        Returns path to the top of the source as a Path() object
        '''
        pass

    @abstractmethod
    def value_string(self, value, rtl=False):
        '''
        Returns the value as a string that can be used in a feature file.
        When rtl is True the value will be for right-to-left use
        '''
        pass

    @abstractmethod
    def below_minimum(self, value, minimum):
        '''
        Returns True if the value is considered greater than minimum and
        False otherwise. The value parameter must be from the kerning()
        dictionary. The minimum parameter is an integer.
        '''
        pass

    @abstractmethod
    def value_is_zero(self, value):
        '''
        Returns True if the value is considered greater than minimum and
        False otherwise. The value parameter must be from the kerning()
        dictionary. The minimum parameter is an integer.
        '''
        pass


class UFOKernAdapter(KernAdapter):
    '''
    Adapter for a single UFO
    '''

    def __init__(self, f):
        self._has_data = True

        if f:
            if not f.kerning:
                print('ERROR: The font has no kerning!')
                self._has_data = False
                return
            if set(f.kerning.values()) == {0}:
                print('ERROR: All kerning values are zero!')
                self._has_data = False
                return
        self.f = f

    def all_glyphs(self):
        return set(self.f.keys())

    def glyph_order(self):
        return {gn: i for (i, gn) in enumerate(self.f.keys())}

    def groups(self):
        return self.f.groups

    def kerning(self):
        return self.f.kerning

    def postscript_font_name(self):
        try:
            return self.f.info.postscriptFontName
        except:
            pass
        return None

    def path(self):
        return Path(self.f.path)

    def value_string(self, value, rtl=False):
        if rtl:
            return '<{0} 0 {0} 0>'.format(value)
        else:
            return str(value)

    def below_minimum(self, value, minimum):
        return abs(value) < minimum

    def value_is_zero(self, value):
        return value == 0

class DesignspaceKernAdapter(KernAdapter):
    '''
    Adapter for a UFO-based variable font with a designspace file
    '''

    def __init__(self, dsDoc):
        self._has_data = True

        try:
            self.fonts = dsDoc.loadSourceFonts(defcon.Font)
        except DesignSpaceDocumentError as err:
            print(err)
            self._has_data = False

        defaultSource = dsDoc.findDefault()
        if defaultSource is not None:
            self.defaultIndex = dsDoc.sources.index(defaultSource)
        else:
            print('ERROR: did not find source at default location')
            self._has_data = False

        default_location = dsDoc.sources[self.defaultIndex].location
        self.defaultInstanceIndex = None
        for i, inst in enumerate(dsDoc.instances):
            if inst.designLocation == default_location:
                self.defaultInstanceIndex = i
                break

        if self.defaultInstanceIndex is None:
            print('could not find named instance for default location')

        self.shortNames = []
        for i, f in enumerate(self.fonts):
            if i == self.defaultIndex:
                self.shortNames.append(None)
            elif SHORTINSTNAMEKEY in f.lib:
                self.shortNames.append(f.lib[SHORTINSTNAMEKEY])
            else:
                self.shortNames.append(self.make_short_name(dsDoc, i))

        self.dsDoc = dsDoc

    def has_locations(self):
        return True

    def get_locations(self, userUnits = False):
        tagDict = {}
        for axisName in self.dsDoc.getAxisOrder():
            tagDict[axisName] = self.dsDoc.getAxis(axisName).tag
        locDict = {}
        for i, ln in enumerate(self.shortNames):
            if ln is None:
                continue
            axisLocs = self.dsDoc.sources[i].designLocation
            if userUnits:
                axisLocs = self.dsDoc.map_backward(axisLocs)
            axisLocsByTag = {}
            for axisName, axisTag in tagDict.items():
                axisLocsByTag[axisTag] = axisLocs[axisName]
            locDict[ln] = axisLocsByTag
        return locDict


        return {}

    def make_short_name(self, dsDoc, sourceIndex):
        source = dsDoc.sources[sourceIndex]
        location = source.location
        anames = []
        for an in dsDoc.getAxisOrder():
            avstr = "%g" % location[an]
            avstr = avstr.replace('.', 'p')
            avstr = avstr.replace('-', 'n')
            anames.append(avstr)
        return '_'.join(anames)


    def calc_glyph_data(self):
        default_glyph_list = self.fonts[self.defaultIndex].keys()
        default_glyph_set = set(default_glyph_list)

        all_extra_glyphs = set()
        self.glyph_sets = []
        for i, f in enumerate(self.fonts):
            if i == self.defaultIndex:
                self.glyph_sets.append(default_glyph_set)
                continue
            current_glyph_set = set(f.keys())
            self.glyph_sets.append(current_glyph_set)
            extra_glyphs = current_glyph_set - default_glyph_set
            if extra_glyphs:
                source_name = self.dsDoc.sources[i].styleName
                print(f'source {source_name} has these extra glyphs'
                      f'not in default: [{", ".join(extra_glyphs)}]')
                all_extra_glyphs |= extra_glyphs

        self.glyph_set = default_glyph_set | all_extra_glyphs

        self._glyph_order = {gn: i for (i, gn) in enumerate(default_glyph_list)}
        if all_extra_glyphs:
            extras_order = {gn: i for (i, gn) in
                            enumerate(all_extra_glyphs,
                                      start=default_glyph_set.size())}
            self._glyph_order.update(extras_order)

    def all_glyphs(self):
        if not hasattr(self, 'glyph_set'):
            self.calc_glyph_data()
        return self.glyph_set

    def glyph_order(self):
        if not hasattr(self, '_glyph_order'):
            self.calc_glyph_data()
        return self._glyph_order

    def groups(self):
        if hasattr(self, '_groups'):
            return self._groups
        # Calculate partial orderings for groups across all fonts
        group_orderings = defaultdict(lambda: defaultdict(set))
        for i, f in enumerate(self.fonts):
            for g, gl in f.groups.items():
                ordering = group_orderings[g]
                for j, gn in enumerate(gl):
                    ordering[gn] |= set(gl[j+1:])

        # Use the partial orderings to calculate a total ordering,
        # or failing that use the order in which the glyphs were
        # encountered
        self._groups = {}
        for g, ordering in group_orderings.items():
            try:
                ts = TopologicalSorter(ordering)
                l = list(ts.static_order())
            except CycleError as err:
                print(f'glyphs in group {g} have different orderings across '
                      'different sources, ordering cannot be preserved')
                l = ordering.keys()
            self._groups[g] = l

        return self._groups

    def kerning(self):
        if hasattr(self, '_kerning'):
            return self._kerning
        if not hasattr(self, 'glyph_sets'):
            self.calc_glyph_data()

        # Collect full set of kerning pairs across sources
        used_kerning_groups = set()
        all_pairs = set()
        for f in self.fonts:
            for l, r in f.kerning.keys():
                all_pairs.add((l, r))
                if is_kerning_group(l):
                    used_kerning_groups.add(l)
                if is_kerning_group(r):
                    used_kerning_groups.add(r)

        # Find and split groups with mixed sparseness
        groups = self.groups()
        group_remap = {}
        for g in used_kerning_groups:
            sparse_patterns = defaultdict(list)
            for gl in groups[g]:
                pattern = (i for i, glyphs in enumerate(self.glyph_sets)
                           if gl in glyphs)
                assert pattern
                sparse_patterns[frozenset(pattern)].append(gl)
            if len(sparse_patterns) == 1:
                # Nothing sparse or all glyphs sparse in the same way
                continue
            remap_list = []
            for i, group_list in enumerate(sparse_patterns.values()):
                new_group_name = g + GROUPSPLITSUFFIX + str(i)
                groups[new_group_name] = group_list
                remap_list.append(new_group_name)
            del groups[g]
            group_remap[g] = remap_list

        # Build up variable kerning values using remapped groups
        self._kerning = {}
        for l, r in all_pairs:
            pair = (l, r)
            left_list = group_remap.get(l, [l])
            right_list = group_remap.get(r, [r])
            for lelem in left_list:
                lglyph = groups.get(lelem, [lelem])[0]
                for relem in right_list:
                    value = []
                    rglyph = groups.get(relem, [relem])[0]
                    for i, f in enumerate(self.fonts):
                        if (lglyph not in self.glyph_sets[i] or
                            rglyph not in self.glyph_sets[i]):
                            value.append(None)
                            continue
                        if pair in f.kerning:
                            value.append(f.kerning[pair])
                        else:
                            value.append(0)
                    self._kerning[(lelem, relem)] = value

        return self._kerning

    def postscript_font_name(self):
        # Try the designspace document first
        if self.defaultInstanceIndex is not None:
            di = self.dsDoc.instances[self.defaultInstanceIndex] 
            if hasattr(di, 'postScriptFontName'):
                return di.postScriptFontName
        # Then the UFO via defcon
        try:
            return self.fonts[self.defaultIndex].info.postscriptFontName
        except:
            pass
        return None

    def path(self):
        return Path(self.dsDoc.path)

    def value_string(self, value, rtl=False):
        assert len(value) == len(self.fonts)
        format_str =  '<{0} 0 {0} 0>' if rtl else '{0}'
        vcopy = value.copy()
        def_value = vcopy.pop(self.defaultIndex) 
        if all(v is None or v == def_value for v in vcopy):
            return format_str.format(def_value)
        else:
            value_strs = []
            for i, v in enumerate(value):
                if v is None:
                    continue
                vstr = format_str.format(v)
                if i == self.defaultIndex:
                    value_strs.append(vstr)
                else:
                    value_strs.append('@' + self.shortNames[i] + ':' + vstr)
            return '(' + ' '.join(value_strs) + ')'

    def below_minimum(self, value, minimum):
        assert len(value) == len(self.fonts)
        return all((v is None or abs(v) < minimum for v in value))

    def value_is_zero(self, value):
        assert len(value) == len(self.fonts)
        return all((v is None or v == 0 for v in value))


class KerningSanitizer(object):
    '''
    Sanitize UFO kerning and groups:
        - check groups for emtpy glyph list and extraneous glyphs
        - check pairs for extraneous glyphs or groups
        - return filtered kerning and groups dictionaries

    Output a report, if needed.

    '''

    def __init__(self, a):
        self.a = a
        self.kerning = {}
        self.groups = {}
        self.reference_groups = {}

        self.source_glyphs = self.a.all_glyphs()
        self.source_glyph_order = self.a.glyph_order()
        self.source_groups = self.a.groups()
        self.source_kerning = self.a.kerning()

        # empty groups
        self.empty_groups = [
            g for (g, gl) in self.source_groups.items() if not gl
        ]
        # groups containing glyphs not in the UFO
        self.invalid_groups = [
            g for (g, gl) in self.source_groups.items() if not
            set(gl) <= self.source_glyphs
        ]
        # remaining groups
        self.valid_groups = [
            g for g in self.source_groups.keys() if
            g not in [set(self.invalid_groups) | set(self.empty_groups)] and
            is_kerning_group(g)
        ]
        self.valid_items = self.source_glyphs | set(self.valid_groups)
        # pairs containing an invalid glyph or group
        self.invalid_pairs = [
            pair for pair in self.source_kerning.keys() if not
            set(pair) <= self.valid_items
        ]
        invalid_pair_set = set(self.invalid_pairs)
        self.kerning = {
            pair: value for pair, value in self.source_kerning.items() if
            pair not in invalid_pair_set
        }
        self.groups = {
            gn: self.source_groups.get(gn)
            for gn in self.get_used_group_names(self.source_groups)
        }
        self.reference_groups = {
            gn: g_set for gn, g_set in self.source_groups.items() if not
            is_kerning_group(gn)
        }

    def get_used_group_names(self, groups):
        '''
        Return all groups which are actually used in kerning,
        by iterating through valid kerning pairs.
        '''
        group_order = {gn: i for (i, gn) in enumerate(groups.keys())}
        used_groups = []
        for pair in self.kerning.keys():
            used_groups.extend([item for item in pair if is_group(item)])
        return sorted(set(used_groups), key=lambda item: group_order[item])

    def report(self):
        '''
        Report findings of invalid pairs and groups.
        '''
        for group in self.empty_groups:
            print(f'group {group} is empty')
        for group in self.invalid_groups:
            glyph_order = {gn: i for (i, gn) in enumerate(groups.keys())}
            glyph_set = self.source_groups[group]
            extraneous_glyphs = sorted(glyph_set - self.source_glyphs,
                key=lambda item: self.source_glyph_order[item])
            print(
                f'group {group} contains extraneous glyph(s): '
                f'[{", ".join(extraneous_glyphs)}]')

        for pair in self.invalid_pairs:
            invalid_items = sorted(
                set(pair) - self.valid_items, key=pair.index)
            for item in invalid_items:
                if is_group(item):
                    item_type = 'group'
                else:
                    item_type = 'glyph'
                print(
                    f'pair ({pair[0]} {pair[1]}) references non-existent '
                    f'{item_type} {item}'
                )


class KernProcessor(object):
    def __init__(
        self, adapter, groups=None, kerning=None, reference_groups=None,
        option_dissolve=False, ignore_suffix=None
    ):
        self.a = adapter
        # kerning dicts containing pair-value combinations
        self.glyph_glyph = {}
        self.glyph_glyph_exceptions = {}
        self.glyph_group = {}
        self.glyph_group_exceptions = {}
        self.group_glyph_exceptions = {}
        self.group_group = {}

        self.rtl_glyph_glyph = {}
        self.rtl_glyph_glyph_exceptions = {}
        self.rtl_glyph_group = {}
        self.rtl_glyph_group_exceptions = {}
        self.rtl_group_glyph_exceptions = {}
        self.rtl_group_group = {}

        self.pairs_unprocessed = []
        self.pairs_processed = []
        self.group_order = []

        self.groups = groups
        self.kerning = kerning
        self.reference_groups = reference_groups

        self.ignore_suffix = ignore_suffix

        if kerning:
            if option_dissolve:
                groups, kerning = self._dissolve_singleton_groups(
                    groups, kerning)

            self.groups = self._remap_groups(groups)
            self.group_order = sorted(self.groups.keys())
            self.kerning = self._remap_kerning(kerning)

            self.grouped_left = self._get_grouped_glyphs(left=True)
            self.grouped_right = self._get_grouped_glyphs(left=False)
            self.rtl_glyphs = self._get_rtl_glyphs(self.groups)

            self._find_exceptions()

            if self.kerning:
                self._sanityCheck()

    def _remap_name(self, item_name):
        '''
        Remap a single item from public.kern style to @MMK style (if it is
        a group). Otherwise, just pass it through.
        '''
        if 'public.kern1.' in item_name:
            stripped_name = item_name.replace('public.kern1.', '')
            if stripped_name.startswith('@MMK_L_'):
                # UFO2 files contain the @ in the XML, Defcon reads it as
                # 'public.kernX.@MMK'
                return stripped_name
            else:
                # UFO3 files just contain the public.kern notation
                return item_name.replace('public.kern1.', '@MMK_L_')

        elif 'public.kern2.' in item_name:
            stripped_name = item_name.replace('public.kern2.', '')
            if stripped_name.startswith('@MMK_R_'):
                return stripped_name
            else:
                return item_name.replace('public.kern2.', '@MMK_R_')
        else:
            return item_name

    def _remap_groups(self, groups):
        '''
        Remap groups dictionary to not contain public.kern prefixes.
        '''
        return {self._remap_name(gn): gl for gn, gl in groups.items()}

    def _remap_kerning(self, kerning):
        '''
        Remap kerning dictionary to not contain public.kern prefixes.
        '''
        remapped_kerning = {}
        for (left, right), value in kerning.items():
            remapped_pair = (self._remap_name(left), self._remap_name(right))
            remapped_kerning[remapped_pair] = value

        return remapped_kerning

    def _is_rtl(self, pair):
        '''
        Check if a given pair is RTL, by looking for a RTL-specific group
        tag, or membership in an RTL group
        '''

        rtl_group = self.reference_groups.get(RTL_GROUP, [])
        all_rtl_glyphs = set(rtl_group) | set(self.rtl_glyphs)

        if set(pair) & set(all_rtl_glyphs):
            # Any item in the pair is an RTL glyph.
            return True

        for tag in RTL_TAGS:
            # Group tags indicate presence of RTL item.
            # This will work for any pair including a RTL group.
            if any([tag in item for item in pair]):
                return True
        return False

    def _get_rtl_glyphs(self, groups):
        rtl_groups = [gn for gn in groups if is_rtl_group(gn)]
        rtl_glyphs = list(itertools.chain.from_iterable(
            groups.get(rtl_group) for rtl_group in rtl_groups))
        return rtl_glyphs

    def _get_grouped_glyphs(self, left=False):
        '''
        Return lists of glyphs used in groups on left or right side.
        This is used to calculate the subtable size for a given list
        of groups (groupFilterList) used within that subtable.
        '''
        grouped = []

        if left:
            for left, right in self.kerning.keys():
                if is_group(left):
                    grouped.extend(self.groups.get(left))
        else:
            for left, right in self.kerning.keys():
                if is_group(right):
                    grouped.extend(self.groups.get(right))

        return sorted(set(grouped))

    def _dissolve_singleton_groups(self, groups, kerning):
        '''
        Find any (non-RTL) group with a single-item glyph list.
        This group can be dissolved into a single glyph to create more
        glyph-to-glyph pairs. The intention is shifting the load from the
        group-to-group subtable.

        The actual effect of this depends on the group setup.
        '''
        singleton_groups = dict(
            [(group_name, glyphs) for group_name, glyphs in groups.items() if(
                len(glyphs) == 1 and not is_rtl_group(group_name))])
        if singleton_groups:
            dissolved_kerning = {}
            for (left, right), value in kerning.items():
                dissolved_left = singleton_groups.get(left, [left])[0]
                dissolved_right = singleton_groups.get(right, [right])[0]
                dissolved_kerning[(dissolved_left, dissolved_right)] = value

            remaining_groups = dict(
                [(gr_name, glyphs) for gr_name, glyphs in groups.items() if(
                    gr_name not in singleton_groups)]
            )
            return remaining_groups, dissolved_kerning

        else:
            return groups, kerning

    def _sanityCheck(self):
        '''
        Check if the number of kerning pairs input
        equals the number of kerning entries output.
        '''
        num_pairs_total = len(self.kerning.keys())
        num_pairs_processed = len(self.pairs_processed)
        num_pairs_unprocessed = len(self.pairs_unprocessed)

        if num_pairs_total != num_pairs_processed + num_pairs_unprocessed:
            num_entries = num_pairs_processed + num_pairs_unprocessed
            num_unprocessed = num_pairs_total - num_entries
            print(
                'Something went wrong ...\n'
                f'Kerning pairs provided: {num_pairs_total}\n'
                f'Kern entries generated: {num_entries}\n'
                f'Pairs not processed: {num_unprocessed}\n'
            )

    def _explode(self, glyph_list_a, glyph_list_b):
        '''
        Return a list of tuples, containing all possible combinations
        of elements in both input lists.
        '''

        return list(itertools.product(glyph_list_a, glyph_list_b))

    def _find_exceptions(self):
        '''
        Process kerning to find which pairs are exceptions,
        and which are just normal pairs.
        '''

        for pair in list(self.kerning.keys())[::-1]:

            # Skip pairs containing the ignore suffix.
            # Not a very sophisticated feature.
            if self.ignore_suffix:
                if any([item.endswith(self.ignore_suffix) for item in pair]):
                    del self.kerning[pair]
                    continue

        glyph_2_glyph = sorted(
            [pair for pair in self.kerning.keys() if(
                not is_group(pair[0]) and
                not is_group(pair[1]))]
        )
        glyph_2_group = sorted(
            [pair for pair in self.kerning.keys() if(
                not is_group(pair[0]) and
                is_group(pair[1]))]
        )
        group_2_item = sorted(
            [pair for pair in self.kerning.keys() if(
                is_group(pair[0]))]
        )

        # glyph to group pairs:
        # ---------------------
        for (glyph, group) in glyph_2_group:
            pair = glyph, group
            value = self.kerning[pair]
            is_rtl_pair = self._is_rtl(pair)
            if glyph in self.grouped_left:
                # it is a glyph_to_group exception!
                if is_rtl_pair:
                    self.rtl_glyph_group_exceptions[pair] = value
                else:
                    self.glyph_group_exceptions[pair] = value
                self.pairs_processed.append(pair)

            else:
                for grouped_glyph in self.groups[group]:
                    gr_pair = (glyph, grouped_glyph)
                    if gr_pair in glyph_2_glyph:
                        gr_value = self.kerning[gr_pair]
                        # that pair is a glyph_to_glyph exception!
                        if is_rtl_pair:
                            self.rtl_glyph_glyph_exceptions[gr_pair] = gr_value
                        else:
                            self.glyph_glyph_exceptions[gr_pair] = gr_value

                # skip the pair if the value is zero
                if self.a.value_is_zero(value):
                    self.pairs_unprocessed.append(pair)
                    continue

                if is_rtl_pair:
                    self.rtl_glyph_group[pair] = value
                else:
                    self.glyph_group[pair] = value
                self.pairs_processed.append(pair)

        # group to group/glyph pairs:
        # ---------------------------
        exploded_pair_list = []
        exploded_pair_list_rtl = []

        for (group_l, item_r) in group_2_item:
            # the right item of the pair may be a group or a glyph
            pair = (group_l, item_r)
            value = self.kerning[pair]
            is_rtl_pair = self._is_rtl(pair)
            l_group_glyphs = self.groups[group_l]

            if is_group(item_r):
                r_group_glyphs = self.groups[item_r]
            else:
                # not a group, therefore a glyph
                if item_r in self.grouped_right:
                    # it is a group_to_glyph exception!
                    if is_rtl_pair:
                        self.rtl_group_glyph_exceptions[pair] = value
                    else:
                        self.group_glyph_exceptions[pair] = value
                    self.pairs_processed.append(pair)
                    continue  # It is an exception, so move on to the next pair

                else:
                    r_group_glyphs = [item_r]

            # skip the pair if the value is zero
            if self.a.value_is_zero(value):
                self.pairs_unprocessed.append(pair)
                continue

            if is_rtl_pair:
                self.rtl_group_group[pair] = value
                exploded_pair_list_rtl.extend(
                    self._explode(l_group_glyphs, r_group_glyphs))
            else:
                self.group_group[pair] = value
                exploded_pair_list.extend(
                    self._explode(l_group_glyphs, r_group_glyphs))
                # list of all possible pair combinations for the
                # @class @class kerning pairs of the font.
            self.pairs_processed.append(pair)

        # Find the intersection of the exploded pairs with the glyph_2_glyph
        # pairs collected above. Those must be exceptions, as they occur twice
        # (once in class-kerning, once as a single pair).
        self.exception_pairs = set(exploded_pair_list) & set(glyph_2_glyph)
        self.exception_pairs_rtl = set(exploded_pair_list_rtl) & set(glyph_2_glyph)

        for pair in self.exception_pairs:
            self.glyph_glyph_exceptions[pair] = self.kerning[pair]

        for pair in self.exception_pairs_rtl:
            self.rtl_glyph_glyph_exceptions[pair] = self.kerning[pair]

        # finally, collect normal glyph to glyph pairs:
        # ---------------------------------------------
        # NB: RTL glyph-to-glyph pairs can only be identified if its
        # glyphs are in the @RTL_KERNING group.

        for glyph_1, glyph_2 in glyph_2_glyph:
            pair = glyph_1, glyph_2
            value = self.kerning[pair]
            is_rtl_pair = self._is_rtl(pair)
            if any(
                [glyph_1 in self.grouped_left, glyph_2 in self.grouped_right]
            ):
                # it is an exception!
                # exceptions expressed as glyph-to-glyph pairs -- these cannot
                # be filtered and need to be added to the kern feature
                # ---------------------------------------------
                if is_rtl_pair:
                    self.rtl_glyph_glyph_exceptions[pair] = value
                else:
                    self.glyph_glyph_exceptions[pair] = value
                self.pairs_processed.append(pair)
            else:
                if (
                    pair not in self.glyph_glyph_exceptions and
                    pair not in self.rtl_glyph_glyph_exceptions
                ):
                    if self._is_rtl(pair):
                        self.rtl_glyph_glyph[pair] = self.kerning[pair]
                    else:
                        self.glyph_glyph[pair] = self.kerning[pair]
                    self.pairs_processed.append(pair)


class MakeMeasuredSubtables(object):

    def __init__(self, kernDict, kerning, groups, maxSubtableSize):

        self.kernDict = kernDict
        self.subtables = []
        self.numberOfKernedGlyphs = self._getNumberOfKernedGlyphs(
            kerning, groups)

        coverageTableSize = 2 + (2 * self.numberOfKernedGlyphs)
        # maxSubtableSize = 2 ** 14

        print('coverage table size:', coverageTableSize)
        print('  max subtable size:', maxSubtableSize)
        # If Extension is not used, coverage and class subtables are
        # pushed to very end of GPOS block.
        #
        # Order is: script list, lookup list, feature list, then
        # table that contains lookups.

        # GPOS table size
        # All GPOS lookups need to be considered
        # Look up size of all GPOS lookups

        measuredSubtables = []
        leftItems = sorted(set([left for left, right in self.kernDict.keys()]))

        groupedGlyphsLeft = set([])
        groupedGlyphsRight = set([])
        usedGroupsLeft = set([])
        usedGroupsRight = set([])

        subtable = []

        for item in leftItems:
            itemPair = [
                pair for pair in self.kernDict.keys() if pair[0] == item]

            for left, right in itemPair:
                groupedGlyphsLeft.update(groups.get(left, [left]))
                groupedGlyphsRight.update(groups.get(right, [right]))
                usedGroupsLeft.add(left)
                usedGroupsRight.add(right)

                leftClassSize = 6 + (2 * len(groupedGlyphsLeft))
                rightClassSize = 6 + (2 * len(groupedGlyphsRight))
                subtableMetadataSize = (
                    coverageTableSize + leftClassSize + rightClassSize)
                subtable_size = (
                    16 + len(usedGroupsLeft) * len(usedGroupsRight) * 2)

            if subtableMetadataSize + subtable_size < maxSubtableSize:
                subtable.append(item)

            else:
                measuredSubtables.append(subtable)

                subtable = []
                subtable.append(item)
                groupedGlyphsLeft = set([])
                groupedGlyphsRight = set([])
                usedGroupsLeft = set([])
                usedGroupsRight = set([])

        # Last subtable:
        if len(subtable):
            measuredSubtables.append(subtable)

        for leftItemList in measuredSubtables:
            stDict = {}
            for leftItem in leftItemList:
                for pair in [
                    pair for pair in self.kernDict.keys() if
                    pair[0] == leftItem
                ]:
                    stDict[pair] = kerning.get(pair)
            self.subtables.append(stDict)

    def _getNumberOfKernedGlyphs(self, kerning, groups):
        leftList = []
        rightList = []
        for left, right in kerning.keys():
            leftList.extend(groups.get(left, [left]))
            rightList.extend(groups.get(right, [right]))

        # This previous approach counts every glyph only once,
        # which I think might be wrong:
        # Coverage table includes left side glyphs only.
        # Could measure only left side in order to get size of coverage table.
        allKernedGlyphs = set(leftList) | set(rightList)
        return len(allKernedGlyphs)
        # (Assume that a glyph must be counted twice when kerned
        # on both sides).
        # return len(set(leftList)) + len(set(rightList))

        # every time you get to 48 k add UseExtension keyword
        # mark is a gpos feature too.


class run(object):

    def __init__(self, adapter, args=None):

        if not args:
            args = Defaults()

        assert adapter.has_data()

        self.a = adapter
        self.minKern = args.min_value
        self.write_subtables = args.write_subtables
        self.subtable_size = args.subtable_size
        self.write_trimmed_pairs = args.write_trimmed_pairs
        self.dissolve_single = args.dissolve_single
        self.ignore_suffix = args.ignore_suffix
        self.trimmedPairs = 0

        ks = KerningSanitizer(self.a)
        ks.report()
        kp = KernProcessor(
            self.a, ks.groups, ks.kerning, ks.reference_groups,
            self.dissolve_single, self.ignore_suffix)

        fea_data = self._make_fea_data(kp)
        self.header = self.make_header(args)
        output_path = self.a.path().parent / args.output_name
        self.write_fea_data(fea_data, output_path)
        if not args.no_locations and self.a.has_locations():
            locations_path = self.a.path().parent / args.locations_name
            self.write_locations(self.a, locations_path, args.user_values)

    def make_header(self, args):
        ps_name = self.a.postscript_font_name()
        header = []
        if args.write_timestamp:
            header.append(f'# Created: {time.ctime()}')
        header.append(f'# PS Name: {ps_name}')
        header.append(f'# MinKern: +/- {args.min_value} inclusive')
        return header

    def _dict2pos(self, pair_value_dict, minimum=0, enum=False, rtl=False):
        '''
        Turn a dictionary to a list of kerning pairs. Kerning pairs whose
        absolute value does not exceed a given threshold can be filtered.
        '''

        data = []
        trimmed = 0
        for (item_1, item_2), value in pair_value_dict.items():

            value_str = self.a.value_string(value, rtl)

            posLine = f'pos {item_1} {item_2} {value_str};'

            if enum:
                data.append('enum ' + posLine)
            else:
                if self.a.below_minimum(value, minimum):
                    if self.write_trimmed_pairs:
                        data.append('# ' + posLine)
                        trimmed += 1
                    else:
                        continue
                else:
                    data.append(posLine)

        self.trimmedPairs += trimmed
        data.sort()

        return '\n'.join(data)

    def _build_st_output(self, st_list, comment, rtl=False):
        st_output = []
        st_break = '\nsubtable;'

        if sum([len(subtable.keys()) for subtable in st_list]) > 0:
            st_output.append(comment)

        for table in st_list:
            if len(table):

                if rtl:
                    self.num_subtables_rtl += 1
                    if self.num_subtables_rtl > 1:
                        st_output.append(st_break)

                else:
                    self.num_subtables += 1
                    if self.num_subtables > 1:
                        st_output.append(st_break)

                st_output.append(
                    self._dict2pos(table, self.minKern, rtl=rtl))
        print(f'{self.num_subtables} subtables created')
        return st_output

    def _make_fea_data(self, kp):
        # Build the output data.

        output = []
        # ---------------
        # list of groups:
        # ---------------
        for grp_name in kp.group_order:
            glyphList = kp.groups[grp_name]
            output.append(f'{grp_name} = [{" ".join(glyphList)}];')

        # ------------------
        # LTR kerning pairs:
        # ------------------
        order_ltr = [
            # container_dict, minKern, comment, enum
            (kp.glyph_glyph, self.minKern,
                '\n# glyph, glyph:', False),
            (kp.glyph_glyph_exceptions, 0,
                '\n# glyph, glyph exceptions:', False),
            (kp.glyph_group_exceptions, 0,
                '\n# glyph, group exceptions:', True),
            (kp.group_glyph_exceptions, 0,
                '\n# group, glyph exceptions:', True),
        ]

        order_ltr_ext = [
            # in case no subtables are desired
            (kp.glyph_group, self.minKern, '\n# glyph, group:', False),
            (kp.group_group, self.minKern, '\n# group, group/glyph:', False),
        ]

        # ------------------
        # RTL kerning pairs:
        # ------------------
        order_rtl = [
            # container_dict, minKern, comment, enum
            (kp.rtl_glyph_glyph, self.minKern,
                '\n# RTL glyph, glyph:', False),
            (kp.rtl_glyph_glyph_exceptions, 0,
                '\n# RTL glyph, glyph exceptions:', False),
            (kp.rtl_glyph_group_exceptions, 0,
                '\n# RTL glyph, group exceptions:', True),
            (kp.rtl_group_glyph_exceptions, 0,
                '\n# RTL group, glyph exceptions:', True),
        ]

        order_rtl_ext = [
            # in case no subtables are desired
            (kp.rtl_glyph_group, self.minKern,
                '\n# RTL glyph, group:', False),
            (kp.rtl_group_group, self.minKern,
                '\n# RTL group, group/glyph:', False)
        ]

        if not self.write_subtables:
            order_ltr.extend(order_ltr_ext)
            order_rtl.extend(order_rtl_ext)

        # Check if LTR pairs exist
        ltr_container_dicts = [i[0] for i in order_ltr_ext + order_ltr]
        if any(ltr_container_dicts):

            for container_dict, minKern, comment, enum in order_ltr:
                if container_dict:
                    output.append(comment)
                    output.append(
                        self._dict2pos(container_dict, minKern, enum))

            if self.write_subtables:
                self.num_subtables = 0

                glyph_to_class_subtables = MakeMeasuredSubtables(
                    kp.glyph_group, kp.kerning, kp.groups,
                    self.subtable_size).subtables
                output.extend(self._build_st_output(
                    glyph_to_class_subtables, '\n# glyph, group:'))

                class_to_class_subtables = MakeMeasuredSubtables(
                    kp.group_group, kp.kerning, kp.groups,
                    self.subtable_size).subtables
                output.extend(self._build_st_output(
                    class_to_class_subtables,
                    '\n# group, glyph and group, group:')
                )

        # Check if RTL pairs exist
        rtl_container_dicts = [i[0] for i in order_rtl_ext + order_rtl]
        if any(rtl_container_dicts):

            lookup_rtl_open = (
                '\n\nlookup RTL_kerning {\n'
                'lookupflag RightToLeft IgnoreMarks;\n')
            lookup_rtl_close = '\n\n} RTL_kerning;\n'

            output.append(lookup_rtl_open)

            for container_dict, minKern, comment, enum in order_rtl:
                if container_dict:
                    output.append(comment)
                    output.append(
                        self._dict2pos(
                            container_dict, minKern, enum, rtl=True))

            if self.write_subtables:
                self.num_subtables_rtl = 0

                rtl_glyph_class_subtables = MakeMeasuredSubtables(
                    kp.rtl_glyph_group, kp.kerning, kp.groups,
                    self.subtable_size).subtables
                output.extend(self._build_st_output(
                    rtl_glyph_class_subtables,
                    '\n# RTL glyph, group:', rtl=True))

                rtl_class_class_subtables = MakeMeasuredSubtables(
                    kp.rtl_group_group, kp.kerning, kp.groups,
                    self.subtable_size).subtables
                output.extend(self._build_st_output(
                    rtl_class_class_subtables,
                    '\n# RTL group, glyph and group, group:', rtl=True))

            output.append(lookup_rtl_close)

        return output

    def write_fea_data(self, data, output_path):

        print(f'Saving {output_path.name} file...')

        if self.trimmedPairs > 0:
            print(f'Trimmed pairs: {self.trimmedPairs}')

        with open(output_path, 'w') as blob:
            blob.write('\n'.join(self.header))
            blob.write('\n\n')
            if data:
                blob.write('\n'.join(data))
                blob.write('\n')

        print(f'Output file written to {output_path}')

    def write_locations(self, adapter, locations_path, userUnits = False):

        print(f'Saving {locations_path.name} file...')

        data = ['# Named locations', '']

        unit = 'u' if userUnits else 'd'
        for name, axisLocs in adapter.get_locations(userUnits).items():
            locationStr = ', '.join(('%s=%g%s' % (tag, val, unit) for
                                     tag, val in axisLocs.items()))
            data.append(f'locationDef {locationStr} @{name};')

        with open(locations_path, 'w') as blob:
            blob.write('\n'.join(data))
            blob.write('\n')

        print(f'Output file written to {locations_path}')


def check_input_file(parser, file_name):
    file_path = Path(file_name)
    if file_path.suffix.lower() == '.ufo':
        if not file_path.exists():
            parser.error(f'{file_name} does not exist')
        elif not file_path.is_dir():
            parser.error(f'{file_name} is not a directory')
    elif file_path.suffix.lower() == '.designspace':
        if not file_path.exists():
            parser.error(f'{file_name} does not exist')
        elif not file_path.is_file():
            parser.error(f'{file_name} is not a file')
    else:
        parser.error(f'Unrecognized input file type')
    return file_name

def get_args(args=None):

    defaults = Defaults()
    parser = argparse.ArgumentParser(
        description=__doc__,
        formatter_class=argparse.ArgumentDefaultsHelpFormatter
    )

    parser.add_argument(
        'input_file',
        type=lambda f: check_input_file(parser, f),
        help='input UFO file')

    parser.add_argument(
        '-o', '--output_name',
        action='store',
        default=defaults.output_name,
        help='change the output file name')

    parser.add_argument(
        '-l', '--locations_name',
        action='store',
        default=defaults.locations_name,
        help='change the locations file name (variable font only)')

    parser.add_argument(
        '-m', '--min_value',
        action='store',
        default=defaults.min_value,
        metavar='INT',
        type=int,
        help='minimum kerning value')

    parser.add_argument(
        '-s', '--write_subtables',
        action='store_true',
        default=defaults.write_subtables,
        help='write subtables')

    parser.add_argument(
        '--subtable_size',
        action='store',
        default=defaults.subtable_size,
        metavar='INT',
        type=int,
        help='specify max subtable size')

    parser.add_argument(
        '-t', '--write_trimmed_pairs',
        action='store_true',
        default=defaults.write_trimmed_pairs,
        help='write trimmed pairs to output file (as comments)')

    parser.add_argument(
        '--write_timestamp',
        action='store_true',
        default=defaults.write_timestamp,
        help='write time stamp in header of output file')

    parser.add_argument(
        '--no_locations',
        action='store_true',
        default=defaults.no_locations,
        help='Do not write locations file (variable font only)')

    parser.add_argument(
        '-u', '--user_values',
        action='store_true',
        default=defaults.user_values,
        help='For variable fonts, output user axis locations '
             'rather than design axis locations')

    parser.add_argument(
        '--dissolve_single',
        action='store_true',
        default=defaults.dissolve_single,
        help='dissolve single-element groups to glyph names')

    parser.add_argument(
        '--ignore_suffix',
        action='store',
        default=defaults.ignore_suffix,
        metavar='.xxx',
        help=(
            'do not write pairs containing this suffix. '
            'This is a rudimentary feature, not working if a '
            'suffixed glyph is part of a kerning group.'
        )
    )

    return parser.parse_args(args)


def main(test_args=None):
    args = get_args(test_args)
    input_path = Path(args.input_file)
    if input_path.is_file():
        dsDoc = DesignSpaceDocument.fromfile(input_path)
        a = DesignspaceKernAdapter(dsDoc)
    else:
        a = UFOKernAdapter(defcon.Font(args.input_file))
    if a.has_data():
        run(a, args)


if __name__ == '__main__':
    main()
