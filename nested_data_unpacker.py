import json
from collections import OrderedDict, defaultdict
from copy import copy
from io import BytesIO
from os import SEEK_END
from sys import argv

from randomtools.utils import fake_yaml as yaml
from randomtools.utils import search_nested_key


def hexify(s):
    if isinstance(s, int):
        return f'{s:0>2x}'
    return ' '.join([f'{w:0>2x}' for w in s])


class BytesEncoder(json.JSONEncoder):
    def default(self, o):
        if isinstance(o, bytes):
            return hexify(o)
        else:
            return super().default(o)


class Unpacker:
    class PointerTable:
        def __init__(self, section):
            self.section = section

        def __len__(self):
            return self.num_pointers * self.pointer_length

        @property
        def config(self):
            return self.section.config

        @property
        def num_pointers(self):
            num_pointers = self.section.get_setting('num_pointers')
            if isinstance(num_pointers, str):
                num_pointers = self.section.evaluate(num_pointers)
            if num_pointers is not None:
                assert isinstance(num_pointers, int)
                return num_pointers
            assert isinstance(self.section.unpacked, list)
            return len(self.section.unpacked)

        @property
        def pointer_length(self):
            return self.section.get_setting('pointer_length')

        @property
        def bytecode(self):
            bytecode = b''
            byteorder = self.section.get_setting('byteorder')
            relative_to = self.section.get_setting('relative_to')
            offset = 0
            if isinstance(relative_to, str):
                assert relative_to.startswith('@')
                label, offset = self.section.split_address_label(relative_to)
                relative_to = self.section.get_address(relative_to)
            if relative_to is None:
                return None
            relative_to += offset

            for pointer in self.pointers:
                slabel, label, offset = None, None, None
                if isinstance(pointer, str):
                    assert pointer.startswith('@')
                    assert '@' not in pointer[1:]
                    slabel, offset = self.section.split_address_label(pointer)
                    assert slabel.startswith('@')
                    assert not slabel.startswith('@@')
                    label = slabel[1:]
                    if self.section.tree[label].unpacked is None:
                        value = 0
                    else:
                        value = self.section.get_address(slabel)
                        if value is not None:
                            value = value + offset - relative_to
                        else:
                            return None
                elif pointer is None:
                    value = 0
                assert value >= 0
                bytecode += value.to_bytes(length=self.pointer_length,
                                           byteorder=byteorder)
            return bytecode


    INHERITABLE_SETTINGS = {
        'byteorder', 'pointer_length',
        }

    def __init__(self, config, label=None, parent=None):
        if label is None:
            assert parent is None
            label = '_root'
        else:
            assert not label.startswith('_')
        assert label is not None
        assert not label.startswith('@')
        self.label = label
        self.config = config
        self._config_values = {}
        self.children = []
        self.parent = parent
        if self.parent is not None:
            self.parent.children.append(self)
        self._addresses = None
        self.sections = None
        if self.parent is None:
            self._tree = {}
            self._addresses = defaultdict(set)
            self._address_cache = {}
            self._nulled_addresses = set()
            self._alignments = {}
            self.sections = {}
        elif self.is_recursive:
            self.sections = {}

        if self.label in self.tree:
            raise Exception(f'Duplicate section label: {self.label}')
        self.index = len(self.tree)
        assert self.index not in {s.index for s in self.tree.values()}
        self.tree[self.label] = self

        if 'start' in self.config:
            self.addresses[f'@{label}'].add(self.config['start'])

        if 'finish' in self.config:
            self.addresses[f'@@{label}'].add(self.config['finish'])

        if 'align' in self.config:
            self.alignments[f'@{label}'] = self.config['align']

        if 'total_length' in self.config:
            total_length = self.config['total_length']
            self.addresses[f'@@{label}'].add(f'@{label},{total_length}')

        if self.sections is not None:
            for key in self.config:
                if not isinstance(self.config[key], dict):
                    continue
                self.sections[key] = Unpacker(self.config[key], key,
                                              parent=self)
                assert self.children[-1] == self.sections[key]

        if self.is_pointers:
            self.check_pointer_dimensions()

        if self.is_regular_list or self.is_pointed_list:
            self.check_list_dimensions()

        if not self.parent:
            #self.propagate_addresses()
            self.preclean()
            self.propagate_addresses()

    @property
    def is_recursive(self):
        return 'data_type' in self.config and \
                self.config['data_type'] == 'recursive'

    @property
    def is_pointers(self):
        return 'data_type' in self.config and \
                self.config['data_type'] == 'pointers'

    @property
    def is_pointed_list(self):
        return 'data_type' in self.config and \
                self.config['data_type'] == 'pointed_list'

    @property
    def is_regular_list(self):
        return 'data_type' in self.config and \
                self.config['data_type'] == 'regular_list'

    @property
    def root(self):
        if hasattr(self, '_root'):
            return self._root
        if not self.parent:
            self._root = self
            return self.root
        self._root = self.parent.root
        return self.root

    @property
    def tree(self):
        return self.root._tree

    @property
    def descendents(self):
        descendents = set(self.children)
        for c in self.children:
            descendents |= c.descendents
        return descendents

    @property
    def addresses(self):
        return self.root._addresses

    @property
    def address_cache(self):
        return self.root._address_cache

    @property
    def nulled_addresses(self):
        return self.root._nulled_addresses

    @property
    def alignments(self):
        return self.root._alignments

    @property
    def start(self):
        return self.get_address(self.slabel)

    @property
    def finish(self):
        return self.get_address(self.flabel)

    @property
    def starts(self):
        addresses = self.addresses[self.slabel]
        if addresses:
            return addresses

    @property
    def finishes(self):
        addresses = self.addresses[self.flabel]
        if addresses:
            return addresses

    @property
    def slabel(self):
        return f'@{self.label}'

    @property
    def flabel(self):
        return f'@@{self.label}'

    def get_setting(self, attribute, caller=None):
        if caller is None:
            caller = self
        if caller is self and attribute in self._config_values:
            return self._config_values[attribute]
        result = None
        if attribute in self.config:
            result = self.config[attribute]
        elif attribute in self.INHERITABLE_SETTINGS and \
                self.parent is not None:
            result = self.parent.get_setting(attribute, caller=caller)
        if isinstance(result, str) and result.startswith('@'):
            test = self.get_address(result)
            if test is not None:
                result = test
        return result

    def set_value(self, attribute, value):
        self._config_values[attribute] = value

    def evaluate(self, expression):
        if isinstance(expression, int):
            return expression
        if not expression.startswith('{'):
            raise NotImplementedError
        assert expression.endswith('}')
        expression = expression[1:-1]
        if '.' in expression:
            label, setting = expression.split('.')
        else:
            label = expression
            setting = None

        section = self.tree[label]
        if setting is not None:
            value = section.get_setting(setting)
            return value

        assert section.config['data_type'] == 'blob'
        if hasattr(section, 'packed'):
            section.packed.seek(0)
            blob = section.packed.read()
        elif hasattr(section, 'unpacked'):
            blob = section.unpacked
        value = int.from_bytes(blob,
                               byteorder=section.get_setting('byteorder'))
        return value

    def split_address_label(self, label):
        if ',' in label:
            label, offset = label.split(',')
            offset = int(offset)
        else:
            offset = 0
        return label, offset

    def get_address(self, label):
        if label in self.address_cache:
            return self.address_cache[label]
        assert label.startswith('@')
        label, offset = self.split_address_label(label)
        key = label
        assert not key.startswith('@@@')
        addresses = {a for a in self.addresses[key] if isinstance(a, int)}
        if not addresses:
            return None
        if len(addresses) == 1:
            address = addresses.pop() + offset
            assert label not in self.address_cache
            self.address_cache[label] = address
            return self.get_address(label)
        raise Exception(f'{key} address conflict: {addresses}')

    def check_pointer_dimensions(self):
        num_pointers = self.get_setting('num_pointers')
        pointers = self.get_setting('pointers')
        if pointers and num_pointers is None:
            num_pointers = len(pointers)
            self.set_value('num_pointers', num_pointers)
        if pointers and num_pointers is not None:
            assert num_pointers == len(pointers)
        pointer_length = self.get_setting('pointer_length')
        if None not in (num_pointers, pointer_length, self.start):
            key = self.flabel
            finish = self.start + (num_pointers * pointer_length)
            if finish not in self.addresses[key]:
                self.addresses[key].add(finish)

    def check_list_dimensions(self):
        num_items = self.get_setting('num_items')
        item_size = self.get_setting('item_size')

        if self.start is not None and self.finish is not None and \
                (num_items, item_size).count(None) == 1:
            total_length = self.finish - self.start
            if num_items is None:
                self.set_value('num_items', total_length // item_size)
            if item_size is None:
                self.set_value('item_size', total_length // num_items)
            num_items = self.get_setting('num_items')
            item_size = self.get_setting('item_size')

        if None not in (num_items, item_size, self.start):
            total_length = self.evaluate(num_items) * self.evaluate(item_size)
            key = self.flabel
            finish = self.start + total_length
            if finish not in self.addresses[key]:
                self.addresses[key].add(finish)
                self.propagate_addresses()

    def propagate_addresses(self, seed=None):
        if isinstance(seed, str):
            seed = {seed}
        elif seed is None:
            seed = set(self.addresses.keys())
        updated = False
        local_updated = True
        done_pairs = set()
        while local_updated:
            local_updated = False
            resolved = defaultdict(set)
            for key1 in sorted(seed):
                assert not isinstance(key1, int)
                key1_address = self.get_address(key1)
                for key2 in list(self.addresses[key1]):
                    if key1 == key2:
                        continue
                    if (key1, key2) in done_pairs:
                        continue
                    done_pairs.add((key1, key2))
                    if isinstance(key2, int):
                        resolved[key2].add(key1)
                        continue
                    if key2 == '!eof':
                        if not key1.startswith('@@'):
                            flabel = f'@{key1}'
                            if '!eof' not in self.addresses[flabel]:
                                self.addresses[flabel].add('!eof')
                                seed.add(flabel)
                                local_updated = True
                        label = key1[2:]
                        length = self.root.get_packed_length()
                        if length is None:
                            continue
                        key2_address = f'@{self.root.label},{length}'
                        if key2_address not in self.addresses[key1]:
                            self.addresses[key1].add(key2_address)
                            local_updated = True
                        continue
                    key2, offset = self.split_address_label(key2)
                    if offset:
                        reverse_key = f'{key1},{-offset}'
                    else:
                        reverse_key = key1

                    if reverse_key not in self.addresses[key2]:
                        self.addresses[key2].add(reverse_key)
                        local_updated = True
                        seed.add(key2)

                    key2_address = self.get_address(key2)
                    if key2_address is None and key1_address is not None:
                        key2_address = key1_address - offset
                        assert key2_address > 0
                        if key2_address not in self.addresses[key2]:
                            self.addresses[key2].add(key2_address)
                            local_updated = True
                            seed.add(key2)
                    if key1_address is None and key2_address is not None:
                        key1_address = key2_address + offset
                        assert key1_address > 0
                        if key1_address not in self.addresses[key1]:
                            self.addresses[key1].add(key1_address)
                            local_updated = True

            for address in resolved:
                keys = resolved[address]
                if len(keys) <= 1:
                    continue
                labels = set()
                for key in keys:
                    labels |= self.addresses[key]
                for key in keys:
                    if labels > self.addresses[key]:
                        seed.add(key)
                        self.addresses[key] |= labels
                        local_updated = True

            updated = updated or local_updated

        self.verify_alignment()
        return updated

    def verify_alignment(self):
        updated = True
        while updated:
            updated = False
            for label in sorted(self.alignments):
                label_align = self.alignments[label]
                if isinstance(label_align, int):
                    m, r = label_align, 0
                else:
                    m, r = label_align
                for other in self.addresses[label]:
                    if isinstance(other, int):
                        if (other % m) != r:
                            raise Exception(
                                    f'FAILED ALIGNMENT {label}: '
                                    f'{other:x} % {m} != {r}')
                        continue
                    other, offset = self.split_address_label(other)
                    r2 = (r - offset) % m
                    other_align = m
                    if r2:
                        other_align = (m, r2)
                    if other in self.alignments:
                        assert self.alignments[other] == other_align
                    else:
                        self.alignments[other] = other_align
                        updated = True

    def guess_start(self):
        if self.start:
            return

        if self.parent is None:
            self.addresses[self.slabel].add(0)
            return

    def guess_finish(self, override=False):
        if self.finish is not None:
            return

        if 'finish' in self.config and not override:
            return

        if self.is_regular_list or self.is_pointed_list:
            self.check_list_dimensions()

        if self.is_pointers:
            self.check_pointer_dimensions()

        if self.parent is None:
            self.addresses[self.flabel].add('!eof')
            return

        # double check
        if self.finish is not None:
            return

        uncertain_address = False
        candidates = set()
        for child in self.parent.children:
            label = child.slabel
            if label in self.nulled_addresses:
                continue
            address = self.get_address(label)
            if address is None:
                uncertain_address = True
                continue
            candidates.add(address)

        if self.start not in candidates:
            return
        candidates = {a for a in candidates if a > self.start}
        self.propagate_addresses({c.flabel for c in
                                  self.parent.descendents | {self.parent}})

        address = self.parent.finish
        if address is not None:
            assert address >= self.start
            candidates.add(address)

        if candidates:
            self.addresses[self.flabel].add(min(candidates))

    def guess_uncle_finish(self):
        if self.finish is not None:
            return
        if self.parent is None:
            return
        if self.parent.parent is None:
            return
        uncles = self.parent.parent.children
        parent_index = uncles.index(self.parent)
        if len(uncles) > parent_index + 1:
            uncle = uncles[parent_index + 1]
            self.addresses[self.parent.flabel].add(uncle.slabel)
        self.propagate_addresses(self.parent.flabel)

    def check_null_pointer(self, pointer):
        if pointer in (None, 0):
            return True
        MAX_POINTER = (1 << (self.get_setting('pointer_length') * 8)) - 1
        NULL_POINTERS = (None, 0, MAX_POINTER)
        return pointer in NULL_POINTERS

    def guess_num_pointers(self):
        assert self.get_setting('num_pointers') is None
        pointers = self.get_setting('pointers')
        if pointers is not None:
            self.set_value('num_pointers', len(pointers))
            return

        byteorder = self.get_setting('byteorder')
        pointer_length = self.get_setting('pointer_length')
        relative_to = self.get_setting('relative_to')
        assert self.start >= self.parent.start
        self.parent.packed.seek(self.start-self.parent.start)
        pointers = []
        non_null = set()
        while True:
            if non_null:
                lowest = min(non_null)
                pointer_area = pointer_length * len(pointers)
                if lowest == pointer_area:
                    break
                elif lowest <= pointer_area:
                    pointers = pointers[:-1]
                    break

            pointer = self.parent.packed.read(pointer_length)
            if len(pointer) < pointer_length:
                break
            pointer = int.from_bytes(pointer, byteorder)

            if not self.check_null_pointer(pointer):
                pointer += (relative_to - self.parent.start)
                pointers.append(pointer)
                non_null.add(pointer)
            else:
                pointers.append(None)

        self.set_value('num_pointers', len(pointers))

    def get_pointer_table_size(self):
        if hasattr(self, '_pointer_table_size'):
            assert self.finish == self._pointer_table_size
            return self._pointer_table_size
        num_pointers = self.get_setting('num_pointers')

        if num_pointers is None:
            self.guess_num_pointers()
        elif isinstance(num_pointers, str):
            self.set_value('num_pointers', self.evaluate(num_pointers))
        assert self.get_setting('num_pointers') is not None

        self.check_pointer_dimensions()
        assert self.finish is not None
        self.propagate_addresses(self.flabel)
        self._pointer_table_size = self.finish
        return self.get_pointer_table_size()

    def preclean(self):
        self.guess_start()
        self.guess_finish()
        for c in self.children:
            c.preclean()

    def set_packed(self, packed=None):
        if hasattr(self, '_packed_length'):
            del(self._packed_length)

        if packed is not None:
            if not isinstance(packed, BytesIO):
                packed = BytesIO(packed)
            self.packed = packed
            self.propagate_addresses({self.slabel, self.flabel})
            return

        assert self.parent is not None
        if not hasattr(self.parent, 'packed'):
            self.parent.set_packed()
        if self.start is None and self.slabel in self.nulled_addresses:
            self.packed = None
            return

        self.guess_finish()
        finish = self.finish
        if finish is None and self.is_pointers:
            finish = self.get_pointer_table_size()
        if finish is None:
            self.guess_finish(override=True)
            finish = self.finish
        if finish is None:
            self.propagate_addresses()
            finish = self.finish
        if None in (self.start, finish):
            import pdb; pdb.set_trace()
        assert None not in (self.start, finish)
        assert finish >= self.start
        assert None not in (self.parent.start, self.parent.finish)
        assert self.parent.start <= self.start <= finish <= self.parent.finish
        self.parent.packed.seek(self.start-self.parent.start)
        data = self.parent.packed.read(finish-self.start)
        assert len(data) == finish-self.start
        self.packed = BytesIO(data)

    def get_packed_length(self):
        if not hasattr(self, 'packed'):
            return None
        if hasattr(self, '_packed_length'):
            return self._packed_length
        self.packed.seek(0)
        self._packed_length = len(self.packed.read())
        return self.get_packed_length()

    def unpack_pointers(self):
        pointer_names = self.get_setting('pointers')
        byteorder = self.get_setting('byteorder')
        pointer_length = self.get_setting('pointer_length')
        relative_to = self.get_setting('relative_to')
        if relative_to is None:
            relative_to = self.start
        elif isinstance(relative_to, str):
            relative_to = self.get_address(relative_to)
        pointers = []
        num_pointers = self.get_setting('num_pointers')
        if pointer_names is None:
            if num_pointers is not None:
                pointer_names = [None] * self.get_setting('num_pointers')
            else:
                self.packed.seek(0, SEEK_END)
                if self.packed.tell() == 0:
                    pointer_names = []
        if num_pointers:
            assert len(pointer_names) == num_pointers
        self.packed.seek(0)
        lowest = None
        propagate_seed = set()
        for i, pointer_name in enumerate(pointer_names):
            value = self.packed.read(pointer_length)
            value = int.from_bytes(value, byteorder=byteorder)
            if self.check_null_pointer(value):
                if isinstance(pointer_name, str):
                    self.nulled_addresses.add(pointer_name)
                    slabel = pointer_name
                    flabel = f'@{slabel}'
                    self.addresses[slabel].add(flabel)
                    self.addresses[flabel].add(slabel)
                    propagate_seed |= {slabel, flabel}
                pointers.append(None)
                continue
            pointers.append(value)
            value += relative_to
            lowest = value if lowest is None else min(lowest, value)
            if isinstance(pointer_name, str) \
                    and pointer_name.startswith('@'):
                self.addresses[pointer_name].add(value)
                propagate_seed.add(pointer_name)
        pointers = [None if self.check_null_pointer(p) else p
                    for p in pointers]

        for section in self.tree.values():
            if pointers and lowest is None:
                break
            if not section.is_pointed_list:
                continue
            if section.config['linked_pointers'] != self.label:
                continue
            if lowest is not None and lowest not in section.starts:
                self.addresses[section.slabel].add(lowest)
                propagate_seed.add(section.slabel)
            elif lowest is None and not pointers:
                self.addresses[section.slabel].add(section.flabel)
                propagate_seed.add(section.slabel)
        self.propagate_addresses(propagate_seed)

        return pointers

    def unpack_pointed_list(self):
        linked_section = self.tree[self.config['linked_pointers']]
        linked_pointers = linked_section.unpack()
        assert isinstance(linked_pointers, list)
        relative_to = linked_section.get_setting('relative_to')
        pointer_offset = relative_to - self.start
        pointers = [p + pointer_offset for p in linked_pointers
                    if p is not None]
        pointers = sorted(set(pointers))
        pointers.append(None)
        datas = {}
        for (a, b) in zip(pointers, pointers[1:]):
            assert 0 <= a
            self.packed.seek(a)
            if b is not None:
                assert a < b
                data = self.packed.read(b-a)
            else:
                data = self.packed.read()
            offset = a - pointer_offset
            assert offset not in datas
            datas[offset] = data

        return datas

    def unpack_regular_list(self):
        num_items = self.get_setting('num_items')
        item_size = self.get_setting('item_size')

        if None in (num_items, item_size):
            self.check_list_dimensions()
            num_items = self.get_setting('num_items')
            item_size = self.get_setting('item_size')

        item_size = self.evaluate(item_size)
        items = []
        self.packed.seek(0)
        for _ in range(self.evaluate(num_items)):
            item = self.packed.read(item_size)
            assert len(item) == item_size
            items.append(item)
        return items

    def unpack(self):
        if hasattr(self, 'unpacked'):
            return self.unpacked

        if self.slabel in self.nulled_addresses:
            return None

        unpacked = None
        if self.sections is not None:
            assert self.is_recursive or self.parent is None
            unpacked = {}
            for key in self.sections:
                assert self.sections[key] in self.children
                unpacked[key] = self.sections[key].unpack()
            self.unpacked = unpacked
            return self.unpack()

        assert self.parent and not self.is_recursive
        if not hasattr(self, 'packed'):
            self.set_packed()

        if self.packed is None:
            return None

        if 'data_type' not in self.config:
            raise Exception(f'Undefined data type: {self.label}')

        if self.config['data_type'] == 'blob':
            assert unpacked is None
            self.packed.seek(0)
            data = self.packed.read()
            unpacked = data

        if self.is_pointers:
            assert unpacked is None
            unpacked = self.unpack_pointers()

        if self.is_pointed_list:
            unpacked = self.unpack_pointed_list()

        if self.is_regular_list:
            unpacked = self.unpack_regular_list()

        if unpacked is None:
            raise Exception(f'Unknown data type: {self.label}')

        subformat = self.get_setting('subformat')
        if subformat is not None:
            if isinstance(unpacked, dict):
                for k, v in list(unpacked.items()):
                    unpacked[k] = self.subunpack(subformat, v)
            elif isinstance(unpacked, list):
                unpacked = [self.subunpack(subformat, v) for v in unpacked]
            elif isinstance(unpacked, bytes):
                unpacked = self.subunpack(subformat, unpacked)
            else:
                import pdb; pdb.set_trace()

        if 'value' in self.config:
            if isinstance(unpacked, bytes):
                value = int.from_bytes(unpacked,
                                       byteorder=self.get_setting('byteorder'))
                evaluated = self.evaluate(self.config['value'])
                if value != evaluated and evaluated != '{%s}' % self.label:
                    raise Exception(f'Validation failure: {self.label}')
            else:
                raise NotImplementedError
        self.unpacked = unpacked
        return self.unpack()

    def set_unpacked(self, unpacked):
        self.unpacked = unpacked
        if unpacked is None:
            for c in self.descendents:
                assert not hasattr(c, 'unpacked')
                c.unpacked = None
            return
        for c in self.children:
            c.set_unpacked(unpacked[c.label])

    def repack_regular_list(self):
        return b''.join(self.unpacked)

    def repack_pointed_list(self):
        SORTED_ORDER = False
        PRESERVE_POINTERS = True
        OPTIMIZE = False
        pointsec = self.tree[self.config['linked_pointers']]
        keys = {k for k in pointsec.unpacked if k is not None}
        assert keys <= set(self.unpacked.keys())

        if OPTIMIZE:
            assert not (SORTED_ORDER or PRESERVE_POINTERS)

        if SORTED_ORDER:
            assert not PRESERVE_POINTERS
            keys = sorted(keys)
        elif PRESERVE_POINTERS:
            assert not SORTED_ORDER
        else:
            raise Exception(f'Undefined order: {self.label}')

        offsets = {}

        if SORTED_ORDER:
            alldata = b''
            for key in keys:
                data = self.unpacked[key]
                if OPTIMIZE and data in alldata:
                    offset = alldata.index(data)
                else:
                    offset = len(alldata)
                    alldata += data
                offsets[key] = offset

        if PRESERVE_POINTERS:
            lowest = 0
            if self.unpacked.keys():
                lowest = min(self.unpacked.keys())
            keys = {key-lowest: key for key in self.unpacked.keys()}
            with BytesIO(b'') as f:
                for verify in (False, True):
                    for key in keys:
                        f.seek(key)
                        mydata = self.unpacked[keys[key]]
                        if not verify:
                            f.write(mydata)
                            offsets[keys[key]] = key
                        else:
                            vdata = f.read(len(mydata))
                            if vdata != mydata:
                                raise Exception(
                                        f'Unable to verify {self.label} data '
                                        f'at offset {key:x}.')
                f.seek(0)
                alldata = f.read()

        pointsec.linked_offsets = offsets
        pointsec.linked_section = self
        return alldata

    def repack_pointers(self):
        if not hasattr(self, 'table'):
            self.table = Unpacker.PointerTable(self)
        if 'pointers' in self.config:
            assert not hasattr(self, 'linked_section')
            self.table.pointers = list(self.config['pointers'])
        if hasattr(self, 'linked_section'):
            assert 'pointers' not in self.config
            pointers = []
            for key in self.unpacked:
                if key is None:
                    pointers.append(None)
                    continue
                else:
                    offset = self.linked_offsets[key]
                    pointers.append(f'@{self.linked_section.label},{offset}')
            self.table.pointers = pointers
        return self.table

    def partial_repack(self):
        if self is self.root and not hasattr(self, '_packed_cache'):
            self._packed_cache = {}
        if self.label in self.root._packed_cache:
            return self.root._packed_cache[self.label]

        subformat = self.get_setting('subformat')
        backup_unpacked = None
        if subformat:
            unpacked = self.unpacked
            backup_unpacked = copy(unpacked)
            if isinstance(unpacked, dict):
                for k, v in list(unpacked.items()):
                    unpacked[k] = self.subrepack(subformat, v)
            elif isinstance(unpacked, list):
                unpacked = [self.subrepack(subformat, v) for v in unpacked]
            elif isinstance(unpacked, bytes):
                unpacked = self.subrepack(subformat, unpacked)
            self.unpacked = unpacked

        packed = None
        if self.children:
            complete = True
            nonpoint_children = [c for c in self.children
                                 if not c.is_pointers]
            point_children = [c for c in self.children if c.is_pointers]
            packed = {}
            for c in nonpoint_children + point_children:
                cpacked = c.partial_repack()
                if cpacked is None:
                    complete = False
                    continue
                packed[c.label] = cpacked
            packed = set(packed.keys())
        elif self.unpacked is None:
            packed = None
        elif self.is_regular_list:
            packed = self.repack_regular_list()
        elif self.is_pointed_list:
            packed = self.repack_pointed_list()
        elif self.is_pointers:
            packed = self.repack_pointers()
        elif self.config['data_type'] == 'blob':
            assert isinstance(self.unpacked, bytes)
            packed = self.unpacked
        else:
            import pdb; pdb.set_trace()

        self.root._packed_cache[self.label] = packed

        if backup_unpacked is not None:
            self.unpacked = backup_unpacked

        return self.partial_repack()

    def calculate_packed_size(self):
        if not self.children:
            packed = self.root._packed_cache[self.label]
            if packed is None:
                return 0
            assert type(packed) in (bytes, Unpacker.PointerTable)
            return len(packed)

        total_size = 0
        for c in self.children:
            total_size += c.calculate_packed_size()

        verify = 0
        for c in self.descendents:
            packed = self.root._packed_cache[c.label]
            if type(packed) in (bytes, Unpacker.PointerTable):
                verify += len(packed)
        assert verify == total_size

        return total_size

    def calculate_packed_addresses(self):
        assert self is self.root
        eof = self.calculate_packed_size()
        assert eof is not None
        local_updated = True
        while local_updated:
            local_updated = False
            problems = set()
            propagate_seed = set()
            for c in self.descendents:
                packed_size = c.calculate_packed_size()
                slabel = f'@{c.label}'
                flabel = f'@{slabel}'
                start = c.get_address(slabel)
                finish = c.get_address(flabel)
                if None not in (start, finish) and \
                        finish - start == packed_size:
                    continue
                if start is not None:
                    finish = start + packed_size
                    if finish not in self.addresses[flabel]:
                        self.addresses[flabel].add(finish)
                        propagate_seed.add(flabel)
                        local_updated = True
                else:
                    problems.add(c)
                if c.finishes and '!eof' in c.finishes \
                        and eof not in c.finishes:
                    local_updated = True
                    self.addresses[flabel].add(eof)
                    propagate_seed.add(flabel)
                finish = c.get_address(flabel)
                if finish is not None:
                    start = finish - packed_size
                    if start not in self.addresses[slabel]:
                        self.addresses[slabel].add(start)
                        propagate_seed.add(slabel)
                        local_updated = True

            if local_updated:
                self.propagate_addresses(propagate_seed)
                continue

            problems = {c for c in problems if c.unpacked is not None}
            if not problems:
                break

            problems = sorted(problems, key=lambda c: c.index)
            for c in problems:
                if local_updated:
                    break
                packed_size = c.calculate_packed_size()
                parent = c.parent
                candidates = {c.parent.start}
                blacklisted = {None}
                for c2 in parent.children:
                    blacklisted.add(c2.start)
                    candidates.add(c2.finish)
                candidates = candidates - blacklisted
                align = None
                if 'align' in c.config:
                    align = c.config['align']
                    if isinstance(align, int):
                        align_m, align_r = align, 0
                    else:
                        align_m, align_r = align
                for candidate in sorted(candidates):
                    if align:
                        while candidate % align_m != align_r:
                            candidate += 1
                    upper = candidate + packed_size
                    test = {a for a in blacklisted if a is not None
                            and candidate <= a < upper}
                    if test:
                        continue
                    self.addresses[c.slabel].add(candidate)
                    self.verify_alignment()
                    local_updated = True
                    break

            if not local_updated:
                raise Exception('Unable to allocate packed data.')

        for c in self.descendents:
            if 'align' in c.config:
                align = c.config['align']
                if c.start % align:
                    raise Exception(
                        f'Section {c.label} misaligned: {c.start:x}')

    def repack(self):
        assert self is self.root
        self.partial_repack()
        self.calculate_packed_addresses()

        packed = BytesIO(b'\x00' * self.calculate_packed_size())
        for verify in (False, True):
            for c in self.descendents:
                cpacked = self._packed_cache[c.label]
                if cpacked is None:
                    continue
                assert cpacked is not None
                if isinstance(cpacked, set):
                    continue
                if isinstance(cpacked, Unpacker.PointerTable):
                    cpacked = cpacked.bytecode
                assert isinstance(cpacked, bytes)
                assert len(cpacked) == c.finish-c.start
                packed.seek(c.start)
                if not verify:
                    packed.write(cpacked)
                else:
                    verification = packed.read(len(cpacked))
                    assert verification == cpacked
                assert packed.tell() == c.finish

        self.set_packed(packed)
        self.packed.seek(0)
        return self.packed.read()

    def subunpack(self, subformat, packed):
        subun = Unpacker(subformat)
        subun.set_packed(packed)
        return subun.unpack()

    def subrepack(self, subformat, unpacked):
        subun = Unpacker(subformat)
        subun.set_unpacked(unpacked)
        return subun.repack()


if __name__ == '__main__':
    config_filename = argv[1]
    data_filenames = argv[2:]
    with open(config_filename) as f:
        config = yaml.safe_load(f.read(), testing=True)
    assert isinstance(config, OrderedDict)
    for fn in data_filenames:
        print(fn)
        u = Unpacker(config)
        with open(fn, 'r+b') as f:
            data = f.read()
            u.set_packed(data)
        unpacked = u.unpack()

        u2 = Unpacker(config)
        u2.set_unpacked(unpacked)
        verify = u2.repack()

        u3 = Unpacker(config)
        u3.set_packed(verify)
        verify_unpacked = u3.unpack()

        if data != verify:
            with open('_nested.a.txt', 'w+') as f:
                f.write(json.dumps(unpacked, indent=2, cls=BytesEncoder))
            with open('_nested.b.txt', 'w+') as f:
                f.write(json.dumps(verify_unpacked, indent=2,
                                   cls=BytesEncoder))
            print('ERROR')
            import pdb; pdb.set_trace()
