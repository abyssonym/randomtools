from utils import (read_multi, write_multi, classproperty,
                   random, md5hash, cached_property)
from functools import total_ordering
from os import path
from hashlib import md5
import string
from copy import copy
from collections import Counter


try:
    from sys import _MEIPASS
    tblpath = path.join(_MEIPASS, "tables")
except ImportError:
    tblpath = "tables"

addresses = lambda: None

MASTER_FILENAME = "master.txt"
TABLE_SPECS = {}
GLOBAL_OUTPUT = None
GLOBAL_TABLE = None
GLOBAL_LABEL = None
GRAND_OBJECT_DICT = {}
PATCH_FILENAMES = []
OPTION_FILENAMES = []
NOVERIFY_PATCHES = []
CMP_PATCH_FILENAMES = []
RANDOM_DEGREE = 0.25
SEED = None
OPEN_FILES = {}


def get_open_file(filename):
    if filename in OPEN_FILES:
        f = OPEN_FILES[filename]
        if not f.closed:
            return OPEN_FILES[filename]
    f = open(filename, "r+b")
    OPEN_FILES[filename] = f
    return get_open_file(filename)


def close_file(filename):
    if filename in OPEN_FILES:
        OPEN_FILES[filename].close()


def get_global_label():
    global GLOBAL_LABEL
    return GLOBAL_LABEL


def set_global_output_filename(filename):
    global GLOBAL_OUTPUT
    GLOBAL_OUTPUT = filename


def set_global_table_filename(filename):
    global GLOBAL_TABLE
    GLOBAL_TABLE = filename


def get_seed():
    global SEED
    return SEED


def set_seed(seed):
    global SEED
    SEED = seed


def determine_global_table(outfile):
    global GLOBAL_LABEL
    tablefiles, labelfiles = {}, {}
    for line in open(path.join(tblpath, MASTER_FILENAME)):
        line = line.strip()
        if not line or line[0] == "#":
            continue
        while "  " in line:
            line = line.replace("  ", " ")
        label, h2, tablefile = line.split()
        tablefiles[h2] = (label, tablefile)
        labelfiles[label] = tablefile
    h = md5hash(outfile)
    if h in tablefiles:
        label, filename = tablefiles[h]
    else:
        print "Unrecognized rom file: %s" % h
        for i, label in enumerate(sorted(labelfiles)):
            print "%s. %s" % ((i+1), label)
        if len(labelfiles) > 1:
            selection = int(raw_input("Choose 1-%s: " % len(labelfiles)))
            label = sorted(labelfiles.keys())[selection-1]
            filename = labelfiles[label]
        else:
            raw_input("Using this rom information. Okay? ")
            label = sorted(labelfiles.keys())[0]
            filename = labelfiles[label]
    GLOBAL_LABEL = label
    set_global_table_filename(filename)


def patch_filename_to_bytecode(patchfilename):
    patch = {}
    definitions = {}
    labels = {}
    next_address = None
    f = open(patchfilename)
    for line in f:
        line = line.strip()
        if '#' in line:
            line = line.split('#')[0].strip()

        if not line:
            continue

        while "  " in line:
            line = line.replace("  ", " ")

        if line.startswith(".def"):
            _, name, value = line.split(' ', 2)
            definitions[name] = value
            continue

        if line.startswith(".label"):
            try:
                _, name, address = line.split(' ')
            except ValueError:
                _, name = line.split(' ')
                address = None
            labels[name] = address
            continue

        for name in definitions:
            if name in line:
                line = line.replace(name, definitions[name])

        address, code = line.split(':')
        if not address.strip():
            address = next_address
        else:
            address = int(address.strip(), 0x10)
        code = code.strip()
        while '  ' in code:
            code = code.replace('  ', ' ')

        if address in patch:
            raise Exception("Multiple %x patches used." % address)
        if code:
            patch[address] = code
        for name in labels:
            if labels[name] is None:
                labels[name] = address

        next_address = address + len(code.split())

    for address in sorted(patch):
        code = patch[address]
        for name in labels:
            if name in code:
                target_address = labels[name]
                jump = target_address - (address + 2)
                if jump < 0:
                    jump = 0x100 + jump
                if not 0 <= jump <= 0xFF:
                    raise Exception("Label out of range %x - %s" %
                                    (address, code))
                code = code.replace(name, "%x" % jump)

        code = map(lambda s: chr(int(s, 0x10)), code.split())
        code = ''.join(code)
        patch[address] = code

    f.close()
    return patch


def select_patches():
    if not OPTION_FILENAMES:
        return

    print
    print "The following optional patches are available."
    for i, patchfilename in enumerate(OPTION_FILENAMES):
        print "%s: %s" % (i+1, patchfilename.split('.')[0])
    print
    s = raw_input("Select which patches to use, separated by a space."
                  "\n(0 for none, blank for all): ")
    print
    s = s.strip()
    if not s:
        return
    while '  ' in s:
        s = s.replace('  ', ' ')
    numbers = map(int, s.split())
    options = [o for (i, o) in enumerate(OPTION_FILENAMES) if i+1 in numbers]
    not_chosen = set(OPTION_FILENAMES) - set(options)
    for pfn in not_chosen:
        PATCH_FILENAMES.remove(pfn)


def write_patch(outfile, patchfilename):
    patchpath = path.join(tblpath, patchfilename)
    pf = open(patchpath, 'r+b')
    magic_word = pf.read(5)
    pf.close()
    f = get_open_file(outfile)
    if magic_word == "\xff\xbcCMP":
        CMP_PATCH_FILENAMES.append(patchfilename)
        return write_cmp_patch(f, patchpath)

    patch = patch_filename_to_bytecode(patchpath)
    for address, code in sorted(patch.items()):
        f.seek(address)
        f.write(code)

    if patchfilename not in PATCH_FILENAMES:
        PATCH_FILENAMES.append(patchfilename)


def write_cmp_patch(outfile, patchfilename, verify=False):
    from interface import get_sourcefile

    sourcefile = open(get_sourcefile(), 'r+b')
    patchfile = open(patchfilename, 'r+b')
    magic_word = patchfile.read(5)
    if magic_word != "\xFF\xBCCMP":
        raise Exception("Not a CMP patch.")
    version = ord(patchfile.read(1))
    pointer_length = ord(patchfile.read(1))

    while True:
        command = patchfile.read(1)
        if not command:
            break
        if command == '\x00':
            address = read_multi(patchfile, length=pointer_length)
            outfile.seek(address)
        elif command == '\x01':
            chunksize = read_multi(patchfile, length=2)
            address = read_multi(patchfile, length=pointer_length)
            sourcefile.seek(address)
            s = sourcefile.read(chunksize)
            if not verify:
                outfile.write(s)
            elif verify:
                s2 = outfile.read(len(s))
                if s != s2:
                    raise Exception("Patch write conflict %s %x" % (
                        patchfilename, outfile.tell()-len(s2)))
        elif command == '\x02':
            chunksize = read_multi(patchfile, length=2)
            s = patchfile.read(chunksize)
            if not verify:
                outfile.write(s)
            elif verify:
                s2 = outfile.read(len(s))
                if s != s2:
                    raise Exception("Patch write conflict %s %x" % (
                        patchfilename, outfile.tell()-len(s2)))
        else:
            raise Exception("Unexpected EOF")

    sourcefile.close()
    patchfile.close()


def write_patches(outfile):
    if not PATCH_FILENAMES:
        return

    print "Writing patches..."
    for patchfilename in PATCH_FILENAMES:
        write_patch(outfile, patchfilename)


def verify_patches(outfile):
    if not PATCH_FILENAMES:
        return

    print "Verifying patches..."
    f = get_open_file(outfile)
    for patchfilename in PATCH_FILENAMES:
        if patchfilename in NOVERIFY_PATCHES:
            continue
        patchpath = path.join(tblpath, patchfilename)
        if patchfilename in CMP_PATCH_FILENAMES:
            write_cmp_patch(f, patchpath, verify=True)
            continue
        patch = patch_filename_to_bytecode(patchpath)
        for address, code in sorted(patch.items()):
            f.seek(address)
            written = f.read(len(code))
            if code != written:
                raise Exception(
                    "Patch %x conflicts with modified data." % address)


def get_activated_patches():
    return list(PATCH_FILENAMES)


def sort_good_order(objects):
    objects = sorted(objects, key=lambda o: o.__name__)
    objects = [o for o in objects if o.__name__ in TABLE_SPECS]
    while True:
        changed = False
        for o in list(objects):
            if hasattr(o, "after_order"):
                index = objects.index(o)
                for o2 in o.after_order:
                    index2 = objects.index(o2)
                    if index2 > index:
                        objects.remove(o)
                        objects.insert(index2, o)
                        changed = True
        if not changed:
            break
    return objects


def set_random_degree(value):
    global RANDOM_DEGREE
    RANDOM_DEGREE = value


def get_random_degree():
    global RANDOM_DEGREE
    return RANDOM_DEGREE


def gen_random_normal(random_degree=None):
    if random_degree is None:
        random_degree = get_random_degree()
    value_a = (random.random() + random.random() + random.random()) / 3.0
    value_b = random.random()
    value_c = 0.5
    if random_degree > 0.5:
        factor = (random_degree * 2) - 1
        return (value_a * (1-factor)) + (value_b * factor)
    else:
        factor = random_degree * 2
        return (value_c * (1-factor)) + (value_a * factor)


def mutate_normal(base, minimum, maximum, random_degree=None,
                  return_float=False, wide=False):
    assert minimum <= base <= maximum
    if minimum == maximum:
        return base
    if random_degree is None:
        random_degree = get_random_degree()
    baseval = base-minimum
    width = maximum-minimum
    factor = gen_random_normal(random_degree=random_degree)
    maxwidth = max(baseval, width-baseval)
    minwidth = min(baseval, width-baseval)
    if wide:
        subwidth = maxwidth
    else:
        width_factor = 1.0
        for _ in xrange(7):
            width_factor *= random.uniform(random_degree, width_factor)
        subwidth = (minwidth * (1-width_factor)) + (maxwidth * width_factor)
    if factor > 0.5:
        subfactor = (factor-0.5) * 2
        modifier = subwidth * subfactor
        value = baseval + modifier
    else:
        subfactor = 1- (factor * 2)
        modifier = subwidth * subfactor
        value = baseval - modifier
    value += minimum
    if not return_float:
        value = int(round(value))
    if value < minimum or value > maximum:
        return mutate_normal(base, minimum, maximum,
                             random_degree=random_degree,
                             return_float=return_float, wide=wide)
    return value


def shuffle_normal(candidates, random_degree=None, wide=False):
    if random_degree is None:
        classes = list(set([c.__class__ for c in candidates]))
        if len(classes) == 1 and hasattr(classes[0], "random_degree"):
            random_degree = classes[0].random_degree
        else:
            random_degree = get_random_degree()
    max_index = len(candidates)-1
    new_indexes = {}
    for i, c in enumerate(candidates):
        new_index = mutate_normal(i, 0, max_index, return_float=True,
                                  random_degree=random_degree, wide=wide)
        #new_index = (i * (1-random_degree)) + (new_index * random_degree)
        new_indexes[c] = new_index
    if candidates and hasattr(candidates[0], "index"):
        shuffled = sorted(candidates,
            key=lambda c: (new_indexes[c], c.signature, c.index))
    else:
        shuffled = sorted(candidates,
            key=lambda c: (new_indexes[c], random.random(), c))
    return shuffled


class TableSpecs:
    def __init__(self, specfile, pointer=None, count=None,
                 grouped=False, pointed=False, delimit=False,
                 pointerfilename=None):
        self.attributes = []
        self.bitnames = {}
        self.total_size = 0
        self.pointer = pointer
        self.count = count
        self.grouped = grouped
        self.pointed = pointed
        self.pointedpoint1 = False
        self.delimit = delimit
        self.pointerfilename=pointerfilename
        for line in open(specfile):
            line = line.strip()
            if not line or line[0] == "#":
                continue
            line = line.strip().split(',')
            if len(line) == 2:
                name, size, other = line[0], line[1], None
            elif len(line) == 3:
                name, size, other = tuple(line)

            if size[:3] == "bit":
                size, bitnames = tuple(size.split(':'))
                size = 1
                bitnames = bitnames.split(" ")
                assert all([bn.strip() for bn in bitnames])
                assert len(bitnames) == len(set(bitnames)) == 8
                self.bitnames[name] = bitnames
            elif size == '?':
                size = 0

            try:
                size = int(size)
                self.total_size += size
            except ValueError:
                a, b = size.split('x')
                self.total_size += (int(a)*int(b))
            self.attributes.append((name, size, other))


@total_ordering
class TableObject(object):
    class __metaclass__(type):
        def __iter__(self):
            for obj in self.ranked:
                yield obj

    def __init__(self, filename=None, pointer=None, index=None,
                 groupindex=0, size=None):
        assert hasattr(self, "specs")
        assert isinstance(self.total_size, int)
        assert index is not None
        self.filename = filename
        self.pointer = pointer
        self.groupindex = groupindex
        self.variable_size = size
        self.index = index
        if filename:
            self.read_data(filename, pointer)
        key = (type(self), self.index)
        assert key not in GRAND_OBJECT_DICT
        GRAND_OBJECT_DICT[key] = self

    def __eq__(self, other):
        if type(self) is type(other):
            return self.index == other.index
        return False

    def __lt__(self, other):
        if other is None:
            return False
        assert type(self) is type(other)
        return (self.rank, self.index) < (other.rank, other.index)

    @classmethod
    def create_new(cls):
        index = max([o.index for o in cls.every]) + 1
        new = cls(index=index)
        #new.old_data = {}
        for name, size, other in new.specsattrs:
            if other in [None, "int"]:
                setattr(new, name, 0)
            elif other == "str":
                setattr(new, name, "")
            elif other == "list":
                setattr(new, name, [])
            #new.old_data[name] = copy(getattr(new, name))

        cls._every.append(new)
        return new

    @classproperty
    def random_degree(cls):
        if hasattr(cls, "custom_random_degree"):
            return cls.custom_random_degree
        else:
            return get_random_degree()

    @classproperty
    def numgroups(cls):
        return len(cls.groups)

    @classproperty
    def specs(cls):
        return TABLE_SPECS[cls.__name__]

    @classproperty
    def specsattrs(cls):
        return cls.specs.attributes

    @classproperty
    def specspointer(cls):
        return cls.specs.pointer

    @classproperty
    def specscount(cls):
        return cls.specs.count

    @classproperty
    def specsgrouped(cls):
        return cls.specs.grouped

    @classproperty
    def specspointed(cls):
        return cls.specs.pointed

    @classproperty
    def specspointedpointer(cls):
        return cls.specs.pointedpointer

    @classproperty
    def specspointedpoint1(cls):
        return cls.specs.pointedpoint1

    @classproperty
    def specspointedsize(cls):
        return cls.specs.pointedsize

    @classproperty
    def specsdelimit(cls):
        return cls.specs.delimit

    @classproperty
    def specsdelimitval(cls):
        return cls.specs.delimitval

    @classproperty
    def specspointerfilename(cls):
        return cls.specs.pointerfilename

    @classproperty
    def specssyncpointers(cls):
        if hasattr(cls.specs, "syncpointers"):
            return cls.specs.syncpointers
        return None

    @classproperty
    def bitnames(cls):
        return cls.specs.bitnames

    @classproperty
    def total_size(cls):
        return cls.specs.total_size

    @classproperty
    def every(cls):
        if hasattr(cls, "_every"):
            return cls._every

        cls._every = list(get_table_objects(cls))
        return cls.every

    @property
    def rank(self):
        return 1

    @cached_property
    def ranked_ratio(self):
        ranked = [o for o in self.ranked if o.rank >= 0]
        if self not in ranked:
            return None
        index = ranked.index(self)
        return index / float(len(ranked)-1)

    @property
    def mutate_valid(self):
        return True

    @property
    def intershuffle_valid(self):
        return True

    @property
    def magic_mutate_valid(self):
        return True

    @property
    def catalogue_index(self):
        return self.index

    @classproperty
    def ranked(cls):
        return sorted(cls.every,
                      key=lambda c: (c.rank, c.signature, c.index))

    def assert_unchanged(self):
        for attr in self.old_data:
            if getattr(self, attr) != self.old_data[attr]:
                raise AssertionError('{0} {1} attribute "{2}" changed.'.format(
                    self.__class__.__name__, ("%x" % self.index), attr))

    def get_bit_similarity_score(self, other, bitmasks=None):
        if bitmasks is None:
            bitmasks = self.bit_similarity_attributes
        score = 0
        for attribute, mask in sorted(bitmasks.items()):
            a = self.old_data[attribute]
            if isinstance(other, dict):
                b = other[attribute]
            else:
                b = other.old_data[attribute]
            i = 0
            while True:
                bit = (1 << i)
                if bit > mask:
                    break
                i += 1
                if not bit & mask:
                    continue
                if (a & bit) == (b & bit):
                    score += 1

        return score

    def get_similar(self, candidates=None, override_outsider=False,
                    random_degree=None):
        if self.rank < 0:
            return self
        if random_degree is None:
            random_degree = self.random_degree

        if candidates is None:
            candidates = [c for c in self.every if c.rank >= 0]
        else:
            assert all([c.rank >= 0 for c in candidates])
        candidates = sorted(set(candidates),
                            key=lambda c: (c.rank, c.signature, c.index))

        if len(candidates) <= 0:
            raise Exception("No candidates for get_similar")

        if override_outsider and self not in candidates:
            index = len([c for c in candidates if c.rank < self.rank])
            index2 = len([c for c in candidates if c.rank <= self.rank])
            if index2 > index:
                index = random.randint(index, index2)
            candidates.insert(index, self)
        elif self not in candidates:
            raise Exception("Must manually override outsider elements.")
        else:
            override_outsider = False

        if len(candidates) <= 1:
            return candidates[0]

        index = candidates.index(self)
        if override_outsider:
            candidates.remove(self)
            index = random.choice([index, index-1])
            index = max(0, min(index, len(candidates)-1))
        index = mutate_normal(index, minimum=0, maximum=len(candidates)-1,
                              random_degree=random_degree)
        chosen = candidates[index]
        if override_outsider:
            assert chosen is not self

        return chosen

    @classmethod
    def get_similar_set(cls, current, candidates=None):
        if candidates is None:
            candidates = [c for c in cls.every if c.rank >= 0]
        candidates = sorted(set(candidates),
                            key=lambda c: (c.rank, c.signature, c.index))
        random.shuffle(sorted(current, key=lambda c: c.index))
        chosens = []
        for c in current:
            while True:
                chosen = c.get_similar(candidates, override_outsider=True)
                assert chosen not in chosens
                chosens.append(chosen)
                candidates.remove(chosen)
                assert chosen not in candidates
                break
        assert len(chosens) == len(current)
        return chosens

    @classmethod
    def get(cls, index):
        if isinstance(index, int):
            return GRAND_OBJECT_DICT[cls, index]
        elif isinstance(index, str) or isinstance(index, unicode):
            objs = [o for o in cls.every if index in o.name]
            if len(objs) == 1:
                return objs[0]
            elif len(objs) >= 2:
                raise Exception("Too many matching objects.")
            else:
                raise Exception("No matching objects.")
        else:
            raise Exception("Bad index.")

    @classproperty
    def groups(cls):
        returndict = {}
        for obj in cls.every:
            if obj.groupindex not in returndict:
                returndict[obj.groupindex] = []
            returndict[obj.groupindex].append(obj)
        return returndict

    @classmethod
    def getgroup(cls, index):
        return [o for o in cls.every if o.groupindex == index]

    @property
    def group(self):
        return self.getgroup(self.groupindex)

    @classmethod
    def has(cls, index):
        try:
            cls.get(index)
            return True
        except KeyError:
            return False

    def get_bit(self, bitname):
        for key, value in sorted(self.bitnames.items()):
            if bitname in value:
                index = value.index(bitname)
                byte = getattr(self, key)
                bitvalue = byte & (1 << index)
                return bool(bitvalue)
        raise Exception("No bit registered under that name.")

    def set_bit(self, bitname, bitvalue):
        bitvalue = 1 if bitvalue else 0
        for key, value in self.bitnames.items():
            if bitname in value:
                index = value.index(bitname)
                assert index <= 7
                byte = getattr(self, key)
                if bitvalue:
                    byte = byte | (1 << index)
                else:
                    byte = byte & (0xFF ^ (1 << index))
                setattr(self, key, byte)
                return
        raise Exception("No bit registered under that name.")

    @property
    def display_name(self):
        if not hasattr(self, "name"):
            self.name = "%x" % self.index
        if isinstance(self.name, int):
            return "%x" % self.name
        return "".join([c for c in self.name if c in string.printable])

    @property
    def verification_signature(self):
        return self.get_verification_signature(old_data=False)

    @property
    def old_verification_signature(self):
        return self.get_verification_signature(old_data=True)

    def get_verification_signature(self, old_data=False):
        labels = sorted([a for (a, b, c) in self.specsattrs
                         if c not in ["str"]])
        if old_data:
            data = str([(label, self.old_data[label]) for label in labels])
        else:
            data = str([(label, getattr(self, label)) for label in labels])

        datahash = md5(data).hexdigest()
        signature = "{0}:{1:0>4}:{2}".format(
            self.__class__.__name__, ("%x" % self.index), datahash)
        return signature

    @property
    def description(self):
        classname = self.__class__.__name__
        pointer = "%x" % self.pointer if self.pointer else "None"
        desc = "{0} {1:02x} {2} {3}".format(
            classname, self.index, pointer, self.display_name)
        return desc

    @property
    def long_description(self):
        s = []
        for attr in sorted(dir(self)):
            if attr.startswith('_'):
                continue

            if attr in ["specs", "catalogue"]:
                continue

            if hasattr(self.__class__, attr):
                class_attr = getattr(self.__class__, attr)
                if (isinstance(class_attr, property)
                        or hasattr(class_attr, "__call__")):
                    continue

            try:
                value = getattr(self, attr)
            except AttributeError:
                continue

            if isinstance(value, dict):
                continue

            if isinstance(value, list):
                if value and not isinstance(value[0], int):
                    continue
                value = " ".join(["%x" % v for v in value])

            if isinstance(value, int):
                value = "%x" % value

            s.append((attr, "%s" % value))

        s = ", ".join(["%s: %s" % (a, b) for (a, b) in s])
        s = "%x - %s" % (self.index, s)
        return s

    @classproperty
    def catalogue(self):
        logs = []
        for obj in sorted(self.every, key=lambda o: o.catalogue_index):
            logs.append(obj.log.strip())

        if any(["\n" in log for log in logs]):
            return "\n\n".join(logs)
        else:
            return "\n".join(logs)

    @property
    def log(self):
        return str(self)

    def __repr__(self):
        return self.description

    def get_variable_specsattrs(self):
        specsattrs = [(name, self.variable_size, other)
                      for (name, size, other)
                      in self.specsattrs if size == 0]
        if not specsattrs:
            raise ValueError("No valid specs attributes.")
        elif len(specsattrs) >= 2:
            raise ValueError("Too many specs attributes.")
        return specsattrs

    def read_data(self, filename=None, pointer=None):
        if pointer is None:
            pointer = self.pointer
        if filename is None:
            filename = self.filename
        if pointer is None or filename is None:
            return

        if self.variable_size is not None:
            specsattrs = self.get_variable_specsattrs()
        else:
            specsattrs = self.specsattrs

        self.old_data = {}
        f = get_open_file(filename)
        f.seek(pointer)
        for name, size, other in specsattrs:
            if other in [None, "int"]:
                value = read_multi(f, length=size)
            elif other == "str":
                value = f.read(size)
            elif other == "list":
                if not isinstance(size, int):
                    number, numbytes = size.split('x')
                    number, numbytes = int(number), int(numbytes)
                else:
                    number, numbytes = size, 1
                value = []
                for i in xrange(number):
                    value.append(read_multi(f, numbytes))
            self.old_data[name] = copy(value)
            setattr(self, name, value)

    def copy_data(self, another):
        for name, _, _ in self.specsattrs:
            value = getattr(another, name)
            setattr(self, name, value)

    def write_data(self, filename=None, pointer=None, syncing=False):
        if pointer is None:
            pointer = self.pointer
        if filename is None:
            filename = self.filename
        if pointer is None or filename is None:
            return

        if not syncing and self.specssyncpointers:
            for p in self.specssyncpointers:
                offset = p - self.specspointer
                new_pointer = self.pointer + offset
                self.write_data(filename=filename, pointer=new_pointer,
                                syncing=True)
            return

        if self.variable_size is not None:
            # doesn't seem to work properly
            raise NotImplementedError
            specsattrs = self.get_variable_specsattrs()
        else:
            specsattrs = self.specsattrs

        f = get_open_file(filename)
        for name, size, other in specsattrs:
            value = getattr(self, name)
            if other in [None, "int"]:
                assert value >= 0
                f.seek(pointer)
                write_multi(f, value, length=size)
                pointer += size
            elif other == "str":
                assert len(value) == size
                f.seek(pointer)
                f.write(value)
                pointer += size
            elif other == "list":
                if not isinstance(size, int):
                    number, numbytes = size.split('x')
                    number, numbytes = int(number), int(numbytes)
                else:
                    number, numbytes = size, 1
                assert len(value) == number
                for v in value:
                    f.seek(pointer)
                    write_multi(f, v, length=numbytes)
                    pointer += numbytes
        return pointer

    @classmethod
    def write_all(cls, filename):
        if cls.specspointedpoint1 or not (
                cls.specsgrouped or cls.specspointed or cls.specsdelimit):
            for o in cls.every:
                o.write_data(filename)
        elif cls.specsgrouped:
            pointer = cls.specspointer
            f = get_open_file(filename)
            for i in range(cls.numgroups):
                objs = [o for o in cls.every if o.groupindex == i]
                f.seek(pointer)
                if cls.specs.groupednum is None:
                    f.write(chr(len(objs)))
                    pointer += 1
                for o in objs:
                    pointer = o.write_data(filename, pointer)
        elif cls.specspointed and cls.specsdelimit:
            pointer = cls.specspointedpointer
            f = get_open_file(filename)
            for i in range(cls.specscount):
                objs = [o for o in cls.every if o.groupindex == i]
                if not objs:
                    continue
                f.seek(cls.specspointer + (cls.specspointedsize * i))
                write_multi(f, pointer-cls.specspointedpointer,
                            length=cls.specspointedsize)
                f.seek(pointer)
                for o in objs:
                    pointer = o.write_data(filename, pointer)
                f.seek(pointer)
                f.write(chr(cls.specsdelimitval))
                pointer += 1
            if pointer == cls.specspointedpointer:
                raise Exception("No objects in pointdelimit data.")
            nullpointer = pointer-1
            for i in range(cls.specscount):
                objs = [o for o in cls.every if o.groupindex == i]
                if objs:
                    continue
                f.seek(cls.specspointer + (cls.specspointedsize * i))
                write_multi(f, nullpointer-cls.specspointedpointer,
                            length=cls.specspointedsize)
        elif cls.specspointed:
            pointer = cls.specspointer
            size = cls.specspointedsize
            f = get_open_file(filename)
            first_pointer = min([o.pointer for o in cls.every if o is not None])
            pointedpointer = max(first_pointer, pointer + (cls.specscount * size))
            mask = (2 ** (8*size)) - 1
            for i in range(cls.specscount):
                #masked = pointedpointer & mask
                masked = (pointedpointer-cls.specspointedpointer) & mask
                objs = [o for o in cls.every if o.groupindex == i]
                if hasattr(cls, "groupsort"):
                    objs = cls.groupsort(objs)
                for o in objs:
                    pointedpointer = o.write_data(filename, pointedpointer)
                f.seek(pointer + (i*size))
                write_multi(f, masked, length=size)
        elif cls.specsdelimit:
            f = get_open_file(filename)
            pointer = cls.specspointer
            for i in range(cls.specscount):
                objs = cls.getgroup(i)
                if hasattr(cls, "groupsort"):
                    objs = cls.groupsort(objs)
                for o in objs:
                    pointer = o.write_data(filename, pointer)
                f.seek(pointer)
                f.write(chr(cls.specsdelimitval))
                pointer += 1

    def preclean(self):
        return

    def cleanup(self):
        return

    @classmethod
    def full_preclean(cls):
        if hasattr(cls, "after_order"):
            for cls2 in cls.after_order:
                if not (hasattr(cls2, "precleaned") and cls2.precleaned):
                    raise Exception("Preclean order violated: %s %s"
                                    % (cls, cls2))
        for o in cls.every:
            o.preclean()
        cls.precleaned = True

    @classmethod
    def full_cleanup(cls):
        if hasattr(cls, "after_order"):
            for cls2 in cls.after_order:
                if not (hasattr(cls2, "cleaned") and cls2.cleaned):
                    raise Exception("Clean order violated: %s %s"
                                    % (cls, cls2))
        for o in cls.every:
            o.cleanup()
        cls.cleaned = True

    @cached_property
    def signature(self):
        s = "%s%s%s" % (
            get_seed(), self.index, self.__class__.__name__)
        return md5(s).hexdigest()

    def reseed(self, salt=""):
        s = "%s%s%s%s" % (
            get_seed(), self.index, salt, self.__class__.__name__)
        value = int(md5(s).hexdigest(), 0x10)
        random.seed(value)

    @classmethod
    def class_reseed(cls, salt=""):
        obj = cls.every[0]
        obj.reseed(salt="cls"+salt)

    @classmethod
    def full_randomize(cls):
        if hasattr(cls, "after_order"):
            for cls2 in cls.after_order:
                if not (hasattr(cls2, "randomize_step_finished")
                        and cls2.randomize_step_finished):
                    raise Exception("Randomize order violated: %s %s"
                                    % (cls, cls2))
        cls.class_reseed("group")
        cls.groupshuffle()
        cls.class_reseed("inter")
        cls.intershuffle()
        cls.class_reseed("randsel")
        cls.randomselect()
        cls.class_reseed("full")
        cls.shuffle_all()
        cls.randomize_all()
        cls.mutate_all()
        cls.randomized = True

    @classmethod
    def mutate_all(cls):
        for o in cls.every:
            if hasattr(o, "mutated") and o.mutated:
                continue
            o.reseed(salt="mut")
            if o.mutate_valid:
                o.mutate()
            o.mutate_bits()
            if o.magic_mutate_valid:
                o.magic_mutate_bits()
            o.mutated = True

    @classmethod
    def randomize_all(cls):
        for o in cls.every:
            if hasattr(o, "randomized") and o.randomized:
                continue
            o.reseed(salt="ran")
            o.randomize()
            o.randomized = True

    @classmethod
    def shuffle_all(cls):
        for o in cls.every:
            if hasattr(o, "shuffled") and o.shuffled:
                continue
            o.reseed(salt="shu")
            o.shuffle()
            o.shuffled = True

    def mutate(self):
        if not hasattr(self, "mutate_attributes"):
            return

        if not self.mutate_valid:
            return

        self.reseed(salt="mut")
        for attribute in sorted(self.mutate_attributes):
            if isinstance(self.mutate_attributes[attribute], type):
                tob = self.mutate_attributes[attribute]
                index = getattr(self, attribute)
                tob = tob.get(index)
                tob = tob.get_similar()
                setattr(self, attribute, tob.index)
            else:
                minmax = self.mutate_attributes[attribute]
                if type(minmax) is tuple:
                    minimum, maximum = minmax
                else:
                    values = [o.old_data[attribute] for o in self.every
                              if o.mutate_valid]
                    minimum, maximum = min(values), max(values)
                    self.mutate_attributes[attribute] = (minimum, maximum)
                value = getattr(self, attribute)
                if value < minimum or value > maximum:
                    continue
                value = mutate_normal(value, minimum, maximum,
                                      random_degree=self.random_degree)
                setattr(self, attribute, value)

    def mutate_bits(self):
        if not hasattr(self, "mutate_bit_attributes"):
            return

        for attribute in sorted(self.mutate_bit_attributes):
            chance = self.mutate_bit_attributes[attribute]
            if random.random() <= chance:
                value = self.get_bit(attribute)
                self.set_bit(attribute, not value)

    def magic_mutate_bits(self):
        if (self.rank < 0 or not hasattr(self, "magic_mutate_bit_attributes")
                or not self.magic_mutate_valid):
            return

        base_candidates = [o for o in self.every
                           if o.magic_mutate_valid and o.rank >= 0]

        if not hasattr(self.__class__, "_candidates_dict"):
            self.__class__._candidates_dict = {}

        self.reseed(salt="magmutbit")
        for attributes in sorted(self.magic_mutate_bit_attributes):
            masks = self.magic_mutate_bit_attributes[attributes]
            if isinstance(attributes, basestring):
                del(self.magic_mutate_bit_attributes[attributes])
                attributes = tuple([attributes])
            if masks is None:
                masks = tuple([None for a in attributes])
            if isinstance(masks, int):
                masks = (masks,)
            bitmasks = dict(zip(attributes, masks))
            for attribute, mask in bitmasks.items():
                if mask is None:
                    mask = 0
                    for c in base_candidates:
                        mask |= getattr(c, attribute)
                    bitmasks[attribute] = mask
            masks = tuple([bitmasks[a] for a in attributes])
            self.magic_mutate_bit_attributes[attributes] = masks

            def obj_to_dict(o):
                return dict([(a, getattr(o, a)) for a in attributes])

            wildcard = [random.randint(0, m<<1) & m for m in masks]
            wildcard = []
            for attribute, mask in bitmasks.items():
                value = random.randint(0, mask<<1) & mask
                while True:
                    if not value:
                        break
                    v = random.randint(0, value) & mask
                    if not v & value:
                        if bin(v).count('1') <= bin(value).count('1'):
                            value = v
                        if random.choice([True, False]):
                            break
                    else:
                        value &= v
                value = self.old_data[attribute] ^ value
                wildcard.append((attribute, value))

            if attributes not in self._candidates_dict:
                candidates = []
                for o in base_candidates:
                    candidates.append(tuple(
                        [getattr(o, a) for a in attributes]))
                counted_candidates = Counter(candidates)
                candidates = []
                for values in sorted(counted_candidates):
                    valdict = dict(zip(attributes, values))
                    frequency = counted_candidates[values]
                    frequency = int(
                        round(frequency ** (1-(self.random_degree**0.5))))
                    candidates.extend([valdict]*frequency)
                self._candidates_dict[attributes] = candidates

            candidates = list(self._candidates_dict[attributes])
            candidates += [dict(wildcard)]
            candidates = sorted(
                candidates, key=lambda o: (
                    self.get_bit_similarity_score(o, bitmasks=bitmasks),
                    o.signature if hasattr(o, "signature") else -1,
                    o.index if hasattr(o, "index") else -1),
                reverse=True)
            index = candidates.index(obj_to_dict(self))
            max_index = len(candidates)-1
            index = mutate_normal(index, 0, max_index,
                                  random_degree=self.random_degree, wide=True)
            chosen = candidates[index]
            if chosen is self:
                continue
            if not isinstance(chosen, dict):
                chosen = chosen.old_data
            for attribute, mask in sorted(bitmasks.items()):
                diffmask = (getattr(self, attribute) ^ chosen[attribute])
                diffmask &= mask
                if not diffmask:
                    continue
                i = 0
                while True:
                    bit = (1 << i)
                    i += 1
                    if bit > (diffmask | mask):
                        break

                    if (bit & mask and not bit & diffmask
                            and random.random() < self.random_degree ** 6):
                        diffmask |= bit

                    if bit & diffmask:
                        if random.random() < ((self.random_degree**0.5)/2.0):
                            continue
                        else:
                            diffmask ^= bit
                setattr(self, attribute, getattr(self, attribute) ^ diffmask)

    def randomize(self):
        if not hasattr(self, "randomize_attributes"):
            return
        if not self.intershuffle_valid:
            return

        self.reseed(salt="ran")
        candidates = [c for c in self.every
                      if c.rank >= 0 and c.intershuffle_valid]
        for attribute in sorted(self.randomize_attributes):
            chosen = random.choice(candidates)
            setattr(self, attribute, chosen.old_data[attribute])

    def shuffle(self):
        if not hasattr(self, "shuffle_attributes"):
            return

        self.reseed(salt="shu")
        for attributes in sorted(self.shuffle_attributes):
            if len(attributes) == 1:
                attribute = attributes[0]
                value = sorted(getattr(self, attribute))
                random.shuffle(value)
                setattr(self, attribute, value)
                continue
            values = [getattr(self, attribute) for attribute in attributes]
            random.shuffle(values)
            for attribute, value in zip(attributes, values):
                setattr(self, attribute, value)

    @classmethod
    def intershuffle(cls, candidates=None, random_degree=None):
        if not hasattr(cls, "intershuffle_attributes"):
            return

        if random_degree is None:
            random_degree = cls.random_degree

        if candidates is None:
            candidates = list(cls.every)

        candidates = [o for o in candidates
                      if o.rank >= 0 and o.intershuffle_valid]

        cls.class_reseed("inter")
        hard_shuffle = False
        if (len(set([o.rank for o in candidates])) == 1
                or all([o.rank == o.index for o in candidates])):
            hard_shuffle = True

        for attributes in cls.intershuffle_attributes:
            if hard_shuffle:
                shuffled = list(candidates)
                random.shuffle(shuffled)
            else:
                candidates = sorted(candidates,
                    key=lambda c: (c.rank, c.signature, c.index))
                shuffled = shuffle_normal(candidates,
                                          random_degree=random_degree)

            if isinstance(attributes, str) or isinstance(attributes, unicode):
                attributes = [attributes]

            for attribute in attributes:
                swaps = []
                for a, b in zip(candidates, shuffled):
                    aval, bval = getattr(a, attribute), getattr(b, attribute)
                    swaps.append(bval)
                for a, bval in zip(candidates, swaps):
                    setattr(a, attribute, bval)

    @classmethod
    def randomselect(cls, candidates=None):
        if not hasattr(cls, "randomselect_attributes"):
            return

        if candidates is None:
            candidates = list(cls.every)
        candidates = [o for o in candidates
                      if o.rank >= 0 and o.intershuffle_valid]
        if len(set([o.rank for o in candidates])) <= 1:
            hard_shuffle = True
        else:
            hard_shuffle = False

        for o in candidates:
            o.reseed("randsel")
            for attributes in cls.randomselect_attributes:
                if hard_shuffle:
                    o2 = random.choice(candidates)
                else:
                    o2 = o.get_similar(candidates)
                if isinstance(attributes, basestring):
                    attributes = [attributes]
                for attribute in attributes:
                    setattr(o, attribute, o2.old_data[attribute])
            o.random_selected = True

    @classmethod
    def groupshuffle(cls):
        if (not hasattr(cls, "groupshuffle_enabled")
                or not cls.groupshuffle_enabled):
            return

        cls.class_reseed("group")
        shuffled = range(cls.numgroups)
        random.shuffle(shuffled)
        swapdict = {}
        for a, b in zip(range(cls.numgroups), shuffled):
            a = cls.getgroup(a)
            b = cls.getgroup(b)
            for a1, b1 in zip(a, b):
                swapdict[a1] = (b1.groupindex, b1.index, b1.pointer)

        for o in cls.every:
            groupindex, index, pointer = swapdict[o]
            o.groupindex = groupindex
            o.index = index
            o.pointer = pointer


already_gotten = {}


def get_table_objects(objtype, filename=None):
    pointer = objtype.specspointer
    number = objtype.specscount
    grouped = objtype.specsgrouped
    pointed = objtype.specspointed
    delimit = objtype.specsdelimit
    pointerfilename = objtype.specspointerfilename
    identifier = (objtype, pointer, number)
    if identifier in already_gotten:
        return already_gotten[identifier]

    if filename is None:
        filename = GLOBAL_OUTPUT
    objects = []

    def add_objects(n, groupindex=0, p=None):
        if p is None:
            p = pointer
        accumulated_size = 0
        for i in xrange(n):
            obj = objtype(filename, p, index=len(objects),
                          groupindex=groupindex)
            objects.append(obj)
            p += obj.total_size
            accumulated_size += obj.total_size
        return accumulated_size

    def add_variable_object(p1, p2):
        size = p2 - p1
        obj = objtype(filename, p1, index=len(objects),
                      groupindex=0, size=size)
        objects.append(obj)
        return size

    if pointerfilename is not None:
        for line in open(path.join(tblpath, pointerfilename)):
            line = line.strip()
            if not line or line[0] == '#':
                continue
            pointer = int(line.split()[0], 0x10)
            add_objects(1, p=pointer)
    elif not grouped and not pointed and not delimit:
        add_objects(number)
    elif grouped:
        counter = 0
        while len(objects) < number:
            if objtype.specs.groupednum is None:
                f = get_open_file(filename)
                f.seek(pointer)
                value = ord(f.read(1))
                pointer += 1
            else:
                value = objtype.specs.groupednum
            pointer += add_objects(value, groupindex=counter)
            counter += 1
    elif pointed and delimit:
        size = objtype.specspointedsize
        counter = 0
        f = get_open_file(filename)
        while counter < number:
            f.seek(pointer)
            subpointer = read_multi(f, size) + objtype.specspointedpointer
            while True:
                f.seek(subpointer)
                peek = ord(f.read(1))
                if peek == objtype.specsdelimitval:
                    break
                obj = objtype(filename, subpointer, index=len(objects),
                              groupindex=counter, size=None)
                objects.append(obj)
                subpointer += objtype.total_size
            pointer += size
            counter += 1
    elif pointed and objtype.total_size > 0:
        size = objtype.specspointedsize
        counter = 0
        f = get_open_file(filename)
        while counter < number:
            f.seek(pointer)
            subpointer = read_multi(f, size) + objtype.specspointedpointer
            f.seek(pointer + size)
            subpointer2 = read_multi(f, size) + objtype.specspointedpointer
            groupcount = (subpointer2 - subpointer) / objtype.total_size
            if objtype.specspointedpoint1:
                groupcount = 1
            add_objects(groupcount, groupindex=counter, p=subpointer)
            pointer += size
            counter += 1
    elif pointed and objtype.total_size == 0:
        size = objtype.specspointedsize
        counter = 0
        f = get_open_file(filename)
        while counter < number:
            f.seek(pointer + (size*counter))
            subpointer = read_multi(f, size) + objtype.specspointedpointer
            f.seek(pointer + (size*counter) + size)
            subpointer2 = read_multi(f, size) + objtype.specspointedpointer
            add_variable_object(subpointer, subpointer2)
            counter += 1
    elif delimit:
        f = get_open_file(filename)
        for counter in xrange(number):
            while True:
                f.seek(pointer)
                peek = ord(f.read(1))
                if peek == objtype.specsdelimitval:
                    pointer += 1
                    break
                obj = objtype(filename, pointer, index=len(objects),
                              groupindex=counter, size=None)
                objects.append(obj)
                pointer += obj.total_size

    already_gotten[identifier] = objects

    return get_table_objects(objtype, filename=filename)


def set_table_specs(filename=None):
    if filename is None:
        filename = GLOBAL_TABLE
    tablesfile = path.join(tblpath, filename)
    for line in open(tablesfile):
        line = line.strip()
        if not line or line[0] == "#":
            continue

        if line[0] == '$':
            attr, value = line.lstrip('$').strip().split(' ', 1)
            attr = attr.strip()
            value = int(value.strip(), 0x10)
            setattr(addresses, attr, value)
            continue

        if any(line.startswith(s) for s in [".patch", ".option"]):
            _, patchfilename = line.strip().split(' ', 1)
            patchfilename = patchfilename.strip()
            PATCH_FILENAMES.append(patchfilename)
            if line.startswith(".option"):
                OPTION_FILENAMES.append(patchfilename)
            if ".no_verify" in line:
                NOVERIFY_PATCHES.append(patchfilename)
            continue

        while "  " in line:
            line = line.replace("  ", " ")
        line = line.split()
        groupednum = None
        pointerfilename = None
        pointer = None
        count = None
        syncpointers = False
        if len(line) >= 5:
            (objname, tablefilename, pointer, count,
                organization) = tuple(line[:5])
            args = line[5:]
            if organization.lower() not in ["grouped", "pointed", "point1",
                                            "pointdelimit", "delimit"]:
                raise NotImplementedError
            grouped = True if organization.lower() == "grouped" else False
            pointed = True if organization.lower() == "pointed" else False
            point1 = True if organization.lower() == "point1" else False
            delimit = True if organization.lower() == "delimit" else False
            pointdelimit = True if organization.lower() == "pointdelimit" else False
            pointed = pointed or point1 or pointdelimit
            delimit = delimit or pointdelimit
            if pointed:
                pointedpointer = int(args[0], 0x10)
                pointedsize = int(args[1]) if len(args) > 1 else 2
            if grouped and len(args) >= 1:
                groupednum = int(args[0])
            if delimit and not pointdelimit:
                delimitval = int(args[0])
            if pointdelimit:
                pointedpointer = int(args[0], 0x10)
                pointedsize = int(args[1]) if len(args) > 1 else 2
                delimitval = int(args[2])
        else:
            grouped = False
            pointed = False
            point1 = False
            delimit = False
            pointdelimit = False
            if len(line) <= 3:
                objname, tablefilename, pointerfilename = tuple(line)
            else:
                objname, tablefilename, pointer, count = tuple(line)
        if pointer is not None and isinstance(pointer, basestring):
            if ',' in pointer:
                pointers = map(lambda p: int(p, 0x10), pointer.split(','))
                pointer = pointers[0]
                syncpointers = True
            else:
                pointer = int(pointer, 0x10)
                syncpointers = False
        if count is not None:
            count = int(count)
        TABLE_SPECS[objname] = TableSpecs(path.join(tblpath, tablefilename),
                                          pointer, count, grouped, pointed,
                                          delimit, pointerfilename)
        if pointed or point1 or pointdelimit:
            TABLE_SPECS[objname].pointedpointer = pointedpointer
            TABLE_SPECS[objname].pointedsize = pointedsize
            TABLE_SPECS[objname].pointedpoint1 = point1
        if grouped:
            TABLE_SPECS[objname].groupednum = groupednum
        if delimit or pointdelimit:
            TABLE_SPECS[objname].delimitval = delimitval
        if syncpointers:
            TABLE_SPECS[objname].syncpointers = pointers
