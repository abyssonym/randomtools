from utils import (read_multi, write_multi, classproperty,
                   random, md5hash)
from functools import total_ordering
from os import path
from hashlib import md5
import string
from copy import copy


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
RANDOM_DEGREE = 0.25
SEED = None


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
    print label
    GLOBAL_LABEL = label
    set_global_table_filename(filename)


def patch_filename_to_bytecode(patchfilename):
    patch = {}
    f = open(path.join(tblpath, patchfilename))
    for line in f:
        line = line.strip()
        if not line or line[0] == '#':
            continue
        address, code = line.split(':')
        address = int(address.strip(), 0x10)
        code = code.strip()
        while '  ' in code:
            code = code.replace('  ', ' ')
        code = map(lambda s: chr(int(s, 0x10)), code.split())
        code = ''.join(code)
        if address in patch:
            raise Exception("Multiple %x patches used." % address)
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


def write_patches(outfile):
    if not PATCH_FILENAMES:
        return

    print "Writing patches..."
    f = open(outfile, 'r+b')
    for patchfilename in PATCH_FILENAMES:
        patch = patch_filename_to_bytecode(patchfilename)
        for address, code in sorted(patch.items()):
            f.seek(address)
            f.write(code)
    f.close()


def verify_patches(outfile):
    if not PATCH_FILENAMES:
        return

    print "Verifying patches..."
    f = open(outfile, 'r+b')
    for patchfilename in PATCH_FILENAMES:
        patch = patch_filename_to_bytecode(patchfilename)
        for address, code in sorted(patch.items()):
            f.seek(address)
            written = f.read(len(code))
            if code != written:
                raise Exception(
                    "Patch %x conflicts with modified data." % address)
    f.close()


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
        return mutate_normal(base, minimum, maximum)
    return value


def shuffle_normal(candidates, random_degree=None):
    if random_degree is None:
        random_degree = get_random_degree()
    max_index = len(candidates)-1
    new_indexes = {}
    new_random_degree = random_degree ** 2
    for i, c in enumerate(candidates):
        new_index = mutate_normal(i, 0, max_index, random_degree=random_degree)
        new_index = (i * (1-new_random_degree)) + (
            new_index * new_random_degree)
        new_indexes[c] = new_index
    shuffled = sorted(candidates,
        key=lambda c: (new_indexes[c], random.random(), c.index))
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
    def bitnames(cls):
        return cls.specs.bitnames

    @classproperty
    def total_size(cls):
        return cls.specs.total_size

    @classproperty
    def every(cls):
        return get_table_objects(cls)

    @property
    def rank(self):
        return self.index

    @property
    def intershuffle_valid(self):
        return True

    @property
    def catalogue_index(self):
        return self.index

    @classproperty
    def ranked(cls):
        return sorted(cls.every,
                      key=lambda c: (c.rank, random.random(), c.index))

    def get_similar(self, candidates=None, override_outsider=False):
        if self.rank < 0:
            return self
        if candidates is None:
            candidates = [c for c in self.ranked if c.rank >= 0]
        candidates = sorted(set(candidates))

        if len(candidates) <= 0:
            raise Exception("No candidates for get_similar")

        if override_outsider and self not in candidates:
            candidates.append(self)
        elif self not in candidates:
            raise Exception("Must manually override outsider elements.")
        else:
            override_outsider = False

        if len(candidates) <= 1:
            return candidates[0]

        candidates = sorted(candidates,
                            key=lambda c: (c.rank, random.random(), c.index))
        index = candidates.index(self)
        if override_outsider:
            candidates.remove(self)
            index = random.choice([index, index-1])
            index = max(0, min(index, len(candidates)-1))
        index = mutate_normal(index, minimum=0, maximum=len(candidates)-1)
        chosen = candidates[index]
        if override_outsider:
            assert chosen is not self

        return chosen

    @classmethod
    def get_similar_set(cls, current, candidates=None):
        if candidates is None:
            candidates = [c for c in cls.ranked if c.rank >= 0]
        candidates = sorted(set(candidates),
                            key=lambda c: (c.rank, random.random(), c.index))
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
        f = open(filename, 'r+b')
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
        f.close()

    def copy_data(self, another):
        for name, _, _ in self.specsattrs:
            value = getattr(another, name)
            setattr(self, name, value)

    def write_data(self, filename=None, pointer=None):
        if pointer is None:
            pointer = self.pointer
        if filename is None:
            filename = self.filename
        if pointer is None or filename is None:
            return

        if self.variable_size is not None:
            # doesn't seem to work properly
            raise NotImplementedError
            specsattrs = self.get_variable_specsattrs()
        else:
            specsattrs = self.specsattrs

        f = open(filename, 'r+b')
        for name, size, other in specsattrs:
            value = getattr(self, name)
            if other in [None, "int"]:
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
        f.close()
        return pointer

    @classmethod
    def write_all(cls, filename):
        if cls.specspointedpoint1 or not (
                cls.specsgrouped or cls.specspointed or cls.specsdelimit):
            for o in cls.every:
                o.write_data(filename)
        elif cls.specsgrouped:
            pointer = cls.specspointer
            f = open(filename, "r+b")
            for i in range(cls.numgroups):
                objs = [o for o in cls.every if o.groupindex == i]
                f.seek(pointer)
                if cls.specs.groupednum is None:
                    f.write(chr(len(objs)))
                    pointer += 1
                for o in objs:
                    pointer = o.write_data(filename, pointer)
            f.close()
        elif cls.specspointed and cls.specsdelimit:
            pointer = cls.specspointedpointer
            f = open(filename, "r+b")
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
            f.close()
        elif cls.specspointed:
            pointer = cls.specspointer
            size = cls.specspointedsize
            f = open(filename, "r+b")
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
            f.close()
        elif cls.specsdelimit:
            f = open(filename, "r+b")
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
            f.close()

    def cleanup(self):
        return

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
                if not (hasattr(cls2, "randomized") and cls2.randomized):
                    raise Exception("Randomize order violated: %s %s"
                                    % (cls, cls2))
        cls.class_reseed("group")
        cls.groupshuffle()
        cls.class_reseed("inter")
        cls.intershuffle()
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
            o.mutate()
            o.mutate_bits()
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
                    values = [getattr(o, attribute) for o in self.every]
                    minimum, maximum = min(values), max(values)
                    self.mutate_attributes[attribute] = (minimum, maximum)
                value = getattr(self, attribute)
                if value < minimum or value > maximum:
                    continue
                value = mutate_normal(value, minimum, maximum)
                setattr(self, attribute, value)

    def mutate_bits(self):
        if not hasattr(self, "mutate_bit_attributes"):
            return

        for attribute in sorted(self.mutate_bit_attributes):
            chance = self.mutate_bit_attributes[attribute]
            if random.random() <= chance:
                value = self.get_bit(attribute)
                self.set_bit(attribute, not value)

    def randomize(self):
        if not hasattr(self, "randomize_attributes"):
            return

        self.reseed(salt="ran")
        for attribute in sorted(self.randomize_attributes):
            if isinstance(self.randomize_attributes[attribute], type):
                tob = self.randomize_attributes[attribute]
                candidates = [t for t in tob.every if t.rank >= 0]
                setattr(self, attribute, random.choice(candidates).index)
            else:
                minimum, maximum = self.randomize_attributes[attribute]
                setattr(self, attribute, random.randint(minimum, maximum))

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
    def intershuffle(cls, candidates=None):
        if not hasattr(cls, "intershuffle_attributes"):
            return

        cls.class_reseed("inter")
        hard_shuffle = False
        if (len(set([o.rank for o in cls.every])) == 1
                or all([o.rank == o.index for o in cls.every])):
            hard_shuffle = True

        for attributes in cls.intershuffle_attributes:
            if candidates is None:
                candidates = list(cls.every)
            candidates = [o for o in candidates
                          if o.rank >= 0 and o.intershuffle_valid]
            if hard_shuffle:
                shuffled = list(candidates)
                random.shuffle(shuffled)
            else:
                candidates = sorted(candidates,
                    key=lambda c: (c.rank, random.random(), c.index))
                shuffled = shuffle_normal(candidates)

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
                f = open(filename, 'r+b')
                f.seek(pointer)
                value = ord(f.read(1))
                f.close()
                pointer += 1
            else:
                value = objtype.specs.groupednum
            pointer += add_objects(value, groupindex=counter)
            counter += 1
    elif pointed and delimit:
        size = objtype.specspointedsize
        counter = 0
        f = open(filename, 'r+b')
        g = open(filename, 'r+b')
        while counter < number:
            f.seek(pointer)
            subpointer = read_multi(f, size) + objtype.specspointedpointer
            while True:
                g.seek(subpointer)
                peek = ord(g.read(1))
                if peek == objtype.specsdelimitval:
                    break
                obj = objtype(filename, subpointer, index=len(objects),
                              groupindex=counter, size=None)
                objects.append(obj)
                subpointer += objtype.total_size
            pointer += size
            counter += 1
        g.close()
        f.close()
    elif pointed and objtype.total_size > 0:
        size = objtype.specspointedsize
        counter = 0
        f = open(filename, 'r+b')
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
        f.close()
    elif pointed and objtype.total_size == 0:
        size = objtype.specspointedsize
        counter = 0
        f = open(filename, 'r+b')
        while counter < number:
            f.seek(pointer + (size*counter))
            subpointer = read_multi(f, size) + objtype.specspointedpointer
            f.seek(pointer + (size*counter) + size)
            subpointer2 = read_multi(f, size) + objtype.specspointedpointer
            add_variable_object(subpointer, subpointer2)
            counter += 1
        f.close()
    elif delimit:
        f = open(filename, 'r+b')
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
        f.close()

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

        if line.startswith(".patch") or line.startswith(".option"):
            _, patchfilename = line.strip().split(' ', 1)
            patchfilename = patchfilename.strip()
            PATCH_FILENAMES.append(patchfilename)
            if line.startswith(".option"):
                OPTION_FILENAMES.append(patchfilename)
            continue

        while "  " in line:
            line = line.replace("  ", " ")
        line = line.split()
        groupednum = None
        pointerfilename = None
        pointer = None
        count = None
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
            pointer = int(pointer, 0x10)
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
