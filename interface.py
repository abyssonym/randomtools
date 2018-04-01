from sys import argv
from os import stat
import string
from time import time
from shutil import copyfile
from collections import defaultdict

from randomtools.tablereader import (
    determine_global_table, sort_good_order, set_table_specs,
    set_global_output_filename, select_patches, write_patches, verify_patches,
    get_random_degree, set_random_degree, set_seed, get_seed, close_file)
from randomtools.utils import (
    utilrandom as random, rewrite_snes_title, rewrite_snes_checksum,
    md5hash)

sourcefile = None
outfile = None
flags = None
user_input_flags = None
difficulty = None
activated_codes = None
all_objects = None


def get_all_objects():
    global all_objects
    return all_objects


def get_sourcefile():
    global sourcefile
    return sourcefile


def get_outfile():
    global outfile
    return outfile


def get_flags():
    global flags
    return flags


def get_user_input_flags():
    global user_input_flags
    return user_input_flags


def get_activated_codes():
    global activated_codes
    return sorted(activated_codes)


def activate_code(code):
    global activated_codes
    activated_codes.add(code)


def rewrite_snes_meta(title, version, lorom=False):
    close_file(outfile)

    for o in get_all_objects():
        if o.random_degree != get_random_degree():
            random_degree = "??"
            break
    else:
        random_degree = int(round((get_random_degree()**0.5) * 100))
        if random_degree >= 100:
            random_degree = "!!"
        else:
            random_degree = "{0:0>2}".format(random_degree)
    rewrite_snes_title("%s %s %s" % (title, random_degree, get_seed()),
                       outfile, version, lorom=lorom)
    rewrite_snes_checksum(outfile, lorom=lorom)


def snescopy(sourcefile, outfile):
    size = stat(sourcefile).st_size
    if size % 0x400 == 0:
        copyfile(sourcefile, outfile)
    elif size % 0x200 == 0:
        print "SNES header detected. Removing header from output file."
        f = open(sourcefile, 'r+b')
        data = f.read()
        f.close()
        data = data[0x200:]
        open(outfile, 'w+').close()
        f = open(outfile, 'r+b')
        f.write(data)
        f.close()
    else:
        raise Exception("Inappropriate file size for SNES rom file.")


def run_interface(objects, custom_degree=False, snes=False, codes=None):
    global sourcefile, outfile, flags, user_input_flags
    global activated_codes, all_objects

    all_objects = objects

    if codes is None:
        codes = {}
    activated_codes = set([])

    args = list(argv)[:5]
    num_args = len(args)
    while len(args) < 5:
        args.append(None)
    _, sourcefile, flags, seed, random_degree = tuple(args)
    if random_degree is None and num_args >= 2:
        random_degree = 0.5

    if sourcefile is None:
        sourcefile = raw_input("Rom filename? ")

    if seed is None and num_args < 2:
        seed = raw_input("Seed? (blank for random) ").strip()

    if seed is None or seed == "":
        seed = time()
    seed = int(seed)
    seed = seed % (10**10)
    set_seed(seed)
    random.seed(seed)

    flagobjects = [o for o in objects if hasattr(o, "flag")
                   and hasattr(o, "flag_description")]
    flagobjects = sorted(flagobjects, key=lambda o: o.flag)
    for o in objects:
        if hasattr(o, "flag") and not hasattr(o, "flag_description"):
            for fo in flagobjects:
                if fo.flag == o.flag:
                    break
            else:
                raise Exception("%s has no flag description." % o.flag)

    allflags = "".join(sorted([f.flag for f in flagobjects]))
    user_input_flags = flags
    if allflags:
        if flags is None and num_args < 2:
            print
            print "Please input the flags for the things you want to randomize."
            for o in flagobjects:
                print "    %s  Randomize %s." % (o.flag,
                                                 o.flag_description.lower())
            print
            flags = raw_input("Flags? (blank for all) ").strip()
            user_input_flags = flags
        elif flags is None:
            flags = allflags

    if flags:
        flags = flags.lower()
        for code, code_options in sorted(codes.items()):
            if isinstance(code_options, basestring):
                code_options = [code_options]
            for co in code_options:
                co = co.lower()
                if co in flags:
                    flags = flags.replace(co, "")
                    activated_codes.add(code)
                    break

    if flags and allflags:
        flags = "".join(sorted([f for f in flags if f in allflags]))
    if not (allflags and flags):
        flags = allflags

    if "." not in sourcefile:
        outfile = [sourcefile, "smc"]
    else:
        outfile = sourcefile.split(".")
    if flags == allflags:
        flagstr = ""
    else:
        flagstr = flags
    outfile = outfile[:-1] + [flagstr, str(seed), outfile[-1]]
    outfile = ".".join(outfile)
    while ".." in outfile:
        outfile = outfile.replace("..", ".")

    try:
        if snes:
            snescopy(sourcefile, outfile)
        else:
            copyfile(sourcefile, outfile)
    except (OSError, IOError), e:
        if e.strerror == "No such file or directory":
            e.strerror = ('%s; Did you include the filename extension? For '
                          'example, ".smc", ".sfc", or ".img". ' % e.strerror)
        raise e
    set_global_output_filename(outfile)
    determine_global_table(outfile)
    set_table_specs()

    custom_degree = custom_degree or random_degree is not None
    if custom_degree:
        custom_split = False
        for o in sorted(objects):
            if hasattr(o, "custom_random_enable") and o.custom_random_enable:
                custom_split = True
                break

        if random_degree is None:
            if custom_split:
                print ("\nIf you would like even more control over the "
                       "randomness, type \"custom\" here.")
            random_degree = raw_input("Randomness? (default: 0.5) ").strip()
            if not random_degree:
                random_degree = 0.5

        if custom_split and (isinstance(random_degree, basestring) and
                "custom" in random_degree.strip().lower()):
            custom_dict = defaultdict(set)
            for o in sorted(objects):
                if (hasattr(o, "custom_random_enable")
                        and o.custom_random_enable):
                    if o.custom_random_enable is True:
                        custom_dict[o.flag].add(o)
                    else:
                        custom_dict[o.custom_random_enable].add(o)

            for k in sorted(custom_dict):
                os = sorted(custom_dict[k], key=lambda o: o.__name__)
                onames = ", ".join([o.__name__ for o in os])
                s = raw_input("Randomness for %s? " % onames).strip()
                if not s:
                    continue
                for o in os:
                    crd = float(s)
                    assert isinstance(crd, float)
                    crd = min(1.0, max(0.0, crd))
                    o.custom_random_degree = crd ** 2

            random_degree = raw_input("Randomness for everything"
                                      " unspecified? ").strip()
            if not random_degree:
                random_degree = 0.5

        random_degree = float(random_degree)
        assert isinstance(random_degree, float)
        random_degree = min(1.0, max(0.0, random_degree))
        set_random_degree(random_degree ** 2)

    if num_args < 3:
        select_patches()

    print
    if flags == allflags:
        flags = string.lowercase
        print ("Randomizing %s with all flags using seed %s"
               % (sourcefile, seed)),
    else:
        flags = flags.lower()
        print ("Randomizing %s with flags '%s' using seed %s"
               % (sourcefile, flags, seed)),
    if custom_degree:
        print "and randomness %s" % random_degree
    print "now."
    print

    if user_input_flags is None:
        user_input_flags = flags

    write_patches(outfile)
    print "Loading and ranking game objects..."
    objects = sort_good_order(objects)
    for o in objects:
        o.every
    for o in objects:
        o.ranked

    for o in objects:
        if hasattr(o, "flag_description") and o.flag in flags:
            print "Randomizing %s." % o.flag_description.lower()
        if not hasattr(o, "flag") or o.flag in flags:
            random.seed(seed)
            o.full_randomize()
        o.randomize_step_finished = True

    if set(flags) >= set(allflags):
        flags = allflags


def clean_and_write(objects):
    objects = sort_good_order(objects)
    for o in objects:
        if hasattr(o, "flag_description") and o.flag in get_flags():
            print "Cleaning %s." % o.flag_description.lower()
        random.seed(get_seed()+1)
        o.full_cleanup()

    print "Saving game objects..."
    for o in objects:
        o.write_all(outfile)

    verify_patches(outfile)


def finish_interface():
    print
    print "Randomization completed successfully."
    print "Output filename: %s" % outfile
    print "MD5 hash: %s" % md5hash(outfile)
    print
    if len(argv) < 2:
        raw_input("Press Enter to close this program. ")
