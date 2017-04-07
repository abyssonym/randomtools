from sys import argv
from os import stat
import string
from time import time
from shutil import copyfile

from randomtools.tablereader import (
    determine_global_table, sort_good_order, set_table_specs,
    set_global_output_filename, select_patches, write_patches, verify_patches)
from randomtools.utils import (
    utilrandom as random, rewrite_snes_title, rewrite_snes_checksum,
    md5hash)

sourcefile = None
outfile = None
flags = None
seed = None
difficulty = None


def get_outfile():
    global outfile
    return outfile


def get_seed():
    global seed
    return seed


def get_flags():
    global flags
    return flags


def rewrite_snes_meta(title, version, lorom=False):
    rewrite_snes_title("%s %s" % (title, seed), outfile, version, lorom=lorom)
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


def run_interface(objects, custom_difficulty=False, snes=False):
    global sourcefile, outfile, flags, seed, difficulty

    args = list(argv)[:5]
    num_args = len(args)
    while len(args) < 5:
        args.append(None)
    _, sourcefile, flags, seed, difficulty = tuple(args)

    if sourcefile is None:
        sourcefile = raw_input("Rom filename? ")

    if seed is None and num_args < 2:
        seed = raw_input("Seed? (blank for random) ").strip()

    if seed is None or seed == "":
        seed = time()
    seed = int(seed)
    seed = seed % (10**10)
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
    if allflags:
        if flags is None and num_args < 2:
            print
            print "Please input the flags for the things you want to randomize."
            for o in flagobjects:
                print "    %s  Randomize %s." % (o.flag,
                                                 o.flag_description.lower())
            print
            flags = raw_input("Flags? (blank for all) ").strip()
        elif flags is None:
            flags = allflags
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

    if not custom_difficulty:
        difficulty = 1.0

    if difficulty is None and num_args < 2:
        difficulty = raw_input("Difficulty? (default: 1.0) ").strip()
        print

    if difficulty is None or difficulty == "":
        difficulty = 1.0
    difficulty = float(difficulty)

    if num_args < 3:
        select_patches()

    if flags == allflags:
        flags = string.lowercase
        print ("Randomizing %s with all flags using seed %s "
               "and difficulty %s." % (sourcefile, seed, difficulty))
    else:
        flags = flags.lower()
        print ("Randomizing %s with flags '%s' using seed %s "
               "and difficulty %s." % (sourcefile, flags, seed, difficulty))
    print

    write_patches(outfile)
    print "Loading game objects..."
    objects = sort_good_order(objects)
    for o in objects:
        o.every

    for o in objects:
        if hasattr(o, "flag_description") and o.flag in flags:
            print "Randomizing %s." % o.flag_description.lower()
        if not hasattr(o, "flag") or o.flag in flags:
            random.seed(seed)
            o.full_randomize()

    if set(flags) >= set(allflags):
        flags = allflags


def clean_and_write(objects):
    objects = sort_good_order(objects)
    for o in objects:
        if hasattr(o, "flag_description"):
            print "Cleaning %s." % o.flag_description.lower()
        random.seed(seed+1)
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
