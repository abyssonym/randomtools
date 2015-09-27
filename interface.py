from sys import argv
import string
from time import time
from shutil import copyfile

from randomtools.tablereader import (
    set_global_table_filename, sort_good_order)
from randomtools.utils import (
    rewrite_snes_title, rewrite_snes_checksum)

outfile = None
flags = None
seed = None
difficulty = None


def rewrite_snes_meta(title, version, megabits):
    rewrite_snes_title("%s %s" % (title, seed), outfile, version)
    rewrite_snes_checksum(outfile, megabits=megabits)


def run_interface(objects):
    global outfile, flags, seed, difficulty

    args = list(argv)[:5]
    num_args = len(args)
    while len(args) < 5:
        args.append(None)
    _, sourcefile, flags, seed, difficulty = tuple(args)

    if sourcefile is None:
        sourcefile = raw_input("Rom filename? ")

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

    if flags is None and num_args < 2:
        print
        print "Please input the flags for the things you want to randomize."
        for o in flagobjects:
            print "    %s  Randomize %s." % (o.flag,
                                             o.flag_description.lower())
        print
        flags = raw_input("Flags? (blank for all) ").strip()

    if seed is None and num_args < 2:
        seed = raw_input("Seed? (blank for random) ").strip()

    if difficulty is None and num_args < 2:
        difficulty = raw_input("Difficulty? (default: 1.0) ").strip()
        print

    if seed is None or seed == "":
        seed = time()
    seed = int(seed)
    seed = seed % (10**10)

    if difficulty is None or difficulty == "":
        difficulty = 1.0
    difficulty = float(difficulty)

    if flags is None or flags == "":
        flags = string.lowercase
        print ("Randomizing %s with all flags using seed %s "
               "and difficulty %s." % (sourcefile, seed, difficulty))
    else:
        flags = flags.lower()
        print ("Randomizing %s with flags '%s' using seed %s "
               "and difficulty %s." % (sourcefile, flags, seed, difficulty))
    print

    if "." not in sourcefile:
        outfile = [sourcefile, "smc"]
    else:
        outfile = sourcefile.split(".")
    outfile = outfile[:-1] + [str(seed), outfile[-1]]
    outfile = ".".join(outfile)
    copyfile(sourcefile, outfile)
    set_global_table_filename(outfile)

    objects = sort_good_order(objects)
    for o in objects:
        o.every

    for o in objects:
        if hasattr(o, "flag_description"):
            print "Randomizing %s." % o.flag_description.lower()
        if not hasattr(o, "flag") or o.flag in flags:
            o.full_randomize()
    for o in objects:
        if hasattr(o, "flag_description"):
            print "Cleaning %s." % o.flag_description.lower()
        o.full_cleanup()

    for o in objects:
        o.write_all(outfile)


def finish_interface():
    print
    print "Randomization completed sucessfully."
    print "Output filename: %s" % outfile
    print
    if len(argv) < 2:
        raw_input("Press Enter to close this program. ")
