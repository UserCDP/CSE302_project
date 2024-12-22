#! /usr/bin/env python3

# --------------------------------------------------------------------
# Requires Python3 >= 3.10

# --------------------------------------------------------------------
import argparse
import os
import platform
import subprocess as sp
import sys

from bxlib.bxast        import *
from bxlib.bxerrors     import Reporter, DefaultReporter
from bxlib.bxparser     import Parser
from bxlib.bxmm         import MM
from bxlib.bxtychecker  import check as tycheck
from bxlib.bxasmgen     import AsmGen
from bxlib.bxtac        import *

# ====================================================================
# Parse command line arguments

def parse_args():
    parser = argparse.ArgumentParser(prog = os.path.basename(sys.argv[0]))

    parser.add_argument(
        '--arch', choices = sorted(AsmGen.BACKENDS.keys()),
        help = 'Target architecture')

    parser.add_argument('input', help = 'input file (.bx)')

    aout = parser.parse_args()

    if os.path.splitext(aout.input)[1].lower() != '.bx':
        parser.error('input filename must end with the .bx extension')

    return aout

# ====================================================================
# Main entry point

def _main():
    args = parse_args()

    if args.arch is None:
        system  = platform.system()
        machine = platform.machine()
        args.arch = AsmGen.select_backend(system, machine)

        if args.arch is None:
            print(f"cannot find ASM backend for {system}/{machine}", file = sys.stderr)
            exit(1)

        args.arch = args.arch.NAME

    try:
        with open(args.input, 'r') as stream:
            prgm = stream.read()

    except IOError as e:
        print(f'cannot read input file {args.input}: {e}')
        exit(1)

    reporter = DefaultReporter(source = prgm)
    prgm = Parser(reporter = reporter).parse(prgm)

    if prgm is None:
        exit(1)

    if not tycheck(prgm, reporter = reporter):
        exit(1)

    tac = MM.mm(prgm)

    abk = AsmGen.get_backend(args.arch)
    asm = abk.lower(tac)

    basename = os.path.splitext(args.input)[0]

    try:
        with open(f'{basename}.s', 'w') as stream:
            stream.write(asm)

    except IOError as e:
        print(f'cannot write outpout file {args.output}: {e}')
        exit(1)

    bxruntime = os.path.join(os.path.dirname(__file__), 'bxlib', 'bxruntime.c')

    sp.check_call(['gcc', '-g', '-c', '-o', f'{basename}.o', f'{basename}.s'])
    sp.check_call(['gcc', '-g', '-o', f'{basename}.exe', bxruntime, f'{basename}.o'])

# --------------------------------------------------------------------
if __name__ == '__main__':
    _main()

