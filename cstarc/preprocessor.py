# This script preprocesses a C file and outputs the result to stdout.
#
# It leverages the C preprocessor to perform tasks like macro expansion and 
# include resolution. However, it only prints the preprocessed lines originating 
# from the input file, excluding those from any included files.
#
# The output can be used as the input to the CStar compiler.

import os
import subprocess
import sys
import re


CC = os.getenv("CC", "cc")
FLAGS = ["-E", "-C", "--std=c2x", "-o", "-"]

if __name__ == "__main__":
    if len(sys.argv) < 2:
        print("Usage: python preprocessor.py <filename> [flags...]")
        sys.exit(1)
    filename = sys.argv[1]
    flags = [*FLAGS, *sys.argv[2:]]
    preprocessing = subprocess.run([CC, *flags, filename], stdout=subprocess.PIPE)
    if preprocessing.returncode != 0:
        sys.exit(1)
    output = preprocessing.stdout.decode("utf-8")

    current_filename = ""
    for line in output.splitlines():
        if matches := re.match(r"# \d+ \"(.*)\"", line):
            current_filename = matches.group(1)
        elif current_filename == filename:
            print(line)
