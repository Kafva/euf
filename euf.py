#!/usr/bin/env python3
import argparse, os
from logging import error
import re
import subprocess
from dataclasses import dataclass
from pygments import lexers
from clang import cindex

@dataclass
class ChangeUnit:
    filepath: str
    function: str

#----------------------------#
# ./euf.py -c 69545dabdbc1f7a9fb5ebc329c0b7987052b2a44 -n a2ac402a3549713e6c909752937b7a54f559beb8 -d ../jq/modules/oniguruma ../jq
# ./euf.py -c 6c51de92d73ee1e6b54257947ca076b3945d41bd -n 5dc3be2af4e436cd5236157e89ff04b43c71f613 -d ../sck ..
# ./euf.py -c 1fe1a3f7a52d8d86df6f59f2a09c63c849934bce -n eb780c3c7294d4ef1db1cb8dcebbfe274e624d99 -d ../DBMS ..


# + Relying on the LLVM diff directly would eliminate the need for parsing out comments and would
# give us a direct mapping as to where we want to point llvm2smt
# - This would involve compiling the dependency in a custom manner where the IR of every TU is dumped
#   before and after the change
# and then diffing these files. It also becomes more difficult to connect the changes in the dependency to points in the project

# How are macros translated to LLVM?
# If a change occurs in macro (function) we would like to analyze this as well

# TODO: (not an immediate priority)
#   1. Exclusion of functions were the change only concerns a comment
#   2. Exclusion of functions were the change actually occurs after the function @@context
# The SMT detection should exclude these changes anyway but we don't want to perform uneccessary work

# Changes outside of function body will produce FPs where the
# body of the function before a change is still printed. 
# To exclude these changes we will ensure that every -/+ is contained
# inside the {...} of the function at start of each @@ context 

EUF_ROOT = os.path.dirname(os.path.realpath(__file__))


# We can have several identical function names with different return values, arguments etc.

if __name__ == '__main__':

    parser = argparse.ArgumentParser(description="")
    parser.add_argument("project", type=str, nargs=1,   help='Project to analyze')
    parser.add_argument("-n", "--commit-new",           help='Git hash of the updated commit in the dependency')
    parser.add_argument("-c", "--commit-current",       help='Git hash of the current commit in the dependency')
    parser.add_argument("-d", "--dependency",           help='Path to the directory with source code for the dependency to upgrade')

    args = parser.parse_args()

    if args.commit_new == "" or args.commit_current == "" or args.dependency == "" or len(args.project) == 0:
        print("Missing required option")
        exit(1)

    PROJECT = args.project[0]
    DIFF_FILE = "/tmp/" + args.commit_new + ".diff"

	# Create a diff between the current and new commit at /tmp/<NEW_COMMIT>.diff
    subprocess.run(["./scripts/euf.sh", "-c", args.commit_current, "-n", args.commit_new, "-d", args.dependency, PROJECT])

    # There is no guarantee that a change context will start with a function name but the `--function-context` option
    # will at least guarantee that the function enclosing every change is part of the diff
    # As a starting point, we consider all function names in the diff changed
    changed_units = []
    current_filepath = ""
    
    # Determining what is a function prototype through a Regex is not trivial:
    #  https://cs.wmich.edu/~gupta/teaching/cs4850/sumII06/The%20syntax%20of%20C%20in%20Backus-Naur%20form.htm
    # We can lex a source file with clang using
    #   clang -fsyntax-only -Xclang -dump-tokens main.c
    # However this does not give us any indication as to what it is a function decleration 
    # To aquire the AST we use
    #   clang -fsyntax-only -Xclang -ast-dump main.c
    # Native python method
    #   https://gist.github.com/scturtle/a7b5349028c249f2e9eeb5688d3e0c5e

    lexer = lexers.get_lexer_by_name("c")

    file_context_content = ""
    
    #with open("toy/diffs/same.h") as f:
    #    src = ''.join(f.readlines())
    #    print(src)
    #    for token in lexer.get_tokens(src): 
    #        print(token)
    

    with open(DIFF_FILE) as f:
        try:
            for line in f:
                    context_match = re.search(r'^\s*diff --git a/([-/_0-9a-z]+\.[ch]).*', line)

                    if context_match: # New file context
                        [ f.readline() for _ in range(3) ] # Skip the next three lines of context information

                        if file_context_content != "":
                            # Extract all function names from the current file
                            for token in lexer.get_tokens(file_context_content): 
                                if str(token[0]) == 'Token.Name.Function':
                                    changed_units.append( ChangeUnit(current_filepath,token[1]) )
                                    print(changed_units[-1])

                        # Move on to next file context
                        current_filepath = context_match.group(1)
                        file_context_content = ""
                    else:
                        file_context_content += line + "\n"
                    
        except UnicodeDecodeError as error:
            print("Error reading {}: {}".format(DIFF_FILE,error))

