#!/usr/bin/env python3
import argparse, os
import subprocess

EUF_ROOT = os.path.dirname(os.path.realpath(__file__))

if __name__ == '__main__':
    # ./euf.py -c 69545dabdbc1f7a9fb5ebc329c0b7987052b2a44 -n 29754fab4e3e332d9d19d68d55d760be48a44c1b -d ../jq/modules/oniguruma ../jq

    parser = argparse.ArgumentParser(description="")
    parser.add_argument("project", type=str, nargs=1, help='Project to analyze')
    parser.add_argument("-n", "--commit-new", help='Git hash of the updated commit in the dependency')
    parser.add_argument("-c", "--commit-current", help='Git hash of the current commit in the dependency')
    parser.add_argument("-d", "--dependency", help='Path to the directory with source code for the dependency to upgrade')

    args = parser.parse_args()
    PROJECT = args.project[0]

	# Create a diff between the current and new commit at /tmp/<NEW_COMMIT>.diff
    subprocess.run(["./scripts/euf.sh", "-c", args.commit_current, "-n", args.commit_new, "-d", args.dependency, PROJECT])


	# We haft to exclude braces inside quoutes and comments

	# Changes outside of function body will produce FPs where the
	# body of the function before a change is still printed. 
	# To exclude these changes we will ensure that every -/+ is contained
	# inside the {...} of the function at start of each @@ context 
    with open("/tmp/{}.diff".format(args.commit_new)) as f:
        for line in f:
            print(line)






