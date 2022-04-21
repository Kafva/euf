# euf
* Requires Python >=3.9, prior versions do not support enough of the type hint feature
* The clang version on the system must match the version in `requirements.txt`

## Ubuntu installation
```sh
git clone --recursive https://github.com/Kafva/euf.git

apt-get install python3.9 python3.9-venv bear clang llvm-12 -y

python3.9 -m venv venv
source ./venv/bin/activate
pip3 install -r requirements.txt

make -C clang-plugins all

apt-get install flex bison make curl patch cmake -y
make -C cbmc install

# Download and setup example projects
apt-get install libidn11-dev libudns-dev libgsasl7-dev
./scripts/examples_env.sh
```

Invoke with a JSON config file
```
(venv) ./euf.py --config tests/configs/basic.json
```

## CBMC fork
To avoid duplicate symbols a fork of CBMC which adds a suffix to all global symbols has been created. The symbol renaming is triggered by starting `cbmc`, `goto-cc` or any of the other Cprover tools with `USE_SUFFIX` set in the environment.

## Tests
Unit tests for the functions of the actual script are ran with
```sh
pytest tests/test.py
```

## Implementation notes
EUF compiles the old and new version of the dependency _twice_, once using `bear` to generate a compile commands database and once with `goto-cc` to create a version of the library that CBMC can interact with. Combining these steps would have been preferable but doing so seems unsupported, (no commands are recorded in `compile_commands.json` if `CC` is overriden with `goto-cc`).

