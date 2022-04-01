# euf
* Requires Python >=3.9, prior versions do not support enough of the type hint feature
* The clang version on the system must match the version in `requirements.txt`

## Ubuntu installation
```bash
apt-get install python3.9 python3.9-venv bear clang llvm-12 jq neovim ccls -y
pip3 install --user pcpp
python3.9 -m venv venv
source ./venv/bin/activate
pip3 install -r requirements.txt

# Build latest CBMC
git submodule update --init --recursive
cd cbmc
apt-get install flex bison make curl patch cmake -y
mkdir -p build
cmake -S . -B build -DCMAKE_C_COMPILER=/usr/bin/clang -DWITH_JBMC=OFF &&
cmake --build build &&
sudo make -C build install
```

Invoke as
```bash
./euf.py --libclang $LIBCLANG \
	--commit-old $OLD_COMMIT \
	--commit-new $NEW_COMMIT \
	--dependency $DEP \
	$PROJECT
```

## CBMC fork
To avoid duplicate symbols a fork of CBMC which adds a suffix to all global symbols has been created. The symbol renaming is triggered by starting `cbmc`, `goto-cc` or any of the other Cprover tools with `USE_SUFFIX` set in the environment.

## Tests
To debug with stdout add `--capture=tee-sys`
> pytest tests/test*
