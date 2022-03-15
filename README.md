# euf
* Requires Python >=3.9, prior versions do not support enough of the type hint feature
* The clang version on the system must match the version in `requirements.txt`

## Ubuntu installation
```bash
apt-get install python3.9 python3.9-venv bear clang llvm-12 jq -y
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

## Tests
To debug with stdout add `--capture=tee-sys`
> pytest tests/test*
