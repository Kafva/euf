# euf
* Requires Python >=3.9, prior versions do not support enough type hints
* The clang version on the system must match the version in `requirements.txt`

## Ubuntu installation
```bash
apt-get install python3.9 python3.9-venv bear clang llvm-12
python3.9 -m venv venv
source ./venv/bin/activate
pip3 install -r requirements.txt
```

Invoke as
```bash
./euf.py --libclang $LIBCLANG \
	--commit-old $OLD_COMMIT \
	--commit-new $NEW_COMMIT \
	--dependency $DEP $PROJECT
```

