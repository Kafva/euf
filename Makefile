#== Demo examples ==#

# Basic example of EUF
basic:
	./euf.py --config tests/configs/basic.json --diff	
	./euf.py --config tests/configs/basic.json	

# Basic example of CBMC
bmc:
	bat ./tests/drivers/example.c
	cbmc ./tests/drivers/example.c --unwind 5 -DCBMC --object-bits 12 --function euf_main --property euf_main.assertion.1


# Analysis of a specific function which has a influential change
xml:
	-git diff --color=always  --no-index \
		~/.cache/euf/libexpat-811c41e3/expat/lib/xmlparse.c \
		~/.cache/euf/libexpat-b1d03960/expat/lib/xmlparse.c \
		| grep -A 15 --color=always  "XML_ErrorString("
	@read
	./expat/test_harness.sh expat/cases/811c41_b1d039.json XML_ErrorString

# Analysis of a specific function which has a equivalent (based on return value) change
entr:
	-git diff --color=always  --no-index \
		~/.cache/euf/libexpat-10d34296/expat/lib/xmlparse.c \
		~/.cache/euf/libexpat-f178826b/expat/lib/xmlparse.c \
		| grep -A 15 --color=always  "ENTROPY_DEBUG("
	@read
	./expat/test_harness.sh expat/cases/10d34296_f178826b.json ENTROPY_DEBUG


# Example run on another project without CBMC
onig:
	./euf.py --config tests/configs/oniguruma.json
