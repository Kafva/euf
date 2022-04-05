basic:
	-git diff --no-index ~/.cache/euf/matrix-d85085cb/src/matrix.c ~/.cache/euf/matrix-867b6581/src/matrix.c
	./euf.py --config tests/configs/basic.json	

bmc:
	cbmc ./tests/drivers/example.c --unwind 5 -DCBMC --object-bits 12 --function euf_main --property euf_main.assertion.1

onig:
	./euf.py --config tests/configs/oniguruma.json

onig_v:
	./euf.py --config tests/configs/oniguruma_v.json

onig_cbmc:
	make -C cbmc example

#head -n24 expat/drivers/XML_ErrorString.c | bat --language c --style full
xml_cbmc:
	-git diff --color=always  --no-index ~/.cache/euf/libexpat-c16300f0/expat/lib/xmlparse.c ~/.cache/euf/libexpat-bbdfcfef/expat/lib/xmlparse.c 
	./run.sh XML_ErrorString


xml_gen:
	git diff --color=always  --no-index ~/.cache/euf/libexpat-811c41e3/expat/lib/xmlparse.c ~/.cache/euf/libexpat-b1d03960/expat/lib/xmlparse.c | grep -A 15 --color=always  "XML_ErrorString("
	./euf.py --config expat/gen.json

# Harnesses:  ~/.cache/euf/libexpat-322ca04c/expat/.harnesses
xml_rand:
	./euf.py --config expat/rand.json

