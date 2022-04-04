basic:
	-git diff --no-index ~/.cache/euf/matrix-d85085cb/src/matrix.c ~/.cache/euf/matrix-867b6581/src/matrix.c
	./euf.py --config tests/configs/basic.json	

onig:
	./euf.py --config tests/configs/oniguruma.json

onig_v:
	./euf.py --config tests/configs/oniguruma_v.json

onig_cbmc:
	make -C cbmc example

xml:
	head -n20 expat/drivers/XML_ErrorString.c | bat --language c --style full
	./run.sh XML_ErrorString

xml_cbmc:
	git diff --color=always  --no-index ~/.cache/euf/libexpat-811c41e3/expat/lib/xmlparse.c ~/.cache/euf/libexpat-b1d03960/expat/lib/xmlparse.c | grep -A 15 --color=always  "XML_ErrorString("
	./euf.py --config expat/gen.json

xml_rand:
	./euf.py --config expat/rand.json

