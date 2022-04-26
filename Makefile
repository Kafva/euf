#== Examples ==#

# Basic example of EUF
basic:
	./euf.py --config tests/configs/basic.json --diff	
	./euf.py --config tests/configs/basic.json	

# Best case example with custom drivers
reduce:
	@rm -rf 	 /home/jonas/.cache/euf/matrix-d85085cb/.harnesses
	@mkdir -p  /home/jonas/.cache/euf/matrix-d85085cb/.harnesses
	@cp tests/drivers/matrix_init_driver_id.c \
		/home/jonas/.cache/euf/matrix-d85085cb/.harnesses/matrix_init_id.c
	@cp tests/drivers/matrix_init_driver.c \
		/home/jonas/.cache/euf/matrix-d85085cb/.harnesses/matrix_init.c
	@cp tests/drivers/matrix_sum_driver_id.c \
		/home/jonas/.cache/euf/matrix-d85085cb/.harnesses/matrix_sum_id.c
	@cp tests/drivers/matrix_sum_driver.c \
		/home/jonas/.cache/euf/matrix-d85085cb/.harnesses/matrix_sum.c
	./euf.py --config tests/configs/matrix.json

# Basic example with influential changes
inf:
	@rm -rf 	 /home/jonas/.cache/euf/matrix-8b39495d/.harnesses
	@mkdir -p  /home/jonas/.cache/euf/matrix-8b39495d/.harnesses
	@cp tests/drivers/matrix_init_driver_id.c \
		/home/jonas/.cache/euf/matrix-8b39495d/.harnesses/matrix_init_id.c
	@cp tests/drivers/matrix_init_driver.c \
		/home/jonas/.cache/euf/matrix-8b39495d/.harnesses/matrix_init.c
	@cp tests/drivers/matrix_sum_driver_id.c \
		/home/jonas/.cache/euf/matrix-8b39495d/.harnesses/matrix_sum_id.c
	@cp tests/drivers/matrix_sum_driver.c \
		/home/jonas/.cache/euf/matrix-8b39495d/.harnesses/matrix_sum.c
	./euf.py --config tests/configs/matrix_inf.json

# Basic example of CBMC
bmc:
	@bat ./tests/drivers/example.c
	@read
	cbmc ./tests/drivers/example.c --unwind 5 -DCBMC \
		--object-bits 12 --function euf_main --property euf_main.assertion.1

# Analysis of a specific function which has a influential change
xml_diff:
	@FILE=expat/lib/xmlparse.c \
	SHOW_DIFF=true \
	EXIT=true \
	CONTEXT_LINES=103 \
	./scripts/test_harness.sh tests/configs/xml.json XML_ErrorString
xml:
	@FILE=xmlparse.c \
	./scripts/test_harness.sh tests/configs/xml.json XML_ErrorString

# Analysis of a specific function which has a 
# equivalent (based on return value) change
entr_diff:
	@FILE=expat/lib/xmlparse.c \
	SHOW_DIFF=true \
	EXIT=true \
	CONTEXT_LINES=10 \
	./scripts/test_harness.sh tests/configs/entr.json ENTROPY_DEBUG
entr:
	@FILE=expat/lib/xmlparse.c \
	./scripts/test_harness.sh tests/configs/entr.json ENTROPY_DEBUG

# Impact set example
entr_full:
	./euf.py --config tests/configs/entr_impact.json

# Huge reduction example
usb:
	./euf.py --config tests/config/usb_example.json

#== dev ==#
# To check if these reduced changes are actually FPs
# 1. Open the FILE and modify the return value manually
# 2. Recompile (done automatically when running)
# 3. Run the recipe, if the verification fails, we do not have a FP
usb_verify:
	@EXIT=false PROJ=libusb \
	FILE=libusb/core.c \
	SHOW_DIFF=true \
	CONTEXT_LINES=30 \
	./scripts/test_harness.sh \
	examples/usb/cases/libusb_5d089e49_f7084fea.json \
	libusb_attach_kernel_driver

fp_verify2:
	@EXIT=false PROJ=libusb \
	FILE=libusb/core.c \
	SHOW_DIFF=true \
	SILENT=false \
	SHOW_FUNC=true \
	CONTEXT_LINES=30 \
	./scripts/test_harness.sh \
	examples/usb/cases/libusb_5d089e49_f7084fea.json \
	libusb_free_streams

fp_verify3:
	@EXIT=false PROJ=libusb \
	FILE=libusb/core.c \
	SHOW_DIFF=true \
	CONTEXT_LINES=30 \
	./scripts/test_harness.sh \
	examples/usb/cases/libusb_5d089e49_f7084fea.json \
	libusb_claim_interface

onig_verify:
	@EXIT=false PROJ=oniguruma \
	FILE=src/regcomp.c \
	SHOW_DIFF=true \
	CONTEXT_LINES=27 \
	./scripts/test_harness.sh \
	examples/onig/cases/libonig_d3d6_6f8c.json \
	renumber_node_backref

onig_verify2:
	@EXIT=false PROJ=oniguruma \
	FILE=src/regcomp.c \
	SHOW_DIFF=true \
	CONTEXT_LINES=0 \
	SILENT=false \
	./scripts/test_harness.sh \
	examples/onig/cases/libonig_d3d6_6f8c.json \
	subexp_recursive_check_trav

onig_verify3:
	@EXIT=false PROJ=oniguruma \
	FILE=src/regcomp.c \
	SHOW_DIFF=true \
	CONTEXT_LINES=30 \
	./scripts/test_harness.sh \
	examples/onig/cases/libonig_d3d6_6f8c.json \
	unset_addr_list_fix

