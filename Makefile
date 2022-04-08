#== Examples ==#

# Basic example of EUF
basic:
	./euf.py --config tests/configs/basic.json --diff	
	./euf.py --config tests/configs/basic.json	

# Best case example with custom drivers
reduce:
	@rm -rf 	 /home/jonas/.cache/euf/matrix-d85085cb/.harnesses
	@mkdir -p  /home/jonas/.cache/euf/matrix-d85085cb/.harnesses
	@cp tests/drivers/matrix_init_driver_id.c 		/home/jonas/.cache/euf/matrix-d85085cb/.harnesses/matrix_init_id.c
	@cp tests/drivers/matrix_init_driver.c 				/home/jonas/.cache/euf/matrix-d85085cb/.harnesses/matrix_init.c
	@cp tests/drivers/matrix_sum_driver_id.c 			/home/jonas/.cache/euf/matrix-d85085cb/.harnesses/matrix_sum_id.c
	@cp tests/drivers/matrix_sum_driver.c 				/home/jonas/.cache/euf/matrix-d85085cb/.harnesses/matrix_sum.c
	./euf.py --config tests/configs/matrix.json

# Basic example with influential changes
inf:
	@rm -rf 	 /home/jonas/.cache/euf/matrix-8b39495d/.harnesses
	@mkdir -p  /home/jonas/.cache/euf/matrix-8b39495d/.harnesses
	@cp tests/drivers/matrix_init_driver_id.c 		/home/jonas/.cache/euf/matrix-8b39495d/.harnesses/matrix_init_id.c
	@cp tests/drivers/matrix_init_driver.c 				/home/jonas/.cache/euf/matrix-8b39495d/.harnesses/matrix_init.c
	@cp tests/drivers/matrix_sum_driver_id.c 			/home/jonas/.cache/euf/matrix-8b39495d/.harnesses/matrix_sum_id.c
	@cp tests/drivers/matrix_sum_driver.c 				/home/jonas/.cache/euf/matrix-8b39495d/.harnesses/matrix_sum.c
	./euf.py --config tests/configs/matrix_inf.json

# Basic example of CBMC
bmc:
	bat ./tests/drivers/example.c
	cbmc ./tests/drivers/example.c --unwind 5 -DCBMC --object-bits 12 --function euf_main --property euf_main.assertion.1

# Analysis of a specific function which has a influential change
xml:
	@FILE=xmlparse.c \
	SHOW_DIFF=1 \
	./expat/test_harness.sh expat/cases/811c41_b1d039.json XML_ErrorString

# Analysis of a specific function which has a equivalent (based on return value) change
entr:
	@FILE=xmlparse.c \
	SHOW_DIFF=1 \
	./expat/test_harness.sh expat/cases/10d34296_f178826b.json ENTROPY_DEBUG

empty:
	./euf.py --config expat/cases/6aa6a82d_c9e1ac00.json --diff
	./euf.py --config expat/cases/6aa6a82d_c9e1ac00.json

rand:
	./euf.py --config .rand/0d21b17b_9288cd54_libexpat.json
	
# Example run on another project without CBMC
onig:
	./euf.py --config tests/configs/oniguruma.json
