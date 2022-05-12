#== Examples ==#

# Basic examples of CBMC
bmc1:
	@bat ./tests/drivers/example.c
	@read
	cbmc ./tests/drivers/example.c \
		--object-bits 12 --function euf_main --property euf_main.assertion.1
bmc2:
	@bat ./tests/drivers/example2.c
	@read
	cbmc ./tests/drivers/example2.c \
		--object-bits 12 --function euf_main --property euf_main.assertion.1 \
		--trace

# Basic example of EUF
basic:
	./euf.py --config tests/configs/basic.json --diff	
	./euf.py --config tests/configs/basic.json	

# Best case example with custom drivers
reduce:
	@rm -rf 	 ~/.cache/euf/matrix-d85085cb/.harnesses
	@mkdir -p  ~/.cache/euf/matrix-d85085cb/.harnesses
	@cp tests/drivers/matrix_init_driver_id.c \
		~/.cache/euf/matrix-d85085cb/.harnesses/matrix_init_id.c
	@cp tests/drivers/matrix_init_driver.c \
		~/.cache/euf/matrix-d85085cb/.harnesses/matrix_init.c
	@cp tests/drivers/matrix_sum_driver_id.c \
		~/.cache/euf/matrix-d85085cb/.harnesses/matrix_sum_id.c
	@cp tests/drivers/matrix_sum_driver.c \
		~/.cache/euf/matrix-d85085cb/.harnesses/matrix_sum.c
	./euf.py --config tests/configs/matrix.json

# Basic example with influential changes
inf:
	@rm -rf 	 ~/.cache/euf/matrix-8b39495d/.harnesses
	@mkdir -p  ~/.cache/euf/matrix-8b39495d/.harnesses
	@cp tests/drivers/matrix_init_driver_id.c \
		~/.cache/euf/matrix-8b39495d/.harnesses/matrix_init_id.c
	@cp tests/drivers/matrix_init_driver.c \
		~/.cache/euf/matrix-8b39495d/.harnesses/matrix_init.c
	@cp tests/drivers/matrix_sum_driver_id.c \
		~/.cache/euf/matrix-8b39495d/.harnesses/matrix_sum_id.c
	@cp tests/drivers/matrix_sum_driver.c \
		~/.cache/euf/matrix-8b39495d/.harnesses/matrix_sum.c
	./euf.py --config tests/configs/matrix_inf.json
