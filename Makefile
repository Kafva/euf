ARG=5

bin/cia: src/*
	@mkdir -p bin
	clang -I include $^ -o $@

run: bin/cia
	$< $(ARG)

#---- Bounded Model Checker ----#
# CBMC is meant to assess if an assertion is true
# foe all possible executions of a program
bmc:
	cbmc -I include src/*


clean:
	rm -f ir/*
