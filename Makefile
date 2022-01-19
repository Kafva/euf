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

#---- llvm2smt ----#
# We need to manually insert (check-sat) into the emitted .smt 
# code to check satisifiability
smt:
	llvm2smt ./ir/shufflevector.ll > shufflevector.smt
	@echo -e "(check-sat)\n(get-model)" >> smt/shufflevector.smt 
	z3 smt/shufflevector.smt

clean:
	rm -f ir/*.old.* ir/*.new.*
