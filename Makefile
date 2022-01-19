ARG=5
.PHONY: smt clean run bmc

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
#@echo -e "(check-sat)\n(get-model)" >> smt/shufflevector.smt 
smt:
	llvm2smt ./ir/shufflevector.ll > smt/shufflevector.smt
	@echo -e "(check-sat)" 		    >> smt/shufflevector.smt 
	z3 smt/shufflevector.smt

clean:
	rm -f ir/*.old.* ir/*.new.*
