ARG=5
UNWIND=10
DIFF_FILE=diffs/strcpy.diff
DEP=strcpy

.PHONY: smt clean run bmc

bin/cia: src/*
	@mkdir -p bin
	clang -I include $^ -o $@

run: bin/cia
	$< $(ARG)

#---- Bounded Model Checker ----#
# CBMC is meant to assess if an assertion is true
# for all possible executions of a program
# To avoid infinite execution for inf loops,
# we need to specify an --unwind depth
bmc:
	cbmc --unwind $(UNWIND) -I include src/*

#--- Basic IR diff -------------#
diff:
	mkdir -p ir

	clang -I include -S -emit-llvm src/$(DEP).c -o ir/$(DEP).ll.old

	# Patch source and recompile
	patch -p1 < $(DIFF_FILE)

	clang -I include -S -emit-llvm src/$(DEP).c -o ir/$(DEP).ll.new

	# Revert patch
	patch -p1 -R < $(DIFF_FILE)

	# llvm-diff --color strcpy.ll.new strcpy.ll.old
	diff --color=always -y ir/$(DEP).ll.old ir/$(DEP).ll.new

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
