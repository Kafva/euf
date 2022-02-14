UNWIND=30
DIFF_FILE=toy/diffs/strcpy.diff
DEP=strcpy
CFLAGS=-DCBMC=false

.PHONY: smt clean run bmc diff


#---- Bounded Model Checker ----#
# CBMC is meant to assess if an assertion is true
# for all possible executions of a program
# To avoid infinite execution for inf loops,
# we need to specify an --unwind depth
bmc:
	cbmc  --trace --function main -DCBMC=true --unwind $(UNWIND) -I toy/include toy/src/* $(ARGS)


#---- llvm2smt ----#
# We need to manually insert (check-sat) and an
# associated (assert) statement into the emitted .smt 
# code to check satisifiability
# The assert statement 
smt:
	./scripts/llvm2smt.sh ./toy/ir/shufflevector.ll > toy/smt/shufflevector.smt
	@echo -e "(assert (and (= |%a_@lhs| |%a_@rhs|) (= |%b_@lhs| |%b_@rhs|) (not (= |_@lhs_result| |_@rhs_result|))))\n(check-sat)" >> toy/smt/shufflevector.smt 
	z3 toy/smt/shufflevector.smt



#--- Toy examples ---#
bin/toy: toy/src/*
	@mkdir -p bin
	clang -I toy/include $(CFLAGS) $^ -o $@

run: bin/toy
	$< "ABCDEGHIJ" 

analyze:
	clang -I toy/include $(CFLAGS) -analyze -analyzer-checker=core.DivideZero toy/src/*

diff:
	@mkdir -p toy/ir

	clang -I toy/include -S -emit-llvm toy/src/$(DEP).c -o toy/ir/$(DEP).old.ll

	# Patch source and recompile
	patch -p1 < $(DIFF_FILE)

	clang -I toy/include -S -emit-llvm toy/src/$(DEP).c -o toy/ir/$(DEP).new.ll

	# Revert patch
	patch -p1 -R < $(DIFF_FILE)

	# llvm-diff --color strcpy.new.ll strcpy.old.ll
	diff --color=always -y toy/ir/$(DEP).old.ll toy/ir/$(DEP).new.ll; true

clean:
	rm -f toy/ir/*.old.* toy/ir/*.new.* bin/*
