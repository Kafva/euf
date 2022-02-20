UNWIND=30
DIFF_FILE=toy/diffs/strcpy.diff
DEP=strcpy
CFLAGS=-DCBMC=false

.PHONY: smt clean run bmc diff oni oniv


# Note that jq actually has a way older version of oniguruma under ./modules

onig: go-clang-bindings
	 go run main.go -D -o 69545dabdbc1f7a9fb5ebc329c0b7987052b2a44 -n a2ac402a3549713e6c909752937b7a54f559beb8 -d ../oniguruma ../jq
oni:
	./euf.py -o 69545dabdbc1f7a9fb5ebc329c0b7987052b2a44 -n a2ac402a3549713e6c909752937b7a54f559beb8 -d ../oniguruma ../jq
oniv:
	./scripts/euf.sh -V -o 69545dabdbc1f7a9fb5ebc329c0b7987052b2a44 -n a2ac402a3549713e6c909752937b7a54f559beb8 -d ../oniguruma ../jq
onic:
	clang -fsyntax-only -Xclang -ast-dump ~/Repos/oniguruma/sample/bug_fix.c

# We need some C-headers for the bindings between Golang and C to work
go-clang-bindings:
	CGO_LDFLAGS="-L`llvm-config --libdir`" go install github.com/go-clang/clang-v3.9/...
	mkdir -p $@
	cp -r ~/.go/pkg/mod/github.com/go-clang/clang-v3.9@*/clang/* $@
	chmod +w go-clang-bindings/**/**


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
