.PHONY: smt clean run bmc diff oni oniv cbmc matrix

#---- CBMC ----#
# CBMC is meant to assess if an assertion is true
# for all possible executions of a program
# To avoid infinite execution for inf loops,
# we need to specify an --unwind depth
# Could be useful:
# 	--drop-unused-functions
cbmc:
	cbmc  --trace -DCBMC --z3 --function main --unwind 10 -I tests/ tests/cbmc_test.c $(ARGS)

# Show human readable goto program
#	cbmc --show-goto-functions -DCBMC -I tests tests/cbmc_test.c
goto:
	goto-cc -DCBMC -I tests/ tests/cbmc_test.c -o ir/cbmc_test.gc

#---- Smack -----#
# A tool to convert `C -> LLVM -> BPL`
# The intermediate step of LLVM should be beneficial in regards to
# correctness since it is closer to the actual output code
# Should be invoked from /usr/local/bin/smack and NOT from ~/bin/smack
#
# Basic invocation
#	./scripts/smack.sh -f ir/fib.ll /fib.ll
#
# Smack can accept more than one source file (both C and LLVM work, with differing results...)
smack:
	./scripts/smack.sh -f tests/smack_test.c /mnt/smack_test.c --check assertions --entry-points main --unroll 3

# We can derive the raw .bpl conversion using
#	clang -I/home/jonas/Repos/smack/share/smack/include -S -emit-llvm ./tests/smack_test.c -o ir/smack_test.ll
#	./scripts/smack.sh -f ir/fib.ll /mnt/fib.ll --no-verify -bpl /mnt/fib.bpl
# The output file contains a lot of auxiliary info but at its core the representation is very straight-forward
bpl:
	./scripts/smack.sh -f tests/smack_test.c /mnt/smack_test.c --no-verify -bpl /mnt/smack_test.bpl

#---- curl => openssl tests ----#
# 9542 crypto/ec/ecp_nistz256_table.c
# 5647 crypto/ec/curve25519.c      (Almost all functions are renamed...)
# 4162 crypto/evp/e_aes.c
# 3454 crypto/x509/x509_vfy.c
# 3440 crypto/ec/ec_curve.c
# 2769 crypto/evp/ctrl_params_translate.c
# 2437 crypto/evp/p_lib.c
# 2378 crypto/ec/ecp_nistp256.c
ctrlp_v:
	./scripts/euf.sh -f crypto/evp/ctrl_params_translate.c \
		-o  9a1c4e41e8d \
		-n  d5f9166bacf \
		-d ../openssl ../curl | bat
ctrlp:
	./euf.py --commit-old 9a1c4e41e8d3fd8fe9d1bd8eeb8b1e1df21da37f \
		 --commit-new d5f9166bacfb3757dfd6117310ad54ab749b11f9 \
		 --verbose 0 \
		 --nproc 10 \
		 --dep-only crypto/evp/ctrl_params_translate.c \
		 --dependency ../openssl ../curl


#---- main => matrix tests  ----#
matrix_v:
	./scripts/euf.sh -V \
		-o  4c9d0424375a8511adecaa3fa820a47ea0b71e98 \
		-n  8133ef044a40ce9257b18fdf9e874427fef2dc44 \
		-d ./matrix ./main | bat
matrix:
	./euf.py --commit-old 4c9d0424375a8511adecaa3fa820a47ea0b71e98 \
		 --commit-new 8133ef044a40ce9257b18fdf9e874427fef2dc44 \
		 --verbose 3 \
		 --dependency ./matrix ./main

#---- jq => oniguruma tests ----#
# The recipe names correspond to the source files in the project/dependency
# that are being processed
# _c: clang -ast-dump
# _v: view diff

# Includes a change to `onig_search` in `regexec.c` which is invoked 
# once in `src/builtin.c` of jq
# 	git blame -L 3374,+100 src/regexec.c
# Note that regexec.c is moved from ./ to ./src between the commits
regexec:
	./euf.py --commit-old 65a9b1aa03c9bc2dc01b074295b9603232cb3b78 \
		 --commit-new 1bd71be9437db6ede501fc88102961423c1ab74c \
		 --project-only src/builtin.c \
		 --verbose 2 \
		 --dep-only src/regexec.c \
		 --dependency ../oniguruma ../jq

regexec_v:
	./scripts/euf.sh -f regexec.c \
		-o 65a9b1aa03c9bc2dc01b074295b9603232cb3b78 \
		-n 1bd71be9437db6ede501fc88102961423c1ab74c \
		-d ../oniguruma ../jq | bat
regexecc:
	clang -fsyntax-only -fno-color-diagnostics -Xclang -ast-dump ~/Repos/oniguruma/src/regexec.c > regexec.ast
	./builtin.sh

regexec_d:
	./euf.py --commit-old 65a9b1aa03c9bc2dc01b074295b9603232cb3b78 \
		 --commit-new 1bd71be9437db6ede501fc88102961423c1ab74c \
		 --dep-only src/regexec.c \
		 --project-only src/builtin.c \
		 --dump-full \
		 --dependency ../oniguruma ../jq

# Note that jq actually has a way older version of oniguruma under ./modules
euc_jp:
	./euf.py --commit-old 69545dabdbc1f7a9fb5ebc329c0b7987052b2a44 \
		 --commit-new a2ac402a3549713e6c909752937b7a54f559beb8 \
		 --dep-only src/euc_jp.c \
		 --dependency ../oniguruma ../jq
euc_jp_v:
	./scripts/euf.sh -V -o 69545dabdbc1f7a9fb5ebc329c0b7987052b2a44 \
		-n a2ac402a3549713e6c909752937b7a54f559beb8 \
		-d ../oniguruma ../jq | bat
bug_fix_c:
	clang -fsyntax-only -Xclang -ast-dump ~/Repos/oniguruma/sample/bug_fix.c




#---- llvm2smt ----#
# We need to manually insert (check-sat) and an
# associated (assert) statement into the emitted .smt 
# code to check satisifiability
# The assert statement 
llvm2smt:
	./scripts/llvm2smt.sh ./toy/ir/shufflevector.ll > toy/smt/shufflevector.smt
	@echo -e "(assert (and (= |%a_@lhs| |%a_@rhs|) (= |%b_@lhs| |%b_@rhs|) (not (= |_@lhs_result| |_@rhs_result|))))\n(check-sat)" >> toy/smt/shufflevector.smt 
	z3 toy/smt/shufflevector.smt



#--- Toy examples ---#
DIFF_FILE=toy/diffs/strcpy.diff
DEP=strcpy
CFLAGS=-DCBMC=false


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
