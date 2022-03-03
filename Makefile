SHELL=/bin/bash
NEW_DIR=~/.cache/euf
SMACK_DEPS=~/Repos/smack-deps
VERBOSE=0

ifneq (,$(findstring Ubuntu,$(shell uname -a))) # if on Ubuntu
LIBCLANG=/usr/lib/llvm-12/lib/libclang.so.1
else
LIBCLANG=/usr/lib/libclang.so.13.0.1
endif

.PHONY: smt clean run bmc diff oni oniv cbmc matrix
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
	./euf.py --libclang $(LIBCLANG) --commit-old 9a1c4e41e8d3fd8fe9d1bd8eeb8b1e1df21da37f \
		 --commit-new d5f9166bacfb3757dfd6117310ad54ab749b11f9 \
		 --verbose $(VERBOSE) \
		 --nproc 10 \
		 --dep-only crypto/evp/ctrl_params_translate.c \
		 --dependency ../openssl ../curl


#---- ../main => ../matrix tests  ----#
# 	get_nearest_even():
#OLD_COMMIT=ddd3658debc3f0452fefbfe6ebe6bff12168752b
#NEW_COMMIT_EQUIV=10ebe64c17a74c01ee010dcbeb7f005a918dd6ce
#NEW_COMMIT_INF=0ef44ff525516f63d3104122261000526db7ab14
#DRIVER=~/Repos/euf/tests/nearest_even_driver.c
#SMACK_DRIVER=~/Repos/euf/tests/smack_nearest_even_driver.c

# 	matrix_sum():
#OLD_COMMIT=e83bd3d253964d2f891d221980874c57cbfa0380
#NEW_COMMIT_EQUIV=1c1d5b0ea012c69576f94c8b31baee4e5eb16691
#NEW_COMMIT_INF=2612a843731f6e851f96879cf913841a26137a2d
#DRIVER=~/Repos/euf/tests/matrix_sum_driver.c
#SMACK_DRIVER=~/Repos/euf/tests/smack_matrix_sum_driver.c

#	matrix_init()
OLD_COMMIT=77f5d019703f2eb12988a62d2be53216df8d4dab
NEW_COMMIT_EQUIV=30b4d5160a3a061eacd165803aa8a40d0d0097b0
NEW_COMMIT_INF=dc838cec7a6ebc47ad5f49107367164da2577a59
DRIVER=~/Repos/euf/tests/matrix_init_driver.c
SMACK_DRIVER=~/Repos/euf/tests/smack_matrix_init_driver.c

#	regexec.c
#OLD_COMMIT=65a9b1aa03c9bc2dc01b074295b9603232cb3b78
#NEW_COMMIT_EQUIV=1bd71be9437db6ede501fc88102961423c1ab74c
#NEW_COMMIT_INF=1bd71be9437db6ede501fc88102961423c1ab74c
#DRIVER=~/Repos/euf/tests/regexec_driver.c

matrix_v:
	./scripts/euf.sh -V \
		-o $(OLD_COMMIT)  \
		-n $(NEW_COMMIT_INF)  \
		-d ../matrix ../main | bat
matrix:
	./euf.py --libclang $(LIBCLANG) --commit-old $(OLD_COMMIT) \
		 --commit-new $(NEW_COMMIT_INF) \
		 --verbose $(VERBOSE) \
		 --dependency ../matrix ../main

matrix_ci:
	LIBCLANG=$(LIBCLANG) \
	NEW_DIR=$(NEW_DIR) \
	COMMIT_OLD=$(OLD_COMMIT) \
	COMMIT_NEW=$(NEW_COMMIT_INF) \
	DEP_FILE_NEW=src/matrix.c \
	DEP_FILE_OLD=src/matrix.c \
	PROJECT_FILE=src/calc.c \
	DEP_OLD=~/Repos/matrix \
	PROJECT=~/Repos/main \
	OUTDIR=~/Repos/euf/tests \
	DRIVER=$(DRIVER) \
	./scripts/cbmc.sh

matrix_ce:
	LIBCLANG=$(LIBCLANG) \
	NEW_DIR=$(NEW_DIR) \
	COMMIT_OLD=$(OLD_COMMIT) \
	COMMIT_NEW=$(NEW_COMMIT_EQUIV) \
	DEP_FILE_NEW=src/matrix.c \
	DEP_FILE_OLD=src/matrix.c \
	PROJECT_FILE=src/calc.c \
	DEP_OLD=~/Repos/matrix \
	PROJECT=~/Repos/main \
	OUTDIR=~/Repos/euf/tests \
	DRIVER=$(DRIVER) \
	./scripts/cbmc.sh

matrix_sce:
	LIBCLANG=$(LIBCLANG) \
	NEW_DIR=$(NEW_DIR) \
	COMMIT_OLD=$(OLD_COMMIT) \
	COMMIT_NEW=$(NEW_COMMIT_EQUIV) \
	DEP_FILE_NEW=src/matrix.c \
	DEP_FILE_OLD=src/matrix.c \
	PROJECT_FILE=src/calc.c \
	DEP_OLD=~/Repos/matrix \
	PROJECT=~/Repos/main \
	OUTDIR=~/Repos/euf/tests \
	DRIVER=$(SMACK_DRIVER) \
	./scripts/smack.sh

matrix_sci:
	LIBCLANG=$(LIBCLANG) \
	NEW_DIR=$(NEW_DIR) \
	COMMIT_OLD=$(OLD_COMMIT) \
	COMMIT_NEW=$(NEW_COMMIT_INF) \
	DEP_FILE_NEW=src/matrix.c \
	DEP_FILE_OLD=src/matrix.c \
	PROJECT_FILE=src/calc.c \
	DEP_OLD=~/Repos/matrix \
	PROJECT=~/Repos/main \
	OUTDIR=~/Repos/euf/tests \
	DRIVER=$(SMACK_DRIVER) \
	./scripts/smack.sh

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
	./euf.py --libclang $(LIBCLANG) --commit-old 65a9b1aa03c9bc2dc01b074295b9603232cb3b78 \
		 --commit-new 1bd71be9437db6ede501fc88102961423c1ab74c \
		 --project-only src/builtin.c \
		 --verbose $(VERBOSE) \
		 --dep-only src/regexec.c \
		 --dependency ../oniguruma ../jq

regexec_v:
	./scripts/euf.sh -f regexec.c \
		-o 65a9b1aa03c9bc2dc01b074295b9603232cb3b78 \
		-n 1bd71be9437db6ede501fc88102961423c1ab74c \
		-d ../oniguruma ../jq | bat
regexec_c:
	COMMIT_OLD=65a9b1aa03c9bc2dc01b074295b9603232cb3b78 \
	COMMIT_NEW=1bd71be9437db6ede501fc88102961423c1ab74c \
	DEP_FILE_NEW=src/regexec.c \
	DEP_FILE_OLD=regexec.c \
	PROJECT_FILE=src/builtin.c \
	DEP_OLD=~/Repos/oniguruma \
	DEP_NEW=/tmp/oniguruma \
	PROJECT=~/Repos/jq \
	OUTDIR=~/Repos/euf/tests \
	DRIVER=$$OUTDIR/regexec_driver.c \
	./scripts/cbmc.sh

regexec_d:
	./euf.py --libclang $(LIBCLANG) --commit-old 65a9b1aa03c9bc2dc01b074295b9603232cb3b78 \
		 --commit-new 1bd71be9437db6ede501fc88102961423c1ab74c \
		 --dep-only src/regexec.c \
		 --project-only src/builtin.c \
		 --dump-full \
		 --dependency ../oniguruma ../jq


regexec_ce:
	LIBCLANG=$(LIBCLANG) \
	NEW_DIR=$(NEW_DIR) \
	COMMIT_OLD=$(OLD_COMMIT) \
	COMMIT_NEW=$(NEW_COMMIT_EQUIV) \
	DEP_FILE_NEW=src/regexec.c \
	DEP_FILE_OLD=regexec.c \
	PROJECT_FILE=src/builtin.c \
	DEP_OLD=~/Repos/oniguruma \
	PROJECT=~/Repos/jq \
	OUTDIR=~/Repos/euf/tests \
	DRIVER=$(DRIVER) \
	./scripts/cbmc.sh


regexec_ast:
	clang -fsyntax-only -fno-color-diagnostics -Xclang -ast-dump ~/Repos/oniguruma/src/regexec.c > regexec.ast

# Note that jq actually has a way older version of oniguruma under ./modules
euc_jp:
	./euf.py --libclang $(LIBCLANG) --commit-old 69545dabdbc1f7a9fb5ebc329c0b7987052b2a44 \
		 --commit-new a2ac402a3549713e6c909752937b7a54f559beb8 \
		 --dep-only src/euc_jp.c \
		 --dependency ../oniguruma ../jq
euc_jp_v:
	./scripts/euf.sh -V -o 69545dabdbc1f7a9fb5ebc329c0b7987052b2a44 \
		-n a2ac402a3549713e6c909752937b7a54f559beb8 \
		-d ../oniguruma ../jq | bat
bug_fix_c:
	clang -fsyntax-only -Xclang -ast-dump ~/Repos/oniguruma/sample/bug_fix.c



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
smack_docker:
	./scripts/smack.sh -f tests/smack_test.c /mnt/smack_test.c --check assertions --entry-points main --unroll 3

# We can derive the raw .bpl conversion using
#	clang -I/home/jonas/Repos/smack/share/smack/include -S -emit-llvm ./tests/smack_test.c -o ir/smack_test.ll
#	./scripts/smack.sh -f ir/fib.ll /mnt/fib.ll --no-verify -bpl /mnt/fib.bpl
# The output file contains a lot of auxiliary info but at its core the representation is very straight-forward
bpl_docker:
	./scripts/smack.sh -f tests/smack_test.c /mnt/smack_test.c --no-verify -bpl /mnt/smack_test.bpl

smack:
	PATH="$(SMACK_DEPS)/z3/bin:$$PATH"
	PATH="$(SMACK_DEPS)/boogie:$$PATH"
	export PATH="$(SMACK_DEPS)/corral:$$PATH"
	smack tests/smack_test.c --check assertions --entry-points main --unroll 3 --solver z3

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
