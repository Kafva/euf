SHELL=/bin/bash
EUF_CACHE=~/.cache/euf
SMACK_DEPS=~/Repos/smack-deps
VERBOSE=2

ifneq (,$(findstring Ubuntu,$(shell uname -a))) # if on Ubuntu
LIBCLANG=/usr/lib/llvm-12/lib/libclang.so.1
else
LIBCLANG=/usr/lib/libclang.so.13.0.1
endif

.PHONY: clean 
# The recipe names correspond to the source files in the project/dependency
# that are being processed
# _c: clang -ast-dump
# _v: view diff

#	oniguruma st.c
#OLD_COMMIT=65a9b1aa03c9bc2dc01b074295b9603232cb3b78
#NEW_COMMIT_EQUIV=e8bd631e187873a2085899bfc99f2f2c6af2adbd
#DRIVER=~/Repos/euf/drivers/st_newsize_driver.c
#UNWIND=2

# 	get_nearest_even():
#OLD_COMMIT=ddd3658debc3f0452fefbfe6ebe6bff12168752b
#NEW_COMMIT_EQUIV=10ebe64c17a74c01ee010dcbeb7f005a918dd6ce
#NEW_COMMIT_INF=0ef44ff525516f63d3104122261000526db7ab14
#DRIVER=~/Repos/euf/drivers/nearest_even_driver.c
#SMACK_DRIVER=~/Repos/euf/drivers/smack_nearest_even_driver.c

# 	matrix_sum():
#OLD_COMMIT=e83bd3d253964d2f891d221980874c57cbfa0380
#NEW_COMMIT_EQUIV=1c1d5b0ea012c69576f94c8b31baee4e5eb16691
#NEW_COMMIT_INF=2612a843731f6e851f96879cf913841a26137a2d
#DRIVER=~/Repos/euf/drivers/matrix_sum_driver.c
#SMACK_DRIVER=~/Repos/euf/drivers/smack_matrix_sum_driver.c

#	matrix_init()
#OLD_COMMIT=77f5d019703f2eb12988a62d2be53216df8d4dab
#NEW_COMMIT_EQUIV=30b4d5160a3a061eacd165803aa8a40d0d0097b0
#NEW_COMMIT_INF=dc838cec7a6ebc47ad5f49107367164da2577a59
#DRIVER=~/Repos/euf/drivers/matrix_init_driver.c
#SMACK_DRIVER=~/Repos/euf/drivers/smack_matrix_init_driver.c
#UNWIND=10

#	libexpat
OLD_COMMIT=bbdfcfef4747d2d66e81c19f4a55e29e291aa171
NEW_COMMIT_INF=e07e39477157723af276abc3a3d04941abd589bb

#---- ? => ../libeXpat examples ----#
# The _impl.c files are for some reason not part of the compile_commands.json database...
expat:
	./euf.py --libclang $(LIBCLANG) --commit-old $(OLD_COMMIT) \
		 --commit-new $(NEW_COMMIT_INF) \
		 --verbose $(VERBOSE) \
		 --dep-source-root ../libexpat/expat \
		 --exclude-dirs ./expat/tests \
		 --force-recompile \
		 --dependency ../libexpat ../main

expat_v:
	./scripts/euf.sh -V \
		-o $(OLD_COMMIT)  \
		-n $(NEW_COMMIT_INF)  \
		-d ../libexpat ../main | bat

#---- ../main => ../matrix examples  ----#
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
	./euf.py --libclang $(LIBCLANG) --commit-old $(OLD_COMMIT) \
		 --commit-new $(NEW_COMMIT_INF) \
		 --verbose $(VERBOSE) \
		 --full --driver $(DRIVER) \
		 --unwind $(UNWIND) \
		 --dependency ../matrix ../main

matrix_ce:
	./euf.py --libclang $(LIBCLANG) --commit-old $(OLD_COMMIT) \
		 --commit-new $(NEW_COMMIT_EQUIV) \
		 --verbose $(VERBOSE) \
		 --full --driver $(DRIVER) \
		 --unwind $(UNWIND) \
		 --dependency ../matrix ../main

matrix_sce:
	LIBCLANG=$(LIBCLANG) \
	EUF_CACHE=$(EUF_CACHE) \
	COMMIT_OLD=$(OLD_COMMIT) \
	COMMIT_NEW=$(NEW_COMMIT_EQUIV) \
	DEP_FILE_NEW=src/matrix.c \
	DEP_FILE_OLD=src/matrix.c \
	PROJECT_FILE=src/calc.c \
	DEP=~/Repos/matrix \
	PROJECT=~/Repos/main \
	OUTDIR=~/Repos/euf/tests \
	DRIVER=$(SMACK_DRIVER) \
	./scripts/smack.sh

matrix_sci:
	LIBCLANG=$(LIBCLANG) \
	EUF_CACHE=$(EUF_CACHE) \
	COMMIT_OLD=$(OLD_COMMIT) \
	COMMIT_NEW=$(NEW_COMMIT_INF) \
	DEP_FILE_NEW=src/matrix.c \
	DEP_FILE_OLD=src/matrix.c \
	PROJECT_FILE=src/calc.c \
	DEP=~/Repos/matrix \
	PROJECT=~/Repos/main \
	OUTDIR=~/Repos/euf/tests \
	DRIVER=$(SMACK_DRIVER) \
	./scripts/smack.sh

#---- jq => oniguruma examples ----#
st:
	./euf.py --libclang $(LIBCLANG) --commit-old $(OLD_COMMIT) \
		 --commit-new $(NEW_COMMIT_EQUIV) \
		 --verbose $(VERBOSE) \
		 --dependency ../oniguruma ../jq

st_ce:
	./euf.py --libclang $(LIBCLANG) --commit-old $(OLD_COMMIT) \
		 --commit-new $(NEW_COMMIT_EQUIV) \
		 --verbose $(VERBOSE) \
		 --dep-only-new src/st.c \
		 --dep-only-old st.c \
		 --full --driver $(DRIVER) \
		 --unwind $(UNWIND) \
		 --dependency ../oniguruma ../jq
st_v:
	./scripts/euf.sh -N \
		-o $(OLD_COMMIT) \
		-n $(NEW_COMMIT_EQUIV) \
		-f st.c \
		-d ../oniguruma ../jq

regexec:
	./euf.py --libclang $(LIBCLANG) --commit-old 65a9b1aa03c9bc2dc01b074295b9603232cb3b78 \
		 --commit-new 1bd71be9437db6ede501fc88102961423c1ab74c \
		 --project-only src/builtin.c \
		 --verbose $(VERBOSE) \
		 --dep-only-new src/regexec.c \
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
	DEP=~/Repos/oniguruma \
	DEP_NEW=/tmp/oniguruma \
	PROJECT=~/Repos/jq \
	OUTDIR=~/Repos/euf/tests \
	DRIVER=$$OUTDIR/regexec_driver.c \
	./scripts/cbmc.sh

regexec_d:
	./euf.py --libclang $(LIBCLANG) --commit-old 65a9b1aa03c9bc2dc01b074295b9603232cb3b78 \
		 --commit-new 1bd71be9437db6ede501fc88102961423c1ab74c \
		 --dep-only-new src/regexec.c \
		 --project-only src/builtin.c \
		 --dump-full \
		 --dependency ../oniguruma ../jq

regexec_ast:
	clang -fsyntax-only -fno-color-diagnostics -Xclang -ast-dump ~/Repos/oniguruma/src/regexec.c > regexec.ast

#---- curl => openssl examples ----#
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
		 --reverse-mapping \
		 --dep-only-new crypto/evp/ctrl_params_translate.c \
		 --dependency ../openssl ../curl

# Note that jq actually has a way older version of oniguruma under ./modules
euc_jp:
	./euf.py --libclang $(LIBCLANG) --commit-old 69545dabdbc1f7a9fb5ebc329c0b7987052b2a44 \
		 --commit-new a2ac402a3549713e6c909752937b7a54f559beb8 \
		 --dep-only-new src/euc_jp.c \
		 --dep-only-old euc_jp.c \
		 --dependency ../oniguruma ../jq
euc_jp_v:
	./scripts/euf.sh -V -o 69545dabdbc1f7a9fb5ebc329c0b7987052b2a44 \
		-n a2ac402a3549713e6c909752937b7a54f559beb8 \
		-d ../oniguruma ../jq | bat
bug_fix_c:
	clang -fsyntax-only -Xclang -ast-dump ~/Repos/oniguruma/sample/bug_fix.c
