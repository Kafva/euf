SHELL=/bin/bash
EUF_CACHE=~/.cache/euf
SMACK_DEPS=~/Repos/smack-deps

ifneq (,$(findstring Ubuntu,$(shell uname -a))) # if on Ubuntu
LIBCLANG=/usr/lib/llvm-12/lib/libclang.so.1
else
LIBCLANG=/usr/lib/libclang.so.13.0.1
endif

.PHONY: clean run run_rev run_full_ce run_full_ci


#--- Defaults ---#
# The recipe names correspond to the source files in the project/dependency
# that are being processed
# _c: clang -ast-dump
# _v: view diff
NPROC=5
VERBOSE=2
UNWIND=1
DEP_ONLY_OLD=""
DEP_ONLY_NEW=""
PROJ_ONLY=""
EXCLUDE_DIRS=""
DEP_SOURCE_ROOT=""

ifdef ONI
	DEP_PROJECT=../oniguruma
	MAIN_PROJECT=../jq
	#	regexec.c
	#OLD_COMMIT=65a9b1aa03c9bc2dc01b074295b9603232cb3b78
	#NEW_COMMIT_INF=1bd71be9437db6ede501fc88102961423c1ab74c
	#NEW_COMMIT_EQUIV=1bd71be9437db6ede501fc88102961423c1ab74c
	#DEP_ONLY_OLD=regexec.c
	#DEP_ONLY_NEW=src/regexec.c
	#PROJ_ONLY=src/builtin.c
	
	#	st.c
	OLD_COMMIT=65a9b1aa03c9bc2dc01b074295b9603232cb3b78
	NEW_COMMIT_EQUIV=e8bd631e187873a2085899bfc99f2f2c6af2adbd
	DRIVER=~/Repos/euf/drivers/st_newsize_driver.c
	UNWIND=2
	DEP_ONLY_OLD=st.c
	DEP_ONLY_NEW=src/st.c
else ifdef MA
	VERBOSE=2
	DEP_PROJECT=../matrix
	MAIN_PROJECT=../main

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
	OLD_COMMIT=77f5d019703f2eb12988a62d2be53216df8d4dab
	NEW_COMMIT_EQUIV=30b4d5160a3a061eacd165803aa8a40d0d0097b0
	NEW_COMMIT_INF=dc838cec7a6ebc47ad5f49107367164da2577a59
	DRIVER=~/Repos/euf/drivers/matrix_init_driver.c
	SMACK_DRIVER=~/Repos/euf/drivers/smack_matrix_init_driver.c
	UNWIND=10
else ifdef EX
	DEP_PROJECT=../libexpat
	DEP_SOURCE_ROOT=../libexpat/expat
	EXCLUDE_DIRS=./expat/tests
	MAIN_PROJECT=../main

	OLD_COMMIT=bbdfcfef4747d2d66e81c19f4a55e29e291aa171
	NEW_COMMIT_INF=e07e39477157723af276abc3a3d04941abd589bb
	NEW_COMMIT_EQUIV=e07e39477157723af276abc3a3d04941abd589bb
else ifdef SSL
	DEP_PROJECT=../openssl
	MAIN_PROJECT=../curl

	OLD_COMMIT=9a1c4e41e8d3fd8fe9d1bd8eeb8b1e1df21da37f
	NEW_COMMIT_EQUIV=d5f9166bacfb3757dfd6117310ad54ab749b11f9
	NEW_COMMIT_INF=d5f9166bacfb3757dfd6117310ad54ab749b11f9
	NPROC=10
	DEP_ONLY_NEW=crypto/evp/ctrl_params_translate.c
endif

run:
	./euf.py --libclang $(LIBCLANG) \
		 --commit-old $(OLD_COMMIT) \
		 --commit-new $(NEW_COMMIT_EQUIV) \
		 --verbose $(VERBOSE) \
		 --dep-only-new $(DEP_ONLY_NEW) \
		 --dep-only-old $(DEP_ONLY_OLD) \
		 --project-only $(PROJ_ONLY) \
		 --nproc $(NPROC) \
		 --exclude-dirs $(EXCLUDE_DIRS) \
		 --dep-source-root $(DEP_SOURCE_ROOT) \
		 --dependency $(DEP_PROJECT) $(MAIN_PROJECT)
run_rev:
	./euf.py --libclang $(LIBCLANG) \
		 --commit-old $(OLD_COMMIT) \
		 --commit-new $(NEW_COMMIT_EQUIV) \
		 --verbose $(VERBOSE) \
		 --dep-only-new $(DEP_ONLY_NEW) \
		 --dep-only-old $(DEP_ONLY_OLD) \
		 --project-only $(PROJ_ONLY) \
		 --nproc $(NPROC) \
		 --exclude-dirs $(EXCLUDE_DIRS) \
		 --dep-source-root $(DEP_SOURCE_ROOT) \
		 --reverse-mapping \
		 --dependency $(DEP_PROJECT) $(MAIN_PROJECT)
run_full_ce:
	./euf.py --libclang $(LIBCLANG) \
		 --commit-old $(OLD_COMMIT) \
		 --commit-new $(NEW_COMMIT_EQUIV) \
		 --verbose $(VERBOSE) \
		 --dep-only-new $(DEP_ONLY_NEW) \
		 --dep-only-old $(DEP_ONLY_OLD) \
		 --full --driver $(DRIVER) \
		 --exclude-dirs $(EXCLUDE_DIRS) \
		 --dep-source-root $(DEP_SOURCE_ROOT) \
		 --unwind $(UNWIND) \
		 --dependency $(DEP_PROJECT) $(MAIN_PROJECT)
run_full_ci:
	./euf.py --libclang $(LIBCLANG) \
		 --commit-old $(OLD_COMMIT) \
		 --commit-new $(NEW_COMMIT_INF) \
		 --verbose $(VERBOSE) \
		 --dep-only-new $(DEP_ONLY_NEW) \
		 --dep-only-old $(DEP_ONLY_OLD) \
		 --full --driver $(DRIVER) \
		 --exclude-dirs $(EXCLUDE_DIRS) \
		 --dep-source-root $(DEP_SOURCE_ROOT) \
		 --unwind $(UNWIND) \
		 --dependency $(DEP_PROJECT) $(MAIN_PROJECT)

#---- Diff viewing  ----#
expat_v:
	./scripts/euf.sh -V \
		-o $(OLD_COMMIT)  \
		-n $(NEW_COMMIT_INF)  \
		-d ../libexpat ../main | bat
matrix_v:
	./scripts/euf.sh -V \
		-o $(OLD_COMMIT)  \
		-n $(NEW_COMMIT_INF)  \
		-d ../matrix ../main | bat
st_v:
	./scripts/euf.sh -N \
		-o $(OLD_COMMIT) \
		-n $(NEW_COMMIT_EQUIV) \
		-f st.c \
		-d ../oniguruma ../jq
regexec_v:
	./scripts/euf.sh -f regexec.c \
		-o $(OLD_COMMIT) \
		-n $(NEW_COMMIT_INF) \
		-d ../oniguruma ../jq | bat
ctrlp_v:
	./scripts/euf.sh -f crypto/evp/ctrl_params_translate.c \
		-o  9a1c4e41e8d \
		-n  d5f9166bacf \
		-d ../openssl ../curl | bat
