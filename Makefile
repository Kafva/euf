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
SKIP_IMPACT=""
GOTO_BUILD_SCRIPT=""
CCDB_BUILD_SCRIPT=""


ifdef ONI 
	VERBOSE=1
	DEP_PROJECT=../oniguruma
	MAIN_PROJECT=../jq
	DEP_LIB_NAME=libonig.a
	CCDB_BUILD_SCRIPT=./scripts/ccdb_oni.sh
	#GOTO_BUILD_SCRIPT=./scripts/mk_goto_oni.sh

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
	NEW_COMMIT_INF=e8bd631e187873a2085899bfc99f2f2c6af2adbd
	DRIVER=~/Repos/euf/drivers/st_newsize_driver.c
	UNWIND=2
	DEP_ONLY_OLD=st.c
	DEP_ONLY_NEW=src/st.c
else ifdef MA
	VERBOSE=2
	DEP_PROJECT=../matrix
	MAIN_PROJECT=../main
	DEP_LIB_NAME=libmatrix.a

	# 	get_nearest_even():
	#DRIVER=~/Repos/euf/drivers/nearest_even_driver.c

	# 	matrix_sum():
	#DRIVER=~/Repos/euf/drivers/matrix_sum_driver.c

	#	matrix_init()
	#OLD_COMMIT=366c7c10cadb13d8dc97e151993270b41b790eee
	OLD_COMMIT=a2590d7c1fde314771f9287195a18a97b819ac1d
	NEW_COMMIT_EQUIV=ce854b98356f0e4555735c657203e866e4f86007
	NEW_COMMIT_INF=ca4b02be80ae3e62dc2c6fe8c9fbd2d0ecc44a5e
	DRIVER=~/Repos/euf/drivers/matrix_init_driver.c
	UNWIND=10
else ifdef EX
	DEP_PROJECT=../libexpat
	DEP_SOURCE_ROOT=../libexpat/expat
	EXCLUDE_DIRS=./expat/tests
	DEP_LIB_NAME=libexpat.a
	MAIN_PROJECT=../jabberd-2.7.0
	NPROC=12
	DRIVER=./drivers/crypto_http_driver.c

	OLD_COMMIT=bbdfcfef4747d2d66e81c19f4a55e29e291aa171
	NEW_COMMIT_EQUIV=c16300f0bc4318f31f9e27eb2702ddbffe086fea
	#NEW_COMMIT_EQUIV=e07e39477157723af276abc3a3d04941abd589bb
	NEW_COMMIT_INF=e07e39477157723af276abc3a3d04941abd589bb
else ifdef SSL
	VERBOSE=1
	DEP_PROJECT=../openssl
	MAIN_PROJECT=../curl
	DEP_LIB_NAME=libcrypto.a
	GOTO_BUILD_SCRIPT=./scripts/mk_goto_openssl.sh
	CCDB_BUILD_SCRIPT=./scripts/ccdb_openssl.sh
	DRIVER=./drivers/crypto_http_driver.c
	SKIP_BLAME=--skip-blame
	EXCLUDE_DIRS=./test
	NPROC=14

	#OLD_COMMIT=9a1c4e41e8d3fd8fe9d1bd8eeb8b1e1df21da37f
	#NEW_COMMIT_EQUIV=d5f9166bacfb3757dfd6117310ad54ab749b11f9
	#NEW_COMMIT_INF=d5f9166bacfb3757dfd6117310ad54ab749b11f9
	#DEP_ONLY_NEW=crypto/evp/ctrl_params_translate.c

	#	redirection_ok()	
	OLD_COMMIT=29f178bddfd
	NEW_COMMIT_EQUIV=b6fec9658be
	DEP_ONLY_NEW=crypto/http/http_client.c
	DEP_ONLY_OLD=crypto/http/http_client.c
endif

run:
	./euf.py --libclang $(LIBCLANG) \
		 --commit-old $(OLD_COMMIT) \
		 --commit-new $(NEW_COMMIT_EQUIV) \
		 --verbose $(VERBOSE) \
		 --dep-only-new $(DEP_ONLY_NEW) \
		 --dep-only-old $(DEP_ONLY_OLD) \
		 --project-only $(PROJ_ONLY) \
		 --deplib-name $(DEP_LIB_NAME) \
		 --nproc $(NPROC) \
		 --ccdb-build-script $(CCDB_BUILD_SCRIPT) \
		 --goto-build-script $(GOTO_BUILD_SCRIPT) \
		 --exclude-dirs $(EXCLUDE_DIRS) \
		 --dep-source-root $(DEP_SOURCE_ROOT) \
		 --dependency $(DEP_PROJECT) $(MAIN_PROJECT)
run_skip:
	./euf.py --libclang $(LIBCLANG) \
		 --commit-old $(OLD_COMMIT) \
		 --commit-new $(NEW_COMMIT_EQUIV) \
		 --verbose $(VERBOSE) \
		 --dep-only-new $(DEP_ONLY_NEW) \
		 --dep-only-old $(DEP_ONLY_OLD) \
		 --project-only $(PROJ_ONLY) \
		 --nproc $(NPROC) \
		 --skip-impact $(SKIP_BLAME) \
		 --exclude-dirs $(EXCLUDE_DIRS) \
		 --ccdb-build-script $(CCDB_BUILD_SCRIPT) \
		 --goto-build-script $(GOTO_BUILD_SCRIPT) \
		 --deplib-name $(DEP_LIB_NAME) \
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
		 --deplib-name $(DEP_LIB_NAME) \
		 --ccdb-build-script $(CCDB_BUILD_SCRIPT) \
		 --goto-build-script $(GOTO_BUILD_SCRIPT) \
		 --reverse-mapping \
		 --dependency $(DEP_PROJECT) $(MAIN_PROJECT)
run_ce:
	./euf.py --libclang $(LIBCLANG) \
		 --commit-old $(OLD_COMMIT) \
		 --commit-new $(NEW_COMMIT_EQUIV) \
		 --verbose $(VERBOSE) \
		 --dep-only-new $(DEP_ONLY_NEW) \
		 --dep-only-old $(DEP_ONLY_OLD) \
		 --full --driver $(DRIVER) \
		 --exclude-dirs $(EXCLUDE_DIRS) \
		 --dep-source-root $(DEP_SOURCE_ROOT) \
		 --deplib-name $(DEP_LIB_NAME) \
		 --ccdb-build-script $(CCDB_BUILD_SCRIPT) \
		 --goto-build-script $(GOTO_BUILD_SCRIPT) \
		 --unwind $(UNWIND) $(SKIP_BLAME) \
		 --dependency $(DEP_PROJECT) $(MAIN_PROJECT)
run_ci:
	./euf.py --libclang $(LIBCLANG) \
		 --commit-old $(OLD_COMMIT) \
		 --commit-new $(NEW_COMMIT_INF) \
		 --verbose $(VERBOSE) \
		 --dep-only-new $(DEP_ONLY_NEW) \
		 --dep-only-old $(DEP_ONLY_OLD) \
		 --full --driver $(DRIVER) \
		 --exclude-dirs $(EXCLUDE_DIRS) \
		 --dep-source-root $(DEP_SOURCE_ROOT) \
		 --deplib-name $(DEP_LIB_NAME) \
		 --ccdb-build-script $(CCDB_BUILD_SCRIPT) \
		 --goto-build-script $(GOTO_BUILD_SCRIPT) \
		 --unwind $(UNWIND) $(SKIP_BLAME) \
		 --dependency $(DEP_PROJECT) $(MAIN_PROJECT)
run_re_ce:
	./euf.py --libclang $(LIBCLANG) \
		 --commit-old $(OLD_COMMIT) \
		 --commit-new $(NEW_COMMIT_EQUIV) \
		 --verbose $(VERBOSE) \
		 --dep-only-new $(DEP_ONLY_NEW) \
		 --dep-only-old $(DEP_ONLY_OLD) \
		 --full --driver $(DRIVER) \
		 --exclude-dirs $(EXCLUDE_DIRS) \
		 --dep-source-root $(DEP_SOURCE_ROOT) \
		 --deplib-name $(DEP_LIB_NAME) \
		 --ccdb-build-script $(CCDB_BUILD_SCRIPT) \
		 --goto-build-script $(GOTO_BUILD_SCRIPT) \
		 --force-recompile \
		 --unwind $(UNWIND) $(SKIP_BLAME) \
		 --dependency $(DEP_PROJECT) $(MAIN_PROJECT)
run_re_ci:
	./euf.py --libclang $(LIBCLANG) \
		 --commit-old $(OLD_COMMIT) \
		 --commit-new $(NEW_COMMIT_INF) \
		 --verbose $(VERBOSE) \
		 --dep-only-new $(DEP_ONLY_NEW) \
		 --dep-only-old $(DEP_ONLY_OLD) \
		 --full --driver $(DRIVER) \
		 --exclude-dirs $(EXCLUDE_DIRS) \
		 --dep-source-root $(DEP_SOURCE_ROOT) \
		 --deplib-name $(DEP_LIB_NAME) \
		 --ccdb-build-script $(CCDB_BUILD_SCRIPT) \
		 --goto-build-script $(GOTO_BUILD_SCRIPT) \
		 --force-recompile \
		 --unwind $(UNWIND) $(SKIP_BLAME) \
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
replace:
	SUFFIX=aaaaaaaa VERBOSE=false RENAME_YML=/home/jonas/Repos/euf/scripts/.test.yml \
		/home/jonas/Repos/euf/scripts/replace.sh /home/jonas/Repos/oniguruma/src/gb18030.c



