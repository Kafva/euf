#!/usr/bin/env bash

#===== http://cprover.diffblue.com/group__goto-programs.html =====#

# src/goto-programs/goto-convert.cpp
# src/goto-programs/write_goto_binary:write_goto_binary()


#===   initialize_from_source_files(sources, options, language_files, goto_model.symbol_table, message_handler);
#===		Ensure that symtab is changed here..?																																===#
# Earlier: src/goto-programs/initialize_goto_model.cpp:205:

#=== src/ansi-c/ansi_c_language.cpp
# Only the language.typecheck() function uses the sym table
#		ansi_c_languaget::typecheck():103

# Earliest stage: src/ansi-c/expr2c.cpp
# This is where we get a panic

# The initialize_goto_model() creates a new `goto_model`
# The functions and symbol table of the goto_model are manipulated in `goto_convert`

# goto_convert.cpp should be a good interface since it is meant to perform transformations...

cd ~/Repos/euf/cbmc
[ "$1" = clean ] && rm -rf build
mkdir -p build
cmake -S . -B build -DCMAKE_EXPORT_COMPILE_COMMANDS=ON -DCMAKE_C_COMPILER=/usr/bin/clang -DWITH_JBMC=OFF &&
	bear -- cmake --build build -- -j$((`nproc` - 1)) &&
sudo make -C build install &&


goto-cc ~/Repos/oniguruma/src/st.c -o st.o && 
	cbmc --show-symbol-table st.o

#goto-cc ~/Repos/oniguruma/src/st.c -o st.o && 
#	cbmc --list-goto-functions st.o

xxd st.o st.xxd
