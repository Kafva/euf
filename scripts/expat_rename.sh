#!/usr/bin/env bash
die(){ echo -e "$1" >&2 ; exit 1; }
: '''
Check which files are different:
	rm -rf expat*/.ccls-cache ; git difftool --no-index ./expat4 ./expat5	
'''


[[ -z "$DEP_SOURCE_ROOT" || -z "$DEP_DIR_EUF" || -z "$SUFFIX" ]] && 
	die "Missing enviroment variable(s)"

SRC_FILES=$(mktemp --suffix .lst)

cd "$DEP_DIR_EUF"
git ls-tree -r HEAD --name-only | grep "\.[hc]$" > "$SRC_FILES"

: '''
	1. Expat has macros which expand to several function calls using a
	custom prefix passed as an argument

	  #define STANDARD_VTABLE(E)
	  E##byteType, E##isNameMin, E##isNmstrtMin, E##byteToAscii, E##charMatches,

	We explicitly replace these using exact regex matching
'''
ARG_LABEL=E
FILEPATH="expat/lib/xmltok.c"
GLOBAL_NAME_SUFFIXES=(
	# NORMAL_VTABLE
	"isName2" "isName3" "isName4" "isNmstrt2" "isNmstrt3"
	"isNmstrt4" "isInvalid2" "isInvalid3" "isInvalid4"
	# STANDARD_VTABLE(E)
	"byteType", "isNameMin", "isNmstrtMin", "byteToAscii", "charMatches"
)

for name in ${GLOBAL_NAME_SUFFIXES[@]}; do
	sed -E -i'' "s/${ARG_LABEL}##${name}/${ARG_LABEL}##${name}${SUFFIX}/" \
		"$FILEPATH"
done

: '''
	2.  

    --- EXPAT
    The functions with a PREFIX are not properly renamed, the cursor lands at the start of
    the line instead of at the actual symbol due to the location reported by clang being
    that of the expanded symbol... However even if we place the cursor at this postion
    the lsp does not understand what it should rename...

    Furthermore, there are still some edge cases were renaming does not work

    lib/xmltok.c:465    -> (renaming utf8_toUtf16 does not work)
    static const struct normal_encoding utf8_encoding_ns_old_b026324c6904b2a
        = {{VTABLE1, utf8_toUtf8, utf8_toUtf16, 1, 1, 0}

    ccls does not seem to be guaranteed to work in the same way every time...
        grep -R 2a_old_ .
    race-conditions or other incosnsitent behaviour

    xmltok_impl.c is not processed at all since it does not have a TU entry 
    (it is #included within xmltok.c) this makes it so that no replacements occur in it
    and no global symbols are enumerated

    I think the replacements in xmltok.c become fucked because it has line numbers from xmltok_impl.c
    ....

    expat:
        xmlparse.c:716:1: warning: function 'XML_ParserCreate_MM_old_b026324c6904b2a' is not declared
        xmlrole.c:517:1: error: failed to find symbol 'entity6_old_b026324c6904b2a'
               state->handler = entity6_old_b026324c6904b2a;

     ccls is able to rename globals inside macro definitions (sometimes)
     clang-suffix cannot rename anything inside of a macro unless we use it on `cc -E` files. 
     With preprocessed files we can also properly rename functions with interoplated names e.g.
        PREFIX(fn) -> processed_fn
     Note that the traversal of the AST will produce macro-expanded names

     For the PREFIX(fn) case specifically we could techincally use '*' in vim
     as a fallback if we manage to place ourselves on fn. This is a complete hack though...

     ms-cpptools cant handle these instances either, we are effectivly trying to rename """references""" 
     to a macro-argument

     Runtests is a huge file, I have a feeling ccls would become less incosnsitent
     if we let it index the big files
        git ls-tree -r HEAD --name-only | xargs -I {} wc -l {} | sort -r -n -k1 | awk '{print $1,$2}' | grep ".[hc]$"

        12188 tests/runtests.c
        8240 lib/xmlparse.c
        1817 lib/xmltok_impl.c
        1676 lib/xmltok.c
        1255 lib/xmlrole.c
        1254 xmlwf/xmlwf.c
        1050 lib/expat.h
        453 gennmtab/gennmtab.c
        393 lib/siphash.h
        319 lib/xmltok.h
        280 xmlwf/xmlfile.c
        241 tests/minicheck.c
        193 xmlwf/xmlmime.c

    tests/chardata.c:
        Renaming _fail_unless() sometimes triggers a bad rename of macro invocations of fail()
    #define fail(x) _fail_unless(x)
        Calls like 'fail(x)' become '_fail_unless' (BUG)
    We need to explicitly blacklist this


	lib/xmlrole.c  
	entity6?????


	lib/xmltok.c

	s/utf8_to_Utf16/ utf8_to_Utf16_old_b026324c6904b2a /
	s/utf8_to_Utf8/ utf8_to_Utf8_old_b026324c6904b2a /

	The resolution for  
	lib/xmltok.c:169	#define utf8_isNmstrt4 isNever
	lib/xmltok.c:155	#define utf8_isName4 isNever

	does not work since utf8_isNmstrt4 has been given a suffix



	... ccls works _____sometimes_______ for certain identifiers
	.... Maybe its an #if defined() problem?
	........ If we are lucky
'''
