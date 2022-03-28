#!/usr/bin/env bash
die(){ echo -e "$1" >&2 ; exit 1; }
: '''
Check which files are different:
	rm -rf expat*/.ccls-cache ; git difftool --no-index ./expat4 ./expat5	

DEP_DIR_EUF=~/.cache/euf/libexpat-bbdfcfef SUFFIX=_old_b026324c6904b2a ~/Repos/euf/scripts/expat_rename.sh

'''

[[ -z "$DEP_DIR_EUF" || -z "$SUFFIX" ]] && 
	die "Missing enviroment variable(s)"

# Every word that we replace needs to be enclosed by some character 
# NOT in this set (or have nothing around it)
DELIM="[^_0-9a-zA-Z]"
SRC_FILES=$(mktemp --suffix .lst)

cd "$DEP_DIR_EUF"
git ls-tree -r HEAD --name-only | grep "\.[hc]$" > "$SRC_FILES"

: '''
	#== 1. Patch function generators ==#
	Expat has macros which expand to several function calls using a
	custom prefix passed as an argument

	lib/xmltok.c
	#define STANDARD_VTABLE(E)
		E##byteType, E##isNameMin, E##isNmstrtMin, E##byteToAscii, E##charMatches,

	We explicitly replace these using exact regex matching

	Note that the little2_ and big2_ versions of the utf8 functions are defined through a macro
	we need to manually replace inside DEFINE_UTF16_TO_UTF8 and DEFINE_UTF16_TO_UTF16 to resolve this

	lib/xmltok.c
		#define DEFINE_UTF16_TO_UTF8(E)
  		static enum XML_Convert_Result PTRCALL E##toUtf8( 

'''
ARG_LABEL=E
FILEPATH="expat/lib/xmltok.c"
GLOBAL_NAME_SUFFIXES=(
	# NORMAL_VTABLE(E)
	"isName2" "isName3" "isName4" "isNmstrt2" "isNmstrt3"
	"isNmstrt4" "isInvalid2" "isInvalid3" "isInvalid4"
	# STANDARD_VTABLE(E)
	"byteType" "isNameMin" "isNmstrtMin" "byteToAscii" "charMatches"
	# DEFINE_UTF16_TO_UTF8(E)
	"toUtf8"
	# DEFINE_UTF16_TO_UTF16(E)
	"toUtf16"
)

for name in ${GLOBAL_NAME_SUFFIXES[@]}; do
	sed -E -i'' "s/${ARG_LABEL}##${name}(${DELIM}|$)/${ARG_LABEL}##${name}${SUFFIX}\1/" \
		"$FILEPATH"
done

: '''
	#== 2. Exact replace specific identifiers ==#
	The "utf8_toUtf8" and "utf8_toUtf16" symbols inside struct decls are sometimes recognized in the replacement
	conducted by ccls but generally fail so we perform an exact replace as a backup

  lib/xmltok.c:465
  static const struct normal_encoding utf8_encoding_ns_old_b026324c6904b2a
      = {{VTABLE1, utf8_toUtf8, utf8_toUtf16, 1, 1, 0}
    
	Renaming _fail_unless() sometimes triggers a bad rename of macro invocations of fail()
	Calls like "fail(x)" become "_fail_unless" (BUG)
  We need to explicitly blacklist this and perform a manual replace

	tests/chardata.c:
		#define fail(x) _fail_unless(x)

	More spurious failures occur for:

	lib/expat.h:
		XML_SetBillionLaughsAttackProtectionActivationThreshold
		XML_SetBillionLaughsAttackProtectionMaximumAmplification

	lib/xmltok.c
		initScan
		getEncodingIndex
		streqci (uncommon)
		initUpdatePosition (uncommon)
'''


replace_ident(){
	sed -E -i'' '/^\s*(#\s*include|\/\/)/!'"s/(${DELIM}|^)(${1})(${DELIM}|$)/\1\2${SUFFIX}\3/g" "$2"
}

while read -r line; do
	replace_ident utf8_toUtf8  $line
	replace_ident utf8_toUtf16 $line
	replace_ident _fail_unless $line
	replace_ident	XML_SetBillionLaughsAttackProtectionActivationThreshold $line
	replace_ident XML_SetBillionLaughsAttackProtectionMaximumAmplification $line
	replace_ident initScan $line
	replace_ident getEncodingIndex $line
	replace_ident streqci $line
	replace_ident initUpdatePosition $line
done < $SRC_FILES

: '''
	#== 3. Patch specific #defines ==#
	The resolution for  
		lib/xmltok.c:169	#define utf8_isNmstrt4 isNever
		lib/xmltok.c:155	#define utf8_isName4 isNever

	does not work since utf8_isNmstrt4, utf8_isName4 and isNever have been given suffixes
	We do an exact replace for this edge case

	This define also needs to have suffixes manually added
		lib/xmltok.c:786 #define VTABLE VTABLE1, little2_toUtf8, little2_toUtf16
'''

sed -E -i'' "s/#define utf8_isNmstrt4 isNever/#define utf8_isNmstrt4${SUFFIX} isNever${SUFFIX}/;
						 s/#define utf8_isName4 isNever/#define utf8_isName4${SUFFIX} isNever${SUFFIX}/;
						 s/#\s*define VTABLE VTABLE1, little2_toUtf8, little2_toUtf16/#define VTABLE VTABLE1, little2_toUtf8${SUFFIX}, little2_toUtf16${SUFFIX}/;
" "$FILEPATH"
