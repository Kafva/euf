#!/usr/bin/env bash
die(){ echo -e "$1" >&2 ; exit 1; }
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
