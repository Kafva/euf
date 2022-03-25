#!/usr/bin/env bash
die(){ echo -e "$1" >&2 ; exit 1; }

[[ -z "$1" ]] && die "Missing argument(s)"


: '''
    1. Expat has macros which expand to several function calls using a
    custom prefix passed as an argument
    
      #define STANDARD_VTABLE(E)
      E##byteType, E##isNameMin, E##isNmstrtMin, E##byteToAscii, E##charMatches,
    
    We explicitly replace these using exact regex matching


CONFIG.NAME_GENERATORS = [
        MacroNameGenerator(
                filepath = "expat/lib/xmltok.c",
                arg = "E",
                global_name_suffixes = [
                    "byteType", "isNameMin", "isNmstrtMin", "byteToAscii", "charMatches"
                ]
        ),
        MacroNameGenerator(
                filepath = "expat/lib/xmltok.c",
                arg = "E",
                global_name_suffixes = [
                    "isName2", "isName3", "isName4", "isNmstrt2", "isNmstrt3",
                    "isNmstrt4", "isInvalid2", "isInvalid3", "isInvalid4"
                ]
        )
]

'''

