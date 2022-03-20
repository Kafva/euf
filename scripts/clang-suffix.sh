#!/usr/bin/env bash
[[  -z "$SUFFIX" || -z "$RENAME_TXT"  || -z "$SETX" || -z "$EXPAND" ||
    -z "$PLUGIN" || -z "$TARGET_FILE" || -z "$INTERNAL_FLAGS" ]] &&
	die "Missing environment variable(s)"
# To allow us to replace references to global symbols inside macros
# we first preprocess the file, only expanding #define statements
# In oniguruma this results in certain functions gaining a 'onig_' prefix...
# due to a #define in regint.h
#
# Using the --passthru-includes option avoids expansion of the #include lines
# in the output but it still processes defines in these headers. The .h files
# could contain #macros so this is preferable.
#
# The question is if compilation will still go through with the normal
# build process with the header included...
#
# I have a feeling it will since any macros in the .c file will simply already
# have been expanded...
#   https://stackoverflow.com/q/65045678/9033629

expand_macros(){
  pcpp --passthru-comments --passthru-includes ".*" \
    --line-directive --passthru-unfound-includes  \
    $CFLAGS "$1"
}

$SETX && set -x

# We do not want to expand header files
if $EXPAND; then
	expanded_file="/tmp/expanded_$(basename $TARGET_FILE)"

	expand_macros "$TARGET_FILE" > "$expanded_file"

	# Verify that the expanded file does not have any weird
	# re-#define behaviour
	diff <(expand_macros $expanded_file) $expanded_file ||
	  die "Preprocessing is not idempotent for $TARGET_FILE"

	mv "$expanded_file" "$TARGET_FILE"
fi


# To properly compare the old and new version it may be neccessary 
# to expand #defines in the new version as well

outfile="/tmp/old_$(basename $TARGET_FILE)"

# Hack for oniguruma
printf $TARGET_FILE | grep -q "oniguruma" &&
	touch "$PWD/config.h"

# We always include /usr/include
# Note that we move the output regardless of if errors occured 
# (neccessary during macro replacement)
clang -cc1 -load "$PLUGIN" \
	-plugin AddSuffix \
	-plugin-arg-AddSuffix -names-file -plugin-arg-AddSuffix $RENAME_TXT  \
	-plugin-arg-AddSuffix -suffix -plugin-arg-AddSuffix $SUFFIX \
	$INTERNAL_FLAGS "$TARGET_FILE" $CFLAGS -I/usr/include > "$outfile" ;

mv "$outfile" "$TARGET_FILE"
