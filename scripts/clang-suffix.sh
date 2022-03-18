#!/usr/bin/env bash
[[  -z "$SUFFIX" || -z "$RENAME_TXT"  || -z "$SETX" ||
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

expanded_file="$(mktemp --suffix .c)"

expand_macros "$TARGET_FILE" > "$expanded_file"

# Verify that the expanded file does not have any weird
# re-#define behaviour
diff <(expand_macros $expanded_file) $expanded_file ||
  die "Preprocessing is not idempotent for $TARGET_FILE"

mv "$expanded_file" "$TARGET_FILE"

outfile="$(mktemp --suffix .c)"

# We always include /usr/include
clang -cc1 -load "$PLUGIN" \
	-plugin AddSuffix \
	-plugin-arg-AddSuffix -names-file -plugin-arg-AddSuffix $RENAME_TXT  \
	-plugin-arg-AddSuffix -suffix -plugin-arg-AddSuffix $SUFFIX \
	$INTERNAL_FLAGS "$TARGET_FILE" $CFLAGS -I/usr/include > "$outfile"

mv "$outfile" "$TARGET_FILE"

$SETX && set +x
