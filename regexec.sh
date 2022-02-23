# Expand all preprocessor directives for both versions of regexec.c
# To create indpendent versions

cd ~/Repos/oniguruma &&
git checkout 65a9b1aa03c9bc2dc01b074295b9603232cb3b78

/usr/bin/gcc \
-DHAVE_CONFIG_H \
-I. \
-I.. \
-Wall \
-g \
-O2 \
-c \
-fPIC \
-DPIC \
-E \
regexec.c > ~/Repos/euf/tests/regexec.old.c


