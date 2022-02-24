# Expand all preprocessor directives for both versions of regexec.c
# To create indpendent versions

# NOTE: We need to 
cd ~/Repos/oniguruma &&
git checkout 65a9b1aa03c9bc2dc01b074295b9603232cb3b78


/usr/bin/gcc \
-DHAVE_CONFIG_H \
-I. \
-I. \
-I/usr/local/include \
-Wall \
-g \
-O2 \
-c \
-E \
regexec.c > ~/Repos/euf/tests/regexec.old.c


git checkout 1bd71be9437db6ede501fc88102961423c1ab74c

/usr/bin/gcc \
-DHAVE_CONFIG_H \
-I. \
-I.. \
-Wall \
-g \
-O2 \
-c \
-E \
src/regexec.c > ~/Repos/euf/tests/regexec.new.c

