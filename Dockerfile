FROM euf-base
# EUF needs to be able to build the dependency that it analyzes
# and additional dependencies may need to be installed as a conseqeunce
USER root
RUN apt-get update && apt-get upgrade -y && apt-get install -y \
  libidn11-dev libudns-dev libgsasl7-dev libssl-dev neovim

USER euf
WORKDIR /home/euf/euf

# Required to avoid errors when analyzing jabberd with clang-plugins
RUN sudo ln -s /usr/include/x86_64-linux-gnu/openssl/opensslconf.h \
               /usr/include/openssl/opensslconf.h

ENTRYPOINT ["./euf.py"]
