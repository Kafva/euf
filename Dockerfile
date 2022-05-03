FROM euf-base
# EUF needs to be able to build the dependency that it analyzes
# and additional packages will likely need to be installed as a consequence

# Note that we install headers for dependencies that we are analyzing
# e.g. libgusb-dev. This is to avoid errors during the state space analysis. 
# Installing the current version that is being analyzed as the system 
# version would technically be more sound.
USER root
RUN apt-get update && apt-get upgrade -y && apt-get install -y \
  libidn11-dev libudns-dev libgsasl7-dev libssl-dev \
  libudev-dev libgusb-dev neovim

USER euf
WORKDIR /home/euf/euf

# Required to avoid errors when analyzing jabberd with clang-plugins
RUN sudo ln -s /usr/include/x86_64-linux-gnu/openssl/opensslconf.h \
               /usr/include/openssl/opensslconf.h

ENTRYPOINT ["./euf.py"]
