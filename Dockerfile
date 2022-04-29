FROM ubuntu:21.10 as euf-base

# Avoid interactive timezone prompt
ENV DEBIAN_FRONTEND=noninteractive
ENV TZ=Etc/Utc

# 'sudo' is used inside of the cbmc install target
RUN apt-get update && apt-get upgrade -y && apt-get install -y \
    clang llvm-13 git flex bison make curl patch cmake \
    build-essential autoconf sudo z3 bear libclang-dev \
    python3.10 python3.10-venv python3-pip

WORKDIR /app/euf
COPY . .

# Setup Python environment
ENV VIRTUAL_ENV=/app/euf/venv
RUN python3.10 -m venv $VIRTUAL_ENV

# Update the PATH to `activate` the virtual environment
ENV PATH="$VIRTUAL_ENV/bin:$PATH"

RUN python3.10 -m pip install -r requirements.txt

# Build submodules
RUN make -C cbmc install
 
RUN CLANG_INSTALL_DIR=/usr \
    LLVM_INCLUDE_DIR=/usr/include/llvm-13/llvm \
    LLVM_CMAKE_DIR=/usr/lib/cmake/clang-13 \
    make -C clang-plugins all

# ~~~~~~~~~~~~~~~~~~~~

FROM euf-base

WORKDIR /app/euf
ENV PATH="$VIRTUAL_ENV/bin:$PATH"

# EUF needs to be able to build the dependency that it analyzes
# and additional dependencies may need to be installed as a conseqeunce
RUN apt-get update && apt-get upgrade -y && apt-get install -y \
  libidn11-dev libudns-dev libgsasl7-dev

# Update source files
COPY . .

ENTRYPOINT ["./euf.py"]
