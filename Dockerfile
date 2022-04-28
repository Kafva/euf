FROM ubuntu:20.04 as builder

ENV DEBIAN_FRONTEND=noninteractive 
ENV TZ=UTC
RUN apt-get update && apt-get install -y \
    clang llvm-12 flex bison make \
    curl patch cmake ninja-build \
    wget build-essential libreadline-dev \
    libncursesw5-dev libssl-dev libsqlite3-dev tk-dev libgdbm-dev \
    libc6-dev libbz2-dev libffi-dev zlib1g-dev git

# Build python3.10 from source
WORKDIR /app
RUN curl -OLs https://www.python.org/ftp/python/3.10.0/Python-3.10.0.tar.xz
RUN tar -Jxf Python-3.10.0.tar.xz
WORKDIR /app/Python-3.10.0
RUN ./configure --enable-optimizations
RUN make altinstall -j4

# Build llvm from source
RUN git clone -b release/13.x \
    https://github.com/llvm/llvm-project.git /app/llvm-project

WORKDIR /app/llvm-project/build
RUN ../cmake -S llvm -B . -G "Ninja" \
      -DLLVM_TARGETS_TO_BUILD=host \
      -DLLVM_ENABLE_PROJECTS="clang"
RUN ninja &&
RUN cmake --install . --prefix "/usr/local"

#== EUF setup ==#
#FROM ubuntu:20.04
#COPY --from=builder /app/Python-3.10.0/python3.10 /usr/bin/python3.10

WORKDIR /app/euf
COPY . .

# Setup Python
ENV VIRTUAL_ENV=/app/euf/venv
RUN python3 -m venv $VIRTUAL_ENV

# Update the PATH to `activate` the virtual enviroment
ENV PATH="$VIRTUAL_ENV/bin:$PATH"

RUN pip install --upgrade pip && pip install -r requirements.txt

ENTRYPOINT [ "./euf.py" ]
