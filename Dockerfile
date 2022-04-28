FROM ubuntu:21.10

ENV DEBIAN_FRONTEND=noninteractive 
ENV TZ=UTC
RUN apt-get update && apt-get upgrade -y && apt-get install -y \
    clang llvm-13 git flex bison make curl patch cmake \
    xz-utils wget build-essential libreadline-dev \
    libncursesw5-dev libssl-dev libsqlite3-dev tk-dev libgdbm-dev \
    libc6-dev libbz2-dev libffi-dev zlib1g-dev sudo


RUN apt-get install -y python3.10 python3.10-venv python3-pip

# 21.10 is missing a 'python3.10-pip' package so we build
# python from source instead
#WORKDIR /app
#RUN curl -OLs https://www.python.org/ftp/python/3.10.0/Python-3.10.0.tar.xz
#RUN tar -Jxf Python-3.10.0.tar.xz
#WORKDIR /app/Python-3.10.0
#RUN ./configure --enable-optimizations
#RUN make altinstall -j$((`nproc`-1))

WORKDIR /app/euf
COPY . .

# Setup Python enviroment
ENV VIRTUAL_ENV=/app/euf/venv
RUN python3.10 -m venv $VIRTUAL_ENV

# Update the PATH to `activate` the virtual enviroment
ENV PATH="$VIRTUAL_ENV/bin:$PATH"

RUN python3.10 -m pip install -r requirements.txt

# Build submodules
RUN make -C cbmc install
RUN make -C clang-plugins all

ENTRYPOINT ["./euf.py"]
