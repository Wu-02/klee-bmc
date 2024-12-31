FROM ubuntu:22.04
ENV DEBIAN_FRONTEND=noninteractive

RUN  apt-get update \
  && apt-get install -y wget software-properties-common lsb-release gnupg \
  && rm -rf /var/lib/apt/lists/*

RUN wget https://apt.llvm.org/llvm.sh && \
chmod +x llvm.sh && \
./llvm.sh 14

RUN apt-get install -y curl rsync make cmake unzip gcc-multilib xz-utils zlib1g-dev \
  git build-essential ninja-build pkg-config m4 zlib1g-dev libsqlite3-dev \
  libboost-all-dev libgmp-dev pip
# HACK: see https://github.com/llvm/llvm-project/issues/59903
RUN apt-get download libpolly-14-dev && dpkg --force-all -i libpolly-14-dev*
RUN pip3 install meson lit

COPY . /klee-bmc
WORKDIR /klee-bmc

RUN ./build.sh --targets=all --llvm-dir=/usr/lib/llvm-14
RUN echo core | sudo tee /proc/sys/kernel/core_pattern && \
  cd build-* && lit -v test/Core test/ACSL
