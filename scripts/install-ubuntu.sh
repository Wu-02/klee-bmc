#!/bin/sh

set -e

apt-get update

PACKAGES="llvm-14 lld-14 curl wget rsync make cmake unzip gcc-multilib xz-utils python3 pipx zlib1g-dev git build-essential ninja-build pkg-config m4 zlib1g-dev libsqlite3-dev libboost-all-dev libgmp-dev libpolly-14-dev"

apt-get install $PACKAGES
pipx install meson lit
