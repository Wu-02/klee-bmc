#!/bin/sh
PHASE="building KLEE"
if [ "x$UPDATE" = "x1" -o -z "$(ls -A $SRCDIR/klee)" ]; then
	git_submodule_init
fi

mkdir -p klee/build-${LLVM_VERSION}-${BUILD_TYPE}
pushd klee/build-${LLVM_VERSION}-${BUILD_TYPE}

# Build everything but klee; we will use CMake to build it
deps="solvers json gtest uclibc"
BASE=$(abspath ./subprojects) BITWUZLA_VERSION="0.3.2" BITWUZLA_COMMIT="0.3.2" IMMER_VERSION=v0.8.1 \
JSON_VERSION=v3.11.3 SOLVERS="bitwuzla" GTEST_VERSION=1.11.0 UCLIBC_VERSION=klee_uclibc_v1.4 \
LLVM_VERSION=14.0.6 UCLIBC_VERSION=klee_uclibc_v1.4 ENABLE_OPTIMIZED=1 ENABLE_DEBUG=0 DISABLE_ASSERTIONS=1 \
REQUIRES_RTTI=1 ../scripts/build/build.sh $deps

src=$(compgen -G subprojects/bitwuzla-*-install/)
BITWUZLA_FLAGS="-DENABLE_SOLVER_BITWUZLA=ON -DCMAKE_PREFIX_PATH=$(abspath $src)"
uclibc_path=`abspath $(compgen -G subprojects/klee-uclibc-*-32)`
UCLIBC_FLAGS="-DKLEE_UCLIBC_PATH=${uclibc_path::-3}"

EXTRA_FLAGS=""
if src=$(compgen -G subprojects/json*/); then
	EXTRA_FLAGS="$EXTRA_FLAGS -DJSON_SRC_DIR=$(abspath $src)"
fi

if src=$(compgen -G subprojects/immer*/); then
	EXTRA_FLAGS="$EXTRA_FLAGS -DIMMER_SRC_DIR=$(abspath $src)"
fi

if
	which lit &
	>/dev/null
then
	HAVE_LIT=yes
else
	HAVE_LIT=no
fi

if src=$(compgen -G subprojects/googletest*/); then
	HAVE_GTEST="yes"
	EXTRA_FLAGS="$EXTRA_FLAGS -DGTEST_SRC_DIR=$(abspath $src)"
fi

if [ "$HAVE_LIT"="yes" -a "$HAVE_GTEST" = "yes" ]; then
	ENABLE_TESTS="on"
else
	ENABLE_TESTS="off"
fi

if [ "x$BUILD_TYPE"="xRelWithDebInfo" ]; then
	RUNTIME_BUILD_TYPE="Release+Debug"
else
	RUNTIME_BUILD_TYPE=$BUILD_TYPE
fi

cmake .. \
	-DCMAKE_INSTALL_PREFIX=$LLVM_PREFIX \
	-DCMAKE_BUILD_TYPE=${BUILD_TYPE} \
	-DKLEE_RUNTIME_BUILD_TYPE=${RUNTIME_BUILD_TYPE} \
	-DLLVM_DIR=${LLVM_DIR} \
	-DENABLE_UNIT_TESTS=${ENABLE_TESTS} \
	-DENABLE_SYSTEM_TESTS=${ENABLE_TESTS} \
	-DENABLE_TCMALLOC=OFF \
	-DENABLE_FLOATING_POINT=ON \
	-DENABLE_FP_RUNTIME=ON \
	-DENABLE_ZLIB=ON \
	-DENABLE_KLEE_ASSERTS=OFF \
	$UCLIBC_FLAGS $BITWUZLA_FLAGS ${EXTRA_FLAGS} ||
	clean_and_exit 1 "git"

# clean runtime libs, it may be 32-bit from last build
# make -C runtime -f Makefile.cmake.bitcode clean 2>/dev/null

# build 64-bit libs and install them to prefix
(build && install) || exit 1

mkdir -p $LLVM_PREFIX/lib32/klee/runtime
mv $LLVM_PREFIX/lib/klee/runtime/*32_*.bca $LLVM_PREFIX/lib32/klee/runtime ||
	exitmsg "Cannot move 32-bit klee runtime lib files."
mv $LLVM_PREFIX/lib/klee/runtime/klee-uclibc-32.bca $LLVM_PREFIX/lib32/klee/runtime \
  || exitmsg "Cannot move 32-bit klee-uclibc lib file."
popd
