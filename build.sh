#!/bin/bash
#
# Build script for klee-bmc.

set -eu

PHASE="doing initialization"

source "$(dirname $0)/scripts/build-utils.sh"

RUNDIR=$(pwd)
SRCDIR=$(dirname $0)
ABS_RUNDIR=$(abspath $RUNDIR)
ABS_SRCDIR=$(abspath $SRCDIR)

usage() {
	echo "Usage: $0 [options]"
	echo "Options:"
	echo "  --help|-h             Show this help message"
	echo "  --targets=...         Specify build targets, separated by comma"
	echo "                        Available targets: all, bmc, klee, clam, afl (default: all)"
	echo "  --build-type=...      Specify build type: Debug/Release/RelWithDebInfo/MinSizeRel (default: Release)"
	echo "  --update              Update submodules before building"
	echo "  --llvm-dir=...        Use llvm installed at directory"
	echo "  --prefix=...          Where to install KLEE-BMC"
	echo "  -jN                   Run N jobs in parallel (default: 2)"
	echo "  --install-system-deps Install system dependencies"
}

LLVM_VERSION=14.0.6
export LLVM_CONFIG=llvm-config-14 #HACK: for building afl
# LLVM tools we need
export LLVM_DIR=
export CC=clang

BUILD_TARGETS=
BUILD_TYPE=
CFLAGS=
CPPFLAGS=
LDFLAGS=
JOBS_ARG="-j2"
UPDATE=
INSTALL_SYSTEM_DEPS=
export PREFIX=

while [ $# -gt 0 ]; do
	case $1 in
	'-h' | '--help')
		usage
		exit 0
		;;
	--targets=*)
		BUILD_TARGETS="${1##*=}"
		;;
	--build-type=*)
		BUILD_TYPE=${1##*=}
		;;
	--llvm-dir=*)
		LLVM_DIR=${1##*=}
		;;
  --prefix=*)
    PREFIX=${1##*=}
    PREFIX=$(realpath -m "$PREFIX")

    if [ ! -d "$PREFIX" ]; then # directory does not exist
        mkdir -p "$PREFIX" || {
            echo "Error: Could not create directory $PREFIX"
            exit 1
        }
    fi

    if [ ! -w "$PREFIX" ]; then # directory is not writable
        echo "Error: No write permission to $PREFIX"
        exit 1
    fi
    ;;
	-j*)
		JOBS_ARG="$1"
		;;
	--update)
		UPDATE=1
		;;
	--install-system-deps)
		INSTALL_SYSTEM_DEPS=1
		;;
	*)
		echo "Unknown option: $1"
		usage
		exit 1
		;;
	esac
	shift
done

if [ -z "$BUILD_TARGETS" ]; then
	BUILD_TARGETS="all"
fi
if [ -z "$BUILD_TYPE" ]; then
	BUILD_TYPE="Release"
fi
if [ -z "$PREFIX" ]; then
  PREFIX=${PREFIX:-$(pwd)/$BUILD_TYPE}
fi

if [ "x$LLVM_DIR" != "x" ]; then
	if [ ! -d "$LLVM_DIR" ]; then
		exitmsg "Invalid LLVM directory given: $LLVM_DIR"
	fi
fi

# Try to get the previous build type if no is given
if [ -z "$BUILD_TYPE" ]; then
	if [ -f "CMakeCache.txt" ]; then
		BUILD_TYPE=$(cat CMakeCache.txt | grep CMAKE_BUILD_TYPE | cut -f 2 -d '=')
	fi

	# no build type means Release
	[ -z "$BUILD_TYPE" ] && BUILD_TYPE="Release"

	echo "Previous build type identified as $BUILD_TYPE"
fi

if [ "$BUILD_TYPE" != "Debug" -a \
	"$BUILD_TYPE" != "Release" -a \
	"$BUILD_TYPE" != "RelWithDebInfo" -a \
	"$BUILD_TYPE" != "MinSizeRel" ]; then
	exitmsg "Invalid type of build: $BUILD_TYPE"
fi

if [ "$INSTALL_SYSTEM_DEPS" ]; then
	PHASE="installing system dependencies"
	./scripts/install-system-deps.sh
fi

PHASE="checking system"
source scripts/build/check-deps.sh
check_dependencies

# create prefix directory
mkdir -p $PREFIX/bin

export LLVM_PREFIX="$PREFIX/llvm"
export LLVM_CMAKE_CONFIG_DIR=$LLVM_DIR/lib/cmake/llvm
export LLVM_BUILD_PATH=$LLVM_DIR
export LLVM_CONFIG=${LLVM_DIR}/bin/llvm-config

if [ ! -f $LLVM_CMAKE_CONFIG_DIR/LLVMConfig.cmake ]; then
	exitmsg "Cannot find LLVMConfig.cmake file in the directory $LLVM_DIR"
fi

if [ $($LLVM_CONFIG --version) != $LLVM_VERSION ]; then
	exitmsg "LLVM version mismatch: $($LLVM_CONFIG --version) != $LLVM_VERSION"
fi

if [ "$($LLVM_CONFIG --shared-mode --libs)" = "shared" ]; then
	LLVM_DYLIB="on"
else
	LLVM_DYLIB="off"
fi

declare -A TOOL_DEPS=(
	["all"]="afl bmc klee clam"
	["afl"]="afl"
	["bmc"]="bmc"
	["klee"]="klee"
	["clam"]="clam"
)

get_tool_deps() {
	local tool=$1
	echo "${TOOL_DEPS[$tool]}"
}

build_tool() {
	local tool=$1
	case $tool in
	"afl")
		source scripts/build/afl.sh
	  ;;
	"bmc")
		source scripts/build/bmc.sh
		;;
	"klee")
		source scripts/build/klee.sh
		;;
	"clam")
		source scripts/build/clam.sh
		;;
	*)
		echo "Unknown tool: $tool"
		return 1
		;;
	esac
	if [ "$(pwd)" != $ABS_SRCDIR ]; then
		exitmsg "Inconsistency in the build script, should be in $ABS_SRCDIR, currently in $(pwd)}"
	fi
}

# build targets
if [ ! -z "$BUILD_TARGETS" ]; then
	TARGETS=($(echo "$BUILD_TARGETS" | tr ',' ' '))

	# mark targets and their dependencies to be built
	declare -A TO_BUILD
	for target in "${TARGETS[@]}"; do
		deps=$(get_tool_deps "$target")
		for dep in $deps; do
			TO_BUILD[$dep]=1
		done
	done

	echo "Targets to build: ${!TO_BUILD[@]}"
	for tool in "${!TO_BUILD[@]}"; do
		echo "Building $tool..."
		if ! build_tool "$tool"; then
			exitmsg "Building $tool failed"
		fi
	done
fi
