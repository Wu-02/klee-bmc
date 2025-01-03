#!/bin/bash

#https://unix.stackexchange.com/a/48550
trap '[ "$?" -ne 77 ] || exit 77' ERR

exitmsg() {
	if [ ! -z "$PHASE" ]; then
		echo "ERROR when $PHASE" >/dev/stderr
	fi

	echo "$1" >/dev/stderr
	exit 77
}

abspath() {
	if which realpath &>/dev/null; then
		realpath "$1" || exitmsg "Can not get absolute path of $1"
	elif [[ "$OSTYPE" == *darwin* ]]; then
		greadlink -f "$1" || exitmsg "Can not get absolute path of $1"
	else
		readlink -f "$1" || exitmsg "Can not get absolute path of $1"
	fi
}

download_tar() {
	$GET "$1" || exitmsg "Failed getting $1"
	BASENAME="$(basename $1)"
	tar xf "$BASENAME" || exitmsg "Failed unpacking $1"
	rm -f "BASENAME"
}

download_zip() {
	$GET "$1" || exitmsg "Faield getting $1"
	BASENAME="$(basename $1)"
	unzip "$BASENAME" || exitmsg "Failed unpacking $1"
	rm -f "BASENAME"
}

clean_and_exit() {
	CODE="$1"

	if [ "$2" = "git" ]; then
		echo "run git clean -xdf to clean up."
	else
		echo "run rm -rf $(pwd)/* to clean up"
	fi

	exitmsg "Exited with code $CODE"
}

build() {
	make $JOBS_ARG CFLAGS="$CFLAGS" CPPFLAGS="$CPPFLAGS" LDFLAGS="$LDFLAGS" $@ || exitmsg "Failed build"
	return 0
}

install() {
	make install $JOBS_ARG $@ || exitmsg "Failed install"
	return 0
}

check_llvm_tool() {
	TOOL_PATH="$1"
	TOOL_NAME="$(basename "$1")"
	if [ ! -x "$TOOL_PATH" ]; then
		exitmsg "Cannot find working $TOOL_NAME binary".
	fi

	TOOL_VERSION=$("$TOOL_PATH" --version)
	if [[ ! "$TOOL_VERSION" =~ "$LLVM_VERSION" ]]; then
		exitmsg "$TOOL_NAME has wrong version. Expected: $LLVM_VERSION Found: $TOOL_VERSION"
	fi
}

git_clone_or_pull() {

	REPO="$1"
	FOLDER="$2"
	shift
	shift

	if [ -d "$FOLDER" ]; then
		if [ "x$UPDATE" = "x1" ]; then
			cd $FOLDER && git pull && cd -
		fi
	else
		git clone $REPO $FOLDER $@
	fi
}

git_submodule_init() {
	pushd "$SRCDIR"
	git submodule update --init --recursive || exitmsg "submodule update failed"
	pushd klee; git checkout ebca2f3; popd
	popd
}

GET="curl -LRO"

check_z3() {
	# z3-devel-4.8.4-2.fc30 on Fedora installs Z3 headers to /usr/include/z3
	echo "#include <z3.h>" | gcc - -E &>/dev/null ||
		echo "#include <z3/z3.h>" | gcc - -E &>/dev/null
}

check_zlib() {
	echo "#include <zlib.h>" | gcc - -E &>/dev/null
}

check_32_bit() {
	echo "#include <stdint.h>" | gcc - -E -m32 &>/dev/null
}

check_tcmalloc() {
	echo "#include <gperftools/malloc_extension.h>" | gcc - -E &>/dev/null
}

check_gtest() {
	echo "#include <gtest/gtest.h>" | gcc - -E &>/dev/null
}

get_external_library() {
	LIB="$(ldd $1 | grep $2 | cut -d ' ' -f 3)"
	# if this is not library in our installation, return it
	if [ "$LIB" != "not" ]; then # not found
		if echo "$LIB" | grep -v -q "$PREFIX"; then
			echo "$LIB"
		fi
	else
		exitmsg "Did not find library matching $2"
	fi
}

get_any_library() {
	LIB="$(ldd $1 | grep $2 | cut -d ' ' -f 3)"
	# if this is not library in our installation, return it
	if [ "$LIB" != "not" ]; then # not found
		echo "$LIB"
	else
		exitmsg "Did not find library matching $2"
	fi
}
