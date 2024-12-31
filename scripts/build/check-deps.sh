#!/bin/bash

HAVE_32_BIT_LIBS=$(if check_32_bit; then echo "yes"; else echo "no"; fi)
if [ "$HAVE_32_BIT_LIBS" = "no" ]; then
  exitmsg "KLEE needs 32-bit libc headers to build 32-bit versions of runtime libraries. On Ubuntu, this is the package libc6-dev-i386 (or gcc-multilib), on Fedora-based systems it is glibc-devel.i686."
fi

# TODO: add more dependencies
check_dependencies() {
  local missing=""
  local deps=(
    "curl:Need curl to download files"
    "which:Need 'which' command"
    "patch:Need 'patch' utility"
    "unzip:Need 'unzip' utility"
    "cmake:cmake is needed"
    "make:make is needed"
    "rsync:sbt-instrumentation needs rsync when bootstrapping json"
    "tar:Need tar utility"
    "xz:Need xz utility"
  )

  for dep in "${deps[@]}"; do
    local cmd="${dep%%:*}"
    local msg="${dep#*:}"

    if ! command -v "$cmd" &>/dev/null; then
      echo "$msg"
      missing="$cmd $missing"
    fi
  done

  if [ -n "$missing" ]; then
    exitmsg "Missing dependencies: $missing"
  fi
}
