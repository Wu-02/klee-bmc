#!/bin/sh

set -e

cd $(dirname $0)

if command -v apt-get >/dev/null; then
	SUDO=
	if command -v sudo >/dev/null; then
		SUDO=sudo
	else
		SUDO="su -c"
	fi
	$SUDO ./install-ubuntu.sh
else
	echo "System not supported."
	exit 1
fi
