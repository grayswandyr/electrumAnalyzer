#!/bin/sh

set -e

trim () {
		tr -d '\r\n'
}

TARGET=src/build.ml

VERSION=`git describe --long | trim`

TIME=`date +"%F %T" | trim`

echo "(* FILE GENERATED AT BUILD TIME *)" > $TARGET

echo "let version = \"$VERSION\"" >> $TARGET
echo "let timestamp = \"$TIME\"" >> $TARGET
