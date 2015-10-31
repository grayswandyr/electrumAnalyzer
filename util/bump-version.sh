#/!bin/bash
# run from root of project repo

set -e

# for a git flow release of the form release/0.x.x
VERSION=`git rev-parse --abbrev-ref HEAD | cut -f 2- -d '/'`

sed -i "s/^Version:.*\$/Version: $VERSION/" _oasis

sed -i "s/^version:.*\$/version: \"$VERSION\"/" opam

echo "let version = \"$VERSION\"" > src/version.ml

oasis setup
