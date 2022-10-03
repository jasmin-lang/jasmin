#!/bin/sh

NAME=libjade
BRANCH=main

FILE="$NAME.tar.gz"
ROOT="$NAME-$BRANCH"

OUT="results"

[ 1 -le $# ] || exit 127

DIR="$ROOT/$1"

MAKELINE="-C $DIR CI=1 JASMIN=$PWD/compiler/jasminc.native"

# Exclude primitives that are known not to build
export EXCLUDE=""

echo "Info: $MAKELINE (EXCLUDE=$EXCLUDE)"

curl -v -o $FILE https://codeload.github.com/formosa-crypto/$NAME/tar.gz/refs/heads/$BRANCH
tar xvf $FILE

make $MAKELINE
