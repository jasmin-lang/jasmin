#!/bin/sh

NAME=libjade
BRANCH=release/2023.05

FILE="$NAME.tar.gz"
ROOT=$(echo -n $NAME-$BRANCH | tr / -)

[ 1 -le $# ] || exit 127

DIR="libjade/$1"

MAKELINE="-C $DIR CI=1 JASMIN=$PWD/compiler/jasminc.native"

# Exclude primitives that are known not to build
export EXCLUDE=""

echo "Info: $MAKELINE (EXCLUDE=$EXCLUDE)"

curl -v -o $FILE https://codeload.github.com/formosa-crypto/$NAME/tar.gz/refs/heads/$BRANCH
tar xvf $FILE
rm -rf libjade/
mv $ROOT libjade

make $MAKELINE
