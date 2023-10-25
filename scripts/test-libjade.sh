#!/bin/sh

REPO=formosa-crypto
NAME=libjade
BRANCH=69fa7e0b9f4180d661fb88139d5b56510bd9331d

FILE="$NAME.tar.gz"
ROOT=$(echo -n $NAME-$BRANCH | tr / -)

[ 1 -le $# ] || exit 127

DIR="libjade/$1"

MAKELINE="-C $DIR CI=1 JASMIN=$PWD/compiler/jasminc"

# Exclude primitives that are known not to build
export EXCLUDE=""

echo "Info: $MAKELINE (EXCLUDE=$EXCLUDE)"

curl -v -o $FILE https://codeload.github.com/$REPO/$NAME/tar.gz/$BRANCH
tar xvf $FILE
rm -rf libjade/
mv $ROOT libjade

make $MAKELINE
