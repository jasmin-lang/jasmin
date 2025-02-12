#!/bin/sh

REPO=formosa-crypto
NAME=libjade
BRANCH=13a094f740a37e18e8f8cb32630adaa6a3097af6

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

mv libjade/oldsrc-should-delete/ libjade/src

make $MAKELINE
