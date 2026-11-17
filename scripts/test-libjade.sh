#!/bin/sh

REPO=jasmin-experiments
NAME=libjade-legacy
BRANCH=main

FILE="$NAME.tar.gz"
ROOT=$(echo -n $NAME-$BRANCH | tr / -)

[ 1 -le $# ] || exit 127

DIR="libjade/$1"

MAKELINE="-C $DIR CI=1 JASMIN=$PWD/compiler/jasminc JASMIN2EC=$PWD/compiler/jasmin2ec"

# Exclude primitives that are known not to build
export EXCLUDE=""

echo "Info: $MAKELINE (EXCLUDE=$EXCLUDE)"

curl -v -o $FILE https://gitlab.inria.fr/$REPO/$NAME/-/archive/$BRANCH/$NAME-$BRANCH.tar.bz2
tar xvf $FILE
rm -rf libjade/
mv $ROOT libjade

mv libjade/oldsrc-should-delete/ libjade/src

make $MAKELINE
