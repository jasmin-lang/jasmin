#!/bin/sh

set -e

REPO=formosa-crypto
NAME=formosa-libjade
BRANCH=main

FILE="$NAME.tar.gz"
ROOT=$(echo -n $NAME-$BRANCH | tr / -)

if [ -z "$JOBS" ]
then
   JOBS=1
fi

DIR=libjade

curl -v -o $FILE https://codeload.github.com/$REPO/$NAME/tar.gz/$BRANCH
tar xvf $FILE
rm -rf $DIR/
mv $ROOT $DIR

LINE="-j$JOBS -C $DIR/src JASMINC=$PWD/compiler/jasminc JASMINCT=$PWD/compiler/jasmin-ct"

echo ASM
make $LINE mlkem
echo CHECK CT
make $LINE ct-mlkem
echo CHECK SCT
make $LINE sct-mlkem
