#!/bin/sh

set -e

REPO=formosa-crypto
NAME=formosa-mlkem
BRANCH=main

FILE="$NAME.tar.gz"
ROOT=$(echo -n $NAME-$BRANCH | tr / -)

DIR=libjade

curl -v -o $FILE https://codeload.github.com/$REPO/$NAME/tar.gz/$BRANCH
tar xvf $FILE
rm -rf $DIR/
mv $ROOT $DIR

NAME=formosa-keccak
BRANCH=main

FILE="$NAME.tar.gz"
ROOT=$(echo -n $NAME-$BRANCH | tr / -)

curl -v -o $FILE https://codeload.github.com/$REPO/$NAME/tar.gz/$BRANCH
tar xvf $FILE

export JASMINPATH=Keccak=$PWD/$ROOT/src/amd64
export JASMINC=$PWD/compiler/jasminc
export JASMINCT=$PWD/compiler/jasmin-ct

make -C $DIR/ -B assembly
