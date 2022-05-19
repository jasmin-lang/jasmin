#!/bin/sh

NAME=libjade
BRANCH=main

FILE=$NAME.tar.gz
DIR=$NAME-$BRANCH

OUT=results

# Exclude primitives that are known not to build
EXCLUDED=crypto_kem

curl -v -o $FILE https://codeload.github.com/formosa-crypto/$NAME/tar.gz/refs/heads/$BRANCH
tar xvf $FILE

for d in $EXCLUDED
do
	rm -rf $DIR/src/$d
done

make -C $DIR/src CI=1 JASMIN=$PWD/compiler/jasminc.native

mkdir -p $OUT
(cd $OUT && tar xvf ../$DIR/src/check.tar.gz)
