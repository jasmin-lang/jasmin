#!/bin/sh

NAME=libjade
BRANCH=main

FILE=$NAME.tar.gz
DIR=$NAME-$BRANCH

OUT=results

# Exclude primitives that are known not to build
export EXCLUDE="./crypto_kem/kyber/kyber512/amd64/avx2/ ./crypto_kem/kyber/kyber768/amd64/avx2/"

curl -v -o $FILE https://codeload.github.com/formosa-crypto/$NAME/tar.gz/refs/heads/$BRANCH
tar xvf $FILE

make -C $DIR/src CI=1 JASMIN=$PWD/compiler/jasminc.native
res=$?

mkdir -p $OUT
(cd $OUT && tar xvf ../$DIR/src/check.tar.gz)

exit $res
