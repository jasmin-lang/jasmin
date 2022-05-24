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
export EXCLUDE="crypto_kem/kyber/kyber512/amd64/avx2/ crypto_kem/kyber/kyber768/amd64/avx2/"

echo "Info: $MAKELINE (EXCLUDE=$EXCLUDE)"

curl -v -o $FILE https://codeload.github.com/formosa-crypto/$NAME/tar.gz/refs/heads/$BRANCH
tar xvf $FILE

make $MAKELINE

mkdir -p $OUT
(cd $OUT && tar xvf ../$DIR/check.tar.gz)

make $MAKELINE err
