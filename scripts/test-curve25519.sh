#!/bin/sh

set -e

REPO=formosa-crypto
NAME=formosa-25519
BRANCH=main

FILE="$NAME.tar.gz"
ROOT=$(echo -n $NAME-$BRANCH | tr / -)

DIR=libjade

curl -v -o $FILE https://codeload.github.com/$REPO/$NAME/tar.gz/$BRANCH
tar xvf $FILE
rm -rf $DIR/
mv $ROOT $DIR


JASMINC=$PWD/compiler/jasminc
JASMIN_CT=$PWD/compiler/jasmin-ct

cd $DIR

for x in ref4 ref5 mulx
do
  FILE=src/crypto_scalarmult/curve25519/amd64/$x/scalarmult.jazz
  echo -n Compile $x
  $JASMINC -wall -o $x.s $FILE && echo ... OK
  echo Check $x for Constant-Time
  $JASMIN_CT --print $FILE
  echo -n Check $x for DOIT Constant-Time
  $JASMIN_CT --doit $FILE >/dev/null && echo ... OK
  echo -n Check $x for Speculative Constant-Time
  $JASMIN_CT --speculative $FILE > $x_sct.log && echo ... OK
  echo
done
