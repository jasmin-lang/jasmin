#!/bin/sh

# Extract the EasyCrypt models of the formosa-libjade entry points
# (ML-KEM, ML-DSA) and check them with EasyCrypt.

set -e

REPO=formosa-crypto
NAME=formosa-libjade
BRANCH=main

FILE="$NAME.tar.gz"
ROOT=$(echo -n $NAME-$BRANCH | tr / -)

DIR=libjade

curl -v -o $FILE https://codeload.github.com/$REPO/$NAME/tar.gz/$BRANCH
tar xvf $FILE
rm -rf $DIR/
mv $ROOT $DIR

JASMIN2EC=$PWD/compiler/jasmin2ec
EASYCRYPT="easycrypt compile $ECARGS"

SRC=$DIR/src
OUT=$DIR/extracted

for MODEL in old barray
do
  mkdir -p $OUT/$MODEL
  for s in 512 768 1024
  do
    echo Extract ML-KEM-$s, array model $MODEL
    $JASMIN2EC --array-model=$MODEL -I Keccak=$SRC/fips202 \
      -o $OUT/$MODEL/Jmlkem$s.ec $SRC/mlkem/avx2/sct/$s/jmlkem.jazz
  done
  for s in 44 65 87
  do
    echo Extract ML-DSA-$s, array model $MODEL
    $JASMIN2EC --array-model=$MODEL -I Keccak=$SRC/fips202 \
      -I Common=$SRC/mldsa/avx2/sct/common \
      -o $OUT/$MODEL/Jmldsa$s.ec $SRC/mldsa/avx2/sct/$s/mldsa.jazz
  done
  for f in $OUT/$MODEL/Jml*.ec
  do
    echo Check $f
    $EASYCRYPT $f
  done
done
