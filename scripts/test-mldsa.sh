#!/bin/sh

set -e

REPO=formosa-crypto
NAME=formosa-mldsa
BRANCH=main

FILE="$NAME.tar.gz"
ROOT=$(echo -n $NAME-$BRANCH | tr / -)

DIR=libjade

curl -v -o $FILE https://codeload.github.com/$REPO/$NAME/tar.gz/$BRANCH
tar xvf $FILE
rm -rf $DIR/
mv $ROOT $DIR

cd $DIR

for p in 44 65 87
do
    for i in "arm-m4 ref" "arm-m4 lowram" "x86-64 ref" "x86-64 avx2"
    do
        set -- $i
        PARAM="ARCHITECTURE=$1 PARAMETER_SET=$p IMPLEMENTATION_TYPE=$2"
        J="JASMINC=$PWD/../compiler/jasminc JASMINCT=$PWD/../compiler/jasmin-ct"
        echo $PARAM
        echo ASM
        make $PARAM $J
        echo CHECK CT
        make $PARAM $J check-ct
        if [ "$i" = "x86-64 ref" ]
        then
            echo CHECK SCT
            make $PARAM $J check-sct
        fi
    done
done
