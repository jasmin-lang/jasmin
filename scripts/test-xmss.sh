#!/bin/sh

set -e

REPO=formosa-crypto
NAME=formosa-xmss
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

for p in hash hash_address sha256 treehash wots xmss
do
    LINE="-j$JOBS -C libjade/test/$p JASMIN=$PWD/compiler/jasminc asm"
    echo make $LINE
    make $LINE

    if [ $p != "sha256" ]
    then
        LINE="-j$JOBS -C libjade/test/$p JAZZCT=$PWD/compiler/jasmin-ct checkCT"
        echo make $LINE
        make $LINE
    fi
done
