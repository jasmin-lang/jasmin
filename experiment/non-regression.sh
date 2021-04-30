#!/bin/sh

SRC=../compiler/tests/cost/crypto/*.jazz

for p in $SRC
do
    $JASMIN_REF/bin/jasminc -o ref.s $p 2>/dev/null
    $JASMIN_CT/bin/jasminc -o ct.s $p 2>/dev/null
    diff ref.s ct.s
    if [ $? ]
    then
	echo $(tput setaf 2)Program “$(basename $p .jazz)” is compiled as before.
    else
        echo $(tput setaf 1)Regression on program $p.
    fi
done
