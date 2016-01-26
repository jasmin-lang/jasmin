#! /bin/bash

DMASM=./dmasm.native
ALL_FAILED=""

# set -x

function ok_tests() {
  WILDCARD=$1
  TRANS=$2

  echo
  echo "*******************************************************************"
  echo "Running ok tests for $WILDCARD!"
  echo

  FAILED=""
  OK=""
  for file in \
              $WILDCARD \
              ; do \
    printf "File $file: \n"
    before=$(date +%s)
    if ! $DMASM -t "$TRANS" $file 2>&1 | \
         grep --colour=always -i \
           -e 'Processed File'; then
      echo "FAILED: rerun with $DMASM -t '$TRANS' $file"
      FAILED="$FAILED\n  $file"
      ALL_FAILED="$ALL_FAILED\n  $file"
    else
      OK="$OK\n  $file"
    fi
    after=$(date +%s)
    dt=$((after - before))
    printf  "  \e[1;32m$dt seconds\e[1;0m\n"
    done

  printf "\nFailed: $FAILED"
  printf "\nOK: $OK"
}

function fail_tests() {
  WILDCARD=$1
  TRANS=$2
  echo
  echo
  echo "*******************************************************************"
  echo "Running mustfail tests!"
  echo

  FAILED=""
  OK=""
  for file in $WILDCARD; do
    ERR=`grep ERROR $file | sed 's/ERROR: //'`
    printf "Testing $file, expecting error ''$ERR''\n"
    if ! $DMASM -t "$TRANS" $file 2>&1 | \
         grep -F "$ERR"; then
      echo "FAILED: rerun with $DMASM -t '$TRANS' $file"
      FAILED="$FAILED\n  $file"
      ALL_FAILED="$ALL_FAILED\n  $file"
    else
      OK="$OK\n  $file"
    fi
  done
  printf "\nFailed:$FAILED"
  printf "\nOK:$OK\n"
}

function run_tests() {
  BASEDIR=$1
  TRANS=$2
  echo ""
  echo "###################################################################"
  echo "Running tests in $BASEDIR"

  ok_tests   "$BASEDIR/ok/*.mil"        "$TRANS"
  fail_tests "$BASEDIR/must_fail/*.mil" "$TRANS"
}

run_tests "tests/parser"   ""
run_tests "tests/typing"   "typecheck"
run_tests "tests/interp"   "interp[n=4][][test_fun][[2,3,4,5]]"
run_tests "tests/compiler" "inline[bar],expand[bar][n=2],save[/tmp/a.mil],interp[][][test][]"

(test -z "$ALL_FAILED" && printf "\nNo failures!\n\n") || printf "\nSome tests failed!\n\n"

#echo "###################################################################"
#echo "Running tests for examples/25519-4limb/ladderstep.mil"

#ok_tests   "examples/25519-4limb/ladderstep.mil" "typecheck"
#ok_tests   "examples/25519-4limb/ladderstep.mil" "typecheck"
