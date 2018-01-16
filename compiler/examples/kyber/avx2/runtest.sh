../../../jasminc.native -lea -pall -pasm ntt.mil > ntt.mil.s
gcc -fomit-frame-pointer -Wall -O3 -Wextra test_ntt.c ntt.s consts.c precomp.c reduce.c ntt.mil.s
./a.out
