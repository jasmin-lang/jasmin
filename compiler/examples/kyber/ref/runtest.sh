../../../jasminc.native -lea -pall -pasm ntt.mil > ntt.mil.s
gcc test_ntt.c ntt.c precomp.c reduce.c ntt.mil.s
./a.out
