.PHONY : clean

25519-4limb-ladder_nofor: bench.c ../25519-4limb/ladder_nofor.s
	gcc -Wfatal-errors -Ofast -mtune=native -DBENCH_CYCLES=10000 -DBENCH_FVARS_DEC="uint64_t b[4] = {9, 0, 0, 0}; uint64_t e[4] = {0x7da518730a6d0777,0x4566b25172c1163c, 0x2a99c0eb872f4cdf,0x2a2cb91da5fb77b1}; uint64_t r[4];" -DBENCH_FTYPE=void  -DBENCH_FNAME=scalarmult -DBENCH_FARGS_DEC="uint64_t *,uint64_t*,uint64_t*" -DBENCH_FVARS_CALL="r,e,b" -o $@ $^

clean:
	find . -name "*~" -exec rm {} \;
	rm -f 25519-4limb-ladder_nofor
