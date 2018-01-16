.PHONY : clean

ntt: bench.c ntt.mil.s ntt.s precomp.c reduce.c consts.c
	gcc -Wfatal-errors -Ofast -mtune=native -o $@ $^

clean:
	find . -name "*~" -exec rm {} \;
	rm -f ntt.mil
