.PHONY : clean

ntt: bench.c ntt.mil.s ntt.c precomp.c reduce.c
	gcc -Wfatal-errors -Ofast -mtune=native -o $@ $^

clean:
	find . -name "*~" -exec rm {} \;
	rm -f ntt.mil