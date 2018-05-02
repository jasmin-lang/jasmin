JASMINC?=jasminc
all: test.out

test.out: test
	./test > test.out
	cmp test.out test.exp

test: test.c gimli.o
	$(CC) -o test test.c gimli.o

gimli.o: gimli.s
	$(CC) -c gimli.s

gimli.s: gimli.jazz
	$(JASMINC) -o $@ $<

clean:
	@echo "cleaning..."
	@rm test test.out gimli.o 2> /dev/null || true

archclean: clean
	@rm -r gimli.s 2> /dev/null || true
