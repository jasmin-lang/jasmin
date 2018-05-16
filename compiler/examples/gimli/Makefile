JASMINC?=jasminc

.SUFFIXES: .s .o .jazz

all: test.out testv.out

test.out: test
	./test > test.out
	cmp test.out test.exp

testv.out: testv
	./testv > testv.out
	cmp testv.out test.exp

test: test.c gimli.o
	$(CC) -o $@ $^

testv: test.c gimliv.o
	$(CC) -o $@ $^

%.o: %.s
	$(CC) -c $<

%.s: %.jazz
	$(JASMINC) -o $@ $<

clean:
	@echo "cleaning..."
	@rm test test.out gimli.o 2> /dev/null || true

archclean: clean
	@rm -r gimli.s 2> /dev/null || true
