JASMINC?=../../jasminc.native

.SUFFIXES: .s .o .jazz .jinc

all: test.out testv.out testv1.out

test.out: test
	./test > test.out
	cmp test.out test.exp

testv.out: testv
	./testv > testv.out
	cmp testv.out test.exp

testv1.out: testv1
	./testv1 > testv1.out
	cmp testv1.out test.exp

test: test.c gimli.o
	$(CC) -o $@ $^

testv: test.c gimliv.o
	$(CC) -o $@ $^

testv1: test.c gimliv1.o
	$(CC) -o $@ $^

gimliv.s gimliv1.s: gimliv.jinc

%.o: %.s
	$(CC) -c $<

%.s: %.jazz
	$(JASMINC) -o $@ $<

clean:
	@echo "cleaning..."
	@rm test testv testv1 test*.out gimli*.o 2> /dev/null || true

archclean: clean
	@rm -r gimli.s gimliv.s gimliv1.s 2> /dev/null || true
