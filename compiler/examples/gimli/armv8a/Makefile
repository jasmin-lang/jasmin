JASMINC?=../../../jasminc

.SUFFIXES: .s .o .jazz .jinc

all: test.out

test.out: test
	./test > test.out
	cmp test.out ../x86-64/test.exp

test: ../x86-64/test.c gimli.o
	$(CC) -o $@ $^

%.o: %.s
	$(CC) -c $<

%.s: %.jazz
	$(JASMINC) -arch armv8a -o $@ $<

clean:
	@echo "cleaning..."
	$(RM) test test*.out gimli*.o 2> /dev/null || true

archclean: clean
	$(RM) -r gimli.s 2> /dev/null || true
