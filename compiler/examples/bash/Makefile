JASMINC=../../jasminc.native

.SUFFIXES: .jazz .c .s .o

all: test

test: bash_ref.o test.o
	$(CC) -o $@ $^

%.s: %.jazz
	$(JASMINC) -o $@ $<

%.o: %.c
	$(CC) -c -o $@ $<

%.o: %.s
	$(CC) -c -o $@ $<
