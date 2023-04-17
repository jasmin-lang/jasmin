JASMINC ?= ../../../jasminc

all: run
	./run

siphash.s: siphash.jazz
	$(JASMINC) -o $@ $<

run: siphash.c siphash.s run.c
	$(CC) -O2 -o $@ $^

clean:
	rm -f run siphash.s
