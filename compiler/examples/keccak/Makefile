JASMINC?=../../jasminc.native

FILES:=keccakP1600 sponge

.SUFFIXES: .japp .jazz .s .o

all: $(foreach f,$(FILES),$(f).o) test

test: test.c sponge.o
	$(CC) -o $@ $^

%.jazz: %.japp
	gpp -o $@ $<

%.s: %.jazz
	$(JASMINC) -o $@ $<

%.o: %.s
	$(CC) -c -o $@ $<

clean:
	$(RM) *.o
