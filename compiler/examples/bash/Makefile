JASMINC=../../jasminc.native

.SUFFIXES: .jazz .c .s .o

all: test testv testc testavx2
	./testc
	./testavx2
	./test
	./testv

test: bash_ref.o test.o
	$(CC) -o $@ $^

testv: bashv.o test.o
	$(CC) -o $@ $^

%.s: %.jazz
	$(JASMINC) -o $@ $<

%.o: %.c
	$(CC) -c -o $@ $<

%.o: %.s
	$(CC) -c -o $@ $<

bash_avx2.o: bash_avx2.c
	gcc -march=core-avx2 -c $<

testavx2: bash_avx2.o test.o
	$(CC) -o $@ $^

testc: bash.c test.o
	$(CC) -o $@ $^
