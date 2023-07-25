CC=clang
AR=llvm-ar

all: libfoo.so libfoo.a dllfoo.so

foo.o: foo.c
	${CC} -c -fPIC -O0 foo.c -o foo.o

myasm.o: myasm.s
	${CC} -c -fPIC -O0 myasm.s -o myasm.o

libfoo.so: foo.o myasm.o
	${CC} -shared -fPIC foo.o myasm.o -o libfoo.so

libfoo.a: foo.o
	${AR} r libfoo.a foo.o myasm.o

dllfoo.so: libfoo.so
	${CC} -shared -fPIC foo.o myasm.o -o dllfoo.so

.PHONY: clean

clean:
	rm -f *.o *.so *.all
