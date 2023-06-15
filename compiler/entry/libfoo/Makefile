CC=clang
AR=llvm-ar

all: libfoo.so libfoo.a dllfoo.so

foo.o: foo.c
	${CC} -c -fPIC -O0 foo.c -o foo.o

libfoo.so: foo.o
	${CC} -shared -fPIC foo.o -o libfoo.so

libfoo.a: foo.o
	${AR} r libfoo.a foo.o

dllfoo.so: libfoo.so
	${CC} -shared -fPIC foo.o -o dllfoo.so

.PHONY: clean

clean:
	rm -f *.o *.so *.a
