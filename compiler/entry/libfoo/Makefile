CC=clang
AR=llvm-ar
KSFLAGS=-lkeystone -lstdc++ -lm
UCFLAGS=-lpthread -lm -lunicorn

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

test_keystone: test_keystone.c 
	${CC} -o test_keystone test_keystone.c ${KSFLAGS}

test_unicorn: test_unicorn.c 
	${CC} -o test_unicorn test_unicorn.c ${UCFLAGS}

.PHONY: clean

clean:
	rm -f *.o *.so *.a test_keystone test_unicorn
