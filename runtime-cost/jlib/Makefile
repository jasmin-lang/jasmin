SRC:=$(wildcard src/*.s)
OBJ:=$(SRC:%.s=%.o)

all: libjlib.a

install: all
	install -m 0755 -d $(PREFIX)/lib
	install -m 0644 -t $(PREFIX)/lib libjlib.a

%.o: %.s
	cc -c -o $@ $<

libjlib.a: $(OBJ)
	ar rv $@ $^
