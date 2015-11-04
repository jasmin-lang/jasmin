OCAMLBUILD=ocamlbuild
MENHIRFLAGS=-use-menhir -menhir "menhir -v"
FINDLIBFLAGS=-use-ocamlfind -classic-display
CFLAGS=-cflags "-w +a-e-9-45-44"
COREFLAGS=-pkg core \
    -pkg sexplib.syntax,comparelib.syntax,fieldslib.syntax,variantslib.syntax \
    -pkg bin_prot.syntax \
    -tag short_paths \
    -cflags -strict-sequence


UNAME_S := $(shell uname -s)
ifeq ($(UNAME_S),Linux)
  CLIBFLAGS=-lflags -cclib,-Xlinker,-cclib,--no-as-needed,-cclib,-Lc_src,-cclib,-larith,-cclib,-Xlinker,-cclib,-rpath,-cclib,`pwd`/_build/c_src
endif
ifeq ($(UNAME_S),Darwin)
  CLIBFLAGS=-lflags -cclib,-Lc_src,-cclib,-larith
endif

OCAMLBUILDFLAGS= $(CFLAGS) $(COREFLAGS) $(FINDLIBFLAGS) $(MENHIRFLAGS)

###########################################################################
# main targets

.PHONY: all dmasm clean doc test-dmasm-assemble test-dmasm-reg \
  run_tests run-run_tests

all: dmasm unit-tests

unit-tests: run-run_tests test-arith

dmasm:
	$(OCAMLBUILD) $(OCAMLBUILDFLAGS) src/Main/dmasm.native

clean:
	-@rm doc/dmasm.html
	-@rm dmasm.native
	-@rm run_tests.native
	$(OCAMLBUILD) -clean

doc:
	cd doc && make

###########################################################################
# Targets for development and testing


test-dmasm-reg: dmasm
	./dmasm.native -p -t "register_allocate[10]" examples/test/register-alloc.mil

test-dmasm-square: dmasm
	./dmasm.native -p -t "expand[n=3],ssa,register_allocate[15],strip_comments,asm[x86-64]" examples/25519-4limb/square.mil

test-dmasm-add-call: dmasm
	./dmasm.native -p -t "expand[n=3],ssa,strip_comments,register_allocate[15],asm[x86-64]" examples/test/add_call.mil
	#./dmasm.native -p -t "expand[n=3],ssa,register_allocate[15],strip_comments,asm[x86-64]" examples/test/add_call.mil

run_tests:
	test -d _build/c_src || mkdir -p _build/c_src
	gcc -fPIC -c c_src/arith.c -o _build/c_src/arith.o
	ar rc _build/c_src/libarith.a _build/c_src/arith.o
	gcc -shared -o _build/c_src/libarith.so _build/c_src/arith.o
	$(OCAMLBUILD) $(OCAMLBUILDFLAGS) $(CLIBFLAGS) src/Main/run_tests.native

run-run_tests: run_tests
	./run_tests.native

test-arith:
	gcc -DTEST c_src/arith.c -o t_arith
	./t_arith

%.inferred.mli:
	ocamlbuild $(OCAMLBUILDFLAGS) src/$@ && cat _build/src/$@

