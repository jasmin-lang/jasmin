OCAMLBUILD=ocamlbuild
MENHIRFLAGS=-use-menhir -menhir "menhir -v --explain --strict"
FINDLIBFLAGS=-use-ocamlfind -classic-display
CFLAGS=-cflags "-w +a-e-9-45-44"
COREFLAGS=-pkg core \
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

.PHONY: all jasminc clean doc \
  run_tests run-run_tests tests

all: jasminc

unit-tests: run-run_tests test-arith

jasminc:
	$(OCAMLBUILD) $(OCAMLBUILDFLAGS) src/Main/jasminc.native

clean:
	-@rm jasminc.native
	$(OCAMLBUILD) -clean

doc:
	cd doc && make

###########################################################################
# Targets for development and testing

test-conv:
	$(OCAMLBUILD) $(OCAMLBUILDFLAGS) src/Test/Tests_Conv.native
	./Tests_Conv.native

demo: jasmin
	./scripts/demo.sh



run_tests:
	test -d _build/c_src || mkdir -p _build/c_src
	gcc -shared -o _build/c_src/libarith.so \
	  c_src/arith.c
	gcc -o _build/c_src/mont_amd64_64 \
	  c_src/arith.c \
	  c_src/mont_amd64_64.c \
	  c_src/ladderstep_amd64_64_consts.s \
	  c_src/ladderstep_amd64_64.s \
	  c_src/work_cswap_amd64_64.s
	$(OCAMLBUILD) $(OCAMLBUILDFLAGS) $(CLIBFLAGS) src/Main/run_tests.native

run-run_tests: run_tests
	./run_tests.native

tests: jasminc
	./scripts/run_tests.sh

test-arith:
	gcc -DTEST c_src/arith.c -o t_arith
	./t_arith

test-curve25519-rust: jasminc
	./jasminc.native ../examples/curve25519/src/scalarmult.rs

%.inferred.mli:
	ocamlbuild $(OCAMLBUILDFLAGS) src/$@ && cat _build/src/$@

