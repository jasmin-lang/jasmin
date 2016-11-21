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

.PHONY: all dmasm clean doc test-dmasm-assemble test-dmasm-reg \
  run_tests run-run_tests tests

all: dmasm

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

test-conv:
	$(OCAMLBUILD) $(OCAMLBUILDFLAGS) src/Test/Tests_Conv.native
	./Tests_Conv.native

test-dmasm-reg: dmasm
	./dmasm.native -p -t "register_allocate[10]" examples/test/register-alloc.mil

test-dmasm-square: dmasm
	./dmasm.native -p -t "expand[n=4],ssa,register_allocate[15],strip_comments,asm[x86-64]" examples/test/add_call.mil

test-dmasm-add-call: dmasm
	./dmasm.native -p -t "expand[n=3],ssa,strip_comments,register_allocate[15],asm[x86-64]" examples/test/add_call.mil

demo: dmasm
	./scripts/demo.sh

test-dmasm-typing: dmasm
	./dmasm.native -p -t "typecheck" tests/typing/must_fail/t_01.mil

test-dmasm-parser: dmasm
	./dmasm.native -p -t "typecheck" tests/parser/ok/t_01.mil

test-dmasm-interp: dmasm
	./dmasm.native -t "interp[n=4][][test_fun][[2,3,4,5]]" tests/interp/ok/t_01.mil

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

tests: dmasm
	./scripts/run_tests.sh

test-arith:
	gcc -DTEST c_src/arith.c -o t_arith
	./t_arith

%.inferred.mli:
	ocamlbuild $(OCAMLBUILDFLAGS) src/$@ && cat _build/src/$@

