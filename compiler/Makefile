OCAMLBUILD=ocamlbuild
MENHIRFLAGS=-use-menhir -menhir "menhir -v"
FINDLIBFLAGS=-use-ocamlfind -classic-display
CFLAGS=-cflags "-w +a-e-9-45-44"
COREFLAGS=-pkg core \
    -pkg sexplib.syntax,comparelib.syntax,fieldslib.syntax,variantslib.syntax \
    -pkg bin_prot.syntax \
    -tag short_paths \
    -cflags -strict-sequence

OCAMLBUILDFLAGS= $(CFLAGS) $(COREFLAGS) $(FINDLIBFLAGS) $(MENHIRFLAGS)

###########################################################################
# main targets

.PHONY: all dmasm clean doc test-dmasm-assemble test-dmasm-reg \
  run_tests run-run_tests

all: dmasm

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

test-dmasm-assemble: dmasm
	./dmasm.native -p -t "asm[x86-64]" examples/test-assemble.mil

test-dmasm-reg: dmasm
	./dmasm.native -p -t "register_alloc" examples/test-register-alloc.mil

test-dmasm-mul:
	./dmasm.native -p -t "expand[n=3],ssa,register_allocate[15],asm[x86-64]" examples/mul-4limb.mil

run_tests:
	$(OCAMLBUILD) $(OCAMLBUILDFLAGS) src/Main/run_tests.native

run-run_tests: run_tests
	./run_tests.native

%.inferred.mli:
	ocamlbuild $(OCAMLBUILDFLAGS) src/$@ && cat _build/src/$@

