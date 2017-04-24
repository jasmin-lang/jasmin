# -*- Makefile -*-

# --------------------------------------------------------------------
DNAME := jasminlang
COQV  ?= 8.5.3
SSRV  := 1.6.1
SSRP  := algebra
ROOT  := $(shell dirname $(realpath $(lastword $(MAKEFILE_LIST))))

# --------------------------------------------------------------------
.PHONY: default publish check-coq check-compile docker

# --------------------------------------------------------------------
default:
	@true

docker:
	docker build -t $(DNAME)/test-box:$(COQV)-$(SSRV) \
	  --build-arg COQVERSION=$(COQV) \
	  --build-arg SSRVERSION=$(SSRV) \
	  --build-arg SSRPACKAGES="$(SSRP:%=coq-mathcomp-%)" \
	  docker/

publish:
	docker push $(DNAME)/test-box:$(COQV)-$(SSRV)

check-coq:
	$(MAKE) -C "$(ROOT)/../proofs"

check-compiler:
	cd $(ROOT)/../compiler && opam pin add -n jasmin .
	opam install depext && opam depext jasmin
	opam install --deps-only jasmin
	$(MAKE) -C "$(ROOT)/../proofs"
	cp $(ROOT)/../proofs/lang/ocaml/*.ml  $(ROOT)/../compiler/src/CIL/
	cp $(ROOT)/../proofs/lang/ocaml/*.mli $(ROOT)/../compiler/src/CIL/
	$(MAKE) -C "$(ROOT)/../compiler"

check-compiler2:
	cd $(ROOT)/../compiler2 && opam pin add -n jasmin .
	opam install depext && opam depext jasmin
	opam install --deps-only jasmin
	$(MAKE) -C "$(ROOT)/../compiler2" CIL build
