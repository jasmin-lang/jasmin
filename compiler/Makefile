# -*- Makefile -*-

# --------------------------------------------------------------------
JSJOBS    ?= 2
CHECKPY   ?=
CHECK     := $(CHECKPY) scripts/runtest --jobs="$(JSJOBS)"
CHECK     += config/tests.config
CHECKCATS ?= \
	x86-64-ATT \
	x86-64-Intel \
	x86-64-nolea \
	arm-m4 \
	x86-64-stack-zero-loop \
	x86-64-stack-zero-unrolled \
	arm-m4-stack-zero-loop \
	arm-m4-stack-zero-unrolled \
	risc-v \
	CCT CCT-DOIT SCT

# --------------------------------------------------------------------
DESTDIR  ?=
PREFIX   ?= /usr/local
BINDIR   := $(PREFIX)/bin
INSTALL  ?= install
DUNE_OPTS ?= --prefix $(PREFIX)

# --------------------------------------------------------------------
DISTDIR ?= jasmin-compiler

# --------------------------------------------------------------------
OBELISK ?= obelisk

# --------------------------------------------------------------------
.PHONY: all CIL check check-ci
.PHONY: clean install uninstall dist

all:
	$(RM) jasminc jasmin2tex jasmin-ct jasmin2ec
	dune build @check @install
	for p in _build/install/default/bin/*; do ln -sf $$p $$(basename $$p); done

CIL:
	$(RM) -f src/CIL/*.ml src/CIL/*.mli ../proofs/extraction.vo
	$(MAKE) -C ../proofs extraction
	cp ../proofs/lang/ocaml/*.ml  src/CIL/
	cp ../proofs/lang/ocaml/*.mli src/CIL/

check: all
	$(CHECK) --report=report.log $(CHECKCATS)

check-ci:
	$(CHECK) --report=- $(CHECKCATS)

check-ec:
	$(MAKE) -C examples/gimli/proofs
	$(MAKE) -C examples/extraction-unit-tests
	$(MAKE) -C examples/extraction-safety-unit-tests

check-all: check
	dune runtest -f

clean:
	dune clean
	$(RM) jasminc jasmin2tex jasmin-ct jasmin2ec

install:
	dune install $(DUNE_OPTS)

uninstall:
	dune uninstall $(DUNE_OPTS)

# --------------------------------------------------------------------
dist: $(DISTDIR).tgz

$(DISTDIR).tgz: MANIFEST
	$(RM) -r $(DISTDIR)
	../scripts/distribution $(DISTDIR)/compiler $<
	cp -riv ../eclib $(DISTDIR)/
	cp ../Makefile.compiler $(DISTDIR)/Makefile
	cp jasmin.opam $(DISTDIR)/
	cp ../README.compiler.md $(DISTDIR)/README.md
	cp ../LICENSE $(DISTDIR)/
	tar -czvf $(DISTDIR).tgz --owner=0 --group=0 $(DISTDIR)
	$(RM) -r $(DISTDIR)

# --------------------------------------------------------------------
jasmin.bnf: src/parser.mly
	$(OBELISK) -i -o $@ $<

jasmin.ebnf: scripts/expand-bnf jasmin.bnf
	@sed -f $^ > $@
