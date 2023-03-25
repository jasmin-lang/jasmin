# -*- Makefile -*-

# --------------------------------------------------------------------
JSJOBS    ?= 2
CHECKPY   ?=
CHECK     := $(CHECKPY) scripts/runtest --jobs="$(JSJOBS)"
CHECK     += config/tests.config
CHECKCATS ?= safety CCT x86-64-ATT x86-64-Intel x86-64-print x86-64-nolea arm-m4

# --------------------------------------------------------------------
DESTDIR  ?=
PREFIX   ?= /usr/local
BINDIR   := $(PREFIX)/bin
LIBDIR   := $(PREFIX)/lib
SHRDIR   := $(PREFIX)/share
INSTALL  ?= ../scripts/install-sh

# --------------------------------------------------------------------
DISTDIR ?= jasmin-compiler

# --------------------------------------------------------------------
OBELISK ?= obelisk

# --------------------------------------------------------------------
.PHONY: all build byte native CIL check check-ci __force__
.PHONY: clean install uninstall dist
.PHONY: %.ml %.mli %.inferred.mli

.PRECIOUS: _c_build/%.s _c_build/%.o

all: build
	@true

build: native

define do-build
	$(RM) jasminc jazz2tex jazz2cl
	dune build jasminc.$(1)
	dune build jazz2tex.$(1)
	dune build jazz2cl.$(1)
	ln -sf "_build/default/jasminc.$(1)" jasminc
	ln -sf "_build/default/jazz2tex.$(1)" jazz2tex
	ln -sf "_build/default/jazz2cl.$(1)" jazz2cl
endef

byte:
	$(call do-build,bc)

native:
	$(call do-build,exe)

CIL:
	rm -f CIL/*.ml CIL/*.mli ../proofs/extraction.vo
	$(MAKE) -C ../proofs extraction
	cp ../proofs/lang/ocaml/*.ml  CIL/
	cp ../proofs/lang/ocaml/*.mli CIL/

check: build
	$(CHECK) --report=report.log $(CHECKCATS)

check-ci:
	$(CHECK) --report=- $(CHECKCATS)

clean:
	dune clean
	rm -rf _c_build
	rm -f jasminc jazz2tex jazz2cl lib*.a

install:
	$(INSTALL) -m 0755 -d $(DESTDIR)$(BINDIR)
	$(INSTALL) -m 0755 -T jasminc $(DESTDIR)$(BINDIR)/jasminc
	$(INSTALL) -m 0755 -T jazz2tex $(DESTDIR)$(BINDIR)/jazz2tex
	$(INSTALL) -m 0755 -T jazz2cl $(DESTDIR)$(BINDIR)/jazz2cl

uninstall:
	$(RM) $(DESTDIR)$(BINDIR)/jasminc
	$(RM) $(DESTDIR)$(BINDIR)/jazz2tex
	$(RM) $(DESTDIR)$(BINDIR)/jazz2cl

# --------------------------------------------------------------------
dist: $(DISTDIR).tgz

$(DISTDIR).tgz: MANIFEST
	$(RM) -r $(DISTDIR)
	../scripts/distribution $(DISTDIR) $<
	tar -czvf $(DISTDIR).tgz --owner=0 --group=0 $(DISTDIR)
	$(RM) -r $(DISTDIR)

# --------------------------------------------------------------------
_c_build: __force__
	[ -e $@ ] || mkdir $@

lib%.a: _c_build/%.o
	rm -f $@ && ar rc $@ $< && ranlib $@

_c_build/%.o: _c_build/%.s
	gcc -c -o $@ $<

_c_build/%.s: examples/%.jazz _c_build jasminc
	./jasminc $< -o $@

# --------------------------------------------------------------------
%.inferred.mli:
	@$(call do-core-build,src/$@) && cat _build/src/$@

# --------------------------------------------------------------------
%.ml:
	$(call do-core-build,src/$*.cmo)

# --------------------------------------------------------------------
%.mli:
	$(call do-core-build,src/$*.cmi)

# --------------------------------------------------------------------
jasmin.bnf: src/parser.mly
	$(OBELISK) -i -o $@ $<

jasmin.ebnf: scripts/expand-bnf jasmin.bnf
	@sed -f $^ > $@
