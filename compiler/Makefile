# -*- Makefile -*-

# --------------------------------------------------------------------
MAKE_PID := $(shell echo $$PPID)
JOB_FLAG := $(shell ps T | sed -n 's/.*$(MAKE_PID).*$(MAKE).* \(-j\|--jobs=*\) *\([0-9]*\).*/-j\2/p')
JOB_NUM  ?= $(or $(patsubst -j%,%,$(or $(JOB_FLAG),-j1)),$(shell nproc))

OCAMLBUILD_JOBS  ?= $(JOB_NUM)
OCAMLBUILD_BIN   ?= ocamlbuild
OCAMLBUILD_EXTRA ?=
OCAMLBUILD_OPTS  := -use-ocamlfind -j $(OCAMLBUILD_JOBS)

# In Emacs, use classic display to enable error jumping.
ifeq ($(shell echo $$TERM), dumb)
 OCAMLBUILD_OPTS += -classic-display
endif
OCAMLBUILD_OPTS += $(OCAMLBUILD_EXTRA)

OCAMLBUILD := $(OCAMLBUILD_BIN) $(OCAMLBUILD_OPTS)

# --------------------------------------------------------------------
JSJOBS    ?= $(JOB_NUM)
CHECKPY   ?=
CHECK     := $(CHECKPY) scripts/runtest --jobs="$(JSJOBS)"
CHECK     += config/tests.config
CHECKCATS ?= all safety CCT nolea print arm

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

build: jasmin.mlpack native

define do-build
	rm -f jasminc
	$(OCAMLBUILD) "$(1)"
	ln -sf "_build/$(1)" jasminc
endef

byte:
	$(call do-build,entry/jasminc.byte)

native:
	$(call do-build,entry/jasminc.native)

jasmin.mlpack: __force__
	( echo '# GENERATED - EDIT jasmin.mlpack.in'; \
	  cat jasmin.mlpack.in; \
	  echo "$(wildcard CIL/*.ml*)" | tr ' ' '\n' | sed 's/\..*$$//' | sort -u ) \
	> jasmin.mlpack

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
	$(OCAMLBUILD) -clean -classic-display
	rm -rf _c_build
	rm -f jasminc.native jasminc.byte lib*.a

install:
	$(INSTALL) -m 0755 -d $(DESTDIR)$(BINDIR)
	$(INSTALL) -m 0755 -T jasminc.native $(DESTDIR)$(BINDIR)/jasminc

uninstall:
	rm -f $(DESTDIR)$(BINDIR)/jasminc

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

_c_build/%.s: examples/%.jazz _c_build jasminc.native
	./jasminc.native $< -o $@

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
