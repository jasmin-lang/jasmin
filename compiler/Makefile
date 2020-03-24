# -*- Makefile -*-

# --------------------------------------------------------------------
OCAMLBUILD_JOBS  ?= 2
OCAMLBUILD_BIN   ?= ocamlbuild
OCAMLBUILD_EXTRA ?=
OCAMLBUILD_OPTS  := -use-ocamlfind -j $(OCAMLBUILD_JOBS)

# In Emacs, use classic display to enable error jumping.
ifeq ($(shell echo $$TERM), dumb)
 OCAMLBUILD_OPTS += -classic-display
endif
OCAMLBUILD_OPTS += $(OCAMLBUILD_EXTRA)

OCAMLBUILD := $(OCAMLBUILD_BIN) $(OCAMLBUILD_OPTS)
INSTALL    := scripts/install-sh

# --------------------------------------------------------------------
JSJOBS    ?= 2
CHECKPY   ?=
CHECK     := $(CHECKPY) scripts/runtest --jobs="$(JSJOBS)"
CHECK     += config/tests.config
CHECKCATS ?= all nolea

# --------------------------------------------------------------------
PREFIX ?= /usr/local
BINDIR := $(PREFIX)/bin
LIBDIR := $(PREFIX)/lib/jasmin
SHRDIR := $(PREFIX)/share/jasmin

# --------------------------------------------------------------------
.PHONY: all build byte native CIL check __force__
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

check-ci: build
	$(CHECK) --report=- $(CHECKCATS)

clean:
	$(OCAMLBUILD) -clean -classic-display
	rm -rf _c_build
	rm -f jasminc.native jasminc.byte lib*.a

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
