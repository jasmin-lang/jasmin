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
PREFIX ?= /usr/local
BINDIR := $(PREFIX)/bin
LIBDIR := $(PREFIX)/lib/jasmin
SHRDIR := $(PREFIX)/share/jasmin

# --------------------------------------------------------------------
.PHONY: all build byte native CIL install uninstall tests __force__
.PHONY: %.ml %.mli %.inferred.mli

all: build
	@true

build: jasmin.mlpack native

define do-build
	$(OCAMLBUILD) "$(1)"
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
	rm -f CIL/*.ml CIL/*.mli
	$(MAKE) -C ../proofs extraction
	cp ../proofs/lang/ocaml/*.ml  CIL/
	cp ../proofs/lang/ocaml/*.mli CIL/

install: build
	$(INSTALL) -m 0755 -d $(DESTDIR)$(BINDIR)
	$(INSTALL) -m 0755 -T jasminc.native $(DESTDIR)$(BINDIR)/jasminc

uninstall:
	rm -f $(DESTDIR)$(BINDIR)/jasminc

_c_build: __force__
	[ -e $@ ] || mkdir $@

lib%.a: _c_build/%.o
	rm -f $@ && ar r $@ $< && ranlib $@

_c_build/%.o: _c_build/%.s
	gcc -c -o $@ $<

_c_build/%.s: examples/%.mil _c_build jasminc.native
	./jasminc.native $< -o $@

tests: native
	scripts/jasmin-test examples/*.mil

clean:
	$(OCAMLBUILD) -clean -classic-display
	rm -rf _c_build
	rm -f jasminc.native jasminc.byte lib*.a

# --------------------------------------------------------------------
%.inferred.mli:
	@$(call do-core-build,src/$@) && cat _build/src/$@

# --------------------------------------------------------------------
%.ml:
	$(call do-core-build,src/$*.cmo)

# --------------------------------------------------------------------
%.mli:
	$(call do-core-build,src/$*.cmi)
