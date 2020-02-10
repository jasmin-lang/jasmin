# -*- Makefile -*-

# --------------------------------------------------------------------
SUBDIRS :=

include Makefile.common

# --------------------------------------------------------------------
.PHONY: install extraction

install: Makefile.coq
	$(MAKE) -f Makefile.coq install

extraction: Makefile.coq
	rm -f lang/ocaml/*.ml lang/ocaml/*.mli
	rm -f lang/extraction.vo
	$(COQMAKE) lang/extraction.vo

# --------------------------------------------------------------------
this-clean::
	rm -f lang/*.glob lang/*.d lang/*.vo lang/.*.vo
	rm -f compiler/*.glob compiler/*.d compiler/*.vo compiler/.*.vo


this-distclean::
	rm -f $(shell find . -name '*~')
