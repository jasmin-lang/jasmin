# -*- Makefile -*-

# --------------------------------------------------------------------
SUBDIRS :=

include Makefile.common

# --------------------------------------------------------------------
.PHONY: install extraction

install:
	$(MAKE) -f Makefile.coq install

extraction: Makefile.coq
	rm -f lang/ocaml/*.ml rm -f lang/ocaml/*.mli
	touch lang/extraction.v && $(COQMAKE) lang/extraction.vo

# --------------------------------------------------------------------
this-clean::
	rm -f src/*.glob src/*.d src/*.vo

this-distclean::
	rm -f $(shell find . -name '*~')
