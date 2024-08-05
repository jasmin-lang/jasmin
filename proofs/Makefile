# -*- Makefile -*-

# --------------------------------------------------------------------
SUBDIRS :=

include Makefile.common

# --------------------------------------------------------------------
.PHONY: install extraction

install: Makefile.coq
	$(MAKE) -f Makefile.coq install

uninstall: Makefile.coq
	$(MAKE) -f Makefile.coq uninstall

extraction: Makefile.coq
	$(RM) lang/ocaml/*.ml lang/ocaml/*.mli
	$(RM) lang/extraction.vo
	+$(COQMAKE) lang/extraction.vo

# --------------------------------------------------------------------
this-clean::
	$(RM) lang/*.glob lang/*.d lang/*.vo lang/.*.vo
	$(RM) compiler/*.glob compiler/*.d compiler/*.vo compiler/.*.vo
	$(RM) arch/*.glob arch/*.d arch/*.vo arch/.*.vo

this-distclean::
	$(RM) $(shell find . -name '*~')
