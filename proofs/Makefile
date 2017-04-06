# -*- Makefile -*-

# --------------------------------------------------------------------
SUBDIRS :=

include Makefile.common

# --------------------------------------------------------------------
.PHONY: install

install:
	$(MAKE) -f Makefile.coq install

# --------------------------------------------------------------------
this-clean::
	rm -f src/*.glob src/*.d src/*.vo

this-distclean::
	rm -f $(shell find . -name '*~')
