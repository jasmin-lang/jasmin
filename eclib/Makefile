# -*- Makefile -*-

# --------------------------------------------------------------------
ECCONF   := tests.config 
ECARGS   ?=
CHECKS   ?= jasmin

# --------------------------------------------------------------------
DESTDIR  ?=
PREFIX   ?= /usr/local
BINDIR   := $(PREFIX)/bin
LIBDIR   := $(PREFIX)/lib
SHRDIR   := $(PREFIX)/share
INSTALL  ?= ../scripts/install-sh

# --------------------------------------------------------------------
.PHONY: default usage check install uninstall

default: check

usage:
	@echo "Usage: make <target> where <target> in [check|install|uninstall]" >&2

check:
	easycrypt runtest $(ECARGS) $(ECCONF) $(CHECKS)

install:
	$(INSTALL) -m 0755 -d $(DESTDIR)$(LIBDIR)/jasmin/easycrypt
	$(INSTALL) -m 0644 -t $(DESTDIR)$(LIBDIR)/jasmin/easycrypt *.ec

uninstall:
	$(RM) -r $(DESTDIR)$(LIBDIR)/jasmin
