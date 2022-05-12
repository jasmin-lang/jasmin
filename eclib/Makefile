# -*- Makefile -*-

# --------------------------------------------------------------------
ECROOT   ?=
ECCHECK  ?=
ECARGS   ?=
ECCONF   := tests.config 
XUNITOUT ?= xunit.xml
CHECKS   ?= jasmin

ifeq ($(ECCHECK),)
ifeq ($(ECROOT),)
ECCHECK := ec-runtest
else
PATH    := ${ECROOT}:${PATH}
ECCHECK := $(ECROOT)/scripts/testing/runtest
endif
endif

# --------------------------------------------------------------------
DESTDIR  ?=
PREFIX   ?= /usr/local
BINDIR   := $(PREFIX)/bin
LIBDIR   := $(PREFIX)/lib
SHRDIR   := $(PREFIX)/share
INSTALL  ?= ../scripts/install-sh

# --------------------------------------------------------------------
.PHONY: default usage check check-xunit install uninstall

default: check

usage:
	@echo "Usage: make <target> where <target> in [check|check-xunit]" >&2

check:
	$(ECCHECK) --bin-args="$(ECARGS)" $(ECCONF) $(CHECKS)

check-xunit:
	$(ECCHECK) --bin-args="$(ECARGS)" --report=$(XUNITOUT) $(ECCONF) $(CHECKS)

install:
	$(INSTALL) -m 0755 -d $(DESTDIR)$(LIBDIR)/jasmin/easycrypt
	$(INSTALL) -m 0644 -t $(DESTDIR)$(LIBDIR)/jasmin/easycrypt *.ec

uninstall:
	rm -rf $(DESTDIR)$(LIBDIR)/jasmin
