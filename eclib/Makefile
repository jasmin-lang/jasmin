# -*- Makefile -*-

# --------------------------------------------------------------------
ECCONF   := tests.config 
ECARGS   ?=
CHECKS   ?= jasmin

# --------------------------------------------------------------------
DESTDIR  ?=
PREFIX   ?= /usr/local
LIBDIR   := $(PREFIX)/lib
INSTALL  ?= install

# --------------------------------------------------------------------
.PHONY: default usage check install uninstall clean

default: check

usage:
	@echo "Usage: make <target> where <target> in [check|clean|install|uninstall]" >&2

check:
	easycrypt runtest $(ECARGS) $(ECCONF) $(CHECKS)

jasmin.conf:
	@echo "# DO NOT MODIFY" | tee $@
	@echo "# This file is generated and may be silently overwritten" | tee -a $@
	@echo "[general]" | tee -a $@
	@echo "idirs=Jasmin:$(LIBDIR)/easycrypt/jasmin" | tee -a $@

install: jasmin.conf
	$(INSTALL) -m 0755 -d $(DESTDIR)$(LIBDIR)/easycrypt/jasmin
	$(INSTALL) -m 0644 -t $(DESTDIR)$(LIBDIR)/easycrypt/jasmin *.ec
	$(INSTALL) -m 0755 -d $(DESTDIR)$(LIBDIR)/easycrypt/config
	$(INSTALL) -m 0644 -t $(DESTDIR)$(LIBDIR)/easycrypt/config *.conf

uninstall:
	$(RM) -r $(DESTDIR)$(LIBDIR)/easycrypt/jasmin
	$(RM) $(DESTDIR)$(LIBDIR)/easycrypt/config/jasmin.conf

clean:
	$(RM) *.conf
