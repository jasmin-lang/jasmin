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
.PHONY: default usage check check-xunit

default: check

usage:
	@echo "Usage: make <target> where <target> in [check|check-xunit]" >&2

check:
	$(ECCHECK) --bin-args="$(ECARGS)" $(ECCONF) $(CHECKS)

check-xunit:
	$(ECCHECK) --bin-args="$(ECARGS)" --report=$(XUNITOUT) $(ECCONF) $(CHECKS)
