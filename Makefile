#! -*- Makefile -*-

# --------------------------------------------------------------------
SED      ?= sed
DISTDIR  := jasmin
PREFIX   ?= /usr/local
# we compute the absolute path, otherwise it does not make sense when
# given to the sub-Makefiles
PREFIX   := $(abspath $(PREFIX))
export PREFIX

# detect the given number of job slots
MAKE_PID := $(shell echo $$PPID)
JOB_FLAG := $(shell ps T | sed -n 's/.*$(MAKE_PID).*$(MAKE).* \(-j\|--jobs=*\) *\([0-9]*\).*/-j\2/p')
JOB_NUM  := $(or $(patsubst -j%,%,$(or $(JOB_FLAG),-j1)),$(shell nproc))
# --------------------------------------------------------------------
.PHONY: all build check clean install uninstall dist distcheck

all: build

build:
	$(MAKE) -C proofs all
	$(MAKE) -C compiler CIL JOB_NUM=$(JOB_NUM)
	$(MAKE) -C compiler all JOB_NUM=$(JOB_NUM)

check:
	$(MAKE) -C eclib check

clean:
	$(MAKE) -C proofs clean
	$(MAKE) -C compiler clean

install:
	$(MAKE) -C compiler install
	$(MAKE) -C eclib install
	$(MAKE) -C proofs install

uninstall:
	$(MAKE) -C compiler uninstall
	$(MAKE) -C eclib uninstall
	$(MAKE) -C proofs uninstall

dist:
	rm -rf jasmin jasmin.tar.gz
	./scripts/distribution $(DISTDIR) MANIFEST
	rm -rf jasmin/proofs/logic
	if [ -x scripts/anonymize ]; then SED=$(SED) scripts/anonymize; fi
	$(SED) -i -e "/logic/d" jasmin/proofs/_CoqProject
	tar -czf jasmin.tar.gz --owner=0 --group=0 jasmin && rm -rf jasmin

distcheck: dist
	tar -xof $(DISTDIR).tar.gz
	set -x; \
	     $(MAKE) -C $(DISTDIR) \
	  && $(MAKE) -C $(DISTDIR) dist \
	  && mkdir $(DISTDIR)/dist1 $(DISTDIR)/dist2 \
	  && ( cd $(DISTDIR)/dist1 && tar -xof ../$(DISTDIR).tar.gz ) \
	  && ( cd $(DISTDIR)/dist2 && tar -xof ../../$(DISTDIR).tar.gz ) \
	  && diff -rq $(DISTDIR)/dist1 $(DISTDIR)/dist2 \
	  || exit 1
	rm -rf $(DISTDIR)
	@echo "$(DISTDIR) is ready for distribution" | \
	  $(SED) -e 1h -e 1s/./=/g -e 1p -e 1x -e '$$p' -e '$$x'
