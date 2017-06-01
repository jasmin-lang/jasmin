#! -*- Makefile -*-

# --------------------------------------------------------------------
DISTDIR := jasmin
UNAME_S := $(shell uname -s)
SED     := sed

ifeq ($(UNAME_S),Darwin)
  SED := gsed
endif

# --------------------------------------------------------------------
.PHONY: all clean dist distcheck

all:
	$(MAKE) -C proofs all
	$(MAKE) -C compiler CIL
	$(MAKE) -C compiler all

clean:
	$(MAKE) -C proofs clean
	$(MAKE) -C compiler clean

dist:
	rm -rf jasmin jasmin.tar.gz
	./scripts/distribution $(DISTDIR) MANIFEST
	rm -rf jasmin/proofs/logic
	$(SED) -i \
	  -e "s/Inria/<Anonymized>/i" \
		-e "s/IMDEA Software Institute/<Anonymized>/i" \
	  -e "s,http://jasmin-lang.github.io/,http://example.com,i" \
	  -e "s,https://github.com/jasmin-lang/jasmin/issues,http://example.com,i" \
	  jasmin/proofs/*/*.v jasmin/compiler/src/*.ml* jasmin/compiler/opam
	$(SED) -i -e "/logic/d" jasmin/proofs/_CoqProject
	tar czf jasmin.tar.gz jasmin && rm -rf jasmin

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
