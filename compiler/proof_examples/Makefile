# -*- Makefile -*-

# --------------------------------------------------------------------
TOP := $(shell dirname $(realpath $(lastword $(MAKEFILE_LIST))/..))

JASMINC  ?= $(TOP)/jasminc

GENFILES := \
   gimli_ref \
   gimli_ref1 \
   gimliv1 gimliv \
   gimliv_ct

ECFILES := \
   gimliv_ct_proof \
   equiv_gimli

ECLIBS := $(wildcard $(TOP)/eclib/*.ec)

FILES := $(GENFILES) $(ECFILES)

# --------------------------------------------------------------------
.PHONY: default check clean

# --------------------------------------------------------------------
default: $(GENFILES:%=%.ec)

check: $(FILES:%=%.ec.check)

clean:
	rm -f $(GENFILES:%=%.ec) $(FILES:%=%.ec.check) *~

# --------------------------------------------------------------------
%.ec: $(JASMINC)

%.ec.check: %.ec $(ECLIBS)
	easycrypt -I Jasmin:$(TOP)/eclib $< && touch $@

# --------------------------------------------------------------------
gimli_ref.ec: gimli_ref.jazz $(JASMINC)
	$(JASMINC) -oec $@ -ec gimli $<

gimli_ref1.ec: gimli_ref1.jazz $(JASMINC)
	$(JASMINC) -oec $@ -ec gimli $<

gimliv1.ec: $(TOP)/examples/gimli/gimliv.jazz $(JASMINC)
	$(JASMINC) -oec $@ -ec gimli1 $<

gimliv.ec: $(TOP)/examples/gimli/gimliv.jazz $(JASMINC)
	$(JASMINC) -oec $@ -ec gimli $<

gimliv_ct.ec: $(TOP)/examples/gimli/gimliv.jazz $(JASMINC)
	$(JASMINC) -oec $@ -ec gimli -CT $<

gimliv_safe.ec: $(TOP)/examples/gimli/gimliv.jazz $(JASMINC)
	$(JASMINC) -oec $@ -ec gimli -safety $<
