# -*- Makefile -*-

# --------------------------------------------------------------------
TOP     := ..
JASMINC := $(TOP)/jasminc.native
FILES   := gimli_ref gimli_ref1 gimliv gimliv1

# --------------------------------------------------------------------
.PHONY: default clean

# --------------------------------------------------------------------
default: $(FILES:%=%.ec)

clean:
	rm -f $(FILES:%=%.ec)

gimli_ref.ec: $(TOP)/examples/gimli/gimli_ref.jazz
	$(JASMINC) -oec $@ -ec gimli_body $<

gimli_ref1.ec: $(TOP)/examples/gimli/gimli_ref1.jazz
	$(JASMINC) -oec $@ -ec gimli_body $<

gimliv.ec: $(TOP)/examples/gimli/gimliv.jazz
	$(JASMINC) -oec $@ -ec gimli_body $<

gimliv1.ec: $(TOP)/examples/gimli/gimliv.jazz
	$(JASMINC) -oec $@ -ec gimli_body1 $<
