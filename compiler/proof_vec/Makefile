# -*- Makefile -*-

# --------------------------------------------------------------------
TOP     := ..
JASMINC := $(TOP)/jasminc.native
FILES   := auth auth-0 auth-1 gimli_ref gimli_ref1 gimliv

# --------------------------------------------------------------------
.PHONY: default clean

# --------------------------------------------------------------------
default: $(FILES:%=%.ec)

clean:
	rm -f $(FILES:%=%.ec)

auth.ec: amd64/auth.jazz
	$(JASMINC) -oec $@ -ec poly1305 $<

auth-0.ec: amd64-0/auth.jazz
	$(JASMINC) -oec $@ -ec poly1305 $<

auth-1.ec: amd64-1/auth.jazz
	$(JASMINC) -oec $@ -ec poly1305 $<

gimli_ref.ec: $(TOP)/examples/gimli/gimli_ref.jazz
	$(JASMINC) -oec $@ -ec gimli_body $<

gimli_ref1.ec: $(TOP)/examples/gimli/gimli_ref1.jazz
	$(JASMINC) -oec $@ -ec gimli_body $<

gimliv.ec: $(TOP)/examples/gimli/gimliv.jazz
	$(JASMINC) -oec $@ -ec gimli_body $<
