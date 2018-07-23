# -*- Makefile -*-

# --------------------------------------------------------------------
TOP     := ..
JASMINC := $(TOP)/jasminc.native
GENFILES := \
   gimli_ref \
   gimli_ref1 \
   gimliv1 gimliv \
   gimliv_ct \
   gimliv_safe \
   poly1305_amd64_5x \
   poly1305_amd64_5xPR \
   poly1305_avx_5x \
   poly1305_avx_5xp \
   poly1305_avx_5xp_ct \
   poly1305_avx_5xp_safe \
   poly1305_amd64_5x_ct \
   poly1305_amd64_5x_safe \
   chacha20_hacl          \
   chacha20_hacl_x2       \
   chacha20_s_avx2        \
   chacha20_avx2          \
   chacha20_avx2_ct       \
   chacha20_avx2_safe     \
   chacha20_avx2_1        \
   chacha20_avx2_1_ct     \
   chacha20_avx2_1_safe   


ECFILES := \
   jasmin_utils \
   jasmin_array \
   jasmin_word  \
   jasmin_memory \
   jasmin_model \
   \
   gimliv_ct_proof \
   gimliv_safe_proof \
   equiv_gimli \
   \
   poly1305_avx_5xp_ct_proof \
   poly1305_avx_5xp_safe_proof \
   equiv_poly1305_avx \
   \
   equiv_chacha20 \
   chacha20_avx2_ct_proof \
   chacha20_avx2_1_ct_proof

#   chacha20_avx2_safe_proof \
#   chacha20_avx2_1_safe_proof


#   poly1305_amd64_5x_ct_proof \
#   poly1305_amd64_5xp_safe_proof \
 

FILES := $(GENFILES) $(ECFILES)

POLY1305 := $(HOME)/gitolite/crypto/src/crypto_onetimeauth/poly1305/jazz
CHACHA20 := $(HOME)/gitolite/crypto/src/crypto_stream/chacha20/jazz
# --------------------------------------------------------------------
.PHONY: default check clean

# --------------------------------------------------------------------
default: $(GENFILES:%=%.ec)

check: $(FILES:%=%.ec.check)

clean:
	rm -f $(GENFILES:%=%.ec) $(FILES:%=%.ec.check) *~

# --------------------------------------------------------------------

gimli_ref.ec: $(TOP)/examples/gimli/gimli_ref.jazz $(JASMINC)
	$(JASMINC) -oec $@ -ec gimli $<

gimli_ref1.ec: $(TOP)/examples/gimli/gimli_ref1.jazz $(JASMINC)
	$(JASMINC) -oec $@ -ec gimli $<

gimliv1.ec: $(TOP)/examples/gimli/gimliv.jazz $(JASMINC)
	$(JASMINC) -oec $@ -ec gimli1 $<

gimliv.ec: $(TOP)/examples/gimli/gimliv.jazz $(JASMINC)
	$(JASMINC) -oec $@ -ec gimli $<

gimliv_ct.ec: $(TOP)/examples/gimli/gimliv.jazz $(JASMINC)
	$(JASMINC) -oec $@ -ec gimli -CT $<

gimliv_safe.ec: $(TOP)/examples/gimli/gimliv.jazz $(JASMINC)
	$(JASMINC) -oec $@ -ec gimli -safety $<

poly1305_amd64_5x.ec: $(POLY1305)/ref-5xpv/auth.jazz $(JASMINC)
	$(JASMINC) -oec $@ -ec poly1305 $<

poly1305_amd64_5xPR.ec: $(POLY1305)/ref-5xpv/auth_for_proof.jazz $(JASMINC)
	$(JASMINC) -oec $@ -ec poly1305 $<

poly1305_avx_5x.ec: $(POLY1305)/avx-5x/auth.jazz $(JASMINC)
	$(JASMINC) -oec $@ -ec poly1305 $<

poly1305_avx_5xp.ec: $(POLY1305)/avx-5xp/auth.jazz $(JASMINC)
	$(JASMINC) -oec $@ -ec poly1305 $<

poly1305_avx_5xp_ct.ec: $(POLY1305)/avx-5xp/auth.jazz $(JASMINC)
	$(JASMINC) -oec $@ -ec poly1305 -CT $<

poly1305_avx_5xp_safe.ec: $(POLY1305)/avx-5xp/auth.jazz $(JASMINC)
	$(JASMINC) -oec $@ -ec poly1305 -safety $<

poly1305_amd64_5x_ct.ec: $(POLY1305)/ref-5xpv/auth.jazz $(JASMINC)
	$(JASMINC) -oec $@ -ec poly1305 -CT $<

poly1305_amd64_5x_safe.ec: $(POLY1305)/ref-5xpv/auth.jazz $(JASMINC)
	$(JASMINC) -oec $@ -ec poly1305 -safety $<

chacha20_hacl.ec: $(CHACHA20)/hacl/chacha20.jazz $(JASMINC)
	$(JASMINC) -oec $@ -ec hacl_2rounds $<

chacha20_hacl_x2.ec: $(CHACHA20)/hacl/chacha20_x2.jazz $(JASMINC)
	$(JASMINC) -oec $@ -ec hacl_2rounds $<

chacha20_s_avx2.ec: $(CHACHA20)/s-avx2/chacha20.jazz $(JASMINC)
	$(JASMINC) -oec $@ -ec avx2_2rounds $<

chacha20_avx2.ec: $(CHACHA20)/avx2/chacha.jazz $(JASMINC)
	$(JASMINC) -oec $@ -ec chacha $<

chacha20_avx2_ct.ec: $(CHACHA20)/avx2/chacha.jazz $(JASMINC)
	$(JASMINC) -oec $@ -ec chacha -CT $<

chacha20_avx2_safe.ec: $(CHACHA20)/avx2/chacha.jazz $(JASMINC)
	$(JASMINC) -oec $@ -ec chacha -safety $<

chacha20_avx2_1.ec: $(CHACHA20)/avx2-1/chacha.jazz $(JASMINC)
	$(JASMINC) -oec $@ -ec chacha $<

chacha20_avx2_1_ct.ec: $(CHACHA20)/avx2-1/chacha.jazz $(JASMINC)
	$(JASMINC) -oec $@ -ec chacha -CT $<

chacha20_avx2_1_safe.ec: $(CHACHA20)/avx2-1/chacha.jazz $(JASMINC)
	$(JASMINC) -oec $@ -ec chacha -safety $<



%.ec: $(JASMINC)

%.ec.check: %.ec
	easycrypt $< && touch $@
