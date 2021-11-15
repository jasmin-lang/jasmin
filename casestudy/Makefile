JASMINC?=../compiler/jasminc
EASYCRYPT?=easycrypt

.SUFFIXES: .jazz .ec .eco

all: modulo_ct.eco modulo_ct_proof.eco copy_mac_ct.eco leakage_models.eco copy_mac_ct_proof_BL_BL.eco copy_mac_ct_proof_BL_CL.eco copy_mac_ct_proof_TV_BL.eco copy_mac_ct_proof_TV_CL.eco

modulo_ct.ec: ../compiler/examples/mod_patch.jazz
	$(JASMINC) -CT -ec verify_mod_const -oec $@ $^

copy_mac_ct.ec: ../compiler/examples/lucky13_split.jazz
	$(JASMINC) -CT -ec ssl3_cbc_copy_mac_BL_BL -ec ssl3_cbc_copy_mac_BL_CL -ec ssl3_cbc_copy_mac_TV_BL -ec ssl3_cbc_copy_mac_TV_CL -oec $@ $^

%.eco: %.ec
	$(EASYCRYPT) $^

clean:
	$(RM) modulo_ct.ec copy_mac_ct.ec *.eco *Array128.ec

check:
	$(JASMINC) --mlk=div32 --dlk=none rotate-mac-cache.jazz
	$(JASMINC) --mlk=div32 --dlk=log  rotate-mac-cache.jazz
