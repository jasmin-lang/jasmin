JASMINC?=../compiler/jasminc
EASYCRYPT?=easycrypt

.SUFFIXES: .jazz .ec .eco

all: modulo_ct.eco modulo_ct_proof.eco copy_mac_ct.eco leakage_models.eco copy_mac_ct_proof_BL_BL.eco copy_mac_ct_proof_BL_CL.eco copy_mac_ct_proof_TV_BL.eco copy_mac_ct_proof_TV_CL.eco copy_mac_ct_proof_TV_CL32.eco check

modulo_ct.ec: ../compiler/examples/mod_patch.jazz
	$(JASMINC) -CT -ec mod_TV -oec $@ $^

copy_mac_ct.ec: ../compiler/examples/lucky13_split.jazz
	$(JASMINC) -CT -ec ssl3_cbc_copy_mac_BL_BL -ec ssl3_cbc_copy_mac_BL_CL -ec ssl3_cbc_copy_mac_TV_BL -ec ssl3_cbc_copy_mac_TV_CL -ec ssl3_cbc_copy_mac_TV_CL32 -oec $@ $^

%.eco: %.ec
	$(EASYCRYPT) $^

clean:
	$(RM) modulo_ct.ec copy_mac_ct.ec *.eco *Array128.ec

check:
	$(JASMINC) 	--dlk=none	--mlk=div32	rotate-mac-cache.jazz
	$(JASMINC) 	--dlk=log  	--mlk=div32	rotate-mac-cache.jazz
	$(JASMINC) 	--dlk=none 	--mlk=full 	BLBL_TVBL.jazz
	$(JASMINC) 	--dlk=log  	--mlk=full 	BLBL_TVBL.jazz
	$(JASMINC) 	--dlk=log  	--mlk=full	BLBL_BLCL.jazz
	$(JASMINC) 	--dlk=log	--mlk=div64	BLBL_BLCL.jazz
