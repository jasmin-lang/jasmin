JASMINC?=../compiler/jasminc
EASYCRYPT?=easycrypt

.SUFFIXES: .jazz .ec .eco

all: modulo_ct.eco modulo_ct_proof.eco copy_mac_ct.eco leakage_models.eco copy_mac_ct_proof_BL_BL_CL.eco copy_mac_ct_proof_BL_BL_BL.eco copy_mac_ct_proof_BL_CL_CL.eco copy_mac_ct_proof_TV_CL_CL.eco copy_mac_ct_proof_TV_CL_TV_CL.eco copy_mac_ct_proof_TV_BL_CL.eco copy_mac_ct_proof_TV_BL_BL.eco copy_mac_ct_proof_TV_BL_TV_CL.eco copy_mac_ct_proof_TV_BL_TV.eco copy_mac_ct_proof_TV_CL32.eco check

modulo_ct.ec: ../compiler/examples/mod_patch.jazz
	$(JASMINC) -CT -ec mod_TV -oec $@ $^

copy_mac_ct.ec: ../compiler/examples/lucky13_split.jazz
	$(JASMINC) -CT -ec ssl3_cbc_copy_mac_BL_BL -ec ssl3_cbc_copy_mac_BL_CL -ec ssl3_cbc_copy_mac_TV_BL -ec ssl3_cbc_copy_mac_TV_CL -ec ssl3_cbc_copy_mac_TV_CL32 -ec ssl3_cbc_copy_mac_TVG_BL -ec ssl3_cbc_copy_mac_TVG_CL -oec $@ $^

%.eco: %.ec
	$(EASYCRYPT) $^

clean:
	$(RM) modulo_ct.ec copy_mac_ct.ec *.eco *Array64.ec

check:
	$(JASMINC) 	--dlk=none	--mlk=div32	rotate_mac_CL_in_32CL.jazz
	$(JASMINC) 	--dlk=log  	--mlk=div32	rotate_mac_CL_in_32CL.jazz
	$(JASMINC) 	--dlk=log 	--mlk=full	rotate_offset_BL_in_TV_model.jazz
	$(JASMINC) 	--dlk=log 	--mlk=full	rotate_mac_CL_in_BL_model.jazz
	$(JASMINC) 	--dlk=none 	--mlk=full	ssl3_cbc_copy_mac_BL_CL_in_BL.jazz
	$(JASMINC) 	--dlk=log 	--mlk=div64	ssl3_cbc_copy_mac_BL_CL_in_TV_CL.jazz
	$(JASMINC) 	--dlk=log 	--mlk=full	ssl3_cbc_copy_mac_BL_CL_in_TV.jazz
	$(JASMINC) 	--dlk=log 	--mlk=full	ssl3_cbc_copy_mac_BL_BL_in_TV.jazz
	$(JASMINC) 	--dlk=log 	--mlk=div64	ssl3_cbc_copy_mac_BL_BL_in_TV_CL.jazz
	$(JASMINC) 	--dlk=none 	--mlk=full	ssl3_cbc_copy_mac_TV_CL_in_BL.jazz
	$(JASMINC) 	--dlk=log 	--mlk=full	ssl3_cbc_copy_mac_TV_CL_in_TV.jazz
	$(JASMINC) 	--dlk=none 	--mlk=full	ssl3_cbc_copy_mac_TVG_CL_in_BL.jazz
	$(JASMINC) 	--dlk=log 	--mlk=full	ssl3_cbc_copy_mac_TVG_CL_in_TV.jazz
