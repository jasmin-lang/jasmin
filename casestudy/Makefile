JASMINC?=../compiler/jasminc
EASYCRYPT?=easycrypt

.SUFFIXES: .jazz .ec .eco

all: modulo_ct.eco modulo_ct_proof.eco copy_mac_ct.eco leakage_models.eco copy_mac_ct_proof_BL_BL_CL.eco copy_mac_ct_proof_BL_BL_BL.eco copy_mac_ct_proof_BL_CL_CL.eco copy_mac_ct_proof_TV_CL_CL.eco copy_mac_ct_proof_TV_CL_TV_CL.eco copy_mac_ct_proof_TV_BL_CL.eco copy_mac_ct_proof_TV_BL_BL.eco copy_mac_ct_proof_TV_BL_TV_CL.eco copy_mac_ct_proof_TV_BL_TV.eco copy_mac_ct_proof_TV_CL32.eco check

modulo_ct.ec: ../compiler/examples/mod_patch.jazz
	$(JASMINC) -CT -ec mod_TV -oec $@ $^

copy_mac_ct.ec: ../compiler/examples/lucky13_split.jazz
	$(JASMINC) -CT -ec ssl3_cbc_copy_mac_BL_BL -ec ssl3_cbc_copy_mac_BL_CL -ec ssl3_cbc_copy_mac_TV_BL -ec ssl3_cbc_copy_mac_TV_CL -ec ssl3_cbc_copy_mac_BL_CL32 -ec ssl3_cbc_copy_mac_TV_CL32 -oec $@ $^

chacha20_ref_ct.ec: chacha20/chacha20_ref/chacha20_ref.jazz
	$(JASMINC) -CT -ec chacha20_ref -oec chacha20/chacha20_ref/$@ $^

chacha20_avx_ct.ec: chacha20/chacha20_avx/chacha20_avx.jazz
	$(JASMINC) -CT -ec chacha20_avx -oec chacha20/chacha20_avx/$@ $^

chacha20_avx2_ct.ec: chacha20/chacha20_avx2/chacha20_avx2.jazz
	$(JASMINC) -CT -ec chacha20_avx2 -oec chacha20/chacha20_avx2/$@ $^

keccak1600_ref_ct.ec: keccak1600/keccak1600_ref/keccak1600_ref.jazz
	$(JASMINC) -CT -ec keccak1600_ref -oec keccak1600/keccak1600_ref/$@ $^

keccak1600_avx_ct.ec: keccak1600/keccak1600_avx/keccak1600_avx.jazz
	$(JASMINC) -CT -ec keccak1600_avx -oec keccak1600/keccak1600_avx/$@ $^

keccak1600_scalar_ct.ec: keccak1600/keccak1600_scalar/keccak1600_scalar.jazz
	$(JASMINC) -CT -ec keccak1600_scalar -oec keccak1600/keccak1600_scalar/$@ $^

poly1305_ref_ct.ec: poly1305/poly1305_ref/poly1305_ref.jazz
	$(JASMINC) -CT -ec poly1305_ref -oec poly1305/poly1305_ref/$@ $^

poly1305_avx_ct.ec: poly1305/poly1305_avx/poly1305_avx.jazz
	$(JASMINC) -CT -ec poly1305_avx -oec poly1305/poly1305_avx/$@ $^

poly1305_avx2_ct.ec: poly1305/poly1305_avx2/poly1305_avx2.jazz
	$(JASMINC) -CT -ec poly1305_avx2 -oec poly1305/poly1305_avx2/$@ $^

%.eco: %.ec
	$(EASYCRYPT) $^

clean:
	$(RM) modulo_ct.ec copy_mac_ct.ec *.eco *Array*.ec

check:
	$(JASMINC) 	-dlk=none	-mlk=div32	rotate_mac_CL_in_32CL.jazz
	$(JASMINC) 	-dlk=log  	-mlk=div32	rotate_mac_CL_in_32CL.jazz
	$(JASMINC) 	-dlk=log 	-mlk=full	rotate_offset_BL_in_TV_model.jazz
	$(JASMINC) 	-dlk=log 	-mlk=full	rotate_mac_CL_in_BL_model.jazz
	$(JASMINC) 	-dlk=none 	-mlk=full	ssl3_cbc_copy_mac_BL_CL_in_BL.jazz
	$(JASMINC) 	-dlk=log 	-mlk=div64	ssl3_cbc_copy_mac_BL_CL_in_TV_CL.jazz
	$(JASMINC) 	-dlk=log 	-mlk=full	ssl3_cbc_copy_mac_BL_CL_in_TV.jazz
	$(JASMINC) 	-dlk=log 	-mlk=full	ssl3_cbc_copy_mac_BL_BL_in_TV.jazz
	$(JASMINC) 	-dlk=log 	-mlk=div64	ssl3_cbc_copy_mac_BL_BL_in_TV_CL.jazz
	$(JASMINC) 	-dlk=none 	-mlk=full	ssl3_cbc_copy_mac_TV_CL_in_BL.jazz
	$(JASMINC) 	-dlk=log 	-mlk=full	ssl3_cbc_copy_mac_TV_CL_in_TV.jazz
