JASMINC?=../compiler/jasminc
EASYCRYPT?=easycrypt
FIND?=find

.SUFFIXES: .jazz .ec .eco

all: modulo_ct.eco modulo_ct_proof.eco copy_mac_ct.eco \
	copy_mac_ct_proof_BL_BL_CL32.eco copy_mac_ct_proof_BL_BL_CL64.eco copy_mac_ct_proof_BL_BL_BL.eco copy_mac_ct_proof_BL_CL64_CL64.eco \
	copy_mac_ct_proof_TV_CL64_CL64.eco copy_mac_ct_proof_TV_CL64_TV_CL64.eco copy_mac_ct_proof_TV_BL_CL64.eco \
	copy_mac_ct_proof_TV_BL_BL.eco copy_mac_ct_proof_TV_BL_TV_CL64.eco copy_mac_ct_proof_TV_BL_TV.eco \
	copy_mac_ct_proof_TV_CL32.eco chacha20/chacha20_ref/chacha20_ref_proof_BL_BL.eco \
	chacha20/chacha20_ref/chacha20_ref_proof_BL_CL32.eco chacha20/chacha20_ref/chacha20_ref_proof_BL_CL64.eco \
	chacha20/chacha20_ref/chacha20_ref_proof_TV_BL.eco chacha20/chacha20_ref/chacha20_ref_proof_TV_CL32.eco \
	chacha20/chacha20_ref/chacha20_ref_proof_TV_CL64.eco chacha20/chacha20_avx/chacha20_avx_proof_BL_BL.eco \
	chacha20/chacha20_avx/chacha20_avx_proof_BL_CL32.eco chacha20/chacha20_avx/chacha20_avx_proof_BL_CL64.eco \
	chacha20/chacha20_avx/chacha20_avx_proof_TV_BL.eco chacha20/chacha20_avx/chacha20_avx_proof_TV_CL32.eco \
	chacha20/chacha20_avx/chacha20_avx_proof_TV_CL64.eco chacha20/chacha20_avx2/chacha20_avx2_proof_BL_BL.eco \
	chacha20/chacha20_avx2/chacha20_avx2_proof_BL_CL32.eco chacha20/chacha20_avx2/chacha20_avx2_proof_BL_CL64.eco \
	chacha20/chacha20_avx2/chacha20_avx2_proof_TV_BL.eco chacha20/chacha20_avx2/chacha20_avx2_proof_TV_CL32.eco \
	chacha20/chacha20_avx2/chacha20_avx2_proof_TV_CL64.eco keccak1600/keccak1600_ref/keccak1600_ref_proof_BL_BL.eco \
	keccak1600/keccak1600_ref/keccak1600_ref_proof_BL_CL32.eco keccak1600/keccak1600_ref/keccak1600_ref_proof_BL_CL64.eco \
	keccak1600/keccak1600_ref/keccak1600_ref_proof_TV_BL.eco keccak1600/keccak1600_ref/keccak1600_ref_proof_TV_CL32.eco \
	keccak1600/keccak1600_ref/keccak1600_ref_proof_TV_CL64.eco keccak1600/keccak1600_scalar/keccak1600_scalar_proof_BL_BL.eco \
	keccak1600/keccak1600_scalar/keccak1600_scalar_proof_BL_CL32.eco keccak1600/keccak1600_scalar/keccak1600_scalar_proof_BL_CL64.eco \
	keccak1600/keccak1600_scalar/keccak1600_scalar_proof_TV_BL.eco keccak1600/keccak1600_scalar/keccak1600_scalar_proof_TV_CL32.eco \
	keccak1600/keccak1600_scalar/keccak1600_scalar_proof_TV_CL64.eco openSSL/pmac_verify_hmac/pmac_verify_hmac_proof_BL_CL32.eco \
	openSSL/pmac_verify_hmac/pmac_verify_hmac_proof_BL_CL64.eco poly1305/poly1305_ref/poly1305_ref_proof_BL_BL.eco \
	poly1305/poly1305_ref/poly1305_ref_proof_BL_CL32.eco poly1305/poly1305_ref/poly1305_ref_proof_BL_CL64.eco \
	poly1305/poly1305_ref/poly1305_ref_proof_TV_BL.eco poly1305/poly1305_ref/poly1305_ref_proof_TV_CL32.eco \
	poly1305/poly1305_ref/poly1305_ref_proof_TV_CL64.eco poly1305/poly1305_avx/poly1305_avx_proof_BL_BL.eco \
	poly1305/poly1305_avx/poly1305_avx_proof_BL_CL32.eco poly1305/poly1305_avx/poly1305_avx_proof_BL_CL64.eco \
	poly1305/poly1305_avx/poly1305_avx_proof_TV_BL.eco poly1305/poly1305_avx/poly1305_avx_proof_TV_CL32.eco \
	poly1305/poly1305_avx/poly1305_avx_proof_TV_CL64.eco poly1305/poly1305_avx2/poly1305_avx2_proof_BL_BL.eco \
	poly1305/poly1305_avx2/poly1305_avx2_proof_BL_CL32.eco poly1305/poly1305_avx2/poly1305_avx2_proof_BL_CL64.eco \
	poly1305/poly1305_avx2/poly1305_avx2_proof_TV_BL.eco poly1305/poly1305_avx2/poly1305_avx2_proof_TV_CL32.eco \
	poly1305/poly1305_avx2/poly1305_avx2_proof_TV_CL64.eco wolfSSL/coding_wolfSSL_proof_BL_CL64.eco check

modulo_ct.ec: ../compiler/examples/mod_patch.jazz
	$(JASMINC) -CT -ec mod_TV -oec $@ $^

copy_mac_ct.ec: ../compiler/examples/lucky13_split.jazz
	$(JASMINC) -CT -ec ssl3_cbc_copy_mac_BL_BL -ec ssl3_cbc_copy_mac_BL_CL \
		-ec ssl3_cbc_copy_mac_TV_BL -ec ssl3_cbc_copy_mac_TV_CL -ec ssl3_cbc_copy_mac_BL_CL32 \
		-ec ssl3_cbc_copy_mac_TV_CL32 -oec $@ $^

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

coding_wolfSSL_ct.ec: wolfSSL/coding_wolfSSL.jazz
	$(JASMINC) -CT -ec Base64_Char2Val_jazz -oec wolfSSL/$@ $^

pmac_verify_hmac_ct.ec: openSSL/pmac_verify_hmac/pmac_verify_hmac.jazz
	$(JASMINC) -CT -ec verify_hmac_jazz -oec openSSL/pmac_verify_hmac/$@ $^

%.eco: %.ec
	$(EASYCRYPT) $^

clean:
	$(FIND) . -name \*.eco -type f -delete

check:
	$(JASMINC) 	-dlk=none	-mlk=div32	counter_examples/rotate_mac_CL_in_32CL.jazz; echo ""
	$(JASMINC) 	-dlk=log  	-mlk=div32	counter_examples/rotate_mac_CL_in_32CL.jazz; echo ""
	$(JASMINC) 	-dlk=log 	-mlk=full	counter_examples/rotate_offset_BL_in_TV_model.jazz; echo ""
	$(JASMINC) 	-dlk=log 	-mlk=full	counter_examples/rotate_mac_CL_in_BL_model.jazz; echo ""
	$(JASMINC) 	-dlk=none 	-mlk=full	counter_examples/ssl3_cbc_copy_mac_BL_CL64_in_BL.jazz; echo ""
	$(JASMINC) 	-dlk=log 	-mlk=div64	counter_examples/ssl3_cbc_copy_mac_BL_CL64_in_TV_CL64.jazz; echo ""
	$(JASMINC) 	-dlk=log 	-mlk=full	counter_examples/ssl3_cbc_copy_mac_BL_CL64_in_TV.jazz; echo ""
	$(JASMINC) 	-dlk=log 	-mlk=full	counter_examples/ssl3_cbc_copy_mac_BL_BL_in_TV.jazz; echo ""
	$(JASMINC) 	-dlk=log 	-mlk=div64	counter_examples/ssl3_cbc_copy_mac_BL_BL_in_TV_CL64.jazz; echo ""
	$(JASMINC) 	-dlk=none 	-mlk=full	counter_examples/ssl3_cbc_copy_mac_TV_CL64_in_BL.jazz; echo ""
	$(JASMINC) 	-dlk=log 	-mlk=full	counter_examples/ssl3_cbc_copy_mac_TV_CL64_in_TV.jazz; echo ""
