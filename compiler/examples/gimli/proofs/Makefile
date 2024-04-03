ECARGS ?=

JASMINC := ../../../jasminc

.SUFFIXES: .jazz .ec

all: gimli_arm.ec gimli_x86.ec gimli_x86_ct.ec gimli_arm_ct.ec gimli_avx.ec gimli_avx_ct.ec
	easycrypt runtest $(ECARGS) ec.config $@

gimli_arm.ec: ../arm-m4/gimli.jazz
	$(JASMINC) -arch arm-m4 -oec $@ $^

gimli_arm_ct.ec: ../arm-m4/gimli.jazz
	$(JASMINC) -arch arm-m4 -CT -oec $@ $^

gimli_x86.ec: ../x86-64/gimli.jazz
	$(JASMINC) -arch x86-64 -oec $@ $^

gimli_x86_ct.ec: ../x86-64/gimli.jazz
	$(JASMINC) -arch x86-64 -CT -oec $@ $^

gimli_avx.ec: ../x86-64/gimliv.jazz ../x86-64/gimliv.jinc
	$(JASMINC) -arch x86-64 -oec $@ $<

gimli_avx_ct.ec: ../x86-64/gimliv.jazz ../x86-64/gimliv.jinc
	$(JASMINC) -arch x86-64 -CT -oec $@ $<
