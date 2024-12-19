ECARGS ?= -I Jasmin:../../../../eclib

JASMIN2EC := ../../../jasmin2ec

CT_MODE ?= CT
GIMLI_CT = gimli_$(shell echo $(CT_MODE) | tr A-Z a-z).ec

.SUFFIXES: .jazz .ec

all: ct gimli_arm.ec gimli_x86.ec gimli_x86_ct.ec gimli_arm_ct.ec gimli_avx.ec gimli_avx_ct.ec
	easycrypt runtest $(ECARGS) ec.config $@

ct: $(GIMLI_CT) gimli_x86_ct.ec gimli_arm_ct.ec gimli_avx_ct.ec
	easycrypt $(ECARGS) $<

gimli_arm.ec: ../arm-m4/gimli.jazz
	$(JASMIN2EC) --arch=arm-m4 -o $@ $^

gimli_arm_ct.ec: ../arm-m4/gimli.jazz
	$(JASMIN2EC) --arch=arm-m4 --model=$(CT_MODE) -o $@ $^

gimli_x86.ec: ../x86-64/gimli.jazz
	$(JASMIN2EC) --arch=x86-64 -o $@ $^

gimli_x86_ct.ec: ../x86-64/gimli.jazz
	$(JASMIN2EC) --arch=x86-64 --model=$(CT_MODE) -o $@ $^

gimli_avx.ec: ../x86-64/gimliv.jazz ../x86-64/gimliv.jinc
	$(JASMIN2EC) --arch=x86-64 -o $@ $<

gimli_avx_ct.ec: ../x86-64/gimliv.jazz ../x86-64/gimliv.jinc
	$(JASMIN2EC) --arch=x86-64 --model=$(CT_MODE) -o $@ $<

.PHONY: all ct
