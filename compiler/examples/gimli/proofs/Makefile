ECARGS ?=

JASMINC := ../../../jasminc

.SUFFIXES: .jazz .ec

all: gimli_arm.ec gimli_x86.ec
	easycrypt runtest $(ECARGS) ec.config $@

gimli_arm.ec: ../arm-m4/gimli.jazz
	$(JASMINC) -arch arm-m4 -oec $@ $^

gimli_x86.ec: ../x86-64/gimli.jazz
	$(JASMINC) -arch x86-64 -oec $@ $^
