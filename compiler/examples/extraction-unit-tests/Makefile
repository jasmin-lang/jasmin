ECARGS ?= -I Jasmin:../../../eclib

JASMIN2EC := ../../jasmin2ec

.SUFFIXES: .jazz .ec

all: gcd.ec loops.ec sdiv.ec add_in_mem.ec proofs.ec
	easycrypt runtest $(ECARGS) ec.config $@

clean:
	$(RM) gcd.ec loops.ec sdiv.ec add_in_mem.ec

%.ec: %.jazz $(JASMIN2EC)
	$(JASMIN2EC) -o $@ $<

.PHONY: all
