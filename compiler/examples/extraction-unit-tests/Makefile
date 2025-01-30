ECARGS ?= -I Jasmin:../../../eclib

JASMIN2EC := ../../jasmin2ec

.SUFFIXES: .jazz .ec

all: loops.ec proofs.ec
	easycrypt runtest $(ECARGS) ec.config $@

clean:
	$(RM) loops.ec

%.ec: %.jazz
	$(JASMIN2EC) -o $@ $^

.PHONY: all
