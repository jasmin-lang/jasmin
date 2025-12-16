ECARGS ?= -I Jasmin:../../../eclib

JASMIN2EC := ../../jasmin2ec

.SUFFIXES: .jazz .ec

SOURCES := $(wildcard *.jazz)
EXTRACTED := $(SOURCES:.jazz=.ec)

all: proofs.ec $(EXTRACTED)
	easycrypt runtest $(ECARGS) ec.config $@

clean:
	$(RM) $(EXTRACTED)

%.ec: %.jazz $(JASMIN2EC)
	$(JASMIN2EC) --model safety -o $@ $<

.PHONY: all
