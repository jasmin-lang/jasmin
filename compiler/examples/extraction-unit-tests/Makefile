ECARGS ?= -I Jasmin:../../../eclib

JASMIN2EC := ../../jasmin2ec

.SUFFIXES: .jazz .ec

SOURCES := $(wildcard *.jazz)
EXTRACTED := $(SOURCES:.jazz=.ec)

all: proofs.ec $(EXTRACTED)
	easycrypt runtest $(ECARGS) ec.config $@

clean:
	$(RM) $(EXTRACTED)

globals_unsigned.ec: JASMIN2ECFLAGS = --global-model sign=unsigned

%.ec: %.jazz $(JASMIN2EC)
	$(JASMIN2EC) $(JASMIN2ECFLAGS) -o $@ $<

.PHONY: all
