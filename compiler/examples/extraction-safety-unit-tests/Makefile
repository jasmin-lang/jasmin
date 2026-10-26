ECARGS ?= -I Jasmin:../../../eclib

JASMIN2EC := ../../jasmin2ec

.SUFFIXES: .jazz .ec

SOURCES := $(wildcard *.jazz)
EXTRACTED := $(SOURCES:.jazz=.ec)
# the specifications of the functions with a contract
SPECS := $(SOURCES:.jazz=_specs.ec)

all: proofs.ec $(EXTRACTED) $(SPECS)
	easycrypt runtest $(ECARGS) ec.config $@

clean:
	$(RM) $(EXTRACTED) $(SPECS)

%.ec %_specs.ec: %.jazz $(JASMIN2EC)
	$(JASMIN2EC) --safety --safety-specs $*_specs.ec -o $*.ec $<

.PHONY: all
