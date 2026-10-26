EXTRACTION_DIR ?= extraction
ARRAY_MODEL ?= barray
MODEL ?= normal

JASMIN2EC := ../../../../jasmin2ec --mjazz -I Lib=. --array-model=$(ARRAY_MODEL) --model=$(MODEL)
SOURCES := $(wildcard *.mjazz)
EXTRACTED := $(SOURCES:.mjazz=.ec)
OUT = $(if $(EQUIV),--mjazz-equiv -o $(EXTRACTION_DIR)/$*.ec,--mfile_ec $(EXTRACTION_DIR))

all: $(EXTRACTION_DIR) $(EXTRACTED)

$(EXTRACTION_DIR):
	mkdir -p $(EXTRACTION_DIR)

%.ec: %.mjazz
	$(JASMIN2EC) $(OUT) $<

clean:
	$(RM) -rf $(EXTRACTION_DIR)

.PHONY: all clean
