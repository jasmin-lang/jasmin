EXTRACTION_DIR := extraction

JASMIN2EC := ../../../../jasmin2ec --mjazz --mfile_ec $(EXTRACTION_DIR)
SOURCES := $(wildcard *.mjazz)
EXTRACTED := $(SOURCES:.mjazz=.ec)

all: extraction $(EXTRACTED)

extraction:
	mkdir -p $(EXTRACTION_DIR)

%.ec: %.mjazz
	$(JASMIN2EC) $<

clean:
	$(RM) -rf $(EXTRACTION_DIR)

.PHONY: all clean
