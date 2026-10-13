EXTRACTION_DIR ?= extraction
ARRAY_MODEL ?= barray
MODEL ?= normal

JASMIN2EC := ../../../../jasmin2ec --mjazz --array-model=$(ARRAY_MODEL) --model=$(MODEL) --mfile_ec $(EXTRACTION_DIR)
TARGET := $(EXTRACTION_DIR)/Keccak1600_ref_test.ec

all: $(TARGET)

$(EXTRACTION_DIR):
	mkdir -p $(EXTRACTION_DIR)

$(TARGET): keccak1600_ref_test.jazz $(wildcard *.jinc) | $(EXTRACTION_DIR)
	$(JASMIN2EC) keccak1600_ref_test.jazz

clean:
	$(RM) -rf $(EXTRACTION_DIR)

.PHONY: all clean
