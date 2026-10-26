EXTRACTION_DIR ?= extraction
ARRAY_MODEL ?= barray
MODEL ?= normal

JASMIN2EC := ../../../../jasmin2ec --mjazz --array-model=$(ARRAY_MODEL) --model=$(MODEL)
TARGET := $(EXTRACTION_DIR)/Keccak1600_ref_test.ec
OUT = $(if $(EQUIV),--mjazz-equiv -o $(TARGET),--mfile_ec $(EXTRACTION_DIR))

all: $(TARGET)

$(EXTRACTION_DIR):
	mkdir -p $(EXTRACTION_DIR)

$(TARGET): keccak1600_ref_test.jazz $(wildcard *.jinc) | $(EXTRACTION_DIR)
	$(JASMIN2EC) $(OUT) keccak1600_ref_test.jazz

clean:
	$(RM) -rf $(EXTRACTION_DIR)

.PHONY: all clean
