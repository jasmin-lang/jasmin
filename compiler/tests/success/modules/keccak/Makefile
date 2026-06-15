EXTRACTION_DIR := extraction

JASMIN2EC := ../../../../jasmin2ec --mjazz --mfile_ec $(EXTRACTION_DIR)
TARGET := $(EXTRACTION_DIR)/Keccak1600_ref_test.ec

all: $(TARGET)

extraction:
	mkdir -p $(EXTRACTION_DIR)

$(TARGET): keccak1600_ref_test.jazz | extraction
	$(JASMIN2EC) keccak1600_ref_test.jazz

clean:
	$(RM) -rf $(EXTRACTION_DIR)

.PHONY: all clean
