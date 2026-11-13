ECLIB ?= ../../../../eclib
ECARGS ?= -I Jasmin:$(ECLIB)
MODELS ?= warray:normal old:normal barray:CT warray:CT

.PHONY: all keccak_build nameres_build sizes_build equiv_build models_build run_test

all: keccak_build nameres_build sizes_build equiv_build models_build run_test

keccak_build:
	$(MAKE) -C keccak

nameres_build:
	$(MAKE) -C nameres

sizes_build:
	$(MAKE) -C sizes

equiv_build:
	for d in keccak nameres sizes; do $(MAKE) -C $$d EXTRACTION_DIR=extraction_equiv EQUIV=1 || exit 1; done

models_build:
	for m in $(MODELS); do \
	  am=$${m%%:*}; mo=$${m##*:}; \
	  $(MAKE) -C keccak EXTRACTION_DIR=extraction_$${am}_$${mo} ARRAY_MODEL=$$am MODEL=$$mo || exit 1; \
	  $(MAKE) -C nameres EXTRACTION_DIR=extraction_$${am}_$${mo} ARRAY_MODEL=$$am MODEL=$$mo || exit 1; \
	  $(MAKE) -C sizes EXTRACTION_DIR=extraction_$${am}_$${mo} ARRAY_MODEL=$$am MODEL=$$mo || exit 1; \
	done

clean:
	$(MAKE) -C keccak clean
	$(MAKE) -C nameres clean
	$(MAKE) -C sizes clean
	for d in keccak nameres sizes; do $(MAKE) -C $$d clean EXTRACTION_DIR=extraction_equiv; done
	for m in $(MODELS); do \
	  d=extraction_$${m%%:*}_$${m##*:}; \
	  $(MAKE) -C keccak clean EXTRACTION_DIR=$$d; \
	  $(MAKE) -C nameres clean EXTRACTION_DIR=$$d; \
	  $(MAKE) -C sizes clean EXTRACTION_DIR=$$d; \
	done

run_test:
	easycrypt runtest $(ECARGS) tests.config mjazz
