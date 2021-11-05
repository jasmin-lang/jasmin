JASMINC?=../compiler/jasminc
EASYCRYPT?=easycrypt

.SUFFIXES: .jazz .ec .eco

all: modulo_ct.eco modulo_ct_proof.eco

modulo_ct.ec: ../compiler/examples/mod_patch.jazz
	$(JASMINC) -CT -ec verify_mod_const -oec $@ $^

%.eco: %.ec
	$(EASYCRYPT) $^

clean:
	$(RM) modulo_ct.ec *.eco
