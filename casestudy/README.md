# Secure implementation of 64-bit modulo

Implementation is in `../compiler/examples/mod_patch.jazz`

Security proof (constant-time in a model in which division/modulo leaks the size of the dividend and the value of the modulus) in `modulo_ct_proof.ec`, lemma `l2`.
It assumes that the modulus (second argument) is public and non-zero.
