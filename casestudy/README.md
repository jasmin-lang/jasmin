# Secure implementation of 64-bit modulo

Implementation is in `../compiler/examples/mod_patch.jazz`

Security proof (constant-time in a model in which 64-bit division/modulo leaks the size of the dividend and the value of the divisor) in `modulo_ct_proof.ec`, lemma `l2`.
It assumes that the divisor (second argument) is public and non-zero.

# Secure MEE-TLS-CBC MAC extraction

Implementation is in `../compiler/examples/lucky13_split.jazz`.

Security proof in `copy_mac_ct_proof.ec`, lemma `l_final`.
Constant-time security under the assumption that 32-bit division/modulo instruction leaks the size of the dividend and the value of the divisor.
It assumes TODO
