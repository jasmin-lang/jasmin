# Secure implementation of 64-bit modulo

Implementation is in `../compiler/examples/mod_patch.jazz`

Security proof (constant-time in a model in which 64-bit division/modulo leaks the size of the dividend and the value of the divisor) in `modulo_ct_proof.ec`, lemma `l2`.
It assumes that the divisor (second argument) is public and non-zero.

# Secure MEE-TLS-CBC MAC extraction (TV model)

Implementation is in `../compiler/examples/lucky13_split.jazz`, function `ssl3_cbc_copy_mac_jasmin`.

Security proof in `copy_mac_ct_proof.ec`, lemma `l_final`.
Constant-time security under the assumption that 32-bit division/modulo instruction leaks the size of the dividend and the value of the divisor (see the `LeakageModelTV` theory at the beginning of the file).
It assumes that the size of the MAC (`md_size`), the length of the data (`orig_len`), and the `out` and `rec` pointers are public.
It also assumes that the records (pointed to by the `rec` arguments) are well-formed and contain at offset 16 a public pointer (to the data).

# Secure MEE-TLS-CBC MAC extraction (CL model)

Implementation is in `../compiler/examples/lucky13_split.jazz`, function `ssl3_cbc_copy_mac_jasmin_cache`.

Security proof in `copy_mac_cache_ct_proof.ec`, lemma `l_final`.
Constant-time security under the assumption that memory accesses leak the 64-octet cache line (see the `LeakageModelCL` theory at the beginning of the file).
In addition to the hypothesis that are also needed in the TV model (see above),
this lemma requires that the `rotated_mac` argument is public and properly aligned with a cache-line boundary.
