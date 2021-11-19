# Secure implementation of 64-bit modulo

Implementation is in `../compiler/examples/mod_patch.jazz`

Security proof (constant-time in a model in which 64-bit division/modulo leaks the size of the dividend and the value of the divisor) in `modulo_ct_proof.ec`, lemma `l2`.
It assumes that the divisor (second argument) is public and non-zero.

# Secure MEE-TLS-CBC MAC extraction (BL model)

Implementation is in `../compiler/examples/lucky13_split.jazz`, function `ssl3_cbc_copy_mac_BL_BL`.

Security proof in `copy_mac_ct_proof.ec`, lemma `l_final`.
Constant-time security under the assumption that 32-bit division/modulo instruction leaks nothing about its operands (see the `LeakageModelBL` theory in the `leakage_models.ec` file).
It assumes that the size of the MAC (`md_size`), the length of the data (`orig_len`), and the `out` and `rec` pointers are public.
It also assumes that the records (pointed to by the `rec` arguments) are well-formed and contain at offset 16 a public pointer (to the data).

- `copy_mac_ct_proof_BL_BL_BL.ec` contains proof that implementation `ssl3_cbc_copy_mac_BL_BL` is constant-time in `BL` model.
- `copy_mac_ct_proof_BL_BL_CL.ec` contains proof that implementation `ssl3_cbc_copy_mac_BL_BL` is constant-time in `CL` model.
- `copy_mac_ct_proof_BL_BL_TV.ec` contains proof that implementation `ssl3_cbc_copy_mac_BL_BL` is constant-time in `TV` model.

# Secure MEE-TLS-CBC MAC extraction (TV model)

Implementation is in `../compiler/examples/lucky13_split.jazz`, function `ssl3_cbc_copy_mac_TV_BL`.

Security proof in `copy_mac_ct_proof.ec`, lemma `l_final`.
Constant-time security under the assumption that 32-bit division/modulo instruction leaks the size of the dividend and the value of the divisor (see the `LeakageModelTV` theory in the `leakage_models.ec` file).
It assumes that the size of the MAC (`md_size`), the length of the data (`orig_len`), and the `out` and `rec` pointers are public.
It also assumes that the records (pointed to by the `rec` arguments) are well-formed and contain at offset 16 a public pointer (to the data).

- `copy_mac_ct_proof_TV_BL_BL.ec` contains proof that implementation `ssl3_cbc_copy_mac_TV_BL` is constant-time in `BL` model.
- `copy_mac_ct_proof_TV_BL_CL.ec` contains proof that implementation `ssl3_cbc_copy_mac_TV_BL` is constant-time in `CL` model.
- `copy_mac_ct_proof_TV_BL_TV.ec` contains proof that implementation `ssl3_cbc_copy_mac_TV_BL` is constant-time in `TV` model.
- `copy_mac_ct_proof_TV_BL_TV_CL.ec` contains proof that implementation `ssl3_cbc_copy_mac_TV_BL` is constant-time in `CL` model.

# Secure MEE-TLS-CBC MAC extraction (CL model)

Implementation is in `../compiler/examples/lucky13_split.jazz`, function `ssl3_cbc_copy_mac_BL_CL`.

Security proof in `copy_mac_ct_proof.ec`, lemma `l_final`.
Constant-time security under the assumption that 32-bit division/modulo instruction leaks nothing about its operators. It leaks cache-line address during memory accesses (see the `LeakageModelCL` theory in the `leakage_models.ec` file).
It assumes that the size of the MAC (`md_size`), the length of the data (`orig_len`), and the `out` and `rec` pointers are public. Also, `rotated_mac` pointer is 64-byte aligned and public. `MAC` will fit in 64 byte cache-line.
It also assumes that the records (pointed to by the `rec` arguments) are well-formed and contain at offset 16 a public pointer (to the data).

- `copy_mac_ct_proof_BL_CL_CL.ec` contains proof that implementation `ssl3_cbc_copy_mac_BL_CL` is constant-time in `CL` model.

# Secure MEE-TLS-CBC MAC extraction (TV+CL model)

Implementation is in `../compiler/examples/lucky13_split.jazz`, function `ssl3_cbc_copy_mac_TV_CL`.

Security proof in `copy_mac_cache_ct_proof.ec`, lemma `l_final`.
Constant-time security under the assumption of the TV model (see above) and It leaks cache-line address during memory accesses (see the `LeakageModelCL` theory in the `leakage_models.ec` file).
It assumes that the size of the MAC (`md_size`), the length of the data (`orig_len`), and the `out` and `rec` pointers are public. Also, `rotated_mac` pointer is 64-byte aligned and public. `MAC` will fit in 64 byte cache-line.
It also assumes that the records (pointed to by the `rec` arguments) are well-formed and contain at offset 16 a public pointer (to the data).

- `copy_mac_ct_proof_TV_CL_CL.ec` contains proof that implementation `ssl3_cbc_copy_mac_TV_CL` is constant-time in `CL` model.
- `copy_mac_ct_proof_TV_CL_CL.ec` contains proof that implementation `ssl3_cbc_copy_mac_TV_CL` is constant-time in `TV_CL` model.