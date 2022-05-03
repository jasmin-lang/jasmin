# Secure implementation of 64-bit modulo

Implementation is in `../compiler/examples/mod_patch.jazz`

Security proof (constant-time in a model in which 64-bit division/modulo leaks the size of the dividend and the value of the divisor) in `modulo_ct_proof.ec`, lemma `l2`.
It assumes that the divisor (second argument) is public and non-zero.

# Secure MEE-TLS-CBC MAC extraction (BL model)

Implementation is in `../compiler/examples/lucky13_split.jazz`, function `ssl3_cbc_copy_mac_BL_BL`.

Constant-time security under the assumption that 32-bit division/modulo instruction leaks nothing about its operands (see the `LeakageModelBL` theory in the `../eclib/leakage_models.ec` file).
It assumes that the size of the MAC (`md_size`), the length of the data (`orig_len`), and the `out` and `rec` pointers are public.
It also assumes that the records (pointed to by the `rec` arguments) are well-formed and contain at offset 16 a public pointer (to the data).

- `copy_mac_ct_proof_BL_BL_BL.ec` contains proof that implementation `ssl3_cbc_copy_mac_BL_BL` is constant-time in `BL` model.
- `copy_mac_ct_proof_BL_BL_CL32.ec` contains proof that implementation `ssl3_cbc_copy_mac_BL_BL` is constant-time in `CL32` model.
- `copy_mac_ct_proof_BL_BL_CL64.ec` contains proof that implementation `ssl3_cbc_copy_mac_BL_BL` is constant-time in `CL64` model.

# Secure MEE-TLS-CBC MAC extraction (TV model)

Implementation is in `../compiler/examples/lucky13_split.jazz`, function `ssl3_cbc_copy_mac_TV_BL`.

Constant-time security under the assumption that 32-bit division/modulo instruction leaks the size of the dividend and the value of the divisor (see the `LeakageModelTV` theory in the `../eclib/leakage_models.ec` file).
It assumes that the size of the MAC (`md_size`), the length of the data (`orig_len`), and the `out` and `rec` pointers are public.
It also assumes that the records (pointed to by the `rec` arguments) are well-formed and contain at offset 16 a public pointer (to the data).

- `copy_mac_ct_proof_TV_BL_BL.ec` contains proof that implementation `ssl3_cbc_copy_mac_TV_BL` is constant-time in `BL` model.
- `copy_mac_ct_proof_TV_BL_CL32.ec` contains proof that implementation `ssl3_cbc_copy_mac_TV_BL` is constant-time in `CL32` model.
- `copy_mac_ct_proof_TV_BL_CL64.ec` contains proof that implementation `ssl3_cbc_copy_mac_TV_BL` is constant-time in `CL64` model.
- `copy_mac_ct_proof_TV_BL_TV.ec` contains proof that implementation `ssl3_cbc_copy_mac_TV_BL` is constant-time in `TV` model.
- `copy_mac_ct_proof_TV_BL_TV_CL32.ec` contains proof that implementation `ssl3_cbc_copy_mac_TV_BL` is constant-time in `CL32` model.
- `copy_mac_ct_proof_TV_BL_TV_CL64.ec` contains proof that implementation `ssl3_cbc_copy_mac_TV_BL` is constant-time in `CL64` model.

# Secure MEE-TLS-CBC MAC extraction (CL64 model)

Implementation is in `../compiler/examples/lucky13_split.jazz`, function `ssl3_cbc_copy_mac_BL_CL`.

Constant-time security under the assumption that 32-bit division/modulo instruction leaks nothing about its operators. It leaks cache-line address during memory accesses (see the `LeakageModelCL` theory in the `../eclib/leakage_models.ec` file).
It assumes that the size of the MAC (`md_size`), the length of the data (`orig_len`), and the `out` and `rec` pointers are public. Also, `rotated_mac` pointer is 64-byte aligned and public. `MAC` will fit in 64 byte cache-line.
It also assumes that the records (pointed to by the `rec` arguments) are well-formed and contain at offset 16 a public pointer (to the data).

- `copy_mac_ct_proof_BL_CL64_CL64.ec` contains proof that implementation `ssl3_cbc_copy_mac_BL_CL` is constant-time in `CL64` model.

# Secure MEE-TLS-CBC MAC extraction (TV+CL64 model)

Implementation is in `../compiler/examples/lucky13_split.jazz`, function `ssl3_cbc_copy_mac_TV_CL`.

Constant-time security under the assumption of the TV model (see above) and It leaks cache-line address during memory accesses (see the `LeakageModelCL` theory in the `../eclib/leakage_models.ec` file).
It assumes that the size of the MAC (`md_size`), the length of the data (`orig_len`), and the `out` and `rec` pointers are public. Also, `rotated_mac` pointer is 64-byte aligned and public. `MAC` will fit in 64 byte cache-line.
It also assumes that the records (pointed to by the `rec` arguments) are well-formed and contain at offset 16 a public pointer (to the data).

- `copy_mac_ct_proof_TV_CL64_CL64.ec` contains proof that implementation `ssl3_cbc_copy_mac_TV_CL` is constant-time in `CL` model.
- `copy_mac_ct_proof_TV_CL64_TV_CL64.ec` contains proof that implementation `ssl3_cbc_copy_mac_TV_CL` is constant-time in `TV_CL64` model.

# Secure implementation of Chacha20 ref

Implementation is in `chacha20/chacha20_ref/chacha20_ref.jazz`, function `chacha20_ref`

Constant-time security under the assumption of the BL model. Also, it does not contain any Time-Variable operations.
- `chacha20_ref_proof_BL_BL.ec` contains proof that implementation `chacha20_ref` is constant-time in `BL` model.
- `chacha20_ref_proof_BL_CL32.ec` contains proof that implementation `chacha20_ref` is constant-time in `CL32` model.
- `chacha20_ref_proof_BL_CL64.ec` contains proof that implementation `chacha20_ref` is constant-time in `CL64` model.
- `chacha20_ref_proof_TV_BL.ec` contains proof that implementation `chacha20_ref` is constant-time in `TV` model.
- `chacha20_ref_proof_TV_CL32.ec` contains proof that implementation `chacha20_ref` is constant-time in `TV_CL32` model.
- `chacha20_ref_proof_TV_CL64.ec` contains proof that implementation `chacha20_ref` is constant-time in `TV_CL64` model.

# Secure implementation of Chacha20 avx

Implementation is in `chacha20/chacha20_avx/chacha20_avx.jazz`, function `chacha20_avx`

Constant-time security under the assumption of the BL model. Also, it does not contain any Time-Variable operations.
- `chacha20_avx_proof_BL_BL.ec` contains proof that implementation `chacha20_avx` is constant-time in `BL` model.
- `chacha20_avx_proof_BL_CL32.ec` contains proof that implementation `chacha20_avx` is constant-time in `CL32` model.
- `chacha20_avx_proof_BL_CL64.ec` contains proof that implementation `chacha20_avx` is constant-time in `CL64` model.
- `chacha20_avx_proof_TV_BL.ec` contains proof that implementation `chacha20_avx` is constant-time in `TV` model.
- `chacha20_avx_proof_TV_CL32.ec` contains proof that implementation `chacha20_avx` is constant-time in `TV_CL32` model.
- `chacha20_avx_proof_TV_CL64.ec` contains proof that implementation `chacha20_avx` is constant-time in `TV_CL64` model.

# Secure implementation of Chacha20 avx2

Implementation is in `chacha20/chacha20_avx2/chacha20_avx2.jazz`, function `chacha20_avx2`

Constant-time security under the assumption of the BL model. Also, it does not contain any Time-Variable operations.
- `chacha20_avx2_proof_BL_BL.ec` contains proof that implementation `chacha20_avx2` is constant-time in `BL` model.
- `chacha20_avx2_proof_BL_CL32.ec` contains proof that implementation `chacha20_avx2` is constant-time in `CL32` model.
- `chacha20_avx2_proof_BL_CL64.ec` contains proof that implementation `chacha20_avx2` is constant-time in `CL64` model.
- `chacha20_avx2_proof_TV_BL.ec` contains proof that implementation `chacha20_avx2` is constant-time in `TV` model.
- `chacha20_avx2_proof_TV_CL32.ec` contains proof that implementation `chacha20_avx2` is constant-time in `TV_CL32` model.
- `chacha20_avx2_proof_TV_CL64.ec` contains proof that implementation `chacha20_avx2` is constant-time in `TV_CL64` model.

# Secure implementation of poly1305 ref

Implementation is in `poly1305/poly1305_ref/poly1305_ref.jazz`, function `poly1305_ref`

Constant-time security under the assumption of the BL model. Also, it does not contain any Time-Variable operations.
- `poly1305_ref_proof_BL_BL.ec` contains proof that implementation `poly1305_ref` is constant-time in `BL` model.
- `poly1305_ref_proof_BL_CL32.ec` contains proof that implementation `poly1305_ref` is constant-time in `CL32` model.
- `poly1305_ref_proof_BL_CL64.ec` contains proof that implementation `poly1305_ref` is constant-time in `CL64` model.
- `poly1305_ref_proof_TV_BL.ec` contains proof that implementation `poly1305_ref` is constant-time in `TV` model.
- `poly1305_ref_proof_TV_CL32.ec` contains proof that implementation `poly1305_ref` is constant-time in `TV_CL32` model.
- `poly1305_ref_proof_TV_CL64.ec` contains proof that implementation `poly1305_ref` is constant-time in `TV_CL64` model.

# Secure implementation of poly1305 avx

Implementation is in `poly1305/poly1305_avx/poly1305_avx.jazz`, function `poly1305_avx`

Constant-time security under the assumption of the BL model. Also, it does not contain any Time-Variable operations.
- `poly1305_avx_proof_BL_BL.ec` contains proof that implementation `poly1305_avx` is constant-time in `BL` model.
- `poly1305_avx_proof_BL_CL32.ec` contains proof that implementation `poly1305_avx` is constant-time in `CL32` model.
- `poly1305_avx_proof_BL_CL64.ec` contains proof that implementation `poly1305_avx` is constant-time in `CL64` model.
- `poly1305_avx_proof_TV_BL.ec` contains proof that implementation `poly1305_avx` is constant-time in `TV` model.
- `poly1305_avx_proof_TV_CL32.ec` contains proof that implementation `poly1305_avx` is constant-time in `TV_CL32` model.
- `poly1305_avx_proof_TV_CL64.ec` contains proof that implementation `poly1305_avx` is constant-time in `TV_CL64` model.

# Secure implementation of poly1305 avx2

Implementation is in `poly1305/poly1305_avx2/poly1305_avx2.jazz`, function `poly1305_avx2`

Constant-time security under the assumption of the BL model. Also, it does not contain any Time-Variable operations.
- `poly1305_avx2_proof_BL_BL.ec` contains proof that implementation `poly1305_avx2` is constant-time in `BL` model.
- `poly1305_avx2_proof_BL_CL32.ec` contains proof that implementation `poly1305_avx2` is constant-time in `CL32` model.
- `poly1305_avx2_proof_BL_CL64.ec` contains proof that implementation `poly1305_avx2` is constant-time in `CL64` model.
- `poly1305_avx2_proof_TV_BL.ec` contains proof that implementation `poly1305_avx2` is constant-time in `TV` model.
- `poly1305_avx2_proof_TV_CL32.ec` contains proof that implementation `poly1305_avx2` is constant-time in `TV_CL32` model.
- `poly1305_avx2_proof_TV_CL64.ec` contains proof that implementation `poly1305_avx2` is constant-time in `TV_CL64` model.

# Secure implementation of keccak1600 ref

Implementation is in `keccak1600/keccak1600_ref/keccak1600_ref.jazz`, function `keccak1600_ref`

Constant-time security under the assumption of the BL model. Also, it does not contain any Time-Variable operations.
- `keccak1600_ref_proof_BL_BL.ec` contains proof that implementation `keccak1600_ref` is constant-time in `BL` model.
- `keccak1600_ref_proof_BL_CL32.ec` contains proof that implementation `keccak1600_ref` is constant-time in `CL32` model.
- `keccak1600_ref_proof_BL_CL64.ec` contains proof that implementation `keccak1600_ref` is constant-time in `CL64` model.
- `keccak1600_ref_proof_TV_BL.ec` contains proof that implementation `keccak1600_ref` is constant-time in `TV` model.
- `keccak1600_ref_proof_TV_CL32.ec` contains proof that implementation `keccak1600_ref` is constant-time in `TV_CL32` model.
- `keccak1600_ref_proof_TV_CL64.ec` contains proof that implementation `keccak1600_ref` is constant-time in `TV_CL64` model.

# Secure implementation of keccak1600 scalar

Implementation is in `keccak1600/keccak1600_scalar/keccak1600_scalar.jazz`, function `keccak1600_scalar`

Constant-time security under the assumption of the BL model. Also, it does not contain any Time-Variable operations.
- `keccak1600_scalar_proof_BL_BL.ec` contains proof that implementation `keccak1600_scalar` is constant-time in `BL` model.
- `keccak1600_scalar_proof_BL_CL32.ec` contains proof that implementation `keccak1600_scalar` is constant-time in `CL32` model.
- `keccak1600_scalar_proof_BL_CL64.ec` contains proof that implementation `keccak1600_scalar` is constant-time in `CL64` model.
- `keccak1600_scalar_proof_TV_BL.ec` contains proof that implementation `keccak1600_scalar` is constant-time in `TV` model.
- `keccak1600_scalar_proof_TV_CL32.ec` contains proof that implementation `keccak1600_scalar` is constant-time in `TV_CL32` model.
- `keccak1600_scalar_proof_TV_CL64.ec` contains proof that implementation `keccak1600_scalar` is constant-time in `TV_CL64` model.

# Secure implementation of keccak1600 avx2

Implementation is in `keccak1600/keccak1600_avx2/keccak1600_avx2.jazz`, function `keccak1600_avx2`

Constant-time security under the assumption of the BL model. Also, it does not contain any Time-Variable operations.
- `keccak1600_avx2_proof_BL_BL.ec` contains proof that implementation `keccak1600_avx2` is constant-time in `BL` model.
- `keccak1600_avx2_proof_BL_CL32.ec` contains proof that implementation `keccak1600_avx2` is constant-time in `CL32` model.
- `keccak1600_avx2_proof_BL_CL64.ec` contains proof that implementation `keccak1600_avx2` is constant-time in `CL64` model.
- `keccak1600_avx2_proof_TV_BL.ec` contains proof that implementation `keccak1600_avx2` is constant-time in `TV` model.
- `keccak1600_avx2_proof_TV_CL32.ec` contains proof that implementation `keccak1600_avx2` is constant-time in `TV_CL32` model.
- `keccak1600_avx2_proof_TV_CL64.ec` contains proof that implementation `keccak1600_avx2` is constant-time in `TV_CL64` model.

# Secure implementation of OpenSSL's pmac_verify_hmac (CL32)

Implementation is in `openSSL/pmac_verify_hmac/pmac_verify_hmac.jazz`, function `verify_hmac_jazz`

pmac is 32-byte aligned buffer with size 80. It is constant-time security under cache line model with size at least 32bytes.
- `pmac_verify_hmac_proof_BL_CL32.ec` contains proof that implementation `verify_hmac_jazz` is constant-time in `CL32` model.
- `pmac_verify_hmac_proof_BL_CL64.ec` contains proof that implementation `verify_hmac_jazz` is constant-time in `CL64` model.
- `pmac_verify_hmac_proof_TV_CL32.ec` contains proof that implementation `verify_hmac_jazz` is constant-time in `TV_CL32` model.
- `pmac_verify_hmac_proof_TV_CL64.ec` contains proof that implementation `verify_hmac_jazz` is constant-time in `TV_CL64` model.

# Secure implementation of WolfSSL's Base64_Char2Val (CL32)

Implementation is in `wolfSSL/coding_wolfSSL.jazz`, function `Base64_Char2Val_jazz`

`base64Decode` is a 64-byte aligned table of size 80. The table fits in two 64-byte cache lines.

- `coding_wolfSSL_proof_BL_CL64.ec` contains proof that implementation `Base64_Char2Val_jazz` is constant-time in `CL64` and the same proof applies for `TV_CL64` model.