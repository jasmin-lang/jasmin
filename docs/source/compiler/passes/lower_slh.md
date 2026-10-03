# Lowering of SLH instructions

This pass checks that the misspeculation flags (MSF) are used as the operators
of selective speculative load hardening require, and replaces these operators
with architecture-specific operators, which are expanded into instructions at
assembly generation. The MSF is 0 when execution is not misspeculating after a
conditional branch and -1 otherwise. `#protect_ptr` is lowered later, by stack
allocation, once the pointer is a register, in the same way as `#protect`.

| operator                    | x86-64                              | ARMv8-A                                |
|-----------------------------|-------------------------------------|----------------------------------------|
| `msf = #init_msf()`         | `LFENCE; MOV msf, 0`                | `DSB SY; ISB; MOV msf, #0`             |
| `msf = #update_msf(b, msf)` | `MOV aux, -1; CMOVcc(!b) msf, aux`  | `MOVN aux, #0; CSEL msf, msf, aux, b`  |
| `msf' = #mov_msf(msf)`      | `MOV msf', msf`                     | `MOV msf', msf`                        |
| `y = #protect(x, msf)`      | `OR x, msf` (`y` is `x`)            | `ORR y, x, msf; CSDB`                  |

On x86-64, values in MMX and vector registers are protected with `POR` and
`VPOR`. On ARMv8-A, only 32-bit and 64-bit values can be protected, and the
operands of these operators must be registers. The other architectures do not
support these operators.

ARMv8-A allows the condition flags of a conditional select, and the results of
other instructions, to be predicted. The `CSDB` after the `ORR` ensures that
the protected value is not used with such predictions of earlier instructions,
in particular the `CSEL` of `#update_msf`. A `CSDB` does not constrain branches:
a protected value is tested by a comparison and a conditional branch on the
flags, never by a branch that reads a register (`CBZ`, `TBZ`).

On both architectures, these sequences defend against the misprediction of
conditional branches. Return misprediction, straight-line speculation after
`RET` and `BR`, and speculative store bypass are not taken into account. On
ARMv8-A, neither are the predictions of values that do not go through
`#protect` (for instance values reloaded from the stack), nor the prediction of
load addresses.

The compilation of these operators is proved to preserve the functional
semantics. Their speculative behaviour is not formally verified.
