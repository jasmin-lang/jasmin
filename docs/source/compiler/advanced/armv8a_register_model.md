# ARMv8-A (AArch64) register model and stack-pointer handling — rationale and sources

This note documents the modeling decisions in the Jasmin AArch64 backend that
concern the **architecture declaration** (`proofs/compiler/armv8a_decl.v`) and
the **stack-pointer handling** in the linearization parameters
(`proofs/compiler/armv8a_params.v`). Each decision departs from a naive "one
Coq constructor per hardware register" model for a documented architectural or
ABI reason; the citations below let a reviewer check every claim.

Primary sources:

- **Arm ARM** — *Arm Architecture Reference Manual, A-profile*, Arm DDI 0487M.a
  (`DDI0487_M.a.a_a-profile_architecture_reference_manual.pdf`,
  sha256 `c07b1302a3db0c6bc0490808c771d66684ddd5adfb2ef64fd23e6beeb7b22e48`).
  Page ids below are the manual's own `Sn-NNNN` labels.
- **AAPCS64** — *Procedure Call Standard for the Arm 64-bit Architecture
  (AArch64)*, Arm IHI 0055F.
- **Apple** — *Writing ARM64 Code for Apple Platforms*, Apple Developer
  documentation.

---

## 1. The general-purpose register set

AArch64 has 31 general-purpose registers `R0..R30`, each addressable as a 64-bit
`X` register or a 32-bit `W` register, plus a dedicated stack pointer `SP`.
`R30` is the procedure-call link register.

> Arm ARM, **B1.2 "Registers in AArch64 Execution state"**, p. B1-203:
> "31 general-purpose registers, R0 to R30 ... The X30 general-purpose register
> is used as the procedure call link register. SP — A 64-bit dedicated Stack
> Pointer register."

The model keeps `R0..R30` and `RSP`. Two registers that a hardware-faithful
model might include are deliberately omitted (§2, §3).

## 2. The zero register (XZR/WZR) is not modeled

In an instruction encoding the 5-bit register field value `31` (`0b11111`) does
**not** name a physical register; its meaning depends on which register accessor
the instruction uses:

> Arm ARM, **B1.2**, p. B1-206:
> "For the general-purpose register X[] accessor, register number 31 accesses
> the zero register, ZR, which reads as zero and ignores writes."

The stack pointer is reached through a **separate `SP[]` accessor**, so the same
field value `31` means `SP` only for the instructions that select it (ADD/SUB in
their SP forms, MOV-to/from-SP, and loads/stores that allow `SP` as base).

Consequences for the model:

- Modeling `ZR` as an allocatable register would be **unsound**: a value written
  to it is discarded and any read returns 0. The register allocator, treating it
  as ordinary storage, produced code such as `mov sp, xzr` (setting SP to 0).
- We therefore omit it entirely, exactly as the Jasmin RISC-V backend omits the
  hardwired `x0`/`zero`. The handful of operations that genuinely need `ZR` as an
  operand — `CMP` (`SUBS` to `ZR`), `NEG`, `TST`, etc. — are emitted as dedicated
  assembler mnemonics by the printer, never as writes to a `ZR` register.
- `RSP` is the single encoding-31 register we keep, and it always denotes `SP`.

## 3. The platform register (x18) is not modeled

`x18` is not an architectural special register; it is reserved by the software
ABI:

> AAPCS64 (IHI 0055F), *General-purpose registers*: r18 is
> "The Platform Register, if needed; otherwise a temporary register", and a
> platform ABI may reserve it.
>
> Apple, *Writing ARM64 Code for Apple Platforms*:
> "The platforms reserve register x18. Don't use this register."

On Apple platforms, under Windows, and under shadow-call-stack Linux, the OS or
runtime may overwrite `x18` **asynchronously** (i.e. between two instructions of
otherwise straight-line user code). Jasmin's register allocator chooses the
register that holds a function's saved stack pointer by proving the program does
not clobber it (`get_reg_oracle` in `compiler/src/regalloc.ml`); that analysis
cannot see writes performed outside the program, so it happily picked `x18` and
the saved SP was corrupted to 0 at run time.

Keeping `x18` out of the allocation pool is the only safe choice across these
platforms. On a platform where `x18` is a plain temporary this merely forgoes
one scratch register; correctness is unaffected.

## 4. The stack pointer must stay 16-byte aligned

Whenever `SP` is used as the base of a memory access it must be 16-byte aligned.
This is an **architectural** check (an exception), not just an ABI convention:

> Arm ARM, **D1.4.10.2 "SP alignment checking"**, p. D1-7135:
> - rule **RRDMXG**: "When the SP is used as the base address of a calculation,
>   regardless of any offset applied by the instruction, if bits [3:0] of the SP
>   are not 0b0000, there is a misaligned SP."
> - rule **RTFVSM**: "If SP alignment checking is enabled, then the execution of
>   a load or store using the SP with a misaligned SP generates a synchronous SP
>   Alignment exception on that load or store."
> - rule **RSTDYJ**: the check is enabled by `SCTLR_EL1.SA` (EL1),
>   `SCTLR_EL1.SA0`/`SCTLR_EL2.SA0` (EL0), etc.

The check is enabled for EL0 on the platforms we target. The 16-byte alignment
of `SP` at public interfaces is also mandated by the AAPCS64 (IHI 0055F, *The
stack*: "SP mod 16 = 0"), which B1.2 (p. B1-203) cross-references.

Jasmin sizes each stack frame to the alignment of the objects it holds
(`sao_align`), which for pure 64-bit code is only 8 bytes, so a raw frame size
need not be a multiple of 16. The backend therefore:

- rounds every frame allocation/deallocation up to a multiple of 16
  (`round_up_16`, used by `armv8a_allocate_stack_frame` /
  `armv8a_free_stack_frame`), so nested calls preserve the invariant; and
- never aligns a re-aligned frame to less than 16 bytes
  (`armv8a_set_up_sp_register`).

The extra padding lands at the top of the frame and is never accessed.

## 5. The stack pointer cannot be an LDR destination

Because a load writes its result through the general-purpose `X[]` accessor, and
register number 31 in that accessor is `ZR` (§2), an A64 `LDR` can never write
`SP`: its destination operand is `<Xt>`, not `<Xt|SP>`. (This differs from
ARMv7, where R13/SP is an ordinary register that `LDR` can target — which is why
the shared linearization default, `lloads_imm_dfl`, is fine for the 32-bit Arm
backend but not here.)

When the saved stack pointer has been spilled to the stack (the usual case for a
function that saves callee-saved registers), it must therefore be reloaded into
a scratch register and then copied to `SP` with a `MOV` (which reaches `SP` via
the `SP[]` accessor). This is what the backend's custom `armv8a_lloads` does: it
restores the ordinary saved registers first (relative to the still-live `SP`),
then loads the saved `SP` into `X17` and issues `MOV SP, X17`.

---

### Cross-reference to the code

| Decision | File / definition | Source |
|---|---|---|
| Omit `XZR` | `armv8a_decl.v` — `register`, `registers`, `register_to_string` | Arm ARM B1.2, p. B1-206 |
| Omit `x18` | `armv8a_decl.v` — `register`, `registers`, `armv8a_internal_call_conv` | AAPCS64 IHI 0055F; Apple ABI |
| Round frames to 16 | `armv8a_params.v` — `round_up_16`, `armv8a_allocate_stack_frame`, `armv8a_free_stack_frame` | Arm ARM D1.4.10.2 (RRDMXG, RTFVSM) |
| Re-align frames ≥ 16 | `armv8a_params.v` — `armv8a_set_up_sp_register` | Arm ARM D1.4.10.2; AAPCS64 |
| Restore `SP` via scratch + `MOV` | `armv8a_params.v` — `armv8a_lloads` | Arm ARM B1.2, p. B1-206 |
