From elpi.apps Require Import derive.std.
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.
From Coq Require Import ZArith.
Require Import utils.

#[only(eqbOK)] derive
Variant shift_kind :=
| SLSL
| SLSR
| SASR
| SROR.

HB.instance Definition _ := hasDecEq.Build shift_kind shift_kind_eqb_OK.

(* Inclusive bounds on the immediate shift amount of an AArch32 (A32/T32)
   shifted-register operand. Unlike AArch64 (see [check_shift_amount] in
   armv8a_decl.v, where the range is [0, datasize) for every shift type), the
   AArch32 range depends on the shift type, because the 5-bit immediate field
   is decoded differently per type.

   Source: [DecodeImmShift(srtype, imm5)] (Arm ARM DDI0487M.a, J1.2.3.7, p.
   J1-16079):
     - '00' LSL: shift_n = UInt(imm5)                         -> 0..31
     - '01' LSR: shift_n = if imm5 == 0 then 32 else UInt(imm5) -> 1..32
     - '10' ASR: shift_n = if imm5 == 0 then 32 else UInt(imm5) -> 1..32
     - '11' ROR: if imm5 == 0 then RRX (a distinct operation), else
                 shift_n = UInt(imm5)                          -> 1..31
   i.e. LSR/ASR encode a shift of 32 as imm5 = 0, and ROR #0 is RRX, so only
   LSL admits an amount of 0. This is why the AArch32 immediate checker
   [CAimmC_arm_shift_amout] (arch_decl.v) is keyed on the [shift_kind]. *)
Definition shift_amount_bounds sk :=
  match sk with
  | SLSL => (0, 31)%Z
  | SLSR => (1, 32)%Z
  | SASR => (1, 32)%Z
  | SROR => (1, 31)%Z
  end.
