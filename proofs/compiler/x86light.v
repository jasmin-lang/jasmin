(* -------------------------------------------------------------------- *)
From mathcomp Require Import all_ssreflect.

Set   Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* -------------------------------------------------------------------- *)
Variant register : Type :=
  | RAX | RCX | RDX | RBX | RSP | RBP | RSI | RDI
  | R8  | R9  | R10 | R11 | R12 | R13 | R14 | R15.

Scheme Equality for register.

Definition reg_eqMixin := comparableClass register_eq_dec.
Canonical reg_eqType := EqType register reg_eqMixin.

(* -------------------------------------------------------------------- *)
Variant asm : Type :=

  (* Data transfert *)
| MOV                           (* copy *)
| CMOVcc                        (* conditional copy *)

  (* Arithmetic *)
| ADD                           (* add unsigned / signed *)
| SUB                           (* sub unsigned / signed *)
| MUL                           (* mul unsigned *)
| IMUL                          (* mul   signed *)
| DIV                           (* div unsigned *)
| IDIV                          (* div   signed *)

| ADC                           (* add with carry *)
| SBB                           (* sub with borrow *)

| INC                           (* increment *)
| DEC                           (* decrement *)

  (* Flag *)
| SETcc                         (* Set byte on condition *)
| SAHF                          (* AH -> FLAGS   *)
| LAHF                          (* FLAGS -> AH   *)

  (* Pointer arithmetic *)
| LEA                           (* Load Effective Address *)

  (* Comparison *)
| TEST                          (* Bit-wise logical and CMP *)
| CMP                           (* Signed sub CMP *)

  (* Jumps *)
| JMP                           (* Unconditional jump *)
| Jcc                           (* Conditional jump *)

  (* Bitwise logical instruction *)
| AND                           (* bit-wise and *)
| OR                            (* bit-wise or  *)
| XOR                           (* bit-wise xor *)
| NOT                           (* bit-wise not *)

  (* Bit scan *)
| BSF                           (* forward *)
| BSR                           (* reverse *)

  (* Bit shifts *)
| SHL                           (* unsigned / left  *)
| SHR                           (* unsigned / right *)
| SAL                           (*   signed / left  *)
| SAR                           (*   signed / right *)
.
