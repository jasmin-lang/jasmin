(* -------------------------------------------------------------------- *)
From mathcomp Require Import all_ssreflect.
(* ------- *) Require Import low_memory memory expr sem.
(* ------- *) (* - *) Import Memory.

Set   Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* -------------------------------------------------------------------- *)
Definition label := positive.

(* -------------------------------------------------------------------- *)
Variant register : Type :=
  | RAX | RCX | RDX | RBX | RSP | RBP | RSI | RDI
  | R8  | R9  | R10 | R11 | R12 | R13 | R14 | R15.

(* -------------------------------------------------------------------- *)
Variant rflag : Type := CF | PF | ZF | SF | OF | DF.

(* -------------------------------------------------------------------- *)
Variant scale : Type := Scale1 | Scale2 | Scale4 | Scale8.

(* -------------------------------------------------------------------- *)
Record address : Type := mkAddress {
  ad_disp   : word;
  ad_base   : option register;
  ad_scale  : option scale;
  ad_offset : option register;
}.

(* -------------------------------------------------------------------- *)
Variant oprd : Type :=
| Imm_op     of word
| Reg_op     of register
| Adr_op     of address.

(* -------------------------------------------------------------------- *)
Variant ireg : Type :=
| Imm_ir of word
| Reg_ir of register.

(* -------------------------------------------------------------------- *)
Variant condfg : Type :=
  EQ | CARRY | LTU | LTS | LEU | LES | GTU | GTS | GEU | GES.

(* -------------------------------------------------------------------- *)
Variant asm : Type :=
| LABEL of positive

  (* Data transfert *)
| MOV    of          oprd & oprd   (* copy *)
| CMOVcc of condfg & oprd & oprd   (* conditional copy *)

  (* Arithmetic *)
| ADD    of oprd & oprd            (* add unsigned / signed *)
| SUB    of oprd & oprd            (* sub unsigned / signed *)
| MUL    of oprd                   (* mul unsigned *)
| IMUL   of oprd & option oprd & option nat
                                   (* mul   signed *)
| DIV    of oprd                   (* div unsigned *)
| IDIV   of oprd                   (* div   signed *)

| ADC    of oprd & oprd            (* add with carry *)
| SBB    of oprd & oprd            (* sub with borrow *)

| INC    of oprd                   (* increment *)
| DEC    of oprd                   (* decrement *)

  (* Flag *)
| SETcc  of condfg & oprd          (* Set byte on condition *)

  (* Pointer arithmetic *)
| LEA    of oprd & oprd            (* Load Effective Address *)

  (* Comparison *)
| TEST   of oprd & oprd            (* Bit-wise logical and CMP *)
| CMP    of oprd & oprd            (* Signed sub CMP *)

  (* Jumps *)
| JMP    of label                  (* Unconditional jump *)
| Jcc    of label                  (* Conditional jump *)

  (* Bitwise logical instruction *)
| AND    of oprd & oprd            (* bit-wise and *)
| OR     of oprd & oprd            (* bit-wise or  *)
| XOR    of oprd & oprd            (* bit-wise xor *)
| NOT    of oprd                   (* bit-wise not *)

  (* Bit scan *)
| BSF    of oprd & oprd            (* forward *)
| BSR    of oprd & oprd            (* reverse *)

  (* Bit shifts *)
| SHL    of oprd & ireg            (* unsigned / left  *)
| SHR    of oprd & ireg            (* unsigned / right *)
| SAL    of oprd & ireg            (*   signed / left  *)
| SAR    of oprd & ireg            (*   signed / right *)
.

(* -------------------------------------------------------------------- *)
Scheme Equality for register.
Scheme Equality for rflag.
Scheme Equality for scale.
Scheme Equality for condfg.

Definition reg_eqMixin := comparableClass register_eq_dec.
Canonical reg_eqType := EqType register reg_eqMixin.

Definition rflag_eqMixin := comparableClass rflag_eq_dec.
Canonical rflag_eqType := EqType rflag rflag_eqMixin.

Definition scale_eqMixin := comparableClass scale_eq_dec.
Canonical scale_eqType := EqType scale scale_eqMixin.

Definition condfg_eqMixin := comparableClass condfg_eq_dec.
Canonical condfg_eqType := EqType condfg condfg_eqMixin.

(* -------------------------------------------------------------------- *)
Module RegMap.
  Definition map := register -> word.

  Definition get (m : map) (x : register) := m x.

  Definition set (m : map) (x : register) (y : word) :=
    fun z => if (z == x) then y else m z.
End RegMap.

(* -------------------------------------------------------------------- *)
Module RflagMap.
  Definition map := rflag -> bool.

  Definition get (m : map) (x : rflag) := m x.

  Definition set (m : map) (x : rflag) (y : bool) :=
    fun z => if (z == x) then y else m z.
End RflagMap.

(* -------------------------------------------------------------------- *)
Notation regmap   := RegMap.map.
Notation rflagmap := RflagMap.map.

Definition regmap0   : regmap   := fun x => I64.repr 0.
Definition rflagmap0 : rflagmap := fun x => false.

(* -------------------------------------------------------------------- *)
Record x86_state := X86State {
  xmem : mem;
  xreg : regmap;
  xrf  : rflagmap;
  xc   : cmd;
}.
