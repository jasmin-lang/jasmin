(* -------------------------------------------------------------------- *)
From mathcomp Require Import all_ssreflect.
(* ------- *) Require Import memory low_memory expr sem.
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
Variant condt : Type :=
| O_ct                  (* overflow *)
| NO_ct                 (* not overflow *)
| B_ct                  (* below, not above or equal *)
| NB_ct                 (* not below, above or equal *)
| E_ct                  (* equal, zero *)
| NE_ct                 (* not equal, not zero *)
| BE_ct                 (* below or equal, not above *)
| NBE_ct                (* not below or equal, above *)
| S_ct                  (* sign *)
| NS_ct                 (* not sign *)
| P_ct                  (* parity, parity even *)
| NP_ct                 (* not parity, parity odd *)
| L_ct                  (* less than, not greater than or equal to *)
| NL_ct                 (* not less than, greater than or equal to *)
| LE_ct                 (* less than or equal to, not greater than *)
| NLE_ct                (* not less than or equal to, greater than *).

(* -------------------------------------------------------------------- *)
Variant asm : Type :=
| LABEL of positive

  (* Data transfert *)
| MOV    of         oprd & oprd    (* copy *)
| CMOVcc of condt & oprd & oprd    (* conditional copy *)

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
| SETcc  of condt & oprd           (* Set byte on condition *)

  (* Pointer arithmetic *)
| LEA    of oprd & oprd            (* Load Effective Address *)

  (* Comparison *)
| TEST   of oprd & oprd            (* Bit-wise logical and CMP *)
| CMP    of oprd & oprd            (* Signed sub CMP *)

  (* Jumps *)
| JMP    of label                  (* Unconditional jump *)
| Jcc    of label & condt          (* Conditional jump *)

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
Scheme Equality for condt.

Definition reg_eqMixin := comparableClass register_eq_dec.
Canonical reg_eqType := EqType register reg_eqMixin.

Definition rflag_eqMixin := comparableClass rflag_eq_dec.
Canonical rflag_eqType := EqType rflag rflag_eqMixin.

Definition scale_eqMixin := comparableClass scale_eq_dec.
Canonical scale_eqType := EqType scale scale_eqMixin.

Definition condt_eqMixin := comparableClass condt_eq_dec.
Canonical condt_eqType := EqType condt condt_eqMixin.

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

(* -------------------------------------------------------------------- *)
Definition st_write_reg (r : register) (w : word) (s : x86_state) :=
  {| xmem := s.(xmem);
     xreg := RegMap.set s.(xreg) r w;
     xrf  := s.(xrf);
     xc   := s.(xc); |}.

(* -------------------------------------------------------------------- *)
Definition st_write_mem (l : word) (w : word) (s : x86_state) :=
  Let m := write_mem s.(xmem) l w in ok
  {| xmem := m;
     xreg := s.(xreg);
     xrf  := s.(xrf);
     xc   := s.(xc); |}.

(* -------------------------------------------------------------------- *)
Coercion word_of_scale (s : scale) : word :=
  I64.repr match s with
  | Scale1 => 1
  | Scale2 => 2
  | Scale4 => 4
  | Scale8 => 8
  end.

(* -------------------------------------------------------------------- *)
Definition decode_addr (s : x86_state) (a : address) : word := nosimpl (
  let: disp   := a.(ad_disp) in
  let: base   := odflt I64.zero (omap (RegMap.get s.(xreg)) a.(ad_base)) in
  let: scale  := odflt I64.one  (omap word_of_scale a.(ad_scale)) in
  let: offset := odflt I64.zero (omap (RegMap.get s.(xreg)) a.(ad_offset)) in

  I64.add disp (I64.add base (I64.mul scale offset))).

(* -------------------------------------------------------------------- *)
Definition write_oprd (o : oprd) (w : word) (s : x86_state) :=
  match o with
  | Imm_op v => type_error
  | Reg_op r => ok (st_write_reg r w s)
  | Adr_op a => st_write_mem (decode_addr s a) w s
  end.

(* -------------------------------------------------------------------- *)
Definition read_oprd (o : oprd) (s : x86_state) :=
  match o with
  | Imm_op v => ok v
  | Reg_op r => ok (RegMap.get s.(xreg) r)
  | Adr_op a => read_mem s.(xmem) (decode_addr s a)
  end.
