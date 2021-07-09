(* ** License
 * -----------------------------------------------------------------------
 * Copyright 2016--2017 IMDEA Software Institute
 * Copyright 2016--2017 Inria
 *
 * Permission is hereby granted, free of charge, to any person obtaining
 * a copy of this software and associated documentation files (the
 * "Software"), to deal in the Software without restriction, including
 * without limitation the rights to use, copy, modify, merge, publish,
 * distribute, sublicense, and/or sell copies of the Software, and to
 * permit persons to whom the Software is furnished to do so, subject to
 * the following conditions:
 *
 * The above copyright notice and this permission notice shall be
 * included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
 * EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.
 * IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY
 * CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT,
 * TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE
 * SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 * ----------------------------------------------------------------------- *)


(* -------------------------------------------------------------------- *)
From mathcomp Require Import all_ssreflect all_algebra.
From CoqWord Require Import ssrZ.
Require oseq.
Require Import ZArith
utils
strings wsize
memory_model
(* word *)
global
oseq
Utf8
Relation_Operators
sem_type.

(* Import Memory. *)

Set   Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* ==================================================================== *)
Definition label := positive.
Definition remote_label := (funname * label)%type.

(* Indirect jumps use labels encoded as pointers: we assume such an encoding exists.
  The encoding and decoding functions are parameterized by a domain:
  they are assumed to succeed on this domain only.
*)
Parameter encode_label : seq remote_label → remote_label → option pointer.
Parameter decode_label : seq remote_label → pointer → option remote_label.
Axiom decode_encode_label : ∀ dom lbl, obind (decode_label dom) (encode_label dom lbl) = Some lbl.
Axiom encode_label_dom : ∀ dom lbl, lbl \in dom → encode_label dom lbl ≠ None.

(* -------------------------------------------------------------------- *)
Variant register : Type :=
  | RAX | RCX | RDX | RBX | RSP | RBP | RSI | RDI
  | R8  | R9  | R10 | R11 | R12 | R13 | R14 | R15.


(* -------------------------------------------------------------------- *)
Variant xmm_register : Type :=
  | XMM0 | XMM1 | XMM2 | XMM3
  | XMM4 | XMM5 | XMM6 | XMM7
  | XMM8 | XMM9 | XMM10 | XMM11
  | XMM12 | XMM13 | XMM14 | XMM15
.

(* -------------------------------------------------------------------- *)
Variant rflag : Type := CF | PF | ZF | SF | OF | DF.

(* -------------------------------------------------------------------- *)
Variant scale : Type := Scale1 | Scale2 | Scale4 | Scale8.

(* -------------------------------------------------------------------- *)
Coercion word_of_scale (s : scale) : pointer :=
  wrepr Uptr match s with
  | Scale1 => 1
  | Scale2 => 2
  | Scale4 => 4
  | Scale8 => 8
  end.

(* -------------------------------------------------------------------- *)
(* disp + base + scale × offset *)
Record reg_address : Type := mkAddress {
  ad_disp   : pointer;
  ad_base   : option register;
  ad_scale  : scale;
  ad_offset : option register;
}.

Definition rip_address := pointer.

Inductive address := 
  | Areg of reg_address
  | Arip of pointer. 

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

Definition string_of_condt (c: condt) : string :=
  match c with
  | O_ct => "O"
  | NO_ct => "NO"
  | B_ct => "B"
  | NB_ct => "NB"
  | E_ct => "E"
  | NE_ct => "NE"
  | BE_ct => "BE"
  | NBE_ct => "NBE"
  | S_ct => "S"
  | NS_ct => "NS"
  | P_ct => "P"
  | NP_ct => "NP"
  | L_ct => "L"
  | NL_ct => "NL"
  | LE_ct => "LE"
  | NLE_ct => "NLE"
  end.

(* -------------------------------------------------------------------- *)
(*
Scheme Equality for sopn.
(* Definition sopn_beq : sopn -> sopn -> bool *)
Lemma sopn_eq_axiom : Equality.axiom sopn_beq.
Proof.
  move=> x y;apply:(iffP idP).
  + by apply: internal_sopn_dec_bl.
  by apply: internal_sopn_dec_lb.
Qed.
*)

Scheme Equality for register.
Scheme Equality for xmm_register.
Scheme Equality for rflag.
Scheme Equality for scale.
Scheme Equality for condt.

Lemma reg_eq_axiom : Equality.axiom register_beq.
Proof.
  move=> x y;apply:(iffP idP).
  + by apply: internal_register_dec_bl.
  by apply: internal_register_dec_lb.
Qed.

Definition reg_eqMixin := Equality.Mixin reg_eq_axiom.
Canonical reg_eqType := EqType register reg_eqMixin.

Lemma xreg_eq_axiom : Equality.axiom xmm_register_beq.
Proof.
  move=> x y;apply:(iffP idP).
  + by apply: internal_xmm_register_dec_bl.
  by apply: internal_xmm_register_dec_lb.
Qed.

Definition xreg_eqMixin := Equality.Mixin xreg_eq_axiom.
Canonical xreg_eqType := EqType _ xreg_eqMixin.

Lemma rflag_eq_axiom : Equality.axiom rflag_beq.
Proof.
  move=> x y;apply:(iffP idP).
  + by apply: internal_rflag_dec_bl.
  by apply: internal_rflag_dec_lb.
Qed.

Definition rflag_eqMixin := Equality.Mixin rflag_eq_axiom.
Canonical rflag_eqType := EqType rflag rflag_eqMixin.

Lemma scale_eq_axiom : Equality.axiom scale_beq.
Proof.
  move=> x y;apply:(iffP idP).
  + by apply: internal_scale_dec_bl.
  by apply: internal_scale_dec_lb.
Qed.

Definition scale_eqMixin := Equality.Mixin scale_eq_axiom.
Canonical scale_eqType := EqType scale scale_eqMixin.

Definition reg_address_beq (addr1: reg_address) addr2 :=
  match addr1, addr2 with
  | mkAddress d1 b1 s1 o1, mkAddress d2 b2 s2 o2 =>
    [&& d1 == d2, b1 == b2, s1 == s2 & o1 == o2]
  end.

Lemma reg_address_eq_axiom : Equality.axiom reg_address_beq.
Proof.
case=> [d1 b1 s1 o1] [d2 b2 s2 o2]; apply: (iffP idP) => /=.
+ by case/and4P ; do 4! move/eqP=> ->.
by case; do 4! move=> ->; rewrite !eqxx.
Qed.

Definition reg_address_eqMixin := Equality.Mixin reg_address_eq_axiom.
Canonical reg_address_eqType := EqType reg_address reg_address_eqMixin.

Definition address_beq (addr1: address) addr2 :=
  match addr1, addr2 with
  | Areg ra1, Areg ra2 => ra1 == ra2
  | Arip p1, Arip p2   => p1 == p2
  | _, _ => false
  end.

Lemma address_eq_axiom : Equality.axiom address_beq.
Proof.
 case=> [ra1 | p1] [ra2 | p2];apply: (iffP idP) => //=.
 + by move=> /eqP ->. + by move=> [->].
 + by move=> /eqP ->. + by move=> [->].
Qed.

Definition address_eqMixin := Equality.Mixin address_eq_axiom.
Canonical address_eqType := EqType address address_eqMixin.

Lemma condt_eq_axiom : Equality.axiom condt_beq.
Proof.
  move=> x y;apply:(iffP idP).
  + by apply: internal_condt_dec_bl.
  by apply: internal_condt_dec_lb.
Qed.

Definition condt_eqMixin := Equality.Mixin condt_eq_axiom.
Canonical condt_eqType := EqType condt condt_eqMixin.

(* -------------------------------------------------------------------- *)
Definition registers :=
  [:: RAX; RCX; RDX; RBX; RSP; RBP; RSI; RDI ;
      R8 ; R9 ; R10; R11; R12; R13; R14; R15 ].

Lemma registers_fin_axiom : Finite.axiom registers.
Proof. by case. Qed.

Definition reg_choiceMixin :=
  PcanChoiceMixin (FinIsCount.pickleK registers_fin_axiom).
Canonical reg_choiceType :=
  Eval hnf in ChoiceType register reg_choiceMixin.

Definition reg_countMixin :=
  PcanCountMixin (FinIsCount.pickleK registers_fin_axiom).
Canonical reg_countType :=
  Eval hnf in CountType register reg_countMixin.

Definition reg_finMixin :=
  FinMixin registers_fin_axiom.
Canonical reg_finType :=
  Eval hnf in FinType register reg_finMixin.

(* -------------------------------------------------------------------- *)
Definition xmm_registers :=
  [:: XMM0; XMM1; XMM2; XMM3; XMM4; XMM5; XMM6; XMM7; XMM8; XMM9; XMM10; XMM11; XMM12; XMM13; XMM14; XMM15 ].

Lemma xmm_registers_fin_axiom : Finite.axiom xmm_registers.
Proof. by case. Qed.

Definition xreg_choiceMixin :=
  PcanChoiceMixin (FinIsCount.pickleK xmm_registers_fin_axiom).
Canonical xreg_choiceType :=
  Eval hnf in ChoiceType xmm_register xreg_choiceMixin.

Definition xreg_countMixin :=
  PcanCountMixin (FinIsCount.pickleK xmm_registers_fin_axiom).
Canonical xreg_countType :=
  Eval hnf in CountType xmm_register xreg_countMixin.

Definition xreg_finMixin :=
  FinMixin xmm_registers_fin_axiom.
Canonical xreg_finType :=
  Eval hnf in FinType xmm_register xreg_finMixin.

(* -------------------------------------------------------------------- *)
Definition rflags := [:: CF; PF; ZF; SF; OF; DF].

Lemma rflags_fin_axiom : Finite.axiom rflags.
Proof. by case. Qed.

Definition rflag_choiceMixin :=
  PcanChoiceMixin (FinIsCount.pickleK rflags_fin_axiom).
Canonical rflag_choiceType :=
  Eval hnf in ChoiceType rflag rflag_choiceMixin.

Definition rflag_countMixin :=
  PcanCountMixin (FinIsCount.pickleK rflags_fin_axiom).
Canonical rflag_countType :=
  Eval hnf in CountType rflag rflag_countMixin.

Definition rflag_finMixin :=
  FinMixin rflags_fin_axiom.
Canonical rflag_finType :=
  Eval hnf in FinType rflag rflag_finMixin.

(* -------------------------------------------------------------------- *)
Module RegMap.
  Definition map := {ffun register -> u64}.

  Definition set (m : map) (x : register) (y : u64) : map :=
    [ffun z => if (z == x) then y else m z].
End RegMap.

(* -------------------------------------------------------------------- *)
Module XRegMap.
  Definition map := {ffun xmm_register -> u256 }.

  Definition set (m : map) (x : xmm_register) (y : u256) : map :=
    [ffun z => if (z == x) then y else m z].
End XRegMap.

(* -------------------------------------------------------------------- *)
Module RflagMap.
  Variant rflagv := Def of bool | Undef.

  Definition map := {ffun rflag -> rflagv}.

  Definition set (m : map) (x : rflag) (y : bool) : map :=
    [ffun z => if (z == x) then Def y else m z].

  Definition oset (m : map) (x : rflag) (y : rflagv) : map :=
    [ffun z => if (z == x) then y else m z].

  Definition update (m : map) (f : rflag -> option rflagv) : map :=
    [ffun rf => odflt (m rf) (f rf)].
End RflagMap.

(* -------------------------------------------------------------------- *)
Notation regmap   := RegMap.map.
Notation xregmap  := XRegMap.map.
Notation rflagmap := RflagMap.map.
Notation Def      := RflagMap.Def.
Notation Undef    := RflagMap.Undef.

Definition regmap0   : regmap   := [ffun x => 0%R].
Definition rflagmap0 : rflagmap := [ffun x => Undef].

Scheme Equality for RflagMap.rflagv.

Lemma rflagv_eq_axiom : Equality.axiom rflagv_beq.
Proof.
  move=> x y;apply:(iffP idP).
  + by apply: internal_rflagv_dec_bl.
  by apply: internal_rflagv_dec_lb.
Qed.

Definition rflagv_eqMixin := Equality.Mixin rflagv_eq_axiom.
Canonical rflagv_eqType := EqType _ rflagv_eqMixin.

(* -------------------------------------------------------------------- *)

Variant asm_arg : Type :=
  | Condt  `(condt)
  | Imm    `(ws:wsize) `(word ws)
  | Reg    `(register)
  | Adr    `(address)
  | XMM    `(xmm_register).

Notation asm_args := (seq asm_arg).

Variant implicite_arg : Type :=
  | IArflag of rflag
  | IAreg   of register.

Variant adr_kind : Type := 
  | AK_compute (* Compute the address *)
  | AK_mem.    (* Compute the address and load from memory *)

Variant arg_desc :=
| ADImplicit  of implicite_arg
| ADExplicit  of adr_kind & nat & option register.

Definition F  f   := ADImplicit (IArflag f).
Definition R  r   := ADImplicit (IAreg   r).
Definition E  n   := ADExplicit AK_mem n None.
Definition Ec n := ADExplicit AK_compute n None.
Definition Ef n r := ADExplicit AK_mem n (Some  r).

Scheme Equality for adr_kind.

Lemma adr_kind_eq_axiom : Equality.axiom adr_kind_beq.
Proof.
  move=> x y;apply:(iffP idP).
  + by apply: internal_adr_kind_dec_bl.
  by apply: internal_adr_kind_dec_lb.
Qed.

Definition adr_kind_eqMixin := Equality.Mixin adr_kind_eq_axiom.
Canonical adr_kind_eqType := EqType _ adr_kind_eqMixin.

Definition asm_arg_beq (a1 a2:asm_arg) :=
  match a1, a2 with
  | Condt t1  , Condt t2   => t1 == t2
  | Imm sz1 w1, Imm sz2 w2 => (sz1 == sz2) && (wunsigned w1 == wunsigned w2)
  | Reg r1    , Reg r2     => r1 == r2
  | Adr a1    , Adr a2     => a1 == a2
  | XMM r1    , XMM r2     => r1 == r2
  | _         , _          => false
  end.

Definition Imm_inj sz sz' w w' (e: @Imm sz w = @Imm sz' w') :
  ∃ e : sz = sz', eq_rect sz (λ s, (word s)) w sz' e = w' :=
  let 'Logic.eq_refl := e in (ex_intro _ erefl erefl).

Lemma asm_arg_eq_axiom : Equality.axiom asm_arg_beq.
Proof.
  case => [t1 | sz1 w1 | r1 | a1 | xr1] [t2 | sz2 w2 | r2 | a2 | xr2]; apply: (iffP idP) => //=.
  1, 5, 7, 9, 11: by move => /eqP ->.
  1, 4-7: by case => ->.
  + by move=> /andP [] /eqP ? /eqP; subst => /wunsigned_inj ->.
  by move=> /Imm_inj [? ];subst => /= ->;rewrite !eqxx.
Qed.

Definition asm_arg_eqMixin := Equality.Mixin asm_arg_eq_axiom.
Canonical asm_arg_eqType := EqType asm_arg asm_arg_eqMixin.

(* -------------------------------------------------------------------- *)
(* Writing a large word to register or memory *)
(* When writing to a register, depending on the instruction,
  the most significant bits are either preserved or cleared. *)
Variant msb_flag := MSB_CLEAR | MSB_MERGE.
Scheme Equality for msb_flag.

Lemma msb_flag_eq_axiom : Equality.axiom msb_flag_beq.
Proof.
  move=> x y;apply:(iffP idP).
  + by apply: internal_msb_flag_dec_bl.
  by apply: internal_msb_flag_dec_lb.
Qed.

Definition msb_flag_eqMixin := Equality.Mixin msb_flag_eq_axiom.
Canonical msb_flag_eqType := EqType msb_flag msb_flag_eqMixin.

(* -------------------------------------------------------------------- *)

Definition check_arg_dest (ad:arg_desc) (ty:stype) :=
  match ad with
  | ADImplicit _ => true
  | ADExplicit _ _ _ => ty != sbool
  end.

Inductive pp_asm_op_ext :=
  | PP_error
  | PP_name
  | PP_iname of wsize
  | PP_iname2 of wsize & wsize
  | PP_viname of velem & bool (* long *)
  | PP_viname2 of velem & velem (* source and target element sizes *)
  | PP_ct of asm_arg.

Record pp_asm_op := mk_pp_asm_op {
  pp_aop_name : string;
  pp_aop_ext  : pp_asm_op_ext;
  pp_aop_args : seq (wsize * asm_arg);
}.

Variant safe_cond :=
  | NotZero of wsize & nat. (* the nth argument of size sz is not zero *)

Record instr_desc_t := mk_instr_desc {
  (* Info for x86 sem *)
  id_msb_flag : msb_flag;
  id_tin      : seq stype;
  id_in       : seq arg_desc;
  id_tout     : seq stype;
  id_out      : seq arg_desc;
  id_semi     : sem_prod id_tin (exec (sem_tuple id_tout));
  id_check    : list asm_arg -> bool;
  id_nargs    : nat;
  (* Info for jasmin *)
  id_eq_size  : (size id_in == size id_tin) && (size id_out == size id_tout);
  id_max_imm  : option wsize;
  id_tin_narr : all is_not_sarr id_tin;
  id_str_jas  : unit -> string;
  id_check_dest : all2 check_arg_dest id_out id_tout;
  id_safe     : seq safe_cond;
  id_wsize    : wsize;  (* ..... *)
  id_pp_asm   : asm_args -> pp_asm_op;
}.
