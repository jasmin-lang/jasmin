(* Definitions shared by the Arm architectures.

 * The Arm architectures (AArch32 and AArch64) share the NZCV flag
 * register, the condition codes evaluated on it, and the flag-combination
 * description. This file holds these common definitions; the
 * architecture-specific declarations ([arm_decl], ...) re-export it.
 *)
From elpi.apps Require Import derive.std.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype seq fintype.
From mathcomp Require Import word_ssrZ.

Require Import
  expr
  flag_combination
  strings
  type
  utils.

Require Import arch_decl.

(* -------------------------------------------------------------------- *)
(* Flags. *)

#[only(eqbOK)] derive
Variant rflag : Type :=
| NF    (* Negative condition flag. *)
| ZF    (* Zero condition flag. *)
| CF    (* Carry condition flag. *)
| VF.   (* Overflow condition flag. *)

#[ export ]
Instance eqTC_rflag : eqTypeC rflag :=
  { ceqP := rflag_eqb_OK }.

Canonical rflag_eqType := @ceqT_eqType _ eqTC_rflag.

Definition rflags := [:: NF; ZF; CF; VF ].

Lemma rflag_fin_axiom : Finite.axiom rflags.
Proof. by case. Qed.

#[ export ]
Instance finTC_rflag : finTypeC rflag :=
  {
    cenum  := rflags;
    cenumP := rflag_fin_axiom;
  }.

Canonical rflag_finType := @cfinT_finType _ finTC_rflag.

Definition flag_to_string (f : rflag) : string :=
  match f with
  | NF => "NF"
  | ZF => "ZF"
  | CF => "CF"
  | VF => "VF"
  end.

#[ export ]
Instance rflag_toS : ToString lbool rflag :=
  { category  := "rflag"
  ; to_string := flag_to_string
  }.

(* -------------------------------------------------------------------- *)
(* Conditions.
   Condition codes evaluated on the NZCV flags (chapter A7.3 from the
   ARMv7-M reference manual; section C1.2.4 from the Arm ARM DDI0487).
   The always-true conditions AL and its encoding-only twin NV are
   deliberately not modeled: an unconditional instruction is simply not
   given a condition operand. *)

#[only(eqbOK)] derive
Variant condt : Type :=
| EQ_ct    (* Equal (Z == 1). *)
| NE_ct    (* Not equal (Z == 0). *)
| CS_ct    (* Carry set, unsigned higher or same (C == 1). *)
| CC_ct    (* Carry clear, unsigned lower (C == 0). *)
| MI_ct    (* Minus, negative (N == 1). *)
| PL_ct    (* Plus, positive or zero (N == 0). *)
| VS_ct    (* Overflow (V == 1). *)
| VC_ct    (* No overflow (V == 0). *)
| HI_ct    (* Unsigned higher (C == 1 && Z == 0). *)
| LS_ct    (* Unsigned lower or same (C == 0 || Z == 1). *)
| GE_ct    (* Signed greater than or equal (N == V). *)
| LT_ct    (* Signed less than (N != V). *)
| GT_ct    (* Signed greater than (Z == 0 && N == V). *)
| LE_ct.   (* Signed less than or equal (Z == 1 || N != V). *)

#[ export ]
Instance eqTC_condt : eqTypeC condt :=
  { ceqP := condt_eqb_OK }.

Canonical condt_eqType := @ceqT_eqType _ eqTC_condt.

Definition condts : seq condt :=
  [:: EQ_ct; NE_ct; CS_ct; CC_ct; MI_ct; PL_ct; VS_ct; VC_ct; HI_ct; LS_ct
    ; GE_ct; LT_ct; GT_ct; LE_ct
  ].

Lemma condt_fin_axiom : Finite.axiom condts.
Proof. by case. Qed.

#[ export ]
Instance finTC_condt : finTypeC condt :=
  {
    cenum := condts;
    cenumP := condt_fin_axiom;
  }.

Canonical condt_finType := @cfinT_finType _ finTC_condt.

Definition string_of_condt (c : condt) : string :=
  match c with
  | EQ_ct => "eq"
  | NE_ct => "ne"
  | CS_ct => "cs"
  | CC_ct => "cc"
  | MI_ct => "mi"
  | PL_ct => "pl"
  | VS_ct => "vs"
  | VC_ct => "vc"
  | HI_ct => "hi"
  | LS_ct => "ls"
  | GE_ct => "ge"
  | LT_ct => "lt"
  | GT_ct => "gt"
  | LE_ct => "le"
  end.

(* -------------------------------------------------------------------- *)
(* Evaluation of the condition codes on the NZCV flags (chapter A7.3 from
   the ARMv7-M reference manual; section C1.2.4 from the Arm ARM
   DDI0487). *)

Definition arm_eval_cond (get : rflag -> result error bool) (c : condt) :
  result error bool :=
  match c with
  | EQ_ct =>
      get ZF
  | NE_ct =>
      Let zf := get ZF in ok (~~ zf)
  | CS_ct =>
      get CF
  | CC_ct =>
      Let cf := get CF in ok (~~ cf)
  | MI_ct =>
      get NF
  | PL_ct =>
      Let nf := get NF in ok (~~ nf)
  | VS_ct =>
      get VF
  | VC_ct =>
      Let vf := get VF in ok (~~ vf)
  | HI_ct =>
      Let cf := get CF in
      Let zf := get ZF in
      ok (cf && ~~ zf)
  | LS_ct =>
      Let cf := get CF in
      Let zf := get ZF in
      ok (~~ cf || zf)
  | GE_ct =>
      Let nf := get NF in
      Let vf := get VF in
      ok (nf == vf)
  | LT_ct =>
      Let nf := get NF in
      Let vf := get VF in
      ok (nf != vf)
  | GT_ct =>
      Let zf := get ZF in
      Let nf := get NF in
      Let vf := get VF in
      ok (~~ zf && (nf == vf))
  | LE_ct =>
      Let zf := get ZF in
      Let nf := get NF in
      Let vf := get VF in
      ok (zf || (nf != vf))
  end.

(* -------------------------------------------------------------------- *)
(* Flag combinations.
   The Arm terminology is different from Intel's (chapter A7.3 from the
   ARMv7-M reference manual; section C1.2.4 from the Arm ARM DDI0487).
   - [CFC_B] is Carry clear (unsigned lower).
   - [CFC_E] is Equal.
   - [CFC_L] is Signed less than.
   - [CFC_BE] is Unsigned lower or same.
   - [CFC_LE] is Signed less than or equal. *)

Definition arm_fc_of_cfc (cfc : combine_flags_core) : flag_combination :=
  let vnf := FCVar0 in
  let vzf := FCVar1 in
  let vcf := FCVar2 in
  let vvf := FCVar3 in
  match cfc with
  | CFC_B => FCNot vcf
  | CFC_E => vzf
  | CFC_L => FCNot (FCEq vnf vvf)
  | CFC_BE => FCOr (FCNot vcf) vzf
  | CFC_LE => FCOr vzf (FCNot (FCEq vnf vvf))
  end.

#[global]
Instance arm_fcp : FlagCombinationParams :=
  {
    fc_of_cfc := arm_fc_of_cfc;
  }.

(* -------------------------------------------------------------------- *)

Definition Z_mod_lnot (z:Z) (ws:wsize) : Z :=
  (zmod_pow2 (Z.lnot z) (nat_of_wsize ws))%Z.

(* Equality between the "new" definition of Z_mod_lnot (using zmod_pow2)
   and an older definition (using mod)
 *)
Lemma Z_lnot_mod_pow2_to_mod (z:Z) (ws:wsize) :
  let m := wbase ws in
  Z_mod_lnot z ws = (Z.lnot (z mod m) mod m)%Z.
Proof.
  rewrite /Z_mod_lnot zmod_pow2E wbaseE /Z.lnot /Z.pred.
  set (n := (2 ^ Z.of_nat ws)%Z).
  assert (Haux: ((-(z mod n)) mod n = (-z) mod n)%Z).
  {
    replace (- (z mod n))%Z with ((-1) * (z mod n))%Z by ring.
    replace (-z)%Z with (-1 * z)%Z by ring.
    apply Zmult_mod_idemp_r.
  }
  symmetry.
  by rewrite Zplus_mod (Zplus_mod (-z)%Z (-1)%Z) Haux.
Qed.
