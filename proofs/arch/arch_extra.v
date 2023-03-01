(* -------------------------------------------------------------------- *)
From mathcomp Require Import all_ssreflect all_algebra.
Require Import xseq strings utils var type values sopn expr arch_decl.
Require Import compiler_util.

Set   Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* should this Section be moved elsewhere? *)
Section Section.

Context `{tS : ToString}.

Definition of_string (s : string) :=
  assoc strings s.

(* -------------------------------------------------------------------- *)
Lemma to_stringK : pcancel to_string of_string.
Proof.
move=> r; rewrite /of_string stringsE; apply /(@assocP _ ceqT_eqType).
+ rewrite -map_comp (map_inj_uniq (T1:=ceqT_eqType)) //.
  + by apply: (enum_uniq (T:=cfinT_finType)).
  by apply inj_to_string.
apply: (map_f (T1:=ceqT_eqType) (T2:=prod_eqType _ ceqT_eqType)).
by rewrite (mem_enum (T:=cfinT_finType)).
Qed.

(* -------------------------------------------------------------------- *)

Lemma of_stringI s r : of_string s = Some r -> to_string r = s.
Proof.
  have h := to_stringK r.
  apply : (assoc_inj (U:= ceqT_eqType) _ h).
  by rewrite stringsE -map_comp (map_inj_uniq (T1:=ceqT_eqType)) ?(enum_uniq (T:=cfinT_finType)).
Qed.

(* -------------------------------------------------------------------- *)
Definition to_var r :=
  {| vtype := rtype; vname := to_string r |}.

Definition of_var (v:var) :=
  if v.(vtype) == rtype then of_string v.(vname)
  else None.

Lemma of_varP v r : of_var v = Some r <-> v.(vtype) = rtype /\ of_string v.(vname) = Some r.
Proof. by rewrite /of_var; split=> [ | []/eqP -> ?]; first case: eqP. Qed.

Lemma to_varK : pcancel to_var of_var.
Proof. by move=> ?; rewrite /to_var /of_var /= eq_refl to_stringK. Qed.

Lemma inj_to_var : injective to_var.
Proof. apply: pcan_inj to_varK. Qed.
Global Arguments inj_to_var {_ _}.

Lemma of_varI {v r} : of_var v = Some r -> to_var r = v.
Proof.
  rewrite /of_var /= /to_var; case: eqP => // heq /of_stringI.
  by case: v heq => /= ?? -> <-.
Qed.

Lemma inj_of_var {v1 v2 r} : of_var v1 = Some r -> of_var v2 = Some r -> v1 = v2.
Proof. by move=> /of_varI <- /of_varI <-. Qed.

End Section.

Section ARCH.

Context `{arch : arch_decl}.

Definition sopn_implicit_arg (i: implicit_arg) :=
  match i with
  | IArflag r => sopn.IArflag (to_var r)
  | IAreg   r => sopn.IArflag (to_var r)
  end.

Definition sopn_arg_desc (ad:arg_desc) :=
  match ad with
  | ADImplicit ia => sopn.ADImplicit (sopn_implicit_arg ia)
  | ADExplicit _ n ox => sopn.ADExplicit n (omap to_var ox)
  end.

End ARCH.

(* Extra ops are non-existing architecture-specific asm instructions that we
   replace by real asm instructions during the asmgen pass.
*)
Class asm_extra (reg xreg rflag cond asm_op extra_op : Type) := 
  { _asm   :> asm reg xreg rflag cond asm_op
  ; _extra :> asmOp extra_op (* description of extra ops *)
  ; to_asm : instr_info -> extra_op -> lvals -> pexprs -> cexec (asm_op_msb_t * lvals * pexprs)
      (* how to compile extra ops into asm op *)
  }.

Definition extra_op_t {reg xreg rflag cond asm_op extra_op} {asm_e : asm_extra reg xreg rflag cond asm_op extra_op} := extra_op.

Section AsmOpI.

Context `{asm_e : asm_extra}.

Inductive extended_op := 
  | BaseOp of asm_op_msb_t
  | ExtOp of extra_op_t.

Definition extended_op_beq o1 o2 := 
  match o1, o2 with
  | BaseOp o1, BaseOp o2 => eq_op (T:= prod_eqType _ ceqT_eqType) o1 o2
  | ExtOp o1, ExtOp o2 => o1 == o2 ::>
  | _, _               => false
  end.

Lemma extended_op_eq_axiom : Equality.axiom extended_op_beq.
Proof.
  by case=> [] o1 [] o2 /=; (constructor || apply: reflect_inj eqP => ?? []).
Qed.

Definition extended_op_eqMixin := Equality.Mixin extended_op_eq_axiom.
Definition extended_op_eqType := EqType extended_op extended_op_eqMixin.

Definition get_instr_desc (o: extended_op) : instruction_desc :=
 match o with
 | BaseOp o =>
   let id := instr_desc o in
   {| str      := id.(id_str_jas)
    ; tin      := id.(id_tin)
    ; i_in     := map sopn_arg_desc id.(id_in)
    ; i_out    := map sopn_arg_desc id.(id_out)
    ; tout     := id.(id_tout)
    ; semi     := id.(id_semi)
    ; semu     := @vuincl_app_sopn_v _ _ id.(id_semi) id.(id_tin_narr)
    ; wsizei   := id.(id_wsize)
    ; i_safe   := id.(id_safe) |}
 | ExtOp o => asm_op_instr o
 end.

Instance eqTC_extended_op : eqTypeC extended_op :=
  { ceqP := extended_op_eq_axiom }.

Global Instance asm_opI : asmOp extended_op :=
  { sopn.asm_op_instr := get_instr_desc }.

End AsmOpI.
