(* -------------------------------------------------------------------- *)
From mathcomp Require Import all_ssreflect all_algebra.
From CoqWord Require Import ssrZ.
Require Import xseq strings utils var type values sopn expr arch_decl.
Require Import compiler_util.

Set   Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

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

Definition vflags      := sv_of_list to_var rflags.
Definition vregisters  := sv_of_list to_var registers.
Definition vxregisters := sv_of_list to_var xregisters.

Definition all_vars_def := 
  Sv.union (Sv.union vregisters vxregisters) vflags.

End ARCH.

(* Extra ops are non-existing architecture-specific asm instructions that we
   replace by real asm instructions during the asmgen pass.
*)
Class asm_extra (reg regx xreg rflag cond asm_op extra_op : Type) := 
  { _asm   :> asm reg regx xreg rflag cond asm_op
  ; _extra :> asmOp extra_op (* description of extra ops *)
  ; to_asm : instr_info -> extra_op -> lvals -> pexprs -> cexec (seq (asm_op_msb_t * lvals * pexprs))
      (* how to compile extra ops into asm op *)
  }.

Definition extra_op_t {reg regx xreg rflag cond asm_op extra_op} {asm_e : asm_extra reg regx xreg rflag cond asm_op extra_op} := extra_op.

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
