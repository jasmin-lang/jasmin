From mathcomp Require Import ssreflect ssrfun ssrbool.
Require Import psem.
Require Export toEC_jazz.
Require Import normalize_cond_proof.
Require Import refresh_for_proof.
Import Utf8.

Section TOEC_PROOF.

Context
  {wsw : WithSubWord}
  {dc : DirectCall}
  {asm_op syscall_state : Type}
  {ep : EstateParams syscall_state}
  {spp : SemPexprParams}
  {sip : SemInstrParams asm_op syscall_state}
  {E E0 : Type -> Type}
  {wE : with_Error E E0}
  {rE0 : EventRels E0}
  {rE0_trans : EventRels_trans rE0 rE0 rE0}
.

#[local] Existing Instance progUnit.
#[local] Existing Instance sCP_unit.

Context
  (fresh_var_ident : v_kind -> instr_info -> string -> atype -> Ident.ident)
  (p p' : uprog)
  (ev : extra_val_t)
  (toEC_ok : toEC_prog fresh_var_ident p = p')
  (fresh_var_ident_fresh :
     forall (ii : instr_info) (x : var),
       ~ Sv.In (refresh_for_clone fresh_var_ident ii x)
         (vars_p (p_funcs (normalize_cond_prog p))))
.

Lemma it_toEC_progP fn :
  wiequiv_f p p' ev ev (rpreF (eS := eq_spec)) fn fn (rpostF (eS := eq_spec)).
Proof using toEC_ok rE0_trans fresh_var_ident_fresh.
have hp1 :=
  normalize_cond_proof
    (wsw:=wsw) (dc:=dc) (asm_op:=asm_op) (syscall_state:=syscall_state)
    (ep:=ep) (spp:=spp) (sip:=sip) (E:=E) (E0:=E0) (wE:=wE) (rE0:=rE0)
    (p := p) (fn := fn) ev erefl.
have hp2 :=
  refresh_for_proof
    (wsw:=wsw) (dc:=dc) (asm_op:=asm_op) (syscall_state:=syscall_state)
    (ep:=ep) (spp:=spp) (sip:=sip) (E:=E) (E0:=E0) (wE:=wE) (rE0:=rE0)
    (fresh_var_ident := fresh_var_ident) (always := false)
    (p := normalize_cond_prog p) (fn := fn) ev toEC_ok fresh_var_ident_fresh.
move: hp1 hp2; apply wiequiv_f_trans => //.
- by move=> fs1 fs3 [_ <-]; exists fs1.
by move=> fs1 fs2 fs3 r1 r3 _ _ [r2 -> ->].
Qed.

End TOEC_PROOF.
