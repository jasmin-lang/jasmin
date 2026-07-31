From mathcomp Require Import ssreflect ssrfun ssrbool.
Require Import psem.
Require Export toEC_jazz.
Require Import normalize_cond_proof.
Require Import refresh_for_proof.
Require Import for_to_while_proof.
Require Import flatten_while_proof.
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
  (normal : bool)
  (p p' : uprog)
  (ev : extra_val_t)
  (toEC_ok : toEC_prog fresh_var_ident normal p = ok p')
.

Lemma it_toEC_progP fn :
  wiequiv_f p p' ev ev (rpreF (eS := eq_spec)) fn fn (rpostF (eS := eq_spec)).
Proof using toEC_ok rE0_trans.
move: toEC_ok; rewrite /toEC_prog; t_xrbindP => p1 hrefresh p2 hp2eq hflatten.
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
    (p := normalize_cond_prog p) (fn := fn) ev hrefresh.
have hp12 :
  wiequiv_f p (to_uprog p1) ev ev
    (rpreF (eS := eq_spec)) fn fn (rpostF (eS := eq_spec)).
- move: hp1 hp2; apply wiequiv_f_trans => //.
  + by move=> fs1 fs3 [_ <-]; exists fs1.
  by move=> fs1 fs2 fs3 r1 r3 _ _ [r2 -> ->].
have hp123 :
  wiequiv_f p (to_uprog p2) ev ev
    (rpreF (eS := eq_spec)) fn fn (rpostF (eS := eq_spec)).
- move: hp2eq; case: normal => /=.
  + move=> hp3.
    have hp4 :=
      for_to_while_proof
        (wsw:=wsw) (dc:=dc) (asm_op:=asm_op) (syscall_state:=syscall_state)
        (ep:=ep) (spp:=spp) (sip:=sip) (E:=E) (E0:=E0) (wE:=wE) (rE0:=rE0)
        (fresh_var_ident := fresh_var_ident) (p := p1) (fn := fn) ev hp3.
    move: hp12 hp4; apply wiequiv_f_trans => //.
    * by move=> fs1 fs3 [_ <-]; exists fs1.
    by move=> fs1 fs2 fs3 r1 r3 _ _ [r2 -> ->].
  by move=> /ok_inj <-; exact hp12.
have hp5 :=
  flatten_while_proof
    (wsw:=wsw) (dc:=dc) (asm_op:=asm_op) (syscall_state:=syscall_state)
    (ep:=ep) (spp:=spp) (sip:=sip) (E:=E) (E0:=E0) (wE:=wE) (rE0:=rE0)
    (p := p2) (fn := fn) ev hflatten.
move: hp123 hp5; apply wiequiv_f_trans => //.
- by move=> fs1 fs3 [_ <-]; exists fs1.
by move=> fs1 fs2 fs3 r1 r3 _ _ [r2 -> ->].
Qed.

End TOEC_PROOF.
