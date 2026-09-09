From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.
Require Import psem.
Require Import arch_decl arch_extra sem_params_of_arch_extra.
Require Export toEC_jazz.
Require Import normalize_cond_proof.
Require Import refresh_for_proof.
Require Import init_local_arrays_proof.
Require Import for_to_while_proof.
Require Import flatten_while_proof.
Require Import remove_baseop_casts_proof.
Require Import normalize_calls_proof.
Require Import make_coercions_explicit_proof.
Require Import remove_nullary_opns_proof.
Require Import legalize_names_proof.
Import Utf8.

Section TOEC_PROOF.

Context
  {reg regx xreg rflag cond asm_op extra_op : Type}
  {asm_e : asm_extra reg regx xreg rflag cond asm_op extra_op}
  {syscall_state : Type}
  {scs : syscall_sem syscall_state}
  {spp : SemPexprParams}
  {E E0 : Type -> Type}
  {wE : with_Error E E0}
  {rE0 : EventRels E0}
  {rE0_trans : EventRels_trans rE0 rE0 rE0}
.

#[local] Existing Instance progUnit.
#[local] Existing Instance sCP_unit.
#[local] Existing Instance sip_of_asm_e.
#[local] Existing Instance indirect_c.
(* [make_coercions_explicit_proof] (EJ-10) only holds under [nosubword]
   (its type-soundness argument needs a variable's runtime value to have
   exactly its declared [vtype]); pinning it here fixes the ambient
   [WithSubWord] instance for the WHOLE composed pipeline lemma below, the
   same way [indirect_c] is pinned for [dc] just above. Every other pass in
   this file remains generic in its own `{wsw}` Context and is specialized
   to [nosubword] only at its own call site below, mirroring how the other
   five passes are specialized to [indirect_c] for `dc`. *)
#[local] Existing Instance nosubword.
(* Likewise, [make_coercions_explicit_proof] pins its own [EstateParams]
   instance to [ep_of_asm_e] (needed so the [PointerData]/[MSFsize] pair
   [sopn_tin] resolves to at its call sites matches the one the pass itself
   uses, see the comment in [make_coercions_explicit_proof.v]). Mirroring
   [wsw]/[dc] above: [ep] is removed from this file's own [Context] and
   every earlier per-pass composition call is specialized to
   [ep := ep_of_asm_e] explicitly at its own call site. *)
#[local] Existing Instance ep_of_asm_e.

Context
  (fresh_var_ident : v_kind -> instr_info -> string -> atype -> Ident.ident)
  (rename : funname -> var -> Ident.ident)
  (normal : bool)
  (p p' : uprog)
  (ev : extra_val_t)
  (toEC_ok : toEC_prog fresh_var_ident rename normal p = ok p')
.

(* [sip_of_asm_e] fully applied: with the [asm_extra] context fixing the
   program's op type to [extended_op], relying on the ambient [sip_of_asm_e]
   instance (rather than passing it fully explicit) makes ssreflect's [have]
   generalize the still-implicit [reg]/.../[scs] arguments into the produced
   term instead of resolving them, so every per-pass lemma call below spells
   [sip] out fully applied. *)
Notation the_sip :=
  (@sip_of_asm_e reg regx xreg rflag cond asm_op extra_op asm_e
     syscall_state scs) (only parsing).

(* Same [have]-generalizes-typeclass-implicits gotcha as [the_sip] above,
   for [ep_of_asm_e] (pinned in place of the generic [{ep}] Context, see the
   comment on [#[local] Existing Instance ep_of_asm_e] above). *)
Notation the_ep :=
  (@ep_of_asm_e reg regx xreg rflag cond asm_op extra_op asm_e
     syscall_state scs) (only parsing).

Lemma it_toEC_progP fn :
  wiequiv_f p p' ev ev
    (rpreF (eS := uincl_spec)) fn fn (rpostF (eS := uincl_spec)).
Proof using toEC_ok rE0_trans.
move: toEC_ok; rewrite /toEC_prog.
t_xrbindP => p1 hrefresh p2 hp2eq p4 hremove p5 hnormalize p6 hmce hlegalize.
have hp1 :=
  normalize_cond_proof
    (wsw:=nosubword) (dc:=indirect_c) (syscall_state:=syscall_state)
    (ep:=the_ep) (spp:=spp) (sip:=the_sip) (E:=E) (E0:=E0) (wE:=wE) (rE0:=rE0)
    (p := p) (fn := fn) ev erefl.
have hp2 :=
  refresh_for_proof
    (wsw:=nosubword) (dc:=indirect_c) (syscall_state:=syscall_state)
    (ep:=the_ep) (spp:=spp) (sip:=the_sip) (E:=E) (E0:=E0) (wE:=wE) (rE0:=rE0)
    (fresh_var_ident := fresh_var_ident) (always := false)
    (p := normalize_cond_prog p) (fn := fn) ev hrefresh.
assert (hp12 :
  wiequiv_f p (to_uprog p1) ev ev
    (rpreF (eS := eq_spec)) fn fn (rpostF (eS := eq_spec))).
- move: hp1 hp2; apply wiequiv_f_trans => //.
  + by move=> fs1 fs3 [_ <-]; exists fs1.
  by move=> fs1 fs2 fs3 r1 r3 _ _ [r2 -> ->].
have hp2i :=
  init_local_arrays_proof
    (wsw:=nosubword) (dc:=indirect_c) (syscall_state:=syscall_state)
    (ep:=the_ep) (spp:=spp) (sip:=the_sip) (E:=E) (E0:=E0) (wE:=wE) (rE0:=rE0)
    (p := to_uprog p1) (fn := fn) ev
    (erefl (init_local_arrays_prog (to_uprog p1))).
assert (hp12i :
  wiequiv_f p (to_uprog (init_local_arrays_prog p1)) ev ev
    (rpreF (eS := eq_spec)) fn fn (rpostF (eS := eq_spec))).
- move: hp12 hp2i; apply wiequiv_f_trans => //.
  + by move=> fs1 fs3 [_ <-]; exists fs1.
  by move=> fs1 fs2 fs3 r1 r3 _ _ [r2 -> ->].
assert (hp123 :
  wiequiv_f p (to_uprog p2) ev ev
    (rpreF (eS := eq_spec)) fn fn (rpostF (eS := eq_spec))).
- move: hp2eq; case: normal => /=.
  + move=> hp3.
    have hp4 :=
      for_to_while_proof
        (wsw:=nosubword) (dc:=indirect_c) (syscall_state:=syscall_state)
        (ep:=the_ep) (spp:=spp) (sip:=the_sip) (E:=E) (E0:=E0) (wE:=wE)
        (rE0:=rE0)
        (fresh_var_ident := fresh_var_ident)
        (p := init_local_arrays_prog p1) (fn := fn) ev hp3.
    move: hp12i hp4; apply wiequiv_f_trans => //.
    * by move=> fs1 fs3 [_ <-]; exists fs1.
    by move=> fs1 fs2 fs3 r1 r3 _ _ [r2 -> ->].
  by move=> /ok_inj <-; exact hp12i.
have hp5 :=
  flatten_while_proof
    (wsw:=nosubword) (dc:=indirect_c) (syscall_state:=syscall_state)
    (ep:=the_ep) (spp:=spp) (sip:=the_sip) (E:=E) (E0:=E0) (wE:=wE) (rE0:=rE0)
    (p := p2) (fn := fn) ev (erefl (flatten_while_prog p2)).
assert (hp1235 :
  wiequiv_f p (flatten_while_prog p2) ev ev
    (rpreF (eS := eq_spec)) fn fn (rpostF (eS := eq_spec))).
- move: hp123 hp5; apply wiequiv_f_trans => //.
  + by move=> fs1 fs3 [_ <-]; exists fs1.
  by move=> fs1 fs2 fs3 r1 r3 _ _ [r2 -> ->].
have hp6 :=
  remove_baseop_casts_proof
    (wsw:=nosubword) (dc:=indirect_c) (syscall_state:=syscall_state)
    (scs:=scs)
    (ep:=the_ep) (spp:=spp) (E:=E) (E0:=E0) (wE:=wE) (rE0:=rE0)
    (fresh_var_ident := fresh_var_ident)
    (p := flatten_while_prog p2) (fn := fn) ev hremove.
assert (hp12356 :
  wiequiv_f p (to_uprog p4) ev ev
    (rpreF (eS := eq_spec)) fn fn (rpostF (eS := eq_spec))).
- move: hp1235 hp6; apply wiequiv_f_trans => //.
  + by move=> fs1 fs3 [_ <-]; exists fs1.
  by move=> fs1 fs2 fs3 r1 r3 _ _ [r2 -> ->].
have hp7 :=
  normalize_calls_proof
    (wsw:=nosubword) (syscall_state:=syscall_state) (scs:=scs)
    (ep:=the_ep) (spp:=spp) (E:=E) (E0:=E0) (wE:=wE) (rE0:=rE0)
    (fresh_var_ident := fresh_var_ident)
    (p := p4) (fn := fn) ev hnormalize.
assert (hp123567 :
  wiequiv_f p p5 ev ev
    (rpreF (eS := eq_spec)) fn fn (rpostF (eS := eq_spec))).
- move: hp12356 hp7; apply wiequiv_f_trans => //.
  + by move=> fs1 fs3 [_ <-]; exists fs1.
  by move=> fs1 fs2 fs3 r1 r3 _ _ [r2 -> ->].
have hp8 :=
  make_coercions_explicit_proof
    (syscall_state:=syscall_state) (scs:=scs)
    (spp:=spp) (E:=E) (E0:=E0) (wE:=wE) (rE0:=rE0)
    (p := p5) (fn := fn) ev hmce.
assert (hp12345678 :
  wiequiv_f p p6 ev ev
    (rpreF (eS := eq_spec)) fn fn (rpostF (eS := eq_spec))).
- move: hp123567 hp8; apply wiequiv_f_trans => //.
  + by move=> fs1 fs3 [_ <-]; exists fs1.
  by move=> fs1 fs2 fs3 r1 r3 _ _ [r2 -> ->].
pose p7 : _uprog := if normal then remove_nullary_opns_prog p6 else p6.
assert (hp9 :
  wiequiv_f p p7 ev ev
    (rpreF (eS := eq_spec)) fn fn (rpostF (eS := eq_spec))).
- rewrite /p7; case: normal => /=; last exact hp12345678.
  have hp9' :=
    remove_nullary_opns_proof
      (wsw:=nosubword) (dc:=indirect_c) (syscall_state:=syscall_state)
      (ep:=the_ep) (spp:=spp) (sip:=the_sip) (E:=E) (E0:=E0) (wE:=wE)
      (rE0:=rE0)
      (p := p6) (fn := fn) ev (erefl (remove_nullary_opns_prog p6)).
  move: hp12345678 hp9'; apply wiequiv_f_trans => //.
  + by move=> fs1 fs3 [_ <-]; exists fs1.
  by move=> fs1 fs2 fs3 r1 r3 _ _ [r2 -> ->].
have hp10 :=
  legalize_names_proof
    (dc:=indirect_c) (syscall_state:=syscall_state)
    (ep:=the_ep) (spp:=spp) (sip:=the_sip) (E:=E) (E0:=E0) (wE:=wE)
    (rE0:=rE0) (rE0_trans := rE0_trans)
    (rename := rename) (p := p7) (p' := p') (fn := fn)
    ev hlegalize.
move: hp9 hp10; apply wiequiv_f_trans => //.
+ by move=> fs1 fs3 h; exists fs1.
by move=> fs1 fs2 fs3 r1 r3 _ _ [r2 -> h].
Qed.

End TOEC_PROOF.
