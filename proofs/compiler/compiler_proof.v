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

From mathcomp Require Import all_ssreflect all_algebra.
Require Import psem compiler_util compiler.
Require Import allocation inline_proof dead_calls_proof
               unrolling_proof constant_prop_proof dead_code_proof
               array_expansion stack_alloc_proof
               lowering_proof
               linear_proof
               psem_of_sem_proof.
Import Utf8.
Import x86_sem x86_gen.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section PROOF.

Variable cparams : compiler_params.

Hypothesis print_progP : forall s p, cparams.(print_prog) s p = p.
Hypothesis print_linearP : forall p, cparams.(print_linear) p = p.

Lemma unroll1P (fn: funname) (p p':prog) gd mem va mem' vr:
  unroll1 p = ok p' ->
  sem_call p gd mem fn va mem' vr ->
  sem_call p' gd mem fn va mem' vr.
Proof.
  rewrite /unroll1=> Heq Hsem.
  apply: (dead_code_callP Heq).
  apply: const_prop_callP.
  exact: unroll_callP.
Qed.

Lemma unrollP (fn: funname) (p p': prog) gd mem va mem' vr:
  unroll Loop.nb p = ok p' ->
  sem_call p gd mem  fn va mem' vr ->
  sem_call p' gd mem fn va mem' vr.
Proof.
  elim: Loop.nb p=> /= [p //|n Hn] p.
  apply: rbindP=> z Hz.
  case: ifP=> [_ [] ->|_ Hu Hs] //.
  apply: (Hn z) =>//.
  exact: unroll1P Hs.
Qed.

Opaque Loop.nb.

Let Ki : ∀ vr (P Q: _ → Prop),
        (∀ vr', P vr' → Q vr') →
        (∃ vr', List.Forall2 value_uincl vr vr' ∧ P vr') →
        (∃ vr', List.Forall2 value_uincl vr vr' ∧ Q vr')
    := λ vr P Q h x, let 'ex_intro vr' (conj u p) := x in ex_intro _ vr' (conj u (h vr' p)).

Let Kj : ∀ m vr (P Q: _ → _ → Prop),
        (∀ m' vr', P m' vr' → Q m' vr') →
        (∃ m' vr', List.Forall2 value_uincl vr vr' ∧ eq_mem m m' ∧ P m' vr') →
        (∃ m' vr', List.Forall2 value_uincl vr vr' ∧ eq_mem m m' ∧ Q m' vr')
    := λ m vr P Q h x,
      let 'ex_intro m' (ex_intro vr' (conj u (conj v p))) := x in
      ex_intro _ m' (ex_intro _ vr' (conj u (conj v (h m' vr' p)))).

Let Km : ∀ m vr (P: _ → Prop) (Q: _ → _ → Prop),
        (∀ vr, P vr → ∃ m' vr', List.Forall2 value_uincl vr vr' ∧ eq_mem m m' ∧ Q m' vr') →
        (∃ vr', List.Forall2 value_uincl vr vr' ∧ P vr') →
        (∃ m' vr', List.Forall2 value_uincl vr vr' ∧ eq_mem m m' ∧ Q m' vr')
  := λ m vr P Q h x,
      let 'ex_intro vr' (conj u p) := x in
      let 'ex_intro m' (ex_intro vr'' (conj u' q)) := h vr' p in
      ex_intro _ m' (ex_intro _ vr'' (conj (Forall2_trans value_uincl_trans u u') q)).

Let K : ∀ vr (P Q: _ → Prop),
        (∀ vr, P vr → ∃ vr', List.Forall2 value_uincl vr vr' ∧ Q vr') →
        (∃ vr', List.Forall2 value_uincl vr vr' ∧ P vr') →
        (∃ vr', List.Forall2 value_uincl vr vr' ∧ Q vr')
  :=
      λ vr P Q h x,
      let 'ex_intro vr1 (conj u p) := x in
      let 'ex_intro vr2 (conj v q) := h _ p in
      ex_intro _ vr2 (conj (Forall2_trans value_uincl_trans u v) q).

Let K' : ∀ vr (P Q: _ → Prop),
        (∀ vr, P vr → ∃ vr', Q vr' ∧ List.Forall2 value_uincl vr vr') →
        (∃ vr', List.Forall2 value_uincl vr vr' ∧ P vr') →
        (∃ vr', List.Forall2 value_uincl vr vr' ∧ Q vr')
  :=
      λ vr P Q h x,
      let 'ex_intro vr1 (conj u p) := x in
      let 'ex_intro vr2 (conj q v) := h _ p in
      ex_intro _ vr2 (conj (Forall2_trans value_uincl_trans u v) q).

Lemma compile_progP entries (p: prog) gd (lp: lprog) mem fn va mem' vr:
  compile_prog cparams entries p = cfok lp ->
  fn \in entries ->
  sem.sem_call p gd mem fn va mem' vr ->
  (forall f, get_fundef lp fn = Some f -> 
     exists p, Memory.alloc_stack mem (lfd_stk_size f) = ok p) ->
  ∃ mem2' vr',
    List.Forall2 value_uincl vr vr' ∧
    eq_mem mem' mem2' ∧
    lsem_fd lp gd mem fn va mem2' vr'.
Proof.
  rewrite /compile_prog.
  apply: rbindP=> p0 Hp0. rewrite !print_progP.
  apply: rbindP=> pca Hpca. rewrite !print_progP.
  apply: rbindP=> p1 Hp1. rewrite !print_progP.
  apply: rbindP=> -[] Hv.
  apply: rbindP=> pv Hpv. rewrite !print_progP.
  apply: rbindP=> -[] Hps.
  apply: rbindP=> ps' Hps'. rewrite !print_progP.
  apply: rbindP=> -[] He.
  case Hlower: fvars_correct=> //.
  apply: rbindP=> -[] He'.
  apply: rbindP=> pd Hpd. rewrite !print_progP.
  case Hpstk: (stk_alloc_prog _ pd)=> [pstk l].
  case Hpstk': (check_prog pd pstk l)=> //.
  apply: rbindP=> pl Hpl [] <-. rewrite !print_linearP.
  move=> Hin Hcall Halloc.
  have Haok : alloc_ok pstk fn mem.
  + rewrite /alloc_ok=> fd Hfd.
    move: (get_map_cfprog Hpl Hfd)=> [f' [Hf'1 Hf'2]].
    apply: rbindP Hf'1=> [fn' Hfn'] [] Hf'.
    have := Halloc _ Hf'2.
    by rewrite -Hf' /=.
  have va_refl := List_Forall2_refl va value_uincl_refl.
  apply: Kj; first by move => vr'; exact: (linear_fdP Hpl).
  apply: Km; first by move => vr' Hvr'; apply: (stack_alloc_proof.check_progP Hpstk' _ Haok); exact: Hvr'.
  apply: Ki; first by move => vr'; exact: (dead_code_callP Hpd).
  apply: K'; first by move => vr' Hvr'; apply: (CheckAllocReg.alloc_callP He'); exact: Hvr'.
  apply: Ki; first by move => vr'; exact: (lower_callP _ _ _ Hlower).
  apply: K'; first by move => vr' Hvr'; apply: (CheckExpansion.alloc_callP He); exact: Hvr'.
  apply: K'; first by move => vr' Hvr'; apply: (remove_init_fdP va_refl); exact: Hvr'.
  apply: Ki; first by move => vr'; exact: (dead_code_callP Hps').
  apply: K'; first by move => vr' Hvr'; apply: (CheckAllocReg.alloc_callP Hps); exact: Hvr'.
  apply: Ki; first by move => vr'; exact: (dead_code_callP Hpv).
  apply: K'; first by move => vr' Hvr'; apply: (CheckAllocReg.alloc_callP Hv); exact: Hvr'.
  apply: Ki; first by move => vr'; exact: const_prop_callP.
  apply: Ki; first by move => vr'; exact: (unrollP Hp1).
  apply: Ki; first by move => vr'; exact: (dead_calls_err_seqP Hpca).
  apply: K'; first by move => vr' Hvr'; apply: (inline_call_errP Hp0 va_refl); exact: Hvr'.
  apply: Ki; first by move => vr'; exact: psem_call.
  exists vr; split => //.
  exact: (List_Forall2_refl _ value_uincl_refl).
Qed.

Lemma compile_prog_to_x86P entries (p: prog) (gd: glob_defs) (xp: xprog) m1 fn va m2 vr :
  compile_prog_to_x86 cparams entries p = cfok xp →
  fn \in entries →
  sem.sem_call p gd m1 fn va m2 vr →
  (∀ f, get_fundef xp fn = Some f →
     ∃ p, Memory.alloc_stack m1 (xfd_stk_size f) = ok p) →
  ∃ fd va',
    get_fundef p fn = Some fd ∧
    mapM2 ErrType truncate_val (f_tyin fd) va = ok va' ∧
  ∃ fd', get_fundef xp fn = Some fd' ∧
  ∀ st1,
    List.Forall2 value_uincl va' (get_reg_values st1 fd'.(xfd_arg)) →
    st1.(xmem) = m1 →
  ∃ st2,
    x86sem_fd xp gd fn st1 st2 ∧
    List.Forall2 value_uincl vr (get_reg_values st2 fd'.(xfd_res)) ∧
    eq_mem m2 st2.(xmem).
Proof.
apply: rbindP=> lp hlp; t_xrbindP => _ /assertP /allP ok_sig hxp hfn hsem hsafe.
have hlsem := compile_progP hlp hfn hsem.
case: hlsem.
- move => fd hfd.
  have [xfd [hxfd]] := get_map_cfprog hxp hfd.
  by move => /hsafe; rewrite (assemble_fd_stk_size hxfd).
move/ok_sig: hfn.
case: hsem => {m1 m2 hsafe fn va vr} m1 m2 fn fd va va' st1 vm2 vr vr1 ok_fd ok_va _ _ _ _ hsig m2' [vr'] [ok_vr'] [hm2' hlsem].
exists fd, va.
split; first exact: ok_fd.
split; first exact: ok_va.
case: (assemble_fdP hxp hlsem) => fd' [va1] [ok_fd'] [ok_va1] [xd] [ok_xd h].
move: ok_va1.
have -> : lfd_tyin fd' = f_tyin fd.
- by move: hsig; rewrite /check_signature ok_fd' ok_fd => /eqP [].
rewrite ok_va => - [?]; subst va1.
exists xd; split; first exact: ok_xd.
move => st hva hm1.
have [st2 [hxsem [hvr' hm2]]] := h st hva hm1.
exists st2.
split; first exact: hxsem.
split; last by rewrite hm2.
exact: (Forall2_trans value_uincl_trans ok_vr' hvr').
Qed.

End PROOF.
