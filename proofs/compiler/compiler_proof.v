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
               makeReferenceArguments_proof
               array_init_proof
               unrolling_proof constant_prop_proof dead_code_proof
               array_expansion array_expansion_proof remove_globals_proof stack_alloc_proof_2
               lowering_proof
               linear_proof
               merge_varmaps_proof
               psem_of_sem_proof.
Import Utf8.
Import x86_sem x86_gen.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section PROOF.

Variable cparams : compiler_params.

Hypothesis print_uprogP : forall s p, cparams.(print_uprog) s p = p.
Hypothesis print_sprogP : forall s p, cparams.(print_sprog) s p = p.
Hypothesis print_linearP : forall p, cparams.(print_linear) p = p.

Lemma unroll1P (fn: funname) (p p':uprog) ev mem va va' mem' vr:
  unroll1 p = ok p' ->
  sem_call p ev mem fn va mem' vr ->
  List.Forall2 value_uincl va va' ->
  exists vr', sem_call p' ev mem fn va' mem' vr' /\ List.Forall2 value_uincl vr vr'.
Proof.
  rewrite /unroll1=> Heq Hsem Hall.
  have hsemu := unroll_callP Hsem.
  have [vr' [hsemc hall']]:= const_prop_callP hsemu Hall.
  have Hall'' : List.Forall2 value_uincl va' va'. by apply List_Forall2_refl.
  have [vr'' [hsemc' hv]] := dead_code_callPu Heq Hall'' hsemc.
  exists vr''; split => //. apply: Forall2_trans hall' hv. 
  move=> v1 v2 v3 h1 h2. by apply: value_uincl_trans h1 h2.
Qed.


Lemma unrollP (fn: funname) (p p': prog) ev mem va va' mem' vr:
  unroll Loop.nb p = ok p' ->
  sem_call p ev mem  fn va mem' vr ->
  List.Forall2 value_uincl va va' ->
  exists vr', sem_call p' ev mem fn va' mem' vr' /\ List.Forall2 value_uincl vr vr'.
Proof.
  elim: Loop.nb p va va' vr => /= [p //|n Hn] p va va' vr.
  apply: rbindP=> z Hz.
  case: ifP=> [_ [] ->|_ Hu Hs Hall].
  + by move=> /sem_call_uincl h/h{h}.
  have [vr' [hsem1 hall1]]:= unroll1P Hz Hs Hall.
  have [vr'' [hsem2 hall2]]:= Hn _ _ _ _ Hu hsem1 (List_Forall2_refl _ value_uincl_refl).
  exists vr'';split => //.
  by apply: Forall2_trans value_uincl_trans hall1 hall2.
Qed.

Opaque Loop.nb.

Let Ki : ∀ vr (P Q: _ → Prop),
        (∀ vr', P vr' → Q vr') →
        (exists2 vr', List.Forall2 value_uincl vr vr' & P vr') →
        (exists2 vr', List.Forall2 value_uincl vr vr' & Q vr')
    := λ vr P Q h x, let 'ex_intro2 vr' u p := x in ex_intro2 _ _ vr' u (h vr' p).

Let K : ∀ vr (P Q: _ → Prop),
        (∀ vr, P vr → ∃ vr', Q vr' ∧ List.Forall2 value_uincl vr vr') →
        (exists2 vr', List.Forall2 value_uincl vr vr' & P vr') →
        (exists2 vr', List.Forall2 value_uincl vr vr' & Q vr')
  :=
      λ vr P Q h x,
      let 'ex_intro2 vr1 u p := x in
      let 'ex_intro vr2 (conj q v) := h _ p in
      ex_intro2 _ _ vr2 (Forall2_trans value_uincl_trans u v) q.

Lemma compiler_first_partP entries (p: prog) (p': uprog) m fn va m' vr :
  compiler_first_part cparams entries p = ok p' →
  fn \in entries →
  sem.sem_call p m fn va m' vr →
  exists2 vr',
    List.Forall2 value_uincl vr vr' &
    psem.sem_call p' tt m fn va m' vr'.
Proof.
  rewrite /compiler_first_part; t_xrbindP => pa.
  rewrite print_uprogP => ok_pa pb.
  rewrite print_uprogP => ok_pb pc.
  rewrite print_uprogP => ok_pc [].
  rewrite !print_uprogP => ok_pd pe ok_pe.
  rewrite !print_uprogP => pf ok_pf pg.
  rewrite !print_uprogP => ok_pg ph ok_ph _ /assertP.
  rewrite print_uprogP => ok_fvars.
  rewrite print_uprogP => <- {p'} ok_fn exec_p.
  apply: Ki; first by move => vr'; apply: (lower_callP (lowering_opt cparams) (warning cparams) (is_var_in_memory cparams) ok_fvars).
  apply: Ki; first by move => vr'; apply: (makeReferenceArguments_callP ok_ph).
  apply: Ki; first by move => vr'; apply: (RGP.remove_globP ok_pg).
  apply: Ki; first by move=> vr'; apply:(expand_callP ok_pf).
  have va_refl := List_Forall2_refl va value_uincl_refl.
  apply: K; first by move =>vr'; apply: (remove_init_fdPu _ va_refl).
  apply: K; first by move => vr' Hvr'; apply: (dead_code_callPu ok_pe va_refl); exact: Hvr'.
  apply: K; first by move => vr'; apply: (CheckAllocRegU.alloc_callP ok_pd).
  rewrite surj_prog.
  apply: K; first by move => vr' Hvr'; apply: (const_prop_callP _ va_refl); exact: Hvr'.
  apply: K; first by move => vr' Hvr'; apply: (unrollP ok_pc _ va_refl); exact: Hvr'.
  apply: Ki; first by move => vr'; exact: (dead_calls_err_seqP (sCP:= sCP_unit) ok_pb).
  apply: K; first by move => vr' Hvr'; apply: (inline_call_errP ok_pa va_refl); exact: Hvr'.
  apply: Ki; first by move => vr'; apply: (add_init_fdP).
  apply: Ki; first by move => vr'; exact: psem_call.
  exists vr => //.
  exact: (List_Forall2_refl _ value_uincl_refl).
Qed.

Lemma check_removeturnP entries remove_return b :
  check_removeturn entries remove_return = ok b →
  ∀ fn, fn \in entries → remove_return fn = None.
Proof.
  move => /assertP /eqP h fn /(in_pmap remove_return).
  case: (remove_return fn) => // r.
  by rewrite h.
Qed.

Lemma compiler_third_partP entries (p: sprog) (p': sprog) (gd: pointer) m fn va m' vr :
  compiler_third_part cparams entries p = ok p' →
  fn \in entries →
  psem.sem_call p gd m fn va m' vr →
  exists2 vr',
    List.Forall2 value_uincl vr vr' &
    psem.sem_call p' gd m fn va m' vr'.
Proof.
  rewrite /compiler_third_part; t_xrbindP.
  move => _ /check_removeturnP ok_rr pa ok_pa [].
  rewrite !print_sprogP => ok_pb pc ok_pc.
  rewrite print_sprogP => <- {p'} ok_fn exec_p.
  have va_refl : List.Forall2 value_uincl va va. apply List_Forall2_refl. done.
  (*apply: Ki; first by move => vr' Hvr'; apply: (dead_code_callPs ok_pc va_refl); exact: Hvr'.
  apply: K; first by move => vr'; apply: (CheckAllocRegS.alloc_callP ok_pb).
  rewrite surj_prog.
  exists vr; first exact: (List_Forall2_refl _ value_uincl_refl).
  have := dead_code_tokeep_callPs ok_pa exec_p.
  by rewrite /fn_keep_only ok_rr.*)
Admitted.

(*
Let Kj : ∀ rip glob m vr (P Q: _ → _ → Prop),
        (∀ m' vr', P m' vr' → Q m' vr') →
        (∃ m' vr', List.Forall2 value_uincl vr vr' ∧ extend_mem m m' rip glob ∧ P m' vr') →
        (∃ m' vr', List.Forall2 value_uincl vr vr' ∧ extend_mem m m' rip glob ∧ Q m' vr')
    := λ rip glob m vr P Q h x,
      let 'ex_intro m' (ex_intro vr' (conj u (conj v p))) := x in
      ex_intro _ m' (ex_intro _ vr' (conj u (conj v (h m' vr' p)))).

Let Km : ∀ rip glob m vr (P: _ → Prop) (Q: _ → _ → Prop),
        (∀ vr, P vr → ∃ m' vr', List.Forall2 value_uincl vr vr' ∧ extend_mem m m' rip glob ∧ Q m' vr') →
        (∃ vr', List.Forall2 value_uincl vr vr' ∧ P vr') →
        (∃ m' vr', List.Forall2 value_uincl vr vr' ∧ extend_mem m m' rip glob ∧ Q m' vr')
  := λ rip glob m vr P Q h x,
      let 'ex_intro vr' (conj u p) := x in
      let 'ex_intro m' (ex_intro vr'' (conj u' q)) := h vr' p in
      ex_intro _ m' (ex_intro _ vr'' (conj (Forall2_trans value_uincl_trans u u') q)).
*)

(*
Lemma compile_progP entries (p: prog) (lp: lprog) mem fn va mem' vr:
  compile_prog cparams entries p = cfok lp ->
  fn \in entries ->
  sem.sem_call p mem fn va mem' vr ->
  forall meml rip, 
    extend_mem mem meml rip lp.(lp_globs) ->
    (forall f, get_fundef lp.(lp_funcs) fn = Some f -> 
       exists p, alloc_stack meml (lfd_stk_size f) = ok p) ->
  ∃ meml' vr',
    List.Forall2 value_uincl vr vr' ∧
    extend_mem mem' meml' rip lp.(lp_globs) /\
    lsem_fd lp rip meml fn va meml' vr'.
Proof.
  rewrite /compile_prog.
  apply: rbindP=> p0 Hp0. rewrite !print_uprogP.
  apply: rbindP=> pca Hpca. rewrite !print_uprogP.
  apply: rbindP=> p1 Hp1. rewrite !print_uprogP.
  apply: rbindP => -[] Hv.
  apply: rbindP=> pv Hpv. rewrite !print_uprogP.
  apply: rbindP=> -[] Hps.
  apply: rbindP=> ps' Hps'. rewrite !print_uprogP.
  apply: rbindP=> -[] He.
  apply: rbindP => pg Hpg. rewrite !print_uprogP.
  apply: rbindP => _ /assertP Hlower.
  apply: rbindP => pstk Hpstk. rewrite !print_sprogP.
  apply: rbindP=> -[] He'.
  apply: rbindP=> pd Hpd. rewrite !print_sprogP.
  apply: rbindP=> pl Hpl [] <-. rewrite !print_linearP.
  move=> Hin Hcall meml rip Hex Halloc.
 (* have Haok : alloc_ok pstk fn meml.
  + rewrite /alloc_ok=> fd Hfd.
    move: Hpl; rewrite /linear_prog; t_xrbindP => ?? lfuncs Hpl [] ?; subst pl.
    move: (get_map_cfprog Hpl Hfd)=> [f' [Hf'1 Hf'2]].
    apply: rbindP Hf'1=> [fn' Hfn'] [] Hf'.
    have := Halloc _ Hf'2.
    by rewrite -Hf' /=. *)
  have va_refl := List_Forall2_refl va value_uincl_refl.
  have eqg : lp_globs pl = sp_globs pd.(p_extra).
  + by move: Hpl; rewrite /linear_prog; t_xrbindP => ???? <-. 
  move: Hex; rewrite eqg => Hex.
  apply: Kj; first by exact: (linear_fdP Hpl).
  apply: Km. 
  + by move=> vr' Hvr'; apply: (stack_alloc_proof.alloc_progP (ev:= tt) Hpstk _ Hex Haok); exact: Hvr'.
  apply: Ki; first by move => vr'; apply: (dead_code_callPu Hpd).
  apply: K'; first by move => vr' Hvr'; apply: (CheckAllocRegU.alloc_callP He'); exact: Hvr'.
  apply: Ki; first by move => vr'; exact: (lower_callP _ _ _ Hlower).
  apply: Ki; first by move => vr';apply: (RGP.remove_globP Hpg).
  apply: K'; first by move => vr' Hvr'; apply: (CheckExpansion.alloc_callP He); exact: Hvr'.
  rewrite surj_prog.
  apply: K'; first by move => vr' Hvr'; apply: (remove_init_fdPu va_refl); exact: Hvr'.
  apply: Ki; first by move => vr'; exact: (dead_code_callPu Hps').
  apply: K'; first by move => vr' Hvr'; apply: (CheckAllocRegU.alloc_callP Hps); exact: Hvr'.
  rewrite surj_prog. 
  apply: Ki; first by move => vr'; exact: (dead_code_callPu Hpv).
  apply: K'; first by move => vr' Hvr'; apply: (CheckAllocRegU.alloc_callP Hv); exact: Hvr'.
  rewrite surj_prog.
  apply: K'; first by move => vr' Hvr'; apply: (const_prop_callP _ va_refl); exact: Hvr'.
  apply: K'; first by move => vr' Hvr'; apply: (unrollP Hp1 _ va_refl); exact: Hvr'.
  apply: Ki; first by move => vr'; exact: (dead_calls_err_seqP (sCP:= sCP_unit) Hpca).
  apply: K'; first by move => vr' Hvr'; apply: (inline_call_errP Hp0 va_refl); exact: Hvr'.
  apply: Ki; first by move => vr'; exact: psem_call.
  exists vr; split => //.
  exact: (List_Forall2_refl _ value_uincl_refl).
Qed.

Lemma compile_prog_to_x86P entries (p: prog) (xp: xprog) m1 fn va m2 vr :
  compile_prog_to_x86 cparams entries p = cfok xp →
  fn \in entries →
  sem.sem_call p m1 fn va m2 vr →
  forall m1' wrip, 
  extend_mem m1 m1' wrip xp.(xp_globs) ->
  (∀ f, get_fundef xp.(xp_funcs) fn = Some f →
     ∃ p, alloc_stack m1' (xfd_stk_size f) = ok p) →
  ∃ fd va',
    get_fundef (p_funcs p) fn = Some fd ∧
    mapM2 ErrType truncate_val (f_tyin fd) va = ok va' ∧
  ∃ fd', get_fundef xp.(xp_funcs) fn = Some fd' ∧
  ∀ st1,
    List.Forall2 value_uincl va' (get_arg_values st1 fd'.(xfd_arg)) →
    st1.(xmem) = m1' →
  ∃ st2,
    x86sem_fd xp wrip fn st1 st2 ∧
    List.Forall2 value_uincl vr (get_arg_values st2 fd'.(xfd_res)) ∧
    extend_mem m2 st2.(xmem) wrip xp.(xp_globs).
Proof.
apply: rbindP=> lp hlp; t_xrbindP => /= _ /assertP /allP ok_sig hxp hfn hsem m1' rip Hex hsafe.
have heq: xp_globs xp = lp_globs lp.
+ by move: hxp; rewrite /assemble_prog; t_xrbindP => _ _; case: x86_variables.reg_of_string => //; t_xrbindP => _ ? _ <-.
rewrite heq in Hex.
have hlsem := compile_progP hlp hfn hsem Hex.
case: hlsem.
- move => fd hfd.
  move: hxp; rewrite /assemble_prog; t_xrbindP => _ _; case: x86_variables.reg_of_string => // sp; t_xrbindP => fs hfs ?; subst xp.
  have [xfd hxfd] := get_map_cfprog hfs hfd.
  by move => /hsafe; rewrite (assemble_fd_stk_size hxfd).
move/ok_sig: hfn.
case: hsem => {m1 m2 hsafe fn va vr Hex} m1 m2 fn fd va va' st1 vm2 vr vr1 ok_fd ok_va _ _ _ _ hsig m2' [vr'] [ok_vr'] [hm2' hlsem].
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
split; first exact: (Forall2_trans value_uincl_trans ok_vr' hvr').
by rewrite heq hm2.
Qed.
*)

End PROOF.

