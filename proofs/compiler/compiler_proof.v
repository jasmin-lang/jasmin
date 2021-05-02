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
               array_expansion remove_globals_proof stack_alloc_proof
               lowering_proof
               linear_proof
               psem_of_sem_proof cost cost_linear cost_asm.
Import Utf8.
Import x86_sem x86_gen.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section PROOF.

Variable cparams : compiler_params.

Hypothesis print_progP : forall s p, cparams.(print_prog) s p = p.
Hypothesis print_linearP : forall p, cparams.(print_linear) p = p.

Definition sem_call_noleak p f mem va mem' vr :=
 exists l, sem_call p f mem va l mem' vr.
    
Lemma unroll1P (fn: funname) (p p':prog) mem va va' mem' vr (lf: leak_c) lts stk:
  unroll1 p = ok (p', lts) ->
  sem_call p mem fn va (fn, lf) mem' vr ->
  List.Forall2 value_uincl va va' ->
  leak_WF_rec fn stk lts lf /\ 
  exists vr', sem_call p' mem fn va' (fn, leak_compile stk lts (fn, lf)) mem' vr' /\
                  List.Forall2 value_uincl vr vr'.
Proof.
  rewrite /unroll1=> heq hsem hall.
  move: heq; t_xrbindP; move=> -[yp ltp] hdp [] <- <-.
  have /= := unroll_callP_wf stk hsem. 
  set lFu := leak_Fun _; move => [wfu {hsem} hsem].
  have /= := const_prop_callP stk refl_equal refl_equal hsem hall.
  set lFc := leak_Fun _; move => [wfc] [vr'] {hsem} [hsem] hrall.
  have /= [wfd {hsem} hsem] := dead_code_callP_wf stk hdp hsem.
  by split => //; exists vr'.
Qed.

Lemma unrollP (fn: funname) (p p': prog) mem va va' mem' vr lts lf stk:
  unroll Loop.nb p = ok (p', lts) ->
  sem_call p mem  fn va (fn, lf) mem' vr ->
  List.Forall2 value_uincl va va' ->
  leak_WF_rec fn stk lts lf /\ 
  exists vr', sem_call p' mem fn va' (fn, (leak_compile stk lts (fn,lf))) mem' vr' /\ 
              List.Forall2 value_uincl vr vr'.
Proof.
  elim: Loop.nb p p' va va' vr lf lts => /= [p //|n hrec] p p' va va' vr lf lts. 
  t_xrbindP => -[p1 lt] hp1 /=.
  case: eqP => [? [? ?]| _].
  + by subst p1 p' lt; apply unroll1P.
  t_xrbindP => -[p2 lts2] hp2 [] ?? hsem hall; subst p2 lts.
  have [hwf1 [vr1 {hsem} [hsem hallr1]]] := unroll1P stk hp1 hsem hall.
  have [hwf2 [vr2 {hsem} [hsem hallr2]]] := hrec _ _ _ _ _ _ _ hp2 hsem (List_Forall2_refl _ value_uincl_refl).
  split; first by apply leak_WF_rec_cat.
  exists vr2; split; first by rewrite leak_compile_cat.
  by apply: Forall2_trans value_uincl_trans hallr1 hallr2.
Qed.

Opaque Loop.nb.

Let htrans : ∀ l l0 l1 : seq value,
             List.Forall2 value_uincl l0 l → List.Forall2 value_uincl l l1 → List.Forall2 value_uincl l0 l1.
Proof. move=> l l0 l1; apply: (Forall2_trans value_uincl_trans). Qed.

Lemma compile_progP entries (p: prog) (gd:glob_decls) (lp: lprog) mem fn va mem' vr lts lf:
  compile_prog cparams entries p = cfok (gd, lp, lts) ->
  fn \in entries ->
  sem.sem_call p mem fn va (fn, lf) mem' vr ->
  forall sp, 
    (forall f, get_fundef lp fn = Some f -> alloc_stack mem (lfd_stk_size f) = ok sp) ->
  (leak_WF_rec fn (top_stack sp) lts.1 lf /\ 
  leak_is_WF (odflt [::] (assoc lts.2 fn)) (leak_compile (top_stack sp) lts.1 (fn,lf))) /\ 
  ∃ mem2' vr',
    List.Forall2 value_uincl vr vr' ∧
    eq_mem mem' mem2' ∧
    lsem_fd lp gd mem fn va (fn, leak_compile_prog (top_stack sp) lts (fn, lf)) mem2' vr'.
Proof.
  move=> hc Hin /psem_call hsem sp halloc.
  have va_refl := List_Forall2_refl va value_uincl_refl.
  move: hc; rewrite /compile_prog.
  apply: rbindP=> -[p0 l0] Hp. rewrite !print_progP.
  assert (h := inline_call_errP (top_stack sp) Hp va_refl hsem).
  case: h => {hsem Hp} [? [? [hsem hall]]].
  apply: rbindP=> pca Hp. rewrite !print_progP.
  have {hsem Hp} hsem := dead_calls_err_seqP Hp Hin hsem.
  apply: rbindP=> -[p1 lp1] Hp. rewrite !print_progP.
  assert (h := unrollP (top_stack sp) Hp hsem va_refl).
  case: h => {hsem Hp} [? [? [hsem /(htrans hall){hall}hall]]].
  set p2 := const_prop_prog (p1, lp1).1.
  have hp2: const_prop_prog (p1, lp1).1 = (p2.1, p2.2) by rewrite surj_pairing.
  assert (h := const_prop_callP (top_stack sp) refl_equal hp2 hsem va_refl).
  case: h => /= {hsem hp2 p2} [? [? [hsem /(htrans hall){hall}hall]]].
  apply: rbindP=> ltc - /= Hp.
  assert (h := CheckAllocReg.alloc_callP_wf Hp (top_stack sp) hsem).
  case: h => /= {hsem Hp} [? [? [hsem /(htrans hall){hall}hall]]].
  apply: rbindP=> -[pv lpv] Hp. rewrite !print_progP.
  assert (h := dead_code_callP_wf (top_stack sp) Hp hsem).
  case: h => /= {hsem Hp} [? hsem].
  apply: rbindP=> lps - Hp.
  assert (h := CheckAllocReg.alloc_callP_wf Hp (top_stack sp) hsem).
  case: h => /= {hsem Hp} [? [? [hsem /(htrans hall){hall}hall]]].
  apply: rbindP=> -[ps' lps'] Hp. rewrite !print_progP.
  assert (h := dead_code_callP_wf (top_stack sp) Hp hsem).
  case: h => /= {hsem Hp} ? hsem.
  set p2 := remove_init_prog ps'.
  have hp2: remove_init_prog ps' = (p2.1, p2.2) by rewrite surj_pairing.
  assert (h := remove_init_fdP_wf (top_stack sp) hp2 va_refl hsem).
  case: h => /= {hsem hp2 p2} [? [? [hsem /(htrans hall){hall}hall]]].
  apply: rbindP => lr - Hp.
  assert (h := CheckExpansion.alloc_callP_wf Hp (top_stack sp) hsem).
  case: h => /= {hsem Hp} [? [? [hsem /(htrans hall){hall}hall]]].
  apply: rbindP => -[pg lg] Hp. rewrite !print_progP.
  assert (h := RGP.remove_globP (top_stack sp) Hp hsem).
  case: h => /= {hsem Hp} [? hsem].
  case Hlower: fvars_correct=> //.
  have := lower_callP (top_stack sp) Hlower refl_equal hsem. 
  move=> /(_ (lowering_opt cparams) (warning cparams)  (is_var_in_memory cparams) Memory.M).
  move=> {hsem} [ ? hsem].
  apply: rbindP=> lr' - Hp.
  assert (h := CheckAllocReg.alloc_callP_wf Hp (top_stack sp) hsem).
  case: h => /= {hsem Hp} [? [? [hsem /(htrans hall){hall}hall]]].
  apply: rbindP=> -[pd ld] Hp. rewrite !print_progP.
  assert (h := dead_code_callP_wf (top_stack sp) Hp hsem).
  case: h => /= {hsem Hp} [? hsem].
  apply: rbindP => -[pstk lpstk] Hp.
  apply: rbindP=> -[pl l] /= Hpl. rewrite !print_linearP => -[] ???; subst gd lp lts. 
  have halloc' : forall fd, get_fundef (pstk, lpstk).1 fn = Some fd ->
    @alloc_stack low_memory.mem Memory.M  mem (sf_stk_sz fd) = ok sp.
  + move=> fd Hfd. move: (get_map_cfprog_leak Hpl Hfd)=> [f'] [lt] [Hf'1] Hf'2 Hf'3. 
    apply: rbindP Hf'1=> [fn' Hfn'] [] Hf' Hlt.
    rewrite -Hf' /= in Hf'2. by apply (halloc _ Hf'2).
  assert (h := stack_alloc_proof.alloc_progP Hp hsem halloc').
  case: h => /= {hsem Hp} ? [m2' [vr' [/(htrans hall){hall}hall[ ? hsem]]]].
  assert (h := linear_fdP (top_stack sp) Hpl hsem).
  case: h => {hsem Hpl} ? hsem; split; last first.
  exists m2'; exists vr'; split => //; split => //.
  + by rewrite /leak_compile_prog /= leak_compile_cat.
  split; first by split => //; apply leak_WF_rec_cat.
  by rewrite leak_compile_cat.
Qed.

Lemma compile_prog_to_x86P entries (p: prog) (gd: glob_decls) (xp: xprog) m1 fn va m2 vr lts lf sp:
  compile_prog_to_x86 cparams entries p = cfok (gd,xp, lts) →
  fn \in entries →
  sem.sem_call p m1 fn va (fn, lf) m2 vr →
  (∀ f, get_fundef xp fn = Some f →
        alloc_stack m1 (xfd_stk_size f) = ok sp) →
  (leak_WF_rec fn (top_stack sp) lts.1 lf /\ 
    leak_is_WF (odflt [::] (assoc lts.2 fn)) (leak_compile (top_stack sp) lts.1 (fn,lf))) /\ 
( ∃ fd va',
    get_fundef (p_funcs p) fn = Some fd ∧
    mapM2 ErrType truncate_val (f_tyin fd) va = ok va' ∧
  ∃ fd', get_fundef xp fn = Some fd' ∧
  ∀ st1,
    List.Forall2 value_uincl va' (get_arg_values st1 fd'.(xfd_arg)) →
    st1.(xmem) = m1 ->
  ∃ st2,
    x86sem_fd xp gd fn st1 (leak_compile_x86 (top_stack sp) lts (fn, lf)) st2 ∧
    List.Forall2 value_uincl vr (get_arg_values st2 fd'.(xfd_res)) ∧
    eq_mem m2 st2.(xmem)).
Proof.
apply: rbindP=> -[[gd1 lp] ltp] hlp /= ; t_xrbindP => /= _ /assertP /allP ok_sig ? hxp ?? hlt hfn hsem hsafe;subst.
have hlsem := compile_progP hlp hfn hsem (sp := sp).
case: hlsem.
+ move=> fd hfd.
  have [xfd [hxfd]] := get_map_cfprog hxp hfd.
  by move => /hsafe; rewrite (assemble_fd_stk_size hxfd).
move=> hleak [hm2'] [vr''] [hvs] [heq] hlsem. split => // {hleak}.
move: hlsem.
move/ok_sig: hfn. move: hvs heq. 
case: hsem=> {m1 m2 hsafe fn va vr} m1 m2 fn fd va va' st1 vm2 vr vr1 lc ok_fd' ok_va' h1 h2 h3 h4 hvs Heq hsig hlsem. exists fd. 
exists va. split=> //. split. apply ok_va'. 
case: (assemble_fdP hxp hlsem) => fd'' [va1] [ok_fd''] [ok_va1] [xd] [ok_xd h].
move: ok_va1.
have -> : lfd_tyin fd'' = f_tyin fd.
- by move: hsig; rewrite /check_signature ok_fd'' ok_fd' /= => /eqP []. 
rewrite ok_va' => - [?]; subst va1.
exists xd; split; first exact: ok_xd.
move => st hva hm1.
have [st2 [hxsem [hvr' hm2]]] := h st hva hm1.
exists st2.
split; first exact: hxsem.
split; last by rewrite hm2.
exact: (Forall2_trans value_uincl_trans hvs hvr').
Qed.

(* lift_x86_pred *) 
Inductive lift_spred_x86_pred (P: mem -> mem -> seq value -> seq value -> Prop) (xp: xprog) (f:funname) (st1 st2: x86_mem) : Prop :=
  | x86_par_intro : forall xfd st1' st2',
     get_fundef xp f = Some xfd ->
     let m1 := st1.(xmem) in
     let m2 := st2.(xmem) in
     alloc_stack m1 (xfd_stk_size xfd) = ok st1' ->
     alloc_stack m2 (xfd_stk_size xfd) = ok st2' ->
     (top_stack st1') = (top_stack st2') ->
     let va1 := get_arg_values st1 xfd.(xfd_arg) in
     let va2 := get_arg_values st2 xfd.(xfd_arg) in
     P st1.(xmem) st2.(xmem) va1 va2 ->
     lift_spred_x86_pred P xp f st1 st2.

Definition constant_time (P : mem -> mem -> seq value -> seq value -> Prop) (p : prog) (f : funname) : Prop :=
  forall mem1 mem2 va1 va2,
  P mem1 mem2 va1 va2 ->  
  exists mem1' mem2' vr1 vr2 lf, 
  sem.sem_call p mem1 f va1 (f, lf) mem1' vr1 /\
  sem.sem_call p mem2 f va2 (f, lf) mem2' vr2.

Definition x86_constant_time (P : x86_mem -> x86_mem -> Prop) (gd: glob_decls) (p : xprog) (f : funname) : Prop :=
  forall st1 st2,
  P st1 st2 ->
  exists st1' st2' lf,
  x86sem_fd p gd f st1 lf st1' /\
  x86sem_fd p gd f st2 lf st2'.

Lemma x86_CT : forall P p gd f xp entries lts,
 compile_prog_to_x86 cparams entries p = cfok (gd,xp, lts) →
 f \in entries ->
 constant_time P p f ->
 x86_constant_time (lift_spred_x86_pred P xp f) gd xp f.
Proof.
  rewrite /constant_time /x86_constant_time.
  move => P p gd f xp entries lts Hcp Hentries Hct st1 st2 [] xfd st1' st2' /= hget hasp hasp' htop.
  move=> /Hct [mem1'] [mem2'] [vr1] [vr2] [lf] [hsem1 hsem2].
  case (compile_prog_to_x86P Hcp Hentries hsem1 (sp := st1')).
  + by move=> xfd'; rewrite hget => -[] <-.
  move=> _ [fd'] [va1'] [] hget1 [] hm1 [xfd']; rewrite hget => -[] [] ?; subst xfd'.
  move=> /(_ st1) [] //. 
  + by apply: value_uincl_truncate_vals hm1.
  move=> st1'' [] hxsem1 _.
  case (compile_prog_to_x86P Hcp Hentries hsem2 (sp := st2')).
  + by move=> ?; rewrite hget => -[] <-.
  move=> _ [fd2'] [va2']; rewrite hget1 => -[] [] ?; subst fd2'.
  move=> [hm2] [xfd']; rewrite hget => -[] [] ?; subst xfd'.
  move=> /(_ st2) [] //.  
  + by apply: value_uincl_truncate_vals hm2.
  rewrite -htop => st2'' [] hxsem2 _.
  by exists st1'', st2'', (leak_compile_x86 (top_stack st1') lts (f, lf)).
Qed.

Lemma compile_prog_to_x86P_cost entries (p: prog) (gd: glob_decls) (xp: xprog) m1 fn va m2 vr lts lf sp ms:
  compile_prog_to_x86 cparams entries p = cfok (gd,xp, lts) →
  transform_costs_l lts = Some ms ->
  fn \in entries →
  sem.sem_call p m1 fn va (fn, lf) m2 vr →
  (∀ f, get_fundef xp fn = Some f →
        alloc_stack m1 (xfd_stk_size f) = ok sp) →
  ∃ fd va',
    get_fundef (p_funcs p) fn = Some fd ∧
    mapM2 ErrType truncate_val (f_tyin fd) va = ok va' ∧
  ∃ fd', get_fundef xp fn = Some fd' ∧
  ∀ st1,
    List.Forall2 value_uincl va' (get_arg_values st1 fd'.(xfd_arg)) →
    st1.(xmem) = m1 ->
  ∃ st2,
    x86sem_fd xp gd fn st1 (leak_compile_x86 (top_stack sp) lts (fn, lf)) st2 ∧
    cost_linear.leqc 
       (asmcost 0 (leak_compile_x86 (top_stack sp) lts (fn, lf))).1
       (Sm.linterp (enter_cost_c cost_i [::] lf) (ms fn)).
Proof.
  move=> hc ht he hsem ha.
  have [h1 [fd [va']]] := compile_prog_to_x86P hc he hsem ha.
  move=> [h2 [h3 [fd' [h4 h5]]]].  
  exists fd, va'; split => //; split => //.
  exists fd'; split => // st1 hall heq.
  case: (h5 st1 hall heq) => st2 [] h6 _; exists st2; split => //.
  rewrite trasnform_cost_il_ok.
  by apply transform_costs_l_ok.
Qed.

End PROOF.
