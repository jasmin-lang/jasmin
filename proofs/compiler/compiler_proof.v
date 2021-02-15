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

Definition sem_call_noleak p f mem va mem' vr :=
 exists l, sem_call p f mem va l mem' vr.

Lemma unroll1P (fn: funname) (p p':prog) mem va va' mem' vr (lf: leak_c) lts stk:
  unroll1 p = ok (p', lts) ->
  sem_call p mem fn va (fn, lf) mem' vr ->
  List.Forall2 value_uincl va va' ->
  exists vr', sem_call p' mem fn va' (fn, (leak_compile stk lts (fn, lf))) mem' vr' 
 /\ List.Forall2 value_uincl vr vr'.
Proof.
  rewrite /unroll1=> Heq Hsem Hall.
  move: Heq. t_xrbindP. move=> -[yp ltp] Hdp [] <- hlts.
  have /= := (unroll_callP stk). 
  move=> Hu. move: (Hu p fn mem mem' va vr (fn, lf) Hsem). move=> {Hu} /= Hu.
  have /= := (const_prop_callP stk refl_equal). rewrite /const_prop_prog /=. move=> Hcp.
  move: (Hcp {|p_globs := p_globs p; p_funcs := [seq (t.1, t.2.1) | t <- [seq (t.1, unroll_fun t.2) | t <- p_funcs p]] |} _ 
         refl_equal fn mem mem' va va' vr 
         (leak_Is (leak_I (leak_Fun [seq (t.1, t.2.2) | t <- [seq (t.1, unroll_fun t.2) | t <- p_funcs p]])) stk
               (leak_Fun [seq (t.1, t.2.2) | t <- [seq (t.1, unroll_fun t.2) | t <- p_funcs p]] fn) lf) Hu Hall).
  move=> {Hcp} /= [vr'] /= [Hcp] Hvs.
  exists vr'. split=> //. 
  have Hdp' := (dead_code_callP stk Hdp). rewrite -hlts /=. by apply Hdp'.
Qed.

Lemma unrollP (fn: funname) (p p': prog) mem va va' mem' vr lts lf stk:
  unroll Loop.nb p = ok (p', lts) ->
  sem_call p mem  fn va (fn, lf) mem' vr ->
  List.Forall2 value_uincl va va' ->
  exists vr', sem_call p' mem fn va' (fn, (leak_compiles stk lts (fn,lf))) mem' vr' /\ List.Forall2 value_uincl vr vr'.
Proof.
  elim: Loop.nb p p' va va' vr lf lts => /= [p //|n Hn] p p' va va' vr lf lts. 
  t_xrbindP => -[z lt] Hz.
  case: ifP.
  + move=> /eqP /= hp [] hp' <- Hsem Hvs. have := (unroll1P stk Hz Hsem Hvs). rewrite hp in hp'. rewrite -hp'.  
    move=> [vr'] [Hsem'] Hvs'. exists vr'. split=> //=. 
  move=> _ Hu Hs Hall. have [vr' [hsem1 hall1]]:= unroll1P stk Hz Hs Hall. move: Hu. t_xrbindP. move=> -[pd ltd] /= Hu [] <- <-.
  move: (Hn z pd va' va' vr' (leak_compile stk lt (fn, lf)) ltd Hu hsem1 (List_Forall2_refl _ value_uincl_refl)).
  move=> [vr''] [hsem] hvs. exists vr''. split=> //=.
  by apply: Forall2_trans value_uincl_trans hall1 hvs.
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

Lemma compile_progP entries (p: prog) (gd:glob_decls) (lp: lprog) mem fn va mem' vr lts lf:
  compile_prog cparams entries p = cfok (gd, lp, lts) ->
  fn \in entries ->
  sem.sem_call p mem fn va (fn, lf) mem' vr ->
  forall sp, (forall f, get_fundef lp fn = Some f ->
  alloc_stack mem (lfd_stk_size f) = ok sp) ->
  ∃ mem2' vr',
    List.Forall2 value_uincl vr vr' ∧
    eq_mem mem' mem2' ∧
    lsem_fd lp gd mem fn va (fn, (leak_compile_prog (top_stack sp) lts (fn, lf))) mem2' vr'.
Proof.
  rewrite /compile_prog.
  apply: rbindP=> -[p0 l0] Hp0. rewrite !print_progP.
  apply: rbindP=> -pca Hpca. rewrite !print_progP.
  apply: rbindP=> -[p1 lp1] Hp1. rewrite !print_progP.
  apply: rbindP=> ltc - /= Hv.
  apply: rbindP=> -[pv lpv] Hpv. rewrite !print_progP.
  apply: rbindP=> lps - Hps.
  apply: rbindP=> -[ps' lps'] Hps'. rewrite !print_progP.
  apply: rbindP => lr - He.
  apply: rbindP => -[pg lg] Hpg. rewrite !print_progP.
  case Hlower: fvars_correct=> //.
  apply: rbindP=> lr' - He'.
  apply: rbindP=> -[pd ld] Hpd. rewrite !print_progP.
  apply: rbindP => -[pstk lpstk] Hpstk.
  apply: rbindP=> -[pl l] /= Hpl [] <- <- hlts. rewrite !print_linearP.
  move=> Hin Hcall sp Halloc.
  have halloc : forall fd, get_fundef (pstk, lpstk).1 fn = Some fd ->
  @alloc_stack low_memory.mem Memory.M  mem (sf_stk_sz fd) = ok sp.
  + move=> fd Hfd. move: (get_map_cfprog_leak Hpl Hfd)=> [f'] [lt] [Hf'1] Hf'2 Hf'3. 
    apply: rbindP Hf'1=> [fn' Hfn'] [] Hf' Hlt.
    rewrite -Hf' /= in Hf'2. by apply (Halloc _ Hf'2).
  have va_refl := List_Forall2_refl va value_uincl_refl.
  apply: Kj. move => m' vr' H. have Hl /= := (linear_fdP (top_stack sp) Hpl).
  rewrite /leak_compile_prog -hlts /=.
  move: H. apply Hl.
  apply: Km. move=> vr' Hvr'. have Hs /= := (stack_alloc_proof.alloc_progP Hpstk _ halloc).
  rewrite /=. eapply Hs. exact: Hvr'.
  apply: Ki. move => vr' Hvr'. have Hd /= := (dead_code_callP (top_stack sp) Hpd).
  move: Hvr'. apply Hd.
  apply: K'. move=> vr' Hvr'. have Hck := (@CheckAllocReg.alloc_callP _ _ _ He'). 
  assert (h := Hck fn mem mem' va vr' (top_stack sp)); move: h => {Hck} Hck.
  apply Hck. exact: Hvr'.
  apply: Ki. move=> vr'.  
  have Hl /= := (lower_callP (top_stack sp) Hlower _). 
  apply Hl => //.
  apply: Ki. move => vr'. have Hrg /= := (RGP.remove_globP (top_stack sp) Hpg).
  apply Hrg.
  apply: K'. move => vr' Hvr'. have Hck := (@CheckExpansion.alloc_callP _ _ _ He). 
  apply (Hck fn mem mem' va vr' (top_stack sp)). 
  + exact: Hvr'.
  apply: K'. move => vr' Hvr'. 
  apply (remove_init_fdP (p := ps')
                (Fs:=[seq (t.1, t.2.2) | t <- [seq (t.1, remove_init_fd t.2) | t <- p_funcs ps']])
               (top_stack sp)
               refl_equal refl_equal va_refl).
  + exact: Hvr'.
  apply: Ki. move => vr'. have hd := (dead_code_callP (top_stack sp) Hps'). apply hd.
  apply: K'. move => vr' Hvr'. have hck := (@CheckAllocReg.alloc_callP _ _ _ Hps). 
(* 
  move: (hck fn mem mem' va vr' (top_stack sp)). move=> {hck} hck.
  apply hck. exact: Hvr'.
  apply: Ki. move => vr'. have Hd := (dead_code_callP (top_stack sp) Hpv). apply Hd.
  apply: K'. move => vr' Hvr'. have Hck := (@CheckAllocReg.alloc_callP _ _ _ Hv). 
  apply Hck; exact: Hvr'.
  apply: K'. move => vr' Hvr'. have Hc := (const_prop_callP). rewrite /const_prop_prog /= in Hc.
  move: (Hc p1 {|p_globs := p_globs p1; p_funcs := [seq (t.1, t.2.1)| t <- [seq (t.1, const_prop_fun t.2) | t <- p_funcs p1]] |}
         [seq (t.1, t.2.2) | t <- [seq (t.1, const_prop_fun t.2) | t <- p_funcs p1]] (top_stack sp) refl_equal refl_equal fn mem mem' va va vr').
  move=> {Hc} Hc. apply Hc. exact: Hvr'. apply va_refl.
  apply: K'. move => vr' Hvr'. have Hu := (unrollP (top_stack sp) Hp1 _ va_refl). 
  apply Hu; exact: Hvr'.
  apply: Ki. move => vr'; exact: (dead_calls_err_seqP Hpca).
  apply: K'. move => vr' Hvr'. have Hi := (inline_call_errP (top_stack sp) Hp0 va_refl). 
  apply Hi. exact: Hvr'.
  apply: Ki. move => vr'; exact: psem_call.
  exists vr; split => //.
  exact: (List_Forall2_refl _ value_uincl_refl).
*)
admit.
Admitted.

Lemma compile_prog_to_x86P entries (p: prog) (gd: glob_decls) (xp: xprog) m1 fn va m2 vr lts lf sp:
  compile_prog_to_x86 cparams entries p = cfok (gd,xp, lts) →
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
    List.Forall2 value_uincl vr (get_arg_values st2 fd'.(xfd_res)) ∧
    eq_mem m2 st2.(xmem).
Proof.
apply: rbindP=> -[[gd1 lp] ltp] hlp /= ; t_xrbindP => /= _ /assertP /allP ok_sig ? hxp ?? hlt hfn hsem hsafe;subst.
have hlsem := compile_progP hlp hfn hsem (sp := sp).
case: hlsem.
move=> fd hfd.
have [xfd [hxfd]] := get_map_cfprog hxp hfd.
by move => /hsafe; rewrite (assemble_fd_stk_size hxfd).
move=> hm2' [vr''] [hvs] [heq] hlsem.
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
Inductive x86_par (P: mem -> mem -> seq value -> seq value -> Prop) (xp: xprog) (f:funname) (st1 st2: x86_mem) : Prop :=
  | x86_par_intro : forall xfd st1' st2',
     get_fundef xp f = Some xfd ->
     let m1 := st1.(xmem) in
     let m2 := st2.(xmem) in
     @alloc_stack low_memory.mem Memory.M m1 (xfd_stk_size xfd) = ok st1' ->
     @alloc_stack low_memory.mem Memory.M m2 (xfd_stk_size xfd) = ok st2' ->
     (top_stack st1') = (top_stack st2') ->
     let va1 := get_arg_values st1 xfd.(xfd_arg) in
     let va2 := get_arg_values st2 xfd.(xfd_arg) in
     P st1.(xmem) st2.(xmem) va1 va2 ->
     x86_par P xp f st1 st2.
   
Definition x86_constant_time (P : x86_mem -> x86_mem -> Prop) (gd: glob_decls) (p : xprog) (f : funname) : Prop :=
  forall st1 st2,
  P st1 st2 ->
  exists st1' st2' lf,
  x86sem_fd p gd f st1 lf st1' /\
  x86sem_fd p gd f st2 lf st2'.

Definition constant_time (P : mem -> mem -> seq value -> seq value -> Prop) (p : prog) (f : funname) : Prop :=
  forall mem1 mem2 va1 va2,
  P mem1 mem2 va1 va2 ->  
  exists mem1' mem2' vr1 vr2 lf, 
  sem.sem_call p mem1 f va1 (f, lf) mem1' vr1 /\
  sem.sem_call p mem2 f va2 (f, lf) mem2' vr2.

Lemma value_uincl_truncate_vals tys va va': 
  mapM2 ErrType truncate_val tys va = ok va' ->
  List.Forall2 value_uincl va' va.
Proof.
  apply mapM2_Forall2 => ????; apply value_uincl_truncate_val.
Qed.

Lemma x86_CT : forall P p gd f xp entries lts,
 compile_prog_to_x86 cparams entries p = cfok (gd,xp, lts) →
 f \in entries ->
 constant_time P p f ->
 x86_constant_time (x86_par P xp f) gd xp f.
Proof.
  rewrite /constant_time /x86_constant_time.
  move => P p gd f xp entries lts Hcp Hentries Hct st1 st2 [] xfd st1' st2' /= hget hasp hasp' htop.
  move=> /Hct [mem1'] [mem2'] [vr1] [vr2] [lf] [hsem1 hsem2].
  case (compile_prog_to_x86P Hcp Hentries hsem1 (sp := st1')).
  + by move=> xfd'; rewrite hget => -[] <-.
  move=> fd' [va1'] [] hget1 [] hm1 [xfd']; rewrite hget => -[] [] ?; subst xfd'.
  move=> /(_ st1) [] //. 
  + by apply: value_uincl_truncate_vals hm1.
  move=> st1'' [] hxsem1 _.
  case (compile_prog_to_x86P Hcp Hentries hsem2 (sp := st2')).
  + by move=> ?; rewrite hget => -[] <-.
  move=> fd2' [va2']; rewrite hget1 => -[] [] ?; subst fd2'.
  move=> [hm2] [xfd']; rewrite hget => -[] [] ?; subst xfd'.
  move=> /(_ st2) [] //.  
  + by apply: value_uincl_truncate_vals hm2.
  rewrite -htop => st2'' [] hxsem2 _.
  by exists st1'', st2'', (leak_compile_x86 (top_stack st1') lts (f, lf)).
Qed.

End PROOF.
