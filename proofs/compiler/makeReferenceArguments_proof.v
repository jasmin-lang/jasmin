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

(* ** Imports and settings *)
From mathcomp Require Import all_ssreflect all_algebra.
Require Import psem compiler_util.
Require Export makeReferenceArguments.
Import Utf8.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope vmap.
Local Open Scope seq_scope.

Section SemInversion.
Context (T : eqType) (pT : progT T) (cs : semCallParams).
Context (p : prog) (ev : extra_val_t).

Derive Inversion_clear sem_nilI
  with (forall s1 s2,  @sem T pT cs p ev s1 [::] s2)
  Sort Prop.

Derive Inversion_clear sem_consI
  with (forall s1 i c s2,  @sem T pT cs p ev s1 (i :: c) s2)
  Sort Prop.

Section SemInversionSeq1.
  Context (s1 : estate) (i : instr) (s2 : estate).
  Context
    (P : ∀ (T : eqType) (pT : progT T),
           semCallParams → prog -> extra_val_t -> estate -> instr -> estate -> Prop).

  Hypothesis Hi :
    (sem_I p ev s1 i s2 -> @P T pT cs p ev s1 i s2).

  Lemma sem_seq1I : sem p ev s1 [:: i] s2 → @P T pT cs p ev s1 i s2.
  Proof.
  by elim/sem_consI=> s hs h_nil; elim/sem_nilI: h_nil hs => /Hi.
  Qed.
End SemInversionSeq1.
End SemInversion.

Section Section.
  Context (is_reg_ptr : var -> bool) (fresh_id : glob_decls -> var -> Ident.ident).

  Lemma make_referenceprog_globs (p p' : uprog) :
    makereference_prog is_reg_ptr fresh_id p = ok p' ->
      p.(p_globs) = p'.(p_globs).
  Proof.
    case: p p' => [???] [???]; t_xrbindP.
    by rewrite /makereference_prog; t_xrbindP.
  Qed.

  Lemma do_prologue_None (p : uprog) ii st x pe :
       is_reg_ptr_expr is_reg_ptr fresh_id p (v_var x) pe = None
    -> do_prologue is_reg_ptr fresh_id p ii st x pe = (st, pe).
  Proof. by rewrite /do_prologue => ->. Qed.

  Lemma do_prologue_Some (p : uprog) ii st x pe y :
       is_reg_ptr_expr is_reg_ptr fresh_id p (v_var x) pe = Some y
    -> do_prologue is_reg_ptr fresh_id p ii st x pe
       = (MkI ii (Cassgn y AT_rename (vtype y) pe) :: st, Plvar y).
  Proof. by rewrite /do_prologue => ->. Qed.

  Lemma make_prologue_tc (p : uprog) ii st xs pes :
      fmap2 (do_prologue is_reg_ptr fresh_id p ii) st xs pes
    = ((make_prologue is_reg_ptr fresh_id p ii xs pes).1 ++ st,
       (make_prologue is_reg_ptr fresh_id p ii xs pes).2).
  Proof.
  rewrite /make_prologue; set F := do_prologue is_reg_ptr fresh_id p ii.
  rewrite -{1}[st](cat0s); move: [::] => st'.
  elim: xs pes st st' => [|x xs ih] // [|pe pes] // st st'.
  case E: (is_reg_ptr_expr is_reg_ptr fresh_id p (v_var x) pe) => [y|].
  + by rewrite /F /= !(do_prologue_Some ii _ E) /= -cat_cons !ih.
  + by rewrite /F /= !(do_prologue_None ii _ E) /= !ih.
  Qed.  

  Lemma make_prologue0 (p : uprog) ii args :
    make_prologue is_reg_ptr fresh_id p ii [::] args = ([::], args).
  Proof. by []. Qed.

  Lemma make_prologue0r (p : uprog) ii xs :
    make_prologue is_reg_ptr fresh_id p ii xs [::] = ([::], [::]).
  Proof. by case: xs. Qed.

  Lemma make_prologueS_None (p : uprog) ii x xs pe pes :
       is_reg_ptr_expr is_reg_ptr fresh_id p (v_var x) pe = None
    -> make_prologue is_reg_ptr fresh_id p ii (x :: xs) (pe :: pes)
       = ((make_prologue is_reg_ptr fresh_id p ii xs pes).1,
          pe :: (make_prologue is_reg_ptr fresh_id p ii xs pes).2).
  Proof.
  move=> h; rewrite {1}/make_prologue /= (do_prologue_None _ _ h) /=.
  by rewrite !make_prologue_tc /= cats0.
  Qed.

  Lemma make_prologueS_Some (p : uprog) ii x xs pe pes y :
       is_reg_ptr_expr is_reg_ptr fresh_id p (v_var x) pe = Some y
    -> make_prologue is_reg_ptr fresh_id p ii (x :: xs) (pe :: pes)
       = (rcons (make_prologue is_reg_ptr fresh_id p ii xs pes).1
                (MkI ii (Cassgn y AT_rename (vtype y) pe)),
          Plvar y :: (make_prologue is_reg_ptr fresh_id p ii xs pes).2).
  Proof.
  move=> h; rewrite {1}/make_prologue /= (do_prologue_Some _ _ h).
  by rewrite !make_prologue_tc /= cats1.
  Qed.
 
  Context (p p' : uprog).
  Context (ev : unit).

 (* Hypothesis uniq_funname : uniq [seq x.1 | x <- p_funcs p]. *)

  Hypothesis Hp : makereference_prog is_reg_ptr fresh_id p = ok p'.

  (*Should be shown by assuming other hypotheses or admitted?*)
  Lemma eq_globs : p_globs p = p_globs p'.
  Proof.
   case : p Hp => /= p_funcs p_globs extra.
   rewrite /makereference_prog.
   (*But Let x in ...*)
   t_xrbindP => /=.
   by move => y _ <-.
  Qed.

  Definition get_sig n :=
   if get_fundef p.(p_funcs) n is Some fd then
     (fd.(f_params), fd.(f_res))
   else ([::], [::]).

  Let Pi s1 (i:instr) s2:=
    forall (X:Sv.t) c', update_i is_reg_ptr fresh_id p get_sig X i = ok c' ->
     Sv.Subset (Sv.union (read_I i) (write_I i)) X ->
     forall vm1, evm s1 =[X] vm1 ->
     exists vm2, [/\ evm s2 =[X] vm2 &
        sem p' ev (with_vm s1 vm1) c' (with_vm s2 vm2)].

  Let Pi_r s1 (i:instr_r) s2 :=
    forall ii, Pi s1 (MkI ii i) s2.

  Let Pc s1 (c:cmd) s2:=
    forall (X:Sv.t) c', update_c (update_i is_reg_ptr fresh_id p get_sig X) c = ok c' ->
     Sv.Subset (Sv.union (read_c c) (write_c c)) X ->
     forall vm1, evm s1 =[X] vm1 ->
     exists vm2, [/\ evm s2 =[X] vm2 &
        sem p' ev (with_vm s1 vm1) c' (with_vm s2 vm2)].

  Let Pfor (i:var_i) vs s1 c s2 :=
    forall X c',
    update_c (update_i is_reg_ptr fresh_id p get_sig X) c = ok c' ->
    Sv.Subset (Sv.add i (Sv.union (read_c c) (write_c c))) X ->
    forall vm1,  evm s1 =[X] vm1 ->
    exists vm2, [/\ evm s2 =[X] vm2  &
      sem_for p' ev i vs (with_vm s1 vm1) c' (with_vm s2 vm2)].

  Let Pfun m fn vargs m' vres :=
    sem_call p' ev m fn vargs m' vres.

  Local Lemma Hskip : sem_Ind_nil Pc.
  Proof.
    move => s X.
    move => _ [<-].
    move => Hs vm1 Hvm1.
    exists vm1.
    split => //.
    by constructor.
    (*by move=> s X _ [<-] hs vm1 hvm1; exists vm1; split => //; constructor.*)
  Qed.

  Local Lemma Hcons : sem_Ind_cons p ev Pc Pi.
  Proof.
    move=> s1 s2 s3 i c _ hi _ hc X c'.
    rewrite /update_c /=.
    t_xrbindP.
    move => lc ci {}/hi hi cc hcc.
    (*Difference between <- and [<-]?*)
    (*move =>h ; rewrite - h ; clear h.*)
    (*[] is just case*)
    (*What is {}/hi again?*)
    (*{}h makes a clear of h*)
    move => <- <-.
    rewrite read_c_cons.
    rewrite write_c_cons.
    move => hsub vm1 hvm1.
    have [|vm2 [hvm2 hs2]]:= hi _ vm1 hvm1; first by SvD.fsetdec.
    have /hc : update_c (update_i is_reg_ptr fresh_id p get_sig X) c = ok (flatten cc).
    + by rewrite /update_c hcc.
    move=> /(_ _ vm2 hvm2) [|vm3 [hvm3 hs3]]; first by SvD.fsetdec.
    exists vm3; split => //=.
    apply: sem_app hs2 hs3.
  Qed.

  Local Lemma HmkI : sem_Ind_mkI p ev Pi_r Pi.
  Proof. by move=> ii i s1 s2 _ Hi X c' /Hi. Qed.

  Local Lemma Hassgn : sem_Ind_assgn p Pi_r.
  Proof.
    move=> s1 s2 x t ty e v v' he htr hw ii X c' [<-].
    rewrite read_Ii /write_I /= vrv_recE read_i_assgn => hsub vm1 hvm1.
    move: he.
    rewrite (read_e_eq_on _ (s:=Sv.empty) (vm' := vm1)); last first.
    + by apply: eq_onI hvm1; rewrite read_eE; SvD.fsetdec.
    rewrite eq_globs => he.

    (*I am supposed to use this, but can't figure out how: how can I get anything of type glob_decls?*)
    have ? := write_lval_eq_on.
    Print glob_decls.
    Print progT.
    Print with_vm.
  Admitted.

(*@: all arguments event implicits*)
(*Check: gives the type of something*)

  Local Lemma Hopn : sem_Ind_opn p Pi_r.
  Proof.
    move => s1 s2 t o xs es He ii X c'.
    rewrite /update_i.
    move => [<-].
    rewrite read_Ii read_i_opn.
    rewrite /write_I /= vrvs_recE => hsub vm1 hvm1.
    Print update_c.
    (*hsub should be simplifiable*)
    (*have /hc : update_c (update_i is_reg_ptr fresh_id p get_sig X) c = ok (c').*)

    exists vm1.
    split.
  Admitted.

  Lemma write_Ii ii i : write_I (MkI ii i) = write_i i.
  Proof. by []. Qed.

  Local Lemma Hif_true : sem_Ind_if_true p ev Pc Pi_r.
  Proof.
    move=> s1 s2 e c1 c2 He Hs Hc ii X c' /=.
    t_xrbindP => i_then i_thenE i_else i_elseE {c'}<-.
    rewrite !(read_Ii, write_Ii) !(read_i_if, write_i_if) => le_X.
    move=> vm1 eq_s1_vm1; case: (Hc X _ i_thenE _ vm1 eq_s1_vm1).
    + by SvD.fsetdec.
    move=> vm2 [eq_s2_vm2 sem_i_then]; exists vm2; split=> //.
    apply/sem_seq1/EmkI; apply: Eif_true => //.
    rewrite -(make_referenceprog_globs Hp) -He.
    rewrite -(@read_e_eq_on _ Sv.empty) // -/(read_e _).
    by apply: (eq_onI _ eq_s1_vm1); SvD.fsetdec.
  Qed.

  Local Lemma Hif_false : sem_Ind_if_false p ev Pc Pi_r.
  Proof.
    move=> s1 s2 e c1 c2 He Hs Hc ii X c' /=.
    t_xrbindP => i_then i_thenE i_else i_elseE {c'}<-.
    rewrite !(read_Ii, write_Ii) !(read_i_if, write_i_if) => le_X.
    move=> vm1 eq_s1_vm1; case: (Hc X _ i_elseE _ vm1 eq_s1_vm1).
    + by SvD.fsetdec.
    move=> vm2 [eq_s2_vm2 sem_i_else]; exists vm2; split=> //.
    apply/sem_seq1/EmkI; apply: Eif_false => //.
    rewrite -(make_referenceprog_globs Hp) -He.
    rewrite -(@read_e_eq_on _ Sv.empty) // -/(read_e _).
    by apply: (eq_onI _ eq_s1_vm1); SvD.fsetdec.
  Qed.


  Local Lemma Hwhile_true : sem_Ind_while_true p ev Pc Pi_r.
  Proof.
    move=> s1 s2 s3 s4 a c e c' sem_s1_s2 H_s1_s2.
    move=> sem_s2_e sem_s2_s3 H_s2_s3 sem_s3_s4 H_s3_s4.
    move=> ii X c'' /=; t_xrbindP=> d dE d' d'E {c''}<-.
    rewrite !(read_Ii, write_Ii) !(read_i_while, write_i_while).
    move=> le_X vm1 eq_s1_vm1.
    case: (H_s1_s2 X _ dE _ _ eq_s1_vm1); first by SvD.fsetdec.
    move=> vm2 [eq_s2_vm2 sem_vm1_vm2].
    case: (H_s2_s3 X _ d'E _ _ eq_s2_vm2); first by SvD.fsetdec.
    move=> vm3 [eq_s3_vm3 sem_vm2_vm3].
    case: (H_s3_s4 ii X [:: MkI ii (Cwhile a d e d')] _ _ vm3) => //=.
    + by rewrite dE d'E.
    + rewrite !(read_Ii, write_Ii) !(read_i_while, write_i_while).
      by SvD.fsetdec.
    move=> vm4 [eq_s4_vm4 sem_vm3_vm4]; exists vm4; split=> //.
    apply/sem_seq1/EmkI; apply: (Ewhile_true sem_vm1_vm2 _ sem_vm2_vm3).
    + rewrite -(make_referenceprog_globs Hp) -sem_s2_e.
      rewrite -(@read_e_eq_on _ Sv.empty) // -/(read_e _).
      by apply: (eq_onI _ eq_s2_vm2); SvD.fsetdec.
    by elim/sem_seq1I: sem_vm3_vm4 => /sem_IE.
  Qed.

  Local Lemma Hwhile_false : sem_Ind_while_false p ev Pc Pi_r.
  Proof.
   move=> s1 s2 a c e c' He Hc eq_s_e ii X c'' /=.
   t_xrbindP => while_false while_falseE c''' eq_c' <-.
   (*Need to have the set in a different order*)
   rewrite !(read_Ii, write_Ii) !(read_i_while, write_i_while).
   (*What are those !() ? rewrite as much as possible*)
   move => le_X vm1 eq_s1_vm1.
   case: (Hc X _ while_falseE _ vm1 eq_s1_vm1).
   + by SvD.fsetdec.
   move => vm2 [eq_s2_vm2 sem_while_false].
   exists vm2 ; split => //.
   apply/sem_seq1/EmkI.
   Print sem_i.
   apply Ewhile_false => //.
   rewrite -(make_referenceprog_globs Hp) - eq_s_e.
   rewrite -(@read_e_eq_on _ Sv.empty) // -/(read_e _).
   by apply: (eq_onI _ eq_s2_vm2) ; SvD.fsetdec.
  Qed.

  Local Lemma Hfor_nil : sem_Ind_for_nil Pfor.
  Proof.
    move => s1 x c X c' Hc le_X vm1 eq_s1_vm1.
    exists vm1 ; split => //.
    by constructor.
  Qed.

  Local Lemma Hfor_cons : sem_Ind_for_cons p ev Pc Pfor.
  Proof.
    move => s1 s2 s3 s4 x w ws c eq_s2 sem_s2_s3 H_s2_s3 H_s3_s4 Pfor_s3_s4 X c'.
    move => eq_c' le_X vm1 eq_s1_vm1.
    case : (write_var_eq_on eq_s2 eq_s1_vm1) => vm2 [eq_s2_vm2 eq_write].
    case : (H_s2_s3 X _ eq_c' _ vm2).
    + by SvD.fsetdec.
    + by apply: (eq_onI _ eq_s2_vm2) ; SvD.fsetdec.
    move => vm3 [eq_s3_vm3 sem_vm2_vm3].
    case : (Pfor_s3_s4 X _ eq_c' _ vm3 eq_s3_vm3) => //.
    move => vm4 [eq_s4_vm4 sem_vm3_vm4].
    exists vm4 ; split => //.
    by apply (EForOne eq_write sem_vm2_vm3 sem_vm3_vm4).
  Qed.

  Local Lemma Hfor : sem_Ind_for p ev Pi_r Pfor.
  Proof.
    move=> s1 s2 x d lo hi c vlo vhi cpl_lo cpl_hi cpl_for sem_s1_s2.
    move=> ii X c' /=; t_xrbindP=> {c'} c' c'E <-.
    rewrite !(read_Ii, write_Ii) !(read_i_for, write_i_for).
    move=> le_X vm1 eq_s1_vm1.
    case: (sem_s1_s2 X _ c'E _ _ eq_s1_vm1); first by SvD.fsetdec.
    move=> vm2 [eq_s2_vm2 sem_vm1_vm2]; exists vm2.
    split=> //; apply/sem_seq1/EmkI/(Efor (vlo := vlo) (vhi := vhi)) => //.
    + rewrite -(make_referenceprog_globs Hp) -cpl_lo.
      rewrite -(@read_e_eq_on _ Sv.empty) // -/(read_e _).
      by apply: (eq_onI _ eq_s1_vm1); SvD.fsetdec.
    + rewrite -(make_referenceprog_globs Hp) -cpl_hi.
      rewrite -(@read_e_eq_on _ Sv.empty) // -/(read_e _).
      by apply: (eq_onI _ eq_s1_vm1); SvD.fsetdec.
  Qed.

  Lemma mapM_size {eT aT bT : Type} (f : aT -> result eT bT) xs ys :
    mapM f xs = ok ys -> size xs = size ys.
  Proof.
  elim: xs ys => /= [|x xs ih] ys; first by case: ys.
  by t_xrbindP=> v _ vs /ih -> <-.
  Qed.

  Definition fresh_vars_in_prologue_i (i : instr) : option var :=
    if i is MkI _ (Cassgn (Lvar x) _ _ _) then Some (v_var x) else None.

  Lemma fresh_vars_in_prologueE c :
    fresh_vars_in_prologue c = pmap fresh_vars_in_prologue_i c.
  Proof. Admitted.

  Lemma read_es_eq_on_sym
     (gd : glob_decls) (es : pexprs) (X : Sv.t) (s : estate) (vm vm' : vmap)
  :
     vm =[read_es_rec X es]  vm' ->
       sem_pexprs gd (with_vm s vm) es = sem_pexprs gd (with_vm s vm') es.
  Proof.
  by apply: @read_es_eq_on gd es X (with_vm s vm) vm'.
  Qed.

  Lemma read_e_eq_on_sym
     (gd : glob_decls) (e : pexpr) (X : Sv.t) (s : estate) (vm vm' : vmap)
  :
     vm =[read_e_rec X e]  vm' ->
       sem_pexpr gd (with_vm s vm) e = sem_pexpr gd (with_vm s vm') e.
  Proof.
  by apply: @read_e_eq_on gd X vm' (with_vm s vm) e.
  Qed.

  Local Lemma Hcall : sem_Ind_call p ev Pi_r Pfun.
  Proof.
    (* f(x1 : v1, ..., xn : vn) : unit
     *
     * f(e1, ..., en)
     *
     *
     * y1 <- e1; ...; yn <- en; assert (forall i, [|yi|] = [|ei|]); body(f)
     *)


    move=> s1 m s2 ii lv fn args vargs aout eval_args h1 h2 h3.
    move=> ii' X c' hupd; rewrite !(read_Ii, write_Ii).
    rewrite !(read_i_call, write_i_call) => le_X vm1 eq_s1_vm1.
    move: hupd => /=; case sigE: (get_sig _) => [xargs xaout].
    case plE: (make_prologue _ _ _ _ _ _) => [pl eargs].
    case epE: (make_epilogue _ _ _ _ _ _) => [ep lvaout].
    t_xrbindP=> _ /assertP /and4P[uq_pl uq_ep /allP fs_pl /allP fs_ep] <-.
    have: exists vm, [
      /\ sem_pexprs (p_globs p') (with_vm s1 vm) eargs = ok vargs
       , evm s1 =[Sv.union X (read_es args)] vm
       & sem p' ev (with_vm s1 vm1) pl (with_vm s1 vm)
    ].
    + rewrite -(make_referenceprog_globs Hp).
      move: vm1 eq_s1_vm1 pl eargs uq_pl fs_pl plE eval_args.
      elim: xargs args vargs le_X {sigE h1 h2 h3 uq_ep fs_ep epE}.
      * move=> args vargs le_X vm1 eq_s1_vm1 pl eargs _ _.
        rewrite make_prologue0 => -[<- <-] eval_args.
        exists vm1; split=> //; last by constructor.
        - rewrite -(@read_es_eq_on _ _ X) // read_esE.
          by apply: (eq_onI _ eq_s1_vm1); SvD.fsetdec.
        - by apply: (eq_onI _ eq_s1_vm1); SvD.fsetdec.
      move=> x xargs ih /= [|arg args] vargs le_X vm1 eq_s1_vm1 pl eargs huniq hfresh.
        - rewrite make_prologue0r => -[<- <-] eval_args.
          exists vm1; split=> //=; last by constructor.
          by apply: (eq_onI _ eq_s1_vm1); SvD.fsetdec.
      case E: (is_reg_ptr_expr is_reg_ptr fresh_id p (v_var x) arg) => [y|].
      * rewrite (make_prologueS_Some _ _ _ E).
        set M := make_prologue _ _ _ _ _ _ => ME.
        case: ME huniq hfresh => [<- <-] Huniq Hfresh /=.
        t_xrbindP=> v sem_v vs sem_vs {vargs} <-.
        case: (ih args vs _ vm1 eq_s1_vm1 M.1 M.2) => //.
        - by move: le_X; rewrite read_es_cons; SvD.fsetdec.
        - move: Huniq; rewrite fresh_vars_in_prologueE.
          rewrite -cats1 pmap_cat /= -fresh_vars_in_prologueE.
          by rewrite uniq_catC /= => /andP[].
        - move=> x' x'_in_M1; apply: Hfresh.
          rewrite fresh_vars_in_prologueE -cats1 pmap_cat.
          by rewrite mem_cat -fresh_vars_in_prologueE x'_in_M1.
        - by rewrite [LHS]surjective_pairing.
        move=> vm [h1 h2 h3].
        have [vm' [h4 get_y h5]]: exists vm', [/\
            vm =[Sv.union (Sv.union X (read_es (arg :: args))) (read_es M.2)] vm'
          , get_var vm' y = ok v & set_var vm y v = ok vm'].
        - admit.
        exists vm'; split=> //.
        - rewrite /get_gvar /= get_y /= -(@read_es_eq_on_sym _ _ X _ vm); first last.
          + by apply: (eq_onI _ h4); rewrite !read_es_cons read_esE; SvD.fsetdec.
          by rewrite h1.
        - transitivity vm.
          + by apply: (eq_onI _ h2); move: le_X; rewrite read_es_cons; SvD.fsetdec.
          + by apply: (eq_onI _ h4); move: le_X; rewrite read_es_cons; SvD.fsetdec.
        - rewrite -cats1; apply: (sem_app h3).
          apply/sem_seq1/EmkI; apply Eassgn with v v.
          + rewrite -(@read_e_eq_on _ X).
            * by rewrite -(make_referenceprog_globs Hp).
            apply: (eq_onI _ h2); move: le_X.
            by rewrite read_eE read_es_cons; SvD.fsetdec.
          + admit.
          + by rewrite /= /write_var h5.
      * rewrite (make_prologueS_None _ _ _ E); set M := make_prologue _ _ _ _ _ _.
        move=> ME; case: ME huniq hfresh => [<- <-] Huniq Hfresh /=.
        t_xrbindP=> v sem_v; case: vargs => // _ _ vargs sem_vs [<- <-].
        case: (ih args vargs _ vm1 eq_s1_vm1 M.1 M.2) => //.
        - by move: le_X; rewrite read_es_cons; SvD.fsetdec.
        - by rewrite [LHS]surjective_pairing.
        move=> vm [h1 h2 h3]; exists vm; split=> //.
        - rewrite -(@read_e_eq_on _ X); last first.
          + rewrite read_eE; apply: (eq_onI _ h2).
            by move: le_X; rewrite read_es_cons; SvD.fsetdec.
          by rewrite sem_v /= h1.
        - by apply: (eq_onI _ h2); move: le_X; rewrite read_es_cons; SvD.fsetdec.
    case=> vm [h1_vm h2_vm h3_vm].
  Admitted.

  Local Lemma Hproc : sem_Ind_proc p ev Pc Pfun.
  Proof.
  Admitted.

  Lemma makeReferenceArguments_callP f mem mem' va vr:
    sem_call p ev mem f va mem' vr ->
    sem_call p' ev mem f va mem' vr.
  Proof.
    move=> Hsem.
    apply (@sem_call_Ind _ _ _ p ev Pc Pi_r Pi Pfor Pfun Hskip Hcons HmkI Hassgn Hopn
               Hif_true Hif_false Hwhile_true Hwhile_false Hfor Hfor_nil Hfor_cons Hcall Hproc
               mem f va mem' vr Hsem).
  Qed.

End Section.

  (*I should have something more specific than s1 and s2*)
  (*
  Lemma mkrefargs_c_incl s1 c s2 : Pc s1 c s2.
  Proof.
    move => X c' up vm1 eq.
    
  Qed.
  *)
