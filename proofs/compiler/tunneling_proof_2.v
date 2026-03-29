From ITree Require Import
  ITree
  ITreeFacts
  Basics.HeterogeneousRelations
  Interp.Recursion
  Eq.Rutt
  Eq.RuttFacts.

From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype.
From Coq Require Import ZArith.
From Coq Require Import Utf8.

Require Import expr_facts compiler_util label linear linear_sem linear_facts it_sems_core_defs relational_logic.
Require Import sem_params.
Import word_ssrZ.

Local Open Scope seq_scope.

Require Import oseq seq_extra unionfind tunneling unionfind_proof.
Require Import linear_sem.

Set SsrOldRewriteGoalsOrder.  (* change Set to Unset when porting the file, then remove the line when requiring MathComp >= 2.6 *)

Section WITH_PARAMS.

Context
  {wsw : WithSubWord}
  {asm_op syscall_state : Type}
  {ep : EstateParams syscall_state}
  {spp : SemPexprParams}
  {sip : SemInstrParams asm_op syscall_state}
  {ovm_i : one_varmap.one_varmap_info}.

Context (p:lprog).
Context (p' : lprog).
Context (pp' : tunnel_program p = ok p').

Lemma p_wf : well_formed_lprog p.
Proof. by move: pp'; rewrite /tunnel_program; case: ifP. Qed.

(* [path_to fn endpc l l'] :
   forall state s, if we can jump just after label (fn, l),
   then we can do a finite number of steps to reach the position
   just after label (fn, l').
   Furthermore the result state is unchanged, excepted the current program counter.
*)

Definition path_to fn endpc l l' :=
  forall s1 s2,
    eval_jump p (fn, l) s1 = ok s2 ->
    exists n,
      exists2 s3,
        lsem_body_n p (untilpc endpc) n.+1 s2 = ok (inl s3)
      & eval_jump p (fn, l') s1 = ok s3.

Definition path_to0 fn endpc l l' :=
  l = l' \/ path_to fn endpc l l'.

Lemma to_estate_eq_eval_jump s1 s2 l :
  to_estate s1 = to_estate s2 ->
  eval_jump p l s1 = eval_jump p l s2.
Proof.
  case: l => /= fn l; case: get_fundef => //= fd.
  case: find_label => //= l'.
  by rewrite -(of_estate_to_estate s1) -(of_estate_to_estate s2) /to_estate /of_estate /= => -[-> -> ->].
Qed.

Lemma eval_jump_to_estate l s1 s2 :
  eval_jump p l s1 = ok s2 -> to_estate s1 = to_estate s2.
Proof.
  case: l => /= fn l; case: get_fundef => //= fd.
  by t_xrbindP => l' _ <-; rewrite -(of_estate_to_estate s1).
Qed.

Lemma path_to_trans l2 l1 l3 fn endpc :
  path_to fn endpc l1 l2 ->
  path_to fn endpc l2 l3 ->
  path_to fn endpc l1 l3.
Proof.
  move=> h12 h23 s1 s2 hj1.
  have [n1 [s3 hsem1 hj2]] := h12 s1 s2 hj1.
  rewrite (to_estate_eq_eval_jump (fn, l2) (eval_jump_to_estate hj1)) in hj2.
  have [n2 [s4 hsem2 hj3]] := h23 s2 s3 hj2.
  exists (n1 + n2.+1); exists s4.
  + by rewrite -addSn lsem_body_n_add hsem1.
  rewrite -hj3.
  apply/to_estate_eq_eval_jump/(eval_jump_to_estate hj1).
Qed.

Lemma path_to0_trans l2 l1 l3 fn endpc :
  path_to0 fn endpc l1 l2 ->
  path_to0 fn endpc l2 l3 ->
  path_to0 fn endpc l1 l3.
Proof.
  move=> [-> // | h1] [ <-| h2].
  + by rewrite /path_to0; auto.
  have := path_to_trans h1 h2; rewrite /path_to0; auto.
Qed.

Definition wf_uf fn endpc (uf:LUF.unionfind) :=
  forall l,
    path_to0 fn endpc l (LUF.find uf l).

Lemma labels_of_body_cat c1 c2 :
  labels_of_body (c1 ++ c2) =
   labels_of_body c1 ++ labels_of_body c2.
Proof. by rewrite /labels_of_body pmap_cat. Qed.

Lemma labels_of_body_cons l c i :
  l \in labels_of_body (i :: c) =
   match li_i i with
   | Llabel _ lbl => l == lbl
   | _ => false
   end || (l \in labels_of_body c).
Proof. by rewrite /labels_of_body /=; case: li_i. Qed.

Lemma labels_of_body_rcons l c i :
  l \in labels_of_body (rcons c i) =
   (l \in labels_of_body c) ||
   match li_i i with
   | Llabel _ lbl => l == lbl
   | _ => false
   end.
Proof.
  by rewrite -cats1 labels_of_body_cat mem_cat labels_of_body_cons in_nil orbF.
Qed.

Lemma eval_jump_label s fn fd lc1 ii1 l1 lc2 :
  get_fundef (lp_funcs p) fn = Some fd ->
  uniq (labels_of_body (lfd_body fd)) ->
  lc1 ++ [:: {| li_ii := ii1; li_i := Llabel InternalLabel l1 |} & lc2] = lfd_body fd ->
  eval_jump p (fn, l1) s = ok (setcpc s fn (size lc1).+1).
Proof.
  move=> hget hu hcat.
  rewrite /eval_jump /find_instr /= hget /= -hcat.
  rewrite /find_label find_cat.
  case: (ifPn (has _ _)).
  + move=> hhas.
    move: hu; rewrite -hcat labels_of_body_cat cat_uniq.
    move=> /and3P [] _; rewrite -all_predC => /allP /(_ l1).
    rewrite labels_of_body_cons /= eqxx /= => /(_ erefl) /negP [].
    rewrite /labels_of_body => {hcat}.
    elim: lc1 hhas => //= i lc1 ih.
    case: i => ii [] //= lk l2.
    rewrite {1}/is_label /= in_cons => /orP [/eqP -> | /ih ->].
    + by rewrite eqxx.
    by rewrite orbT.
  rewrite /= {2 4}/is_label /= eqxx addn0 size_cat /=.
  by rewrite -ltn_subLR // subnn /=.
Qed.

Lemma eval_jump_label2 s fn fd lc1 ii1 l1 i2 lc2 :
  get_fundef (lp_funcs p) fn = Some fd ->
  uniq (labels_of_body (lfd_body fd)) ->
  lc1 ++ [:: {| li_ii := ii1; li_i := Llabel InternalLabel l1 |}, i2 & lc2] = lfd_body fd ->
  [/\ eval_jump p (fn, l1) s = ok (setcpc s fn (size lc1).+1)
    ,  (size lc1).+1 <> size (lfd_body fd)
    & find_instr p (setcpc s fn (size lc1).+1) = Some i2].
Proof.
  move=> hget hu hcat; split.
  + by apply: eval_jump_label hget hu hcat.
  + rewrite -hcat size_cat /=.
    by apply /eqP; rewrite addnS eqSS -{1}(addn0 (size lc1)) eqn_add2l.
  by rewrite /find_instr hget /= -hcat onth_cat -addn1 lt_nm_n /= subSnn.
Qed.

Lemma labels_of_find l c : l \in labels_of_body c -> exists pc, find_label l c = ok pc.
Proof.
  rewrite /find_label; elim: c => //= i c ih.
  have heq: ((find (is_label l) c).+1 < (size c).+1) = ((find (is_label l) c) < (size c)) by done.
  case: i => ii [] > /=;
   try by rewrite heq; move=> /ih [pc hpc]; exists pc.+1 => /=; case: ifP hpc => _ // [->].
  rewrite {1 3}/is_label /= in_cons; case: eqP => /=.
  + by exists 0.
  by rewrite heq => _ /ih [pc hpc]; exists pc.+1 => /=; case: ifP hpc => _ // [->].
Qed.

Definition wfend (endpc : funname * nat) :=
  match get_fundef (lp_funcs p) endpc.1 with
  | Some fd => endpc.2 = size (lfd_body fd)
  | _ => False
  end.

Lemma tunnel_plan_wf_aux endpc fn fd :
  wfend endpc ->
  get_fundef (lp_funcs p) fn = Some fd ->
  let lc := lfd_body fd in
  forall lc2 i lc1 uf,
    lc1 ++ i :: lc2 = lc ->
    (forall l, LUF.find uf l <> l -> l \in labels_of_body lc1) ->
    wf_uf fn endpc uf ->
    wf_uf fn endpc (pairfoldl (tunnel_chart fn) uf i lc2).
Proof.
  move=> hend hget /=.
  move/andP: p_wf => -[_ /allInP] /=.
  move=> /(_ _ (get_fundef_in' hget)) /= /andP [hu hgoto].
  elim => //= i2 lc2 ih i1 lc1 uf hcat hfind hwf.
  apply (ih i2 (rcons lc1 i1) (tunnel_chart fn uf i1 i2)).
  + by rewrite cat_rcons.
  + move=> l; rewrite /tunnel_chart labels_of_body_rcons.
    case: i1 hcat => ii1 [] /=; try by move=> > _ /hfind ->.
    case => /=; last by move=> > _ /hfind ->.
    move=> l1 hcat.
    have hl1 : LUF.find uf l1 = l1.
    + case: ((LUF.find uf l1) =P l1) => // /hfind hin.
      move: hu; rewrite -hcat labels_of_body_cat cat_uniq.
      move=> /and3P [_ /hasP] []; exists l1 => //.
      by rewrite labels_of_body_cons /= eqxx.
    case: i2 hcat => ii2 [] /=; try by move=> > _ /hfind ->.
    + case; last by move=> > _ /hfind ->.
      move=> l2 hcat; rewrite LUF.find_union hl1 eq_sym (eq_sym l).
      case: eqP; last by move=> _ /hfind ->.
      move=> <- _; rewrite orbC.
      by case: eqP => // /hfind ->.
    move=> [fn'  l']; case: eqP => _; last by move=> _ /hfind ->.
    move=> hcat; rewrite LUF.find_union hl1 eq_sym (eq_sym l).
    case: eqP; last by move=> _ /hfind ->.
    move=> <- _; rewrite orbC.
    by case: eqP => // /hfind ->.
  rewrite /tunnel_chart.
  case: i1 hcat => ii1 [] // [] // l1 hcat.
  have hl1 : LUF.find uf l1 = l1.
  + case: ((LUF.find uf l1) =P l1) => // /hfind hin.
    move: hu; rewrite -hcat labels_of_body_cat cat_uniq.
    move=> /and3P [_ /hasP] []; exists l1 => //.
    by rewrite labels_of_body_cons /= eqxx.
  case: i2 hcat => ii2 [] // [] //.
  + move=> l2 hcat.
    have hl2 : LUF.find uf l2 = l2.
    + case: ((LUF.find uf l2) =P l2) => // /hfind hin.
      move: hu; rewrite -hcat labels_of_body_cat cat_uniq.
      move=> /and3P [_ /hasP] []; exists l2 => //.
      by rewrite !labels_of_body_cons /= eqxx /= orbT.
    move=> l; rewrite LUF.find_union hl1 hl2 eq_sym.
    have p12 : path_to fn endpc l1 l2.
    + move=> s1 s2.
      have [hj hsz hfindi]:= eval_jump_label2 s1 hget hu hcat.
      rewrite hj => -[?]; subst s2.
      exists 0; exists (setcpc s1 fn (size lc1).+2).
      + rewrite /= /lsem_body /= /untilpc; case: eqP.
        + move=> ?; subst endpc.
          by move: hend; rewrite /wfend /= hget.
        by rewrite /step hfindi.
      rewrite -cat_rcons in hcat.
      by have := eval_jump_label s1 hget hu hcat; rewrite size_rcons.
    case: eqP => hfl; last by apply hwf.
    apply path_to0_trans with l1.
    + by rewrite -hfl; apply hwf.
    by rewrite /path_to0; auto.
  move=> fn' l2; case: eqP => // ? hcat; subst fn'.
  move=> l; rewrite LUF.find_union hl1 eq_sym.
  have p12 : path_to fn endpc l1 l2.
  + move=> s1 s2.
    have [hj hsz hfindi]:= eval_jump_label2 s1 hget hu hcat.
    rewrite hj => -[?]; subst s2.
    exists 0 => /=.
    move: hgoto; rewrite -hcat /goto_targets pmap_cat /= all_cat /=.
    move=> /and3P [_ + _]; rewrite eqxx /= hcat => /labels_of_find [pc hpc].
    exists (setcpc s1 fn pc.+1).
    + rewrite /= /lsem_body /untilpc /=; case: eqP.
      + move=> ?; subst endpc.
        by move: hend; rewrite /wfend /= hget.
      by rewrite /step hfindi /= /eval_instr /= hget /= hpc /=.
    by rewrite hget /= hpc.
  case: eqP => hfl; last by apply hwf.
  apply path_to0_trans with l1; first by rewrite -hfl; apply hwf.
  apply path_to0_trans with l2; last by apply hwf.
  rewrite /path_to0; auto.
Qed.

Lemma tunnel_plan_wf endpc fn fd :
  wfend endpc ->
  well_formed_lprog p ->
  get_fundef (lp_funcs p) fn = Some fd ->
  let lc := lfd_body fd in
  let uf := tunnel_plan fn LUF.empty lc in
  wf_uf fn endpc uf.
Proof.
  move=> hend wfp hget /=.
  rewrite /tunnel_plan.
  case heq : (lfd_body fd) => /= [ | i lc2].
  + by move=> l; rewrite LUF.find_empty /path_to0; auto.
  have /= /(_ lc2 i [::]):= tunnel_plan_wf_aux hend hget.
  rewrite heq /=; apply => // l; rewrite LUF.find_empty /path_to0; auto.
Qed.

Context {E E0: Type -> Type} {wE: with_Error E E0} {rE0 : EventRels E0}.

Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.

Lemma get_fundefE fn :
  get_fundef (lp_funcs p') fn =
    ssrfun.omap (tunnel_lfundef fn) (get_fundef (lp_funcs p) fn).
Proof.
  move: pp'; rewrite /tunnel_program; case: ifP => // _ [<-].
  by rewrite /get_fundef assoc_mapE.
Qed.

Lemma find_instrE s :
  match find_instr p s with
  | Some i =>
    exists2 fd, get_fundef (lp_funcs p) (lfn s) = Some fd &
        let uf := (tunnel_plan (lfn s) LUF.empty (lfd_body fd)) in
        find_instr p' s = Some (tunnel_bore (lfn s) uf i)
  | None => find_instr p' s = None
  end.
Proof.
  rewrite /find_instr get_fundefE.
  have := pp'.
  rewrite /tunnel_program; case: ifP => //= hwf _.
  case hget : get_fundef => [fd | ] //=.
  rewrite /tunnel_lcmd /tunnel_engine /tunnel_head.
  case hnth : onth => [ i | ]; last first.
  + by rewrite onth_map hnth.
  exists fd => //.
  by rewrite onth_map hnth.
Qed.

Lemma get_label_after_pcE s :
  get_label_after_pc p' s = get_label_after_pc p s.
Proof.
  rewrite /get_label_after_pc.
  case: find_instr (find_instrE (lnext_pc s)) => [ i [fd hget ->] | ->] //=.
  by case: i => ii [] //= [] >; case: ifP.
Qed.

Lemma label_in_lprogE :
  label_in_lprog p' = label_in_lprog p.
Proof.
  rewrite /label_in_lprog.
  move: pp'; rewrite /tunnel_program; case: ifP => // _ [<-] /=.
  f_equal.
  rewrite -map_comp; apply eq_map => - [fn fd] /=.
  f_equal.
  rewrite /label_in_lcmd /tunnel_lcmd /tunnel_engine /tunnel_head.
  move: (tunnel_plan _ _ _) => uf.
  elim: lfd_body => // i c ih /=; rewrite ih.
  by case: i => ii []// [] /= >; case: ifP.
Qed.

Lemma eval_jumpE d s : eval_jump p' d s = eval_jump p d s.
Proof.
  rewrite /eval_jump; case: d => fn lbl.
  rewrite get_fundefE; case: get_fundef => //= fd; f_equal.
  rewrite /find_label size_map.
  have -> // : find (is_label lbl) (tunnel_lcmd fn (lfd_body fd)) =
               find (is_label lbl) (lfd_body fd).
  by rewrite seq.find_map; apply eq_find => -[ii []] // [] > /=; case: ifP.
Qed.

Lemma lp_rspE : lp_rsp p' = lp_rsp p.
Proof. by move: pp'; rewrite /tunnel_program; case: ifP => // _ [<-]. Qed.

Lemma eval_instr_eq i s : eval_instr p' i s = eval_instr p i s.
Proof.
  rewrite /eval_instr.
  rewrite get_label_after_pcE label_in_lprogE lp_rspE.
  case: li_i => //.
  1: move=> [?|].
  all: by move=> >; repeat (apply bind_eq => // ?); rewrite eval_jumpE.
Qed.

Lemma find_instr_goto_targets P s fd i :
  get_fundef (lp_funcs p) (lfn s) = Some fd ->
  all P (goto_targets (lfn s) (lfd_body fd)) ->
  find_instr p s = Some i ->
  all P (goto_targets (lfn s) [::i]).
Proof.
  rewrite /find_instr => -> hall honth.
  have hcat := onth_take_drop honth.
  move: hall; rewrite hcat /goto_targets pmap_cat /= all_cat => /andP [_].
  set X := (X in oapp _ [::] X); rewrite -/X.
  by case: X => //= r /andP[->].
Qed.

Lemma tunnel_cmd endpc s :
  wfend endpc ->
  eqit eq true true (ilsem p' (untilpc endpc) s) (ilsem p (untilpc endpc) s).
Proof.
  move=> hend.
  apply rutt_extras.eqit_iter_n with eq => //.
  move=> {}s _ <-.
  setoid_rewrite i_lsem_body_n; setoid_rewrite i_lsem_body.
  rewrite /lsem_body /untilpc; case: eqP.
  + move=> ->; exists 0; rewrite /= /lsem_body eqxx /=.
    by apply eqit_Ret; constructor.
  move=> /eqP/negPf hne; rewrite /step.
  have := find_instrE s.
  case hi : find_instr => [[ii i] | /=]; last first.
  + move=> ->; exists 0.
    rewrite /= /lsem_body /untilpc hne /step /= hi /=; reflexivity.
  move=> [fd hget] ->.
  have huf := tunnel_plan_wf hend p_wf hget.
  rewrite /= in huf; move: (tunnel_plan _ _ _) huf => uf huf.
  move/andP: p_wf => -[_ /allInP] /= /(_ _ (get_fundef_in' hget)) /= /andP [_ hall].
  case: i hi;
   try by move=> > hi; exists 0; rewrite /= /lsem_body hne /step /= hi /=;
          rewrite ?eval_instr_eq ?Let_Let /=; reflexivity.
  + move=> [fn' r] /=; case: eqP; last first.
    + move=> _; exists 0; rewrite /= /lsem_body hne /step /= hi /=.
      rewrite eval_instr_eq Let_Let /=; reflexivity.
    have := huf r; rewrite /path_to0.
    case: (r =P LUF.find uf r).
    + move=> <-; exists 0; rewrite /= /lsem_body hne /step /= hi /=.
      rewrite eval_instr_eq Let_Let /=; reflexivity.
    move=> hr [ // | hp] ? hfindi; subst fn'.
    rewrite eval_instr_eq.
    have [pc heval]: exists pc, eval_jump p (lfn s, r) s = ok (setcpc s (lfn s) pc).
    + rewrite /eval_jump hget /=.
      have := find_instr_goto_targets hget hall hfindi.
      rewrite /= eqxx andbT /= => /labels_of_find [pc ->] /=; by eauto.
    have [n [s3 hsem hev]]:= hp _ _ heval.
    exists n.+1 => /=.
    rewrite {2}/lsem_body hne /= /step hfindi.
    rewrite /eval_instr /li_i heval hev /=.
    rewrite /= in hsem; rewrite hsem /=; reflexivity.
  move=> f r hfindi /=.
  have := huf r; rewrite /path_to0.
  case: (r =P LUF.find uf r).
  + move=> <-; exists 0; rewrite /= /lsem_body hne /step /= hfindi /=.
    rewrite eval_instr_eq Let_Let /=; reflexivity.
  move=> hr [ // | hp].
  rewrite eval_instr_eq.
  have [pc heval]: exists pc, eval_jump p (lfn s, r) s = ok (setcpc s (lfn s) pc).
  + rewrite /eval_jump hget /=.
    have := find_instr_goto_targets hget hall hfindi.
    rewrite /= eqxx andbT /= => /labels_of_find [pc ->] /=; by eauto.
  have [n [s3 hsem hev]]:= hp _ _ heval.
  rewrite /eval_instr /li_i.
  case heq: (Let x := _ in values.to_bool x) => [ [] | e /=]; last first.
  + exists 0; rewrite /= /lsem_body hne /step /= hfindi /eval_instr /li_i.
    rewrite heq /=; reflexivity.
  + exists 0; rewrite /= /lsem_body hne /step /= hfindi /eval_instr /li_i.
    rewrite heq /=; reflexivity.
  exists n.+1.
  rewrite hev /= {2}/lsem_body hne /step /= hfindi /eval_instr /li_i heval heq /=.
  rewrite /= in hsem; rewrite hsem /=; reflexivity.
Qed.

Lemma tunnel_funcs fn s :
  eqit eq true true (ilsem_exportcall p fn s) (ilsem_exportcall p' fn s).
Proof.
  symmetry.
  rewrite /ilsem_exportcall /endpc.
  rewrite get_fundefE; case hget: get_fundef => [fd | ] /=; last first.
  + rewrite !bind_throw; reflexivity.
  rewrite !bind_ret_l.
  apply eqit_bind; first reflexivity.
  move=> _; apply eqit_bind.
  + rewrite size_map.
    have := [elaborate endpc_untilpc hget]; rewrite /endpc hget => hcond.
    rewrite !(eq_ilsem _ _ hcond); apply tunnel_cmd.
    by rewrite /wfend /= hget.
  move=> s'; reflexivity.
Qed.

End WITH_PARAMS.
