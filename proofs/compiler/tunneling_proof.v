From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype.
Require Import ZArith.
Require Import Utf8.

Require Import oseq expr_facts compiler_util label linear linear_sem.
Require Import sem_params.
Import word_ssrZ.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope seq_scope.

Require Import seq_extra unionfind tunneling unionfind_proof.
Require Import linear_sem.



Section WITH_PARAMS.

Context
  {wsw : WithSubWord}
  {asm_op syscall_state : Type}
  {ep : EstateParams syscall_state}
  {spp : SemPexprParams}
  {sip : SemInstrParams asm_op syscall_state}
  {ovm_i : one_varmap.one_varmap_info}.

Section LprogSemProps.

  Definition is_goto fn l c :=
    match li_i c with
    | Lgoto (fn', l') => (fn == fn') && (l == l')
    | _ => false
    end.

  Definition is_cond pe l c :=
    li_i c = Lcond pe l.

  Definition li_is_label c :=
    if li_i c is Llabel InternalLabel _ then true else false.

  Definition li_is_goto c :=
    if li_i c is Lgoto _ then true else false.

  Definition li_is_cond c :=
    if li_i c is Lcond _ _ then true else false.

  Definition li_is_local_goto fn c :=
    if li_i c is Lgoto (fn', _) then fn == fn' else false.

  Definition is_local_goto_to_label fn c c' :=
    match li_i c, li_i c' with
    | Lgoto (fn', l), Llabel InternalLabel l' => (fn == fn') && (l == l')
    | _, _ => false
    end.

  Definition is_cond_to_label c c' :=
    match li_i c, li_i c' with
    | Lcond _ l, Llabel InternalLabel l' => l == l'
    | _, _ => false
    end.

  Lemma is_label_nth_onth lf l pc :
    is_label l (nth Linstr_align lf pc) ->
    exists ii k, onth lf pc = Some (MkLI ii (Llabel k l)).
  Proof.
    elim: lf pc => [|[ii i] lf IHlf] pc; first by rewrite nth_nil.
    case: pc => [|pc] //=.
    + move => Hislabel; exists ii; case: i Hislabel => //= k l' /eqP <-.
      by exists k.
    by apply/IHlf.
  Qed.

  Lemma is_goto_nth_onth lf fn l pc :
    is_goto fn l (nth Linstr_align lf pc) ->
    exists ii, onth lf pc = Some (MkLI ii (Lgoto (fn, l))).
  Proof.
    elim: lf pc => [|[ii i] lf IHlf] pc; first by rewrite nth_nil.
    case: pc => [|pc] //=.
    + move => Hisgoto; exists ii; case: i Hisgoto => //= -[? ?].
      by move => /andP [/eqP ? /eqP ?]; subst fn l.
    by apply/IHlf.
  Qed.

  Lemma lfd_body_setfb fd fb : lfd_body (setfb fd fb) = fb.
  Proof. by case: fd. Qed.

  Lemma setfb_lfd_body fd : setfb fd (lfd_body fd) = fd.
  Proof. by case: fd. Qed.

  Lemma lp_funcs_setfuncs p lf : lp_funcs (setfuncs p lf) = lf.
  Proof. by case: p. Qed.

  Lemma setfuncs_lp_funcs p : setfuncs p (lp_funcs p) = p.
  Proof. by case: p. Qed.

  Definition setfunc lf (fn : funname) (fd : lfundef) :=
    map (fun f => (f.1, if fn == f.1 then fd else f.2)) lf.

  Lemma setfunc_get_fundef lf fn fd :
    uniq (map fst lf) ->
    get_fundef lf fn = Some fd ->
    setfunc lf fn fd = lf.
  Proof.
    elim: lf => //= -[fn' fd'] lf IHlf; rewrite /fst /= -/fst => /andP.
    move => [Hnotin Huniq]; case: ifP => [/eqP ? [?]|_ Hgfd]; last by rewrite IHlf.
    subst fn' fd'; f_equal; rewrite /setfunc.
    elim: lf Hnotin {IHlf Huniq} => //= -[fn' fd'] lf IHlf.
    rewrite /fst /= -/fst in_cons negb_or; case: ifP => //= Hneq Hnotin.
    by rewrite IHlf.
  Qed.

  Lemma get_fundef_cat (lf1 lf2 : seq (funname * lfundef)) fn :
    get_fundef (lf1 ++ lf2) fn =
    match get_fundef lf1 fn with
    | Some fd => Some fd
    | None => get_fundef lf2 fn
    end.
  Proof. by rewrite /get_fundef assoc_cat; case: (assoc _ _). Qed.

  Lemma get_fundef_in (lf : seq (funname * lfundef)) fn :
    (isSome (get_fundef lf fn)) = (fn \in map fst lf).
  Proof.
    elim: lf => //= -[fn' fd] lf IHlf; rewrite /fst /= -/fst in_cons.
    by case: ifP => [/eqP ? //=|_]; rewrite Bool.orb_false_l.
  Qed.

  Lemma get_fundef_map2 (g : funname -> lfundef -> lfundef) lf fn :
    get_fundef (map (fun f => (f.1, g f.1 f.2)) lf) fn =
    match (get_fundef lf fn) with
    | Some fd => Some (g fn fd)
    | None => None
    end.
  Proof. by elim: lf => [|[fn'' fd''] lf IHlf] //=; case: ifP => // /eqP ->. Qed.

  Lemma get_fundef_map2_only_fn (g : lfundef -> lfundef) lf fn fn' :
    get_fundef (map (fun f => (f.1, if fn == f.1 then g f.2 else f.2)) lf) fn' =
    match get_fundef lf fn' with
    | Some fd => Some (if fn == fn' then g fd else fd)
    | None => None
    end.
  Proof. by rewrite (get_fundef_map2 (fun f1 f2 => if fn == f1 then g f2 else f2) lf). Qed.

  Lemma get_fundef_setfunc lf fn fn' fd :
    get_fundef (setfunc lf fn fd) fn' =
    if fn == fn'
    then 
      if fn \in map fst lf
      then Some fd
      else None
    else get_fundef lf fn'.
  Proof.
    rewrite get_fundef_map2_only_fn -get_fundef_in.
    case: ifP => [/eqP ?|Hneqfn]; last by case: (get_fundef _ _).
    by subst fn'; rewrite /isSome; case: (get_fundef _ _).
  Qed.

  Lemma map_fst_map_pair1 (g : funname -> lfundef -> lfundef) lf :
    map fst (map (fun f => (f.1, g f.1 f.2)) lf) = map fst lf.
  Proof. by rewrite -map_comp; set h:= (_ \o _); rewrite (@eq_map _ _ h fst). Qed.

End LprogSemProps.


Section TunnelingProps.

  Definition pair_pc lc pc :=
    [:: nth Linstr_align (Linstr_align :: lc) pc; nth Linstr_align (Linstr_align :: lc) pc.+1].

  Definition tunnel_lcmd_pc fn lc pc : lcmd :=
    tunnel_engine fn (pair_pc lc pc) lc.

  Definition tunnel_lfundef_pc fn fd pc :=
    setfb fd (tunnel_lcmd_pc fn (lfd_body fd) pc).

  Definition tunnel_funcs_pc lf fn pc :=
    match get_fundef lf fn with
    | Some fd => setfunc lf fn (tunnel_lfundef_pc fn fd pc)
    | None => lf
    end.

  Definition tunnel_lprog_pc p fn pc :=
    setfuncs p (tunnel_funcs_pc (lp_funcs p) fn pc).

  Definition tunnel_lcmd_fn_partial fn lc pc : lcmd :=
    tunnel_engine fn (take pc lc) lc.

  Definition tunnel_lfundef_fn_partial fn fd pc :=
    setfb fd (tunnel_lcmd_fn_partial fn (lfd_body fd) pc).

  Definition tunnel_funcs_fn_partial lf fn pc :=
    match get_fundef lf fn with
    | Some fd => setfunc lf fn (tunnel_lfundef_fn_partial fn fd pc)
    | None => lf
    end.

  Definition tunnel_lprog_fn_partial p fn pc :=
    setfuncs p (tunnel_funcs_fn_partial (lp_funcs p) fn pc).

  Definition tunnel_funcs_fn lf fn :=
    match get_fundef lf fn with
    | Some fd => setfunc lf fn (tunnel_lfundef fn fd)
    | None => lf
    end.

  Definition tunnel_lprog_fn p fn :=
    setfuncs p (tunnel_funcs_fn (lp_funcs p) fn).

  Definition tunnel_funcs_partial lf n :=
    tunnel_funcs (take n lf) ++ drop n lf.

  Definition tunnel_lprog_partial p n :=
    setfuncs p (tunnel_funcs_partial (lp_funcs p) n).

  Lemma size_tunnel_head fn uf lc :
    size (tunnel_head fn uf lc) = size lc.
  Proof. by rewrite /tunnel_head size_map. Qed.

  Lemma size_tunnel_engine fn lc lc' :
    size (tunnel_engine fn lc lc') = size lc'.
  Proof. by rewrite /tunnel_engine size_tunnel_head. Qed.

  Lemma size_tunnel_lcmd fn lc :
    size (tunnel_lcmd fn lc) = size lc.
  Proof. by rewrite /tunnel_lcmd size_tunnel_engine. Qed.

  Lemma labels_of_body_rcons lc c :
    labels_of_body (rcons lc c) =
    if li_i c is Llabel _ lbl
    then rcons (labels_of_body lc) lbl
    else labels_of_body lc.
  Proof. by rewrite /labels_of_body -cats1 pmap_cat -!/(labels_of_body _); case: c => ii [] //= *; rewrite ?cats0 ?cats1. Qed.

  Lemma labels_of_body_tunnel_head fn fb uf :
    labels_of_body (tunnel_head fn uf fb) = labels_of_body fb.
  Proof.
    elim: fb => //= -[ii i] fb ->.
    rewrite /tunnel_bore; case: i => // -[fn' fd'] /=.
    by case: ifP => //; case: ifP.
  Qed.

  Lemma labels_of_body_tunnel_engine fn fb fb' :
    labels_of_body (tunnel_engine fn fb fb') = labels_of_body fb'.
  Proof. by rewrite /tunnel_engine labels_of_body_tunnel_head. Qed.

  Lemma labels_of_body_tunnel_lcmd_pc fn fb pc :
    labels_of_body (tunnel_lcmd_pc fn fb pc) = labels_of_body fb.
  Proof. by rewrite /tunnel_lcmd_pc labels_of_body_tunnel_engine. Qed.

  Lemma funnames_setfunc lf fn fd :
    map fst (setfunc lf fn fd) = map fst lf.
  Proof.
    rewrite /setfunc.
    by move: (map_fst_map_pair1 (fun fn' fd' => if fn == fn' then fd else fd') lf) => ->.
  Qed.

  Lemma funnames_tunnel_funcs_pc lf fn pc :
    map fst (tunnel_funcs_pc lf fn pc) = map fst lf.
  Proof.
    rewrite /tunnel_funcs_pc; case Hgfd: (get_fundef _ _) => [fd|//].
    by rewrite funnames_setfunc.
  Qed.

  Lemma funnames_tunnel_funcs_fn lf fn :
    map fst (tunnel_funcs_fn lf fn) = map fst lf.
  Proof.
    rewrite /tunnel_funcs_fn; case Hgfd: (get_fundef _ _) => [fd|//].
    by rewrite funnames_setfunc.
  Qed.

  Lemma funnames_tunnel_funcs lf :
    map fst (tunnel_funcs lf) = map fst lf.
  Proof. by rewrite /tunnel_funcs map_fst_map_pair1. Qed.

  Lemma get_fundef_tunnel_funcs lf fn :
    get_fundef (tunnel_funcs lf) fn =
    match get_fundef lf fn with
    | Some fd => Some (tunnel_lfundef fn fd)
    | None => None
    end.
  Proof. by rewrite /tunnel_funcs get_fundef_map2. Qed.

  Variant tunnel_chart_spec fn (uf : LUF.unionfind) : linstr -> linstr -> LUF.unionfind -> Type :=
  | TC_LabelLabel ii ii' l l' :
      tunnel_chart_spec fn uf (MkLI ii (Llabel InternalLabel l)) (MkLI ii' (Llabel InternalLabel l')) (LUF.union uf l l')

  | TC_LabelGotoEq ii ii' l l' :
      tunnel_chart_spec fn uf (MkLI ii (Llabel InternalLabel l)) (MkLI ii' (Lgoto (fn, l'))) (LUF.union uf l l')

  | TC_LabelGotoNEq ii ii' l l' fn' of (fn != fn') :
      tunnel_chart_spec fn uf (MkLI ii (Llabel InternalLabel l)) (MkLI ii' (Lgoto (fn', l'))) uf

  | TC_Otherwise c c' of (~~ ((li_is_label c && li_is_label c') || (li_is_label c && li_is_goto c'))) :
      tunnel_chart_spec fn uf c c' uf.

  Lemma tunnel_chartP fn uf c c' : tunnel_chart_spec fn uf c c' (tunnel_chart fn uf c c').
  Proof.
  case: c c' => [ii i] [ii' i']; case: i'; case: i; try by move=> *; apply: TC_Otherwise.
  all: case; try by move => *; apply: TC_Otherwise.
  + move => l [] >.
    - exact: TC_LabelLabel.
    exact: TC_Otherwise.
  move=> l [fn' l'] /=; case: ifPn => [/eqP<-|].
  + by apply: TC_LabelGotoEq.
  by apply: TC_LabelGotoNEq.
  Qed.

  Lemma tunnel_plan_nil fn uf :
    tunnel_plan fn uf [::] = uf.
  Proof. by rewrite /tunnel_plan /tunnel_chart. Qed.

  Lemma tunnel_plan1 fn uf c :
    tunnel_plan fn uf [:: c] = uf.
  Proof. by rewrite /tunnel_plan /tunnel_chart. Qed.

  Lemma tunnel_plan_cons_cons fn uf fb c c' :
    tunnel_plan fn uf (c :: c' :: fb) = tunnel_plan fn (tunnel_chart fn uf c c') (c' :: fb).
  Proof. by rewrite /tunnel_plan. Qed.

  Lemma tunnel_plan_rcons_rcons fn uf fb c c' :
    tunnel_plan fn uf (rcons (rcons fb c) c') = tunnel_chart fn (tunnel_plan fn uf (rcons fb c)) c c'.
  Proof. by rewrite /tunnel_plan pairfoldl_rcons last_rcons. Qed.

  Lemma find_tunnel_plan_rcons_id fn lc c l :
    l \notin labels_of_body lc ->
    uniq (labels_of_body (rcons lc c)) ->
    LUF.find (tunnel_plan fn LUF.empty (rcons lc c)) l = l.
  Proof.
    elim/last_ind: lc c l => //= lc c'.
    move => IHlc c l; rewrite tunnel_plan_rcons_rcons labels_of_body_rcons; move: IHlc.
    have Htunnel_chart:= (tunnel_chartP fn (tunnel_plan fn LUF.empty (rcons lc c')) c' c).
    inversion Htunnel_chart
    as [ii ii' l' l''
       |ii ii' l' l'' Heqc' Heqc Heq
       |ii ii' l' l'' fn' Hneqfn Heqc' Heqc Heq
       |c'' c''' Hnor Heqc' Heqc Heq];
    subst c c' => {Htunnel_chart} IHlc /=.
    + rewrite mem_rcons in_cons negb_or => /andP /= [Hneql Hnotin].
      rewrite !labels_of_body_rcons /= !rcons_uniq => /andP [_ /andP [Hnotin' Huniq]].
      rewrite LUF.find_union (IHlc _ l) //; last first.
      - by rewrite labels_of_body_rcons /= rcons_uniq Hnotin'.
      rewrite (IHlc _ l') //; last first.
      - by rewrite labels_of_body_rcons /= rcons_uniq Hnotin'.
      by case: ifP => // /eqP ?; subst l'; rewrite eq_refl in Hneql.
    + rewrite mem_rcons in_cons negb_or => /andP /= [Hneql Hnotin] {Heq}.
      rewrite !labels_of_body_rcons /= rcons_uniq => /andP [Hnotin' Huniq].
      rewrite eq_refl LUF.find_union (IHlc _ l) //; last first.
      - by rewrite labels_of_body_rcons /= rcons_uniq Hnotin'.
      rewrite (IHlc _ l') //; last first.
      - by rewrite labels_of_body_rcons /= rcons_uniq Hnotin'.
      by case: ifP => // /eqP ?; subst l'; rewrite eq_refl in Hneql.
    + rewrite mem_rcons in_cons negb_or => /andP /= [Hneql Hnotin] {Heq}.
      rewrite !labels_of_body_rcons /= rcons_uniq => /andP [Hnotin' Huniq].
      case: ifP; last by rewrite IHlc // labels_of_body_rcons /= rcons_uniq Hnotin'.
      by move => /eqP ?; subst fn'; rewrite eq_refl in Hneqfn.
    move: Hnor (IHlc c'' l) => {Heq IHlc}; case: c''' c'' => [ii' i'] [ii i].
    by case: i => [? ? ?|?|? ?| | |? ?|[? ?]|?|? ?|? ?]; (case: i' => [? ? ?|?|? ?| | |? ?|[? ?]|?|? ?|? ?] //= _ IHlc);
    rewrite labels_of_body_rcons //= => Hnotin; (try by rewrite rcons_uniq => /andP [_]; apply IHl);
    (try by move: Hnotin; rewrite mem_rcons in_cons negb_or => /andP /= [_ Hnotin]; apply IHlc);
    rewrite rcons_uniq => /andP [_]; apply IHlc => //;
    move: Hnotin; rewrite mem_rcons in_cons negb_or => /andP [].
  Qed.

  Variant tunnel_bore_weak_spec fn uf : linstr -> linstr -> Type :=
  | TBW_GotoEq ii l :
      tunnel_bore_weak_spec fn uf (MkLI ii (Lgoto (fn, l))) (MkLI ii (Lgoto (fn, LUF.find uf l)))
  | TBW_Cond ii pe l :
      tunnel_bore_weak_spec fn uf (MkLI ii (Lcond pe l)) (MkLI ii (Lcond pe (LUF.find uf l)))
  | TBW_Otherwise c :
      tunnel_bore_weak_spec fn uf c c.

  Variant tunnel_bore_spec fn uf : linstr -> linstr -> Type :=
  | TB_GotoEq ii l :
      tunnel_bore_spec fn uf (MkLI ii (Lgoto (fn, l))) (MkLI ii (Lgoto (fn, LUF.find uf l)))
  | TB_GotoNEq ii l fn' of (fn != fn') :
      tunnel_bore_spec fn uf (MkLI ii (Lgoto (fn', l))) (MkLI ii (Lgoto (fn', l)))
  | TB_Cond ii pe l :
      tunnel_bore_spec fn uf (MkLI ii (Lcond pe l)) (MkLI ii (Lcond pe (LUF.find uf l)))
  | TB_Otherwise c  of (~~ (li_is_goto c || li_is_cond c)):
      tunnel_bore_spec fn uf c c.

  Lemma tunnel_boreWP fn uf c : tunnel_bore_weak_spec fn uf c (tunnel_bore fn uf c).
  Proof.
    case: c => [ii i]; case: i.
    1-6,8-9:
      by intros; apply: TBW_Otherwise.
    + move => [? ?] /=; case: ifPn => [/eqP <-|].
      - by apply: TBW_GotoEq.
      by intros; apply: TBW_Otherwise.
    by intros => /=; apply: TBW_Cond.
  Qed.

  Lemma tunnel_boreP fn uf c : tunnel_bore_spec fn uf c (tunnel_bore fn uf c).
  Proof.
    case: c => [ii i]; case: i.
    1-6,8-9:
      by intros; apply: TB_Otherwise.
    + move => [fn' ?] /=; case: ifPn => [/eqP <-|].
      - by apply: TB_GotoEq.
      by intros; apply: TB_GotoNEq.
    by intros => /=; apply: TB_Cond.
  Qed.

  Lemma tunnel_bore_empty fn :
    tunnel_bore fn LUF.empty =1 idfun.
  Proof. by case/tunnel_boreWP. Qed.

  Lemma tunnel_bore_union fn uf l l' :
    LUF.find uf l = l ->
    forall c,
      tunnel_bore fn (LUF.union uf l l') c =
      tunnel_bore fn (LUF.union LUF.empty l (LUF.find uf l')) (tunnel_bore fn uf c).
  Proof.
    move => Heqfindl c.
    case: (tunnel_boreP fn uf c) => [ii l''|ii l'' fn'|ii pe l''|c'] //=.
    + by rewrite eq_refl !LUF.find_union !LUF.find_empty Heqfindl.
    + by case: ifP.
    + by rewrite !LUF.find_union !LUF.find_empty Heqfindl.
    by case: c' => ii [].
  Qed.

  Lemma tunnel_head_empty fn :
    tunnel_head fn LUF.empty =1 idfun.
  Proof. by move => ? /=; rewrite /tunnel_head (eq_map (tunnel_bore_empty fn)) map_id. Qed.

  Lemma tunnel_head_union fn uf l l' lc :
    LUF.find uf l = l ->
    tunnel_head fn (LUF.union uf l l') lc =
    tunnel_head fn (LUF.union LUF.empty l (LUF.find uf l')) (tunnel_head fn uf lc).
  Proof.
    move => Heqfindl; rewrite /tunnel_head.
    by rewrite (eq_map (@tunnel_bore_union fn uf l l' _)) // map_comp.
  Qed.

  Lemma nth_align_tunnel_head fn uf lc pc :
    nth Linstr_align (tunnel_head fn uf lc) pc = tunnel_bore fn uf (nth Linstr_align lc pc).
  Proof.
    rewrite /tunnel_head.
    case Hsize: (pc < size lc); last first.
    + move: (negbT Hsize); rewrite -leqNgt => {Hsize} Hsize.
      by rewrite !nth_default // size_map.
    by rewrite (@nth_map _ Linstr_align).
  Qed.

  Variant tunnel_lcmd_pc_spec fn (lc : lcmd) pc : lcmd -> Type :=
  | TL_LabelLabel l l' :
      is_label l (nth Linstr_align (Linstr_align :: lc) pc) ->
      is_label l' (nth Linstr_align (Linstr_align :: lc) pc.+1) ->
      tunnel_lcmd_pc_spec fn lc pc (tunnel_head fn (LUF.union LUF.empty l l') lc)

  | TL_LabelGotoEq l l' :
      is_label l (nth Linstr_align (Linstr_align :: lc) pc) ->
      is_goto fn l' (nth Linstr_align (Linstr_align :: lc) pc.+1) ->
      tunnel_lcmd_pc_spec fn lc pc (tunnel_head fn (LUF.union LUF.empty l l') lc)

  | TL_LabelGotoNEq l l' fn' :
      fn != fn' ->
      is_label l (nth Linstr_align (Linstr_align :: lc) pc) ->
      is_goto fn' l' (nth Linstr_align (Linstr_align :: lc) pc.+1) ->
      tunnel_lcmd_pc_spec fn lc pc lc

  | TL_Otherwise :
      ~~ ((li_is_label (nth Linstr_align (Linstr_align :: lc) pc) &&
           li_is_label (nth Linstr_align (Linstr_align :: lc) pc.+1)) || 
          (li_is_label (nth Linstr_align (Linstr_align :: lc) pc) &&
           li_is_goto (nth Linstr_align (Linstr_align :: lc) pc.+1))) ->
      tunnel_lcmd_pc_spec fn lc pc lc.

  Lemma tunnel_lcmd_pcP fn lc pc :
    tunnel_lcmd_pc_spec fn lc pc (tunnel_lcmd_pc fn lc pc).
  Proof.
    rewrite /tunnel_lcmd_pc /tunnel_engine /pair_pc /tunnel_plan /=.
    set c:= nth _ _ _; set c':= nth _ _ _.
    have Htunnel_chart:= (tunnel_chartP fn LUF.empty c c').
    inversion Htunnel_chart as
      [ii ii' l l' Heqc Heqc' Heq
      |ii ii' l l' Heqc Heqc' Heq
      |ii ii' l l' fn' Hneqfn Heqc Heqc' Heq
      |c'' c''' Hneg Heqc Heqc' Heq];
    rewrite /c in Heqc; rewrite /c' in Heqc' => /= {Htunnel_chart Heq}.
    + apply TL_LabelLabel.
      - by rewrite -Heqc /is_label /= eq_refl.
      by rewrite /= -Heqc' /is_label /= eq_refl.
    + rewrite eq_refl; apply TL_LabelGotoEq.
      - by rewrite -Heqc /is_label /= eq_refl.
      by rewrite /= -Heqc' /is_goto /= !eq_refl.
    + case: ifP => [/eqP ?|_]; first by subst fn'; rewrite eq_refl in Hneqfn.
      rewrite tunnel_head_empty /=; apply (@TL_LabelGotoNEq _ _ _ l l' fn') => //.
      - by rewrite -Heqc /is_label /= eq_refl.
      by rewrite /= -Heqc' /is_goto /= !eq_refl.
    by subst c'' c'''; rewrite tunnel_head_empty /=; apply TL_Otherwise.
  Qed.

  Lemma tunnel_lcmd_fn_partial0 fn lc :
    tunnel_lcmd_fn_partial fn lc 0 = lc.
  Proof. by rewrite /tunnel_lcmd_fn_partial take0 /tunnel_engine /tunnel_plan /= tunnel_head_empty. Qed.

  Lemma subseq_pmap_take {aT: Type} {rT: eqType} (f: aT → option rT) n m :
    subseq (pmap f (take n m)) (pmap f m).
  Proof.
    elim: n m; first by move => ?; rewrite take0 sub0seq.
    move => n ih [] // a m; rewrite /take -/(take n m) /pmap -!/(pmap f _).
    case: (f a); last exact: ih.
    by move => r; rewrite /= eqxx.
  Qed.

  Lemma tunnel_lcmd_fn_partial_pc fn lc pc :
    uniq (labels_of_body lc) ->
    tunnel_lcmd_fn_partial fn lc pc.+1 = tunnel_lcmd_pc fn (tunnel_lcmd_fn_partial fn lc pc) pc.
  Proof.
    rewrite /tunnel_lcmd_fn_partial /tunnel_lcmd_pc /tunnel_engine => Huniq.
    have Hsubseq: subseq (labels_of_body (take pc.+1 lc)) (labels_of_body lc).
    + exact: subseq_pmap_take.
    move: (subseq_uniq Hsubseq Huniq) => {Hsubseq Huniq}.
    case Hsize: (pc < size lc); last first.
    + move: (negbT Hsize); rewrite -leqNgt => {Hsize} Hsize.
      rewrite !take_oversize //; last by apply/leqW.
      rewrite /pair_pc (@nth_default _ _ _ (pc.+1)) /=; last first.
      - by rewrite size_tunnel_head //; apply/leqW.
      rewrite tunnel_plan_cons_cons tunnel_plan1 /= /tunnel_chart /=.
      by case: (nth _ _ _) => _ [ | | | | |[] l| | | | ]; rewrite /= tunnel_head_empty.
    rewrite (take_nth Linstr_align) //; case: pc Hsize => [|pc] Hsize.
    + rewrite take0 /= tunnel_plan1 tunnel_plan_nil.
      rewrite tunnel_head_empty /= /pair_pc /=.
      by rewrite /tunnel_plan /= tunnel_head_empty.
    rewrite (take_nth Linstr_align); last by exact (ltnW Hsize).
    rewrite tunnel_plan_rcons_rcons /pair_pc.
    set c:= nth _ _ _; set c':= nth _ _ _; set tc:= nth _ _ _; set tc':= nth _ _ _.
    have ->: [:: tc; tc'] = rcons (rcons [::] tc) tc' by trivial.
    rewrite tunnel_plan_rcons_rcons tunnel_plan1 /tc /tc'.
    rewrite -2!nth_behead /behead !nth_align_tunnel_head -/c -/c'.
    move: {tc tc'} c c' => c c'; set uf:= tunnel_plan _ _ _.
    have := (tunnel_chartP fn uf c c'); rewrite /uf => {uf} Htunnel_chart.
    inversion Htunnel_chart
    as [ii ii' l' l''
       |ii ii' l' l'' Heqc' Heqc Heq
       |ii ii' l' l'' fn' Hneqfn Heqc' Heqc Heq
       |c'' c''' Hnor Heqc' Heqc Heq];
    subst c c' => {Htunnel_chart} //=;
    rewrite !labels_of_body_rcons //=.
    + rewrite !rcons_uniq => /andP [Hnotin'' /andP [Hnotin' Huniq]].
      rewrite tunnel_head_union //; last first.
      - rewrite find_tunnel_plan_rcons_id //.
        by rewrite labels_of_body_rcons /= rcons_uniq Hnotin'.
      rewrite find_tunnel_plan_rcons_id //.
      - apply/negP => Hin; move: Hnotin'' => /negP Hnotin''; apply/Hnotin''.
        by rewrite mem_rcons in_cons Hin; case: (_ == _).
      by rewrite labels_of_body_rcons /= rcons_uniq Hnotin'.
    + rewrite !eq_refl rcons_uniq => {Heq} /andP [Hnotin' Huniq].
      set uf:= tunnel_plan _ _ _; rewrite tunnel_head_union //.
      rewrite find_tunnel_plan_rcons_id //.
      by rewrite labels_of_body_rcons /= rcons_uniq Hnotin'.
    + case: ifP; first by move => /eqP ?; subst fn'; rewrite eq_refl in Hneqfn. 
      by move => -> /= {Heq}; rewrite tunnel_head_empty.
    move: Hnor {Heq}; case c'' => [ii i]; case c''' => [ii' i'].
    by case i => [? ? ?|?|? ?| | |[] ?|[? ?]|?|? ?|? ?]; (case i' => [? ? ?|? ?|?| | |[] ?|[? ?]|?|? ?|? ?] //=);
    rewrite ?tunnel_head_empty //; case: ifP; rewrite tunnel_head_empty.
  Qed.

  Lemma tunnel_lcmd_fn_partial_eq fn lc :
    tunnel_lcmd fn lc = tunnel_lcmd_fn_partial fn lc (size lc).
  Proof. by rewrite /tunnel_lcmd_fn_partial /tunnel_lcmd take_size. Qed.

  Lemma tunnel_funcs_rcons lf fn fd :
    tunnel_funcs (rcons lf (fn, fd)) =
    rcons (tunnel_funcs lf) (fn, tunnel_lfundef fn fd).
  Proof. by rewrite /tunnel_funcs map_rcons. Qed.

  Lemma tunnel_funcs_fn_partial0 lf fn :
    uniq (map fst lf) ->
    tunnel_funcs_fn_partial lf fn 0 = lf.
  Proof.
    rewrite /tunnel_funcs_fn_partial /tunnel_lfundef_fn_partial.
    case Hgfd: (get_fundef _ _) => [fd|//] Huniq.
    by rewrite tunnel_lcmd_fn_partial0 setfb_lfd_body setfunc_get_fundef.
  Qed.

  Lemma tunnel_funcs_fn_partial_pc lf fn pc :
    match get_fundef lf fn with
    | Some fd =>
        uniq (labels_of_body (lfd_body fd)) ->
        tunnel_funcs_fn_partial lf fn pc.+1 = tunnel_funcs_pc (tunnel_funcs_fn_partial lf fn pc) fn pc
    | None => tunnel_funcs_fn_partial lf fn pc.+1 = lf
    end.
  Proof.
    rewrite /tunnel_funcs_fn_partial /tunnel_funcs_pc.
    case Hgfd: (get_fundef _ _) => [fd|//].
    rewrite get_fundef_setfunc eq_refl -get_fundef_in Hgfd /=.
    rewrite /tunnel_lfundef_fn_partial /tunnel_lfundef_pc /setfunc -map_comp.
    move => Huniq; rewrite tunnel_lcmd_fn_partial_pc // lfd_body_setfb.
    set f:= (fun _ => _); set g:= (fun _ => _); rewrite (@eq_map _ _ f (f \o g)) //.
    by rewrite /f /g => -[fn' fd'] //=; case: ifP.
  Qed.

  Lemma tunnel_funcs_fn_partial_eq lf fn :
    uniq (map fst lf) ->
    tunnel_funcs_fn lf fn =
    match get_fundef lf fn with
    | Some fd => tunnel_funcs_fn_partial lf fn (size (lfd_body fd))
    | None => lf
    end.
  Proof.
    rewrite /tunnel_funcs_fn_partial /tunnel_funcs_fn => Huniq.
    case: (get_fundef _ _) => // fd.
    rewrite /setfunc /tunnel_lfundef_fn_partial /tunnel_lfundef.
    by rewrite tunnel_lcmd_fn_partial_eq.
  Qed.

  Lemma tunnel_funcs_partial0 lf :
    tunnel_funcs_partial lf 0 = lf.
  Proof. by rewrite /tunnel_funcs_partial take0 drop0. Qed.

  Lemma tunnel_funcs_partial_fn lf n :
    uniq (map fst lf) ->
    tunnel_funcs_partial lf n.+1 =
    match onth lf n with
    | Some (fn, _) => tunnel_funcs_fn (tunnel_funcs_partial lf n) fn
    | None => tunnel_funcs_partial lf n
    end.
  Proof.
    rewrite /tunnel_funcs_partial -{1}(@cat_take_drop n.+1 _ lf).
    rewrite take_onth (drop_onth n); case Honth: (onth _ _) => [[fn fd]|] //.
    rewrite tunnel_funcs_rcons cat_rcons /tunnel_funcs_fn.
    rewrite get_fundef_cat /= eq_refl get_fundef_tunnel_funcs.
    rewrite map_cat /= cat_uniq /= negb_or.
    move => /andP [_ /andP [/andP [Hnotint _] /andP [Hnotind _]]].
    move: (get_fundef_in (take n lf) fn).
    case Hgfd: (get_fundef _ _) => [fd'|] //=.
    + by move => Hin; rewrite -Hin in Hnotint.
    move => _; rewrite /setfunc map_cat /= eq_refl cat_rcons.
    f_equal; last first.
    + f_equal; move: Hnotind {Honth Hnotint Hgfd}.
      set lfd:= drop _ _; move: lfd => lfd {lf}.
      elim: lfd => //= -[fn' fd'] lfd IHlfd.
      rewrite in_cons negb_or => /andP [Hneq Hnotin].
      by rewrite -IHlfd //; move: Hneq; rewrite /fst /=; case: ifP.
    rewrite -funnames_tunnel_funcs in Hnotint.
    move: Hnotint {Honth Hnotind Hgfd}.
    set lft:= tunnel_funcs _; move: lft => lft {lf}.
    elim: lft => //= -[fn' fd'] lft IHlft.
    rewrite in_cons negb_or => /andP [Hneq Hnotin].
    by rewrite -IHlft //; move: Hneq; rewrite /fst /=; case: ifP.
  Qed.

  Lemma tunnel_funcs_partial_eq lf :
    tunnel_funcs lf = tunnel_funcs_partial lf (size lf).
  Proof. by rewrite /tunnel_funcs_partial take_size drop_size cats0. Qed.

  Lemma tunnel_lprog_fn_partial0 p fn :
    uniq (map fst (lp_funcs p)) ->
    tunnel_lprog_fn_partial p fn 0 = p.
  Proof.
    rewrite /tunnel_lprog_fn_partial => Huniq.
    by rewrite tunnel_funcs_fn_partial0 // setfuncs_lp_funcs.
  Qed.

  Lemma tunnel_lprog_fn_partial_pc p fn pc :
    match get_fundef (lp_funcs p) fn with
    | Some fd =>
        uniq (labels_of_body (lfd_body fd)) ->
        tunnel_lprog_fn_partial p fn pc.+1 = tunnel_lprog_pc (tunnel_lprog_fn_partial p fn pc) fn pc
    | None => tunnel_lprog_fn_partial p fn pc.+1 = p
    end.
  Proof.
    rewrite /tunnel_lprog_fn_partial /tunnel_lprog_pc /setfuncs.
    move: (tunnel_funcs_fn_partial_pc (lp_funcs p) fn pc).
    case Hgfd: (get_fundef _ _) => [fd|//]; case: {Hgfd} p => ? ? ? ? ? //=.
    + by move => Heq Huniq; rewrite Heq.
    by move => ->.
  Qed.

  Lemma tunnel_lprog_fn_partial_eq p fn :
    uniq (map fst (lp_funcs p)) ->
    tunnel_lprog_fn p fn =
    match get_fundef (lp_funcs p) fn with
    | Some fd => tunnel_lprog_fn_partial p fn (size (lfd_body fd))
    | None => p
    end.
  Proof.
    rewrite /tunnel_lprog_fn_partial /tunnel_lprog_fn => Huniq.
    rewrite tunnel_funcs_fn_partial_eq // /setfuncs.
    by case: {Huniq} p => ? ? ? ? ?; case: (get_fundef _ _).
  Qed.

  Lemma tunnel_lprog_partial0 p :
    tunnel_lprog_partial p 0 = p.
  Proof. by rewrite /tunnel_lprog_partial tunnel_funcs_partial0 setfuncs_lp_funcs. Qed.

  Lemma tunnel_lprog_partial_fn p n :
    uniq (map fst (lp_funcs p)) ->
    tunnel_lprog_partial p n.+1 =
    match onth (lp_funcs p) n with
    | Some (fn, _) => tunnel_lprog_fn (tunnel_lprog_partial p n) fn
    | None => tunnel_lprog_partial p n
    end.
  Proof.
    rewrite /tunnel_lprog_fn /tunnel_lprog_partial lp_funcs_setfuncs => Huniq.
    rewrite tunnel_funcs_partial_fn //; case: (onth _ _) => // -[fn _].
    by case: {Huniq} p => ? ? ? ?; rewrite /setfuncs.
  Qed.

  Lemma tunnel_lprog_partial_eq p :
    tunnel_lprog p = tunnel_lprog_partial p (size (lp_funcs p)).
  Proof. by rewrite /tunnel_lprog_partial /tunnel_lprog tunnel_funcs_partial_eq. Qed.

End TunnelingProps.


Section TunnelingWFProps.

  Lemma well_formed_tunnel_lcmd_pc fn fb pc :
    well_formed_body fn fb →
    well_formed_body fn (tunnel_lcmd_pc fn fb pc).
  Proof.
    rewrite /well_formed_body labels_of_body_tunnel_lcmd_pc.
    move => /andP [->] /=.
    have Htunnel_lcmd:= tunnel_lcmd_pcP fn fb pc.
    inversion Htunnel_lcmd as
      [l l' Hpc HSpc Heq
      |l l' Hpc HSpc Heq
      |l l' fn' Hneq Hpc HSpc Heq
      |Hneg Heq].
    3-4:
      by rewrite -!Heq.
    + clear Heq Htunnel_lcmd.
      all: rewrite !all_pmap all_map => /allE/List.Forall_forall h; apply/allE/List.Forall_forall => i hi.
      all: move/h: (hi).
      all: case: i hi => ii [] // [] /= f lbl hi.
      all: case: ifP => /= -> //=.
      all: rewrite LUF.find_union !LUF.find_empty.
      all: case: eqP => // ? _; subst lbl.
      { case/is_label_nth_onth: HSpc => jj [] k /= /(@onth_In _ _); clear.
        elim: fb; first by [].
        case => ii /= i m ih [].
        - by case => _{ii} ->{i}; rewrite inE eqxx.
       by move/ih; case: i => //= ? ?; rewrite inE => ->; rewrite orbT. }
      case/is_goto_nth_onth: HSpc => jj /= /(@onth_In _ _ _ _) /h.
      by rewrite /= eqxx.
  Qed.

  Lemma well_formed_tunnel_lcmd fn fb :
    well_formed_body fn fb →
    well_formed_body fn (tunnel_lcmd fn fb).
  Proof.
    rewrite tunnel_lcmd_fn_partial_eq => Hwf.
    elim: (size fb) => [|n IHn]; first by rewrite tunnel_lcmd_fn_partial0.
    rewrite tunnel_lcmd_fn_partial_pc; last first.
    + by move: Hwf; rewrite /well_formed_body => /andP [].
    by apply/well_formed_tunnel_lcmd_pc.
  Qed.

  Lemma get_fundef_well_formed_funcs_body lf fn fd :
    get_fundef lf fn = Some fd ->
    well_formed_funcs lf ->
    well_formed_body fn (lfd_body fd).
  Proof.
    move => Hgfd /andP [_]; move: Hgfd.
    elim: lf => //= -[fn' fd'] lf IHlf.
    case: ifP; last by move => _ Hgfd /andP [_]; apply/IHlf.
    by move => /eqP ? [?] /= /andP [Hwfb _]; subst fn' fd'.
  Qed.

  Lemma well_formed_tunnel_funcs_pc lf fn pc :
    well_formed_funcs lf ->
    well_formed_funcs (tunnel_funcs_pc lf fn pc).
  Proof.
    rewrite /well_formed_funcs => /andP [Huniq Hall]; apply/andP; split.
    + by rewrite funnames_tunnel_funcs_pc.
    rewrite /tunnel_funcs_pc; case Hgfd: (get_fundef _ _) => [fd|//].
    rewrite /setfunc all_map; elim: lf Hgfd Huniq Hall => //= -[fn' fd'] lf IHlf.
    case: ifP => [/eqP ? [?]|_ ? /andP [_ ?] /andP [-> /=]]; last by apply IHlf.
    subst fn' fd' => /andP [Hnotin Huniq] /andP [Hwf Hall]; apply/andP; split; last first.
    + rewrite {1}/fst /= in Hnotin; move: Hnotin Hall {IHlf Huniq Hwf}.
      elim: lf => [//|[fn' fd'] lf IHlf]; rewrite /= in_cons negb_or.
      by move => /andP []; case: ifP => // _ _ Hnotin /andP [-> /=]; apply/IHlf.
    by rewrite /tunnel_lfundef_pc lfd_body_setfb; apply/well_formed_tunnel_lcmd_pc.
  Qed.

  Lemma well_formed_tunnel_funcs_fn lf fn :
    well_formed_funcs lf ->
    well_formed_funcs (tunnel_funcs_fn lf fn).
  Proof.
    rewrite /well_formed_funcs => /andP [Huniq Hall]; apply/andP; split.
    + by rewrite funnames_tunnel_funcs_fn.
    rewrite /tunnel_funcs_fn; case Hgfd: (get_fundef _ _) => [fd|//].
    rewrite /setfunc all_map; elim: lf Hgfd Huniq Hall => //= -[fn' fd'] lf IHlf.
    case: ifP => [/eqP ? [?]|_ ? /andP [_ ?] /andP [-> /=]]; last by apply IHlf.
    subst fn' fd' => /andP [Hnotin Huniq] /andP [Hwf Hall]; apply/andP; split; last first.
    + rewrite {1}/fst /= in Hnotin; move: Hnotin Hall {IHlf Huniq Hwf}.
      elim: lf => [//|[fn' fd'] lf IHlf]; rewrite /= in_cons negb_or.
      by move => /andP []; case: ifP => // _ _ Hnotin /andP [-> /=]; apply/IHlf.
    by rewrite /tunnel_lfundef lfd_body_setfb; apply/well_formed_tunnel_lcmd.
  Qed.

  Lemma well_formed_tunnel_lprog_pc p fn pc :
    well_formed_lprog p ->
    well_formed_lprog (tunnel_lprog_pc p fn pc).
  Proof.
    case: p => >; rewrite /well_formed_lprog /=.
    by apply well_formed_tunnel_funcs_pc.
  Qed.

  Lemma well_formed_tunnel_lprog_fn p fn :
    well_formed_lprog p ->
    well_formed_lprog (tunnel_lprog_fn p fn).
  Proof.
    case: p => >; rewrite /well_formed_lprog /=.
    by apply well_formed_tunnel_funcs_fn.
  Qed.

  Lemma tunnel_lprog_ind_pc (P : lprog -> lprog -> Prop) :
    (forall p, P p p) ->
    (forall p2 p1 p3, P p1 p2 -> P p2 p3 -> P p1 p3) ->
    (forall p fn pc,
      well_formed_lprog p ->
      P p (tunnel_lprog_pc p fn pc)) ->
    forall p fn,
      well_formed_lprog p ->
      P p (tunnel_lprog_fn p fn).
  Proof.
    move => HPrefl HPtrans IHp p fn Hwfp.
    apply (@proj2 (well_formed_lprog (tunnel_lprog_fn p fn))).
    rewrite tunnel_lprog_fn_partial_eq; last by move: Hwfp => /andP [].
    case Hgfd: (get_fundef _ _) => [fd|//].
    elim: (size (lfd_body fd)) => [|pc IHpc].
    + rewrite tunnel_lprog_fn_partial0; first by split => //; apply/HPrefl.
      by move: Hwfp => /andP [].
    move: (tunnel_lprog_fn_partial_pc p fn pc); rewrite Hgfd => ->; last first.
    + by case/andP: (get_fundef_well_formed_funcs_body Hgfd Hwfp).
    move: IHpc => [Hwftp HPtp]; split.
    + by apply well_formed_tunnel_lprog_pc.
    apply (HPtrans (tunnel_lprog_fn_partial p fn pc)) => //.
    by apply IHp.
  Qed.

  Lemma tunnel_lprog_ind_fn (P : lprog -> lprog -> Prop) :
    (forall p, P p p) ->
    (forall p2 p1 p3, P p1 p2 -> P p2 p3 -> P p1 p3) ->
    (forall p fn,
      well_formed_lprog p ->
      P p (tunnel_lprog_fn p fn)) ->
    forall p,
      well_formed_lprog p ->
      P p (tunnel_lprog p).
  Proof.
    move => HPrefl HPtrans IHp p Hwfp.
    apply (@proj2 (well_formed_lprog (tunnel_lprog p))).
    rewrite tunnel_lprog_partial_eq.
    elim: (size (lp_funcs p)) => [|n IHn].
    + by rewrite tunnel_lprog_partial0; split => //; apply/HPrefl.
    rewrite tunnel_lprog_partial_fn; last by move: Hwfp => /andP [].
    case: (onth _ _) => // -[fn _]; move: IHn => [Hwftp HPtp]; split.
    + by apply well_formed_tunnel_lprog_fn.
    apply (HPtrans (tunnel_lprog_partial p n)) => //.
    by apply IHp.
  Qed.

  Lemma tunnel_lprog_ind (P : lprog -> lprog -> Prop) :
    (forall p, P p p) ->
    (forall p2 p1 p3, P p1 p2 -> P p2 p3 -> P p1 p3) ->
    (forall p fn pc,
      well_formed_lprog p ->
      P p (tunnel_lprog_pc p fn pc)) ->
    forall p,
      well_formed_lprog p ->
      P p (tunnel_lprog p).
  Proof.
    move => HPrefl HPtrans IHp.
    apply tunnel_lprog_ind_fn => //.
    by apply tunnel_lprog_ind_pc.
  Qed.

End TunnelingWFProps.


Section TunnelingSem.

  Variant find_instr_tunnel_lprog_pc_spec p s fn pc oc : option linstr -> Type :=
  | FT_GotoLabelLabel fd c l l':
      get_fundef (lp_funcs p) fn = Some fd ->
      fn == lfn s ->
      oc = Some c ->
      is_goto fn l c ->
      is_label l (nth Linstr_align (Linstr_align :: (lfd_body fd)) pc) ->
      is_label l' (nth Linstr_align (Linstr_align :: (lfd_body fd)) pc.+1) ->
      find_instr_tunnel_lprog_pc_spec p s fn pc oc (Some (MkLI (li_ii c) (Lgoto (fn, l'))))

  | FT_CondLabelLabel fd c pe l l':
      get_fundef (lp_funcs p) fn = Some fd ->
      fn == lfn s ->
      oc = Some c ->
      is_cond pe l c ->
      is_label l (nth Linstr_align (Linstr_align :: (lfd_body fd)) pc) ->
      is_label l' (nth Linstr_align (Linstr_align :: (lfd_body fd)) pc.+1) ->
      find_instr_tunnel_lprog_pc_spec p s fn pc oc (Some (MkLI (li_ii c) (Lcond pe l')))

  | FT_GotoLabelGoto fd c l l':
      get_fundef (lp_funcs p) fn = Some fd ->
      fn == lfn s ->
      oc = Some c ->
      is_goto fn l c ->
      is_label l (nth Linstr_align (Linstr_align :: (lfd_body fd)) pc) ->
      is_goto fn l' (nth Linstr_align (Linstr_align :: (lfd_body fd)) pc.+1) ->
      find_instr_tunnel_lprog_pc_spec p s fn pc oc (Some (MkLI (li_ii c) (Lgoto (fn, l'))))

  | FT_CondLabelGoto fd c pe l l':
      get_fundef (lp_funcs p) fn = Some fd ->
      fn == lfn s ->
      oc = Some c ->
      is_cond pe l c ->
      is_label l (nth Linstr_align (Linstr_align :: (lfd_body fd)) pc) ->
      is_goto fn l' (nth Linstr_align (Linstr_align :: (lfd_body fd)) pc.+1) ->
      find_instr_tunnel_lprog_pc_spec p s fn pc oc (Some (MkLI (li_ii c) (Lcond pe l')))

  | FT_Otherwise :
      match get_fundef (lp_funcs p) fn with
      | Some fd =>
          (fn != lfn s) ||
          ( ~~ ((((ssrfun.omap
                     (fun c => is_local_goto_to_label fn c (nth Linstr_align (Linstr_align :: (lfd_body fd)) pc))
                     oc) == Some true) &&
                   li_is_label (nth Linstr_align (Linstr_align :: (lfd_body fd)) pc.+1)) || 
                ((ssrfun.omap
                    (fun c => is_cond_to_label c (nth Linstr_align (Linstr_align :: (lfd_body fd)) pc))
                    oc == Some true) &&
                  li_is_label (nth Linstr_align (Linstr_align :: (lfd_body fd)) pc.+1)) || 
                ((ssrfun.omap
                    (fun c => is_local_goto_to_label fn c (nth Linstr_align (Linstr_align :: (lfd_body fd)) pc))
                    oc == Some true) &&
                  li_is_local_goto fn (nth Linstr_align (Linstr_align :: (lfd_body fd)) pc.+1)) || 
                ((ssrfun.omap
                    (fun c => is_cond_to_label c (nth Linstr_align (Linstr_align :: (lfd_body fd)) pc))
                    oc == Some true) &&
                  li_is_local_goto fn (nth Linstr_align (Linstr_align :: (lfd_body fd)) pc.+1))))
      | None => true
      end ->
      find_instr_tunnel_lprog_pc_spec p s fn pc oc oc.

  Lemma find_instr_tunnel_lprog_pcP p s fn pc :
    find_instr_tunnel_lprog_pc_spec p s fn pc (find_instr p s) (find_instr (tunnel_lprog_pc p fn pc) s).
  Proof.
    rewrite /find_instr /tunnel_lprog_pc lp_funcs_setfuncs /tunnel_funcs_pc.
    case Hgfd: (get_fundef (lp_funcs p) fn) => [fd|]; last first.
    + by apply FT_Otherwise; rewrite Hgfd.
    rewrite get_fundef_setfunc; case: ifP => [/eqP ?|Hneq]; last first.
    + by apply FT_Otherwise; rewrite Hgfd Hneq.
    subst fn; rewrite -get_fundef_in Hgfd /=.
    case: tunnel_lcmd_pcP => [l l'|l l'|l l' fn' Hneq Hpc HSpc|Hneg].
    + rewrite /tunnel_head onth_map; case Honth: (onth _ _) => [[ii i]|]; last first.
      - by move => Hpc HSpc; apply FT_Otherwise; rewrite Hgfd eq_refl.
      case: i Honth => [? ? ?|?|? ?| | |? ?|[fn l'']|?|? ?|pe l''] /= Honth Hpc HSpc /=.
      1-6,8-9:
        by apply FT_Otherwise; rewrite Hgfd eq_refl.
      - case: ifP => [/eqP ?|Hneq]; last first.
        * apply FT_Otherwise; rewrite Hgfd eq_refl //=.
          rewrite /is_local_goto_to_label /= Hneq /=; move: Hpc HSpc.
          set c:= nth _ _ _; set c':= nth _ _ _; move: c c' => [? i] [? i'].
          by case: i; case: i' => //; case => ? [].
        subst fn; rewrite LUF.find_union !LUF.find_empty.
        case: ifP => [/eqP ?|Hneq]; last first.
        * apply FT_Otherwise; rewrite Hgfd eq_refl //=.
          rewrite /is_local_goto_to_label /=; move: Hpc HSpc.
          set c:= nth _ _ _; set c':= nth _ _ _; move: c c' => [? i] [? i'].
          case: i; case: i' => //= k3 l''' k4 l'''' /eqP ? /eqP ?; subst l''' l''''.
          case: k4; last by [].
          by rewrite eq_sym in Hneq; rewrite Hneq Bool.andb_false_r.
        subst l''; set c:= MkLI _ _.
        move: (@FT_GotoLabelLabel p s (lfn s) pc (Some c) fd c l l' Hgfd).
        by rewrite eq_refl /= => HFT; apply HFT => //; rewrite /c /is_goto /= !eq_refl.
      rewrite LUF.find_union !LUF.find_empty.
      case: ifP => [/eqP ?|Hneq]; last first.
      * apply FT_Otherwise; rewrite Hgfd eq_refl //=.
        rewrite /is_cond_to_label /=; move: Hpc HSpc.
        set c:= nth _ _ _; set c':= nth _ _ _; move: c c' => [? i] [? i'].
        case: i; case: i' => //= k3 l''' k4 l'''' /eqP ? /eqP ?; subst l''' l''''.
        case: k4; last by [].
        by rewrite eq_sym in Hneq; rewrite Hneq Bool.andb_false_r.
      subst l''; set c:= MkLI _ _.
      move: (@FT_CondLabelLabel p s (lfn s) pc (Some c) fd c pe l l').
      by rewrite eq_refl /= => HFT; apply: HFT.
    + rewrite /tunnel_head onth_map; case Honth: (onth _ _) => [[ii i]|]; last first.
      - by move => Hpc HSpc; apply FT_Otherwise; rewrite Hgfd eq_refl.
      case: i Honth => [? ? ?|?|? ?| | |? ?|[fn l'']|?|? ?|pe l''] /= Honth Hpc HSpc /=.
      1-6,8-9:
        by apply FT_Otherwise; rewrite Hgfd eq_refl.
      - case: ifP => [/eqP ?|Hneq]; last first.
        * apply FT_Otherwise; rewrite Hgfd eq_refl //=.
          rewrite /is_local_goto_to_label /= Hneq /=; move: Hpc HSpc.
          set c:= nth _ _ _; set c':= nth _ _ _; move: c c' => [? i] [? i'].
          by case: i; case: i' => // ? [].
        subst fn; rewrite LUF.find_union !LUF.find_empty.
        case: ifP => [/eqP ?|Hneq]; last first.
        * apply FT_Otherwise; rewrite Hgfd eq_refl //=.
          rewrite /is_local_goto_to_label /=; move: Hpc HSpc.
          set c:= nth _ _ _; set c':= nth _ _ _; move: c c' => [? i] [? i'].
          case: i; case: i' => // -[fn l'''] k4 l'''' /eqP ? /andP [/eqP ? /eqP ?]; subst fn l''' l''''.
          case: k4; last by [].
          by rewrite eq_sym in Hneq; rewrite /= Hneq Bool.andb_false_r.
        subst l''; set c:= MkLI _ _.
        move: (@FT_GotoLabelGoto p s (lfn s) pc (Some c) fd c l l' Hgfd).
        by rewrite eq_refl /= => HFT; apply HFT => //; rewrite /c /is_goto /= !eq_refl.
      rewrite LUF.find_union !LUF.find_empty.
      case: ifP => [/eqP ?|Hneq]; last first.
      * apply FT_Otherwise; rewrite Hgfd eq_refl //=.
        rewrite /is_cond_to_label /=; move: Hpc HSpc.
        set c:= nth _ _ _; set c':= nth _ _ _; move: c c' => [? i] [? i'].
        case: i; case: i' => //= -[fn l'''] k4 l'''' /eqP ? /andP [/eqP ? /eqP ?]; subst fn l''' l''''.
        case: k4; last by [].
        by rewrite eq_sym in Hneq; rewrite Hneq Bool.andb_false_r.
      subst l''; set c:= MkLI _ _.
      move: (@FT_CondLabelGoto p s (lfn s) pc (Some c) fd c pe l l').
      by rewrite eq_refl /= => HFT; apply: HFT.
    + apply FT_Otherwise; rewrite Hgfd eq_refl /=; move: Hpc HSpc => /=.
      set c:= nth _ _ _; set c':= nth _ _ _; move: c c' => [ii i] [ii' i'].
      case: i => //= k2 l'' /eqP ?; subst l''.
      case: i' => //= -[fn'' l''] /andP [/eqP ? /eqP ?]; subst fn'' l''.
      set oc:= onth _ _; case: oc => [c''|//=]; case: c'' => [ii'' i''].
      case: i'' => //= [[fn'' l'']|pe l'']; rewrite !Bool.orb_false_r negb_or.
      - rewrite /is_local_goto_to_label /li_is_label /li_is_local_goto //=.
        by rewrite Bool.andb_false_r /= negb_and; apply/orP; right.
      rewrite /is_cond_to_label /li_is_label /li_is_local_goto //=.
      by rewrite Bool.andb_false_r /= negb_and; apply/orP; right.
    apply FT_Otherwise; rewrite Hgfd eq_refl /=; move: Hneg => /=.
    set oc:= onth _ _; case: oc => [[ii'' i'']|//=].
    set c:= nth _ _ _; set c':= nth _ _ _; move: c c' => [ii i] [ii' i'].
    rewrite /is_local_goto_to_label /is_cond_to_label /li_is_label /li_is_local_goto.
    by case: i => [| | | | |[] |[]| | | ]; (case: i' => [| | | | |[] |[]| | | ]);
    (case: i'' => [| | | | | |[]| | | ] => //=); intros; rewrite Bool.orb_false_r Bool.andb_false_r.
  Qed.

  Lemma find_label_tunnel_lcmd_pc l fn lc pc :
    find_label l (tunnel_lcmd_pc fn lc pc) = find_label l lc.
  Proof.
    rewrite /find_label /tunnel_lcmd_pc /tunnel_engine /tunnel_head.
    rewrite size_map seq.find_map; set p:= preim _ _.
    rewrite (@eq_find _ p (is_label l)) //.
    move => [ii i]; rewrite /p => {p} /=.
    by case: i => //= -[fn' l']; case: ifP.
  Qed.

  Lemma label_in_lcmd_tunnel_lcmd_pc fn lc pc :
    label_in_lcmd (tunnel_lcmd_pc fn lc pc) = label_in_lcmd lc.
  Proof.
    rewrite /label_in_lcmd; case: tunnel_lcmd_pcP => //.
    + move => l l' _ _; elim: lc => //= -[ii i] lc <-.
      by case: i => //= -[fn' l'']; case: ifP.
    move => l l' _ _; elim: lc => //= -[ii i] lc <-.
    by case: i => //= -[fn' l'']; case: ifP.
  Qed.

  Lemma label_in_lprog_tunnel_lprog_pc p fn pc :
    uniq (map fst (lp_funcs p)) ->
    label_in_lprog (tunnel_lprog_pc p fn pc) = label_in_lprog p.
  Proof.
    rewrite /label_in_lprog /tunnel_lprog_pc /tunnel_funcs_pc.
    case Hgfd: (get_fundef _ _) => [fd|//=].
    rewrite lp_funcs_setfuncs /setfunc.
    elim: {p} (lp_funcs p) Hgfd => //= -[fn' fd'] lf IHlf.
    case: ifP => [/eqP ? [?]|Hneq Hgfd /andP [Hnotin Huniq]]; last by rewrite IHlf.
    subst fn' fd' => /andP [Hnotin _] {IHlf}; rewrite {1}/fst /= in Hnotin.
    f_equal; first by rewrite /tunnel_lfundef_pc lfd_body_setfb /snd /= label_in_lcmd_tunnel_lcmd_pc.
    elim: lf Hnotin => //= -[fn' fd'] lf IHlf.
    rewrite in_cons negb_or => /andP [Hneq Hnotin].
    by rewrite IHlf //; f_equal; move: Hneq; case: ifP.
  Qed.

  Lemma eval_jump_tunnel_lprog_pc p fn pc :
    eval_jump (tunnel_lprog_pc p fn pc) =2 eval_jump p.
  Proof.
    rewrite /eval_jump /tunnel_lprog_pc /tunnel_funcs_pc lp_funcs_setfuncs.
    case Hgfd: (get_fundef _ fn) => [fd|] //= -[fn' l] s.
    rewrite get_fundef_setfunc -get_fundef_in Hgfd /=.
    case: ifP => // /eqP ?; subst fn'; rewrite Hgfd /=.
    by rewrite find_label_tunnel_lcmd_pc.
  Qed.

  Lemma tunnel_get_label_after_pc p fn pc s:
    get_label_after_pc (tunnel_lprog_pc p fn pc) s =
    get_label_after_pc p s.
  Proof.
    rewrite /get_label_after_pc.
    case: (find_instr_tunnel_lprog_pcP p (setpc s (lpc s).+1) fn pc); last done.
    + by move=> fd c l1 l2 hgetf hfn -> /=; case c => ? -[].
    + by move=> fd c pe l1 l2 hgetf hfn -> /=; case c => ? -[].
    + by move=> fd c l1 l2 hgetf hfn -> /=; case c => ? -[].
    by move=> fd c pe l1 l2 hgetf hfn -> /=; case c => ? -[].
  Qed.

  Lemma eval_instr_tunnel_lprog_pc p fn pc :
    uniq (map fst (lp_funcs p)) ->
    eval_instr (tunnel_lprog_pc p fn pc) =2 eval_instr p.
  Proof.
    move => Huniq [ii i] s; case: i => [ | | | | | |[fn' l]|pe|lv l|pe l] //=.
    + move=> o r; rewrite /eval_instr /= label_in_lprog_tunnel_lprog_pc //.
      case: o.
      * move=> lr.
        rewrite tunnel_get_label_after_pc /rencode_label.
        apply bind_eq => // l.
        case: encode_label => //= wl; apply bind_eq => // m.
        by rewrite eval_jump_tunnel_lprog_pc.
      rewrite tunnel_get_label_after_pc /rencode_label.
      apply bind_eq => // u. apply bind_eq => // vm.
      case: encode_label => //= wl; apply bind_eq => // m.
      by rewrite eval_jump_tunnel_lprog_pc.
    + rewrite /eval_instr /= label_in_lprog_tunnel_lprog_pc /rdecode_label //.
      apply bind_eq => // ?; apply bind_eq => // ?.
      case: decode_label => //= ?;  by rewrite eval_jump_tunnel_lprog_pc.
    + rewrite /eval_instr /= /tunnel_funcs_pc; case Hgfd: (get_fundef (lp_funcs p) fn) => [fd|//].
      rewrite get_fundef_setfunc -get_fundef_in Hgfd /=; case: ifP => // /eqP ?; subst fn'.
      by rewrite Hgfd /tunnel_lfundef_pc lfd_body_setfb /= find_label_tunnel_lcmd_pc.
    + rewrite /eval_instr /= label_in_lprog_tunnel_lprog_pc /rdecode_label //.
      apply bind_eq => // u. case: (decode_label _ _) => //= r.
      by rewrite eval_jump_tunnel_lprog_pc.
    + by rewrite /eval_instr /= label_in_lprog_tunnel_lprog_pc.
    rewrite /eval_instr /= /tunnel_funcs_pc; case Hgfd: (get_fundef (lp_funcs p) fn) => [fd|//].
    rewrite get_fundef_setfunc -get_fundef_in Hgfd /=; case: ifP => // /eqP ?; subst fn.
    by rewrite Hgfd /= find_label_tunnel_lcmd_pc.
  Qed.

  Lemma nth_label_find_label l lc pc :
    uniq (labels_of_body lc) ->
    is_label l (nth Linstr_align lc pc) ->
    find_label l lc = ok pc.
  Proof.
    elim: lc pc => [|[ii i] lc IHlc] pc //=; first by rewrite nth_nil.
    move: IHlc; rewrite /find_label //= => IHlc.
    case Hislabel: (is_label l (MkLI _ _)).
    + rewrite ltn0Sn; move: Hislabel; case: i => //= k l'.
      move => {IHlc} /eqP ?; subst l' => /andP [/negP Hnotin _].
      case: pc => // pc /= Hislabel; exfalso; apply: Hnotin.
      move: Hislabel.
      elim: lc pc => [|[{ii} ii i] lc IHlc] pc //=; first by rewrite nth_nil.
      case: pc => [|pc] //=.
      - by case: i => // k' l' /eqP ?; subst l'; rewrite /= inE eqxx.
      move/IHlc; clear.
      by case: i => //= ? ? hi; rewrite inE hi orbT.
    case: pc => [|pc] //=; first by rewrite Hislabel.
    move => Huniq {Hislabel} Hislabel.
    rewrite -(addn1 (find _ _)) -(addn1 (size _)) ltn_add2r.
    move: (IHlc pc) => {IHlc}; rewrite Hislabel => {Hislabel}.
    case: ifP; last first.
    + move => _; have ->: uniq (labels_of_body lc); last by move => /(_ isT isT).
      by move: Huniq; case: i => [? ? ?|?|?| | |? l'|[? ?]|?|? ?|? ?] //= /andP [].
    move => Hfind /(_ _ isT) IHlc; f_equal; rewrite addn1; f_equal.
    have {Huniq} Huniq: uniq (labels_of_body lc); last by case: (IHlc Huniq).
    by move: Huniq {Hfind IHlc}; case: i => //= ? l' /andP [].
  Qed.

  Lemma find_labelI lbl c pc :
    find_label lbl c = ok pc →
    find (is_label lbl) c = pc ∧ pc < size c.
  Proof. by rewrite /find_label; case: ifP => // pc_in_bounds /ok_inj <-. Qed.

  Lemma find_label_of_body c lbl :
    lbl \in labels_of_body c →
    ∃ pc : nat, find_label lbl c = ok pc.
  Proof.
    elim: c => // - [] ii a c ih /=.
    case: a; cycle 6.
    1-9: by move => > /ih[] pc /find_labelI[] ? ok_pc; exists pc.+1; subst pc;
           rewrite /find_label /= ltnS ok_pc.
    move => ? lbl'; rewrite /= inE; case: eqP => lbl_lbl'.
    - subst; exists 0.
      by rewrite /find_label /is_label /= eqxx lt0n.
    case/ih => pc /find_labelI[] ? ok_pc; exists pc.+1; subst pc.
    rewrite /find_label /is_label /=.
    by case: eqP lbl_lbl' => // _ _; rewrite ltnS ok_pc.
  Qed.

  Lemma local_goto_find_label p s c fd l :
    find_instr p s = Some c ->
    get_fundef (lp_funcs p) (lfn s) = Some fd ->
    well_formed_body (lfn s) (lfd_body fd) ->
    is_goto (lfn s) l c ->
    exists pc, find_label l (lfd_body fd) = ok pc.
  Proof.
    case: c => ii [] //= -[fn l'] Hfindinstr Hgfd /andP[] _.
    rewrite all_pmap => /allE /List.Forall_forall Hall.
    move => /andP [/eqP ? /eqP ?]; subst fn l'.
    move: Hfindinstr; rewrite /find_instr Hgfd => /(@onth_In _ _) /Hall.
    rewrite /= eqxx.
    exact: find_label_of_body.
  Qed.

End TunnelingSem.


Section TunnelingProof.

  Lemma tunnel_lprog_pc_lsem1 p fn pc s1 s2 :
    well_formed_lprog p ->
    lsem1 (tunnel_lprog_pc p fn pc) s1 s2 ->
    lsem1 p s1 s2 \/
    exists s3, lsem1 p s1 s3 /\
           lsem1 p s3 s2.
  Proof.
    move => Hwf; move: (Hwf) => /andP [Huniq Hall]; rewrite /lsem1 /step.
    case: find_instr_tunnel_lprog_pcP =>
      [fd c l l'|fd c pe l l'|fd c l l'|fd c pe l l'|_];
      last first.
    + by case: (find_instr _ _) => // oc; rewrite eval_instr_tunnel_lprog_pc //; left.
    + move => Hgfd /eqP ? Hfindinstr; subst fn; rewrite Hfindinstr.
      have Hwfb:= (get_fundef_well_formed_funcs_body Hgfd Hwf).
      move: (Hwfb) => /andP [Huniql Hallg].
      rewrite eval_instr_tunnel_lprog_pc //; case: c Hfindinstr => ii [] //=.
      move => pe' l'' Hfindinstr [ ? ? ]; subst pe' l''.
      rewrite {1 2 3}/eval_instr /= => Hpc HSpc; t_xrbindP => b v Hv Hb.
      rewrite Hv /= Hb /=; case: ifP => [HisTb|]; last by left.
      rewrite Hgfd /=; case: pc Hpc HSpc => [//=|pc] Hpc HSpc; rewrite /= in Hpc.
      rewrite (@nth_label_find_label l (lfd_body fd) pc) //=.
      t_xrbindP => pc' Hfindlabel'; move => ?; subst s2.
      right; eexists; split; first reflexivity.
      rewrite /find_instr Hgfd; case: (is_goto_nth_onth HSpc) => ii' ->.
      by rewrite /eval_instr /= Hgfd /= Hfindlabel' /=.
    + move => Hgfd /eqP ? Hfindinstr; subst fn; rewrite Hfindinstr.
      have Hwfb:= (get_fundef_well_formed_funcs_body Hgfd Hwf).
      move: (Hwfb) => /andP [Huniql Hallg].
      rewrite eval_instr_tunnel_lprog_pc //; case: c Hfindinstr => ii [] //=.
      move => [fn' l''] Hfindinstr /andP [/eqP ? /eqP ?]; subst fn' l''.
      rewrite {1 2 3}/eval_instr /= => Hpc HSpc.
      rewrite Hgfd /=; case: pc Hpc HSpc => [//=|pc] Hpc HSpc; rewrite /= in Hpc.
      rewrite (@nth_label_find_label l (lfd_body fd) pc) //=.
      t_xrbindP => pc' Hfindlabel'; move => ?; subst s2.
      right; eexists; split; first reflexivity.
      rewrite /find_instr Hgfd; case: (is_goto_nth_onth HSpc) => ii' ->.
      by rewrite /eval_instr /= Hgfd /= Hfindlabel' /=.
    + move => Hgfd /eqP ? Hfindinstr; subst fn; rewrite Hfindinstr.
      have Hwfb:= (get_fundef_well_formed_funcs_body Hgfd Hwf).
      move: (Hwfb) => /andP [Huniql Hallg].
      rewrite eval_instr_tunnel_lprog_pc //; case: c Hfindinstr => ii [] //=.
      move => pe' l'' Hfindinstr [ ? ? ]; subst pe' l''.
      rewrite {1 2 3}/eval_instr /= => Hpc HSpc; t_xrbindP => b v Hv Hb.
      rewrite Hv /= Hb /=; case: ifP => [HisTb|]; last by left.
      rewrite Hgfd /=; case: pc Hpc HSpc => [//=|pc] Hpc HSpc; rewrite /= in Hpc.
      rewrite (@nth_label_find_label l (lfd_body fd) pc) //=.
      rewrite (@nth_label_find_label l' (lfd_body fd) pc.+1) //=.
      move => [?]; subst s2.
      right; eexists; split; first reflexivity.
      rewrite /find_instr Hgfd.
      by case: (is_label_nth_onth HSpc) => ii' [] ? ->.
    move => Hgfd /eqP ? Hfindinstr; subst fn; rewrite Hfindinstr.
    have Hwfb:= (get_fundef_well_formed_funcs_body Hgfd Hwf).
    move: (Hwfb) => /andP [Huniql Hallg].
    rewrite eval_instr_tunnel_lprog_pc //; case: c Hfindinstr => ii [] //=.
    move => [fn' l''] Hfindinstr /andP [/eqP ? /eqP ?]; subst fn' l''.
    rewrite {1 2 3}/eval_instr /= => Hpc HSpc.
    rewrite Hgfd /=; case: pc Hpc HSpc => [//=|pc] Hpc HSpc; rewrite /= in Hpc.
    rewrite (@nth_label_find_label l (lfd_body fd) pc) //=.
    rewrite (@nth_label_find_label l' (lfd_body fd) pc.+1) //=.
    move => [?]; subst s2.
    right; eexists; split; first reflexivity.
    rewrite /find_instr Hgfd.
    by case: (is_label_nth_onth HSpc) => ii' [] ? ->.
  Qed.

  Lemma tunnel_lprog_pc_lsem p fn pc s1 s2 :
    well_formed_lprog p ->
    lsem (tunnel_lprog_pc p fn pc) s1 s2 ->
    lsem p s1 s2.
  Proof.
    move => Hwf Htlsem12; pattern s1, s2; set Q:= (fun _ => _); move: Htlsem12; apply: lsem_ind_r.
    + by rewrite /Q => s; apply Relation_Operators.rt_refl.
    rewrite /Q => {Q} s3 s4 s5 Htlsem34 Htlsem145 Hlsem34.
    apply (lsem_trans Hlsem34); case: (tunnel_lprog_pc_lsem1 Hwf Htlsem145).
    + by move => Hlsem145; apply Relation_Operators.rt_step.
    by case => s6 [Hlsem146 Hlsem165]; apply: (lsem_trans (s2 := s6));
    apply Relation_Operators.rt_step.
  Qed.

  Lemma lsem1_tunnel_lprog_pc p fn pc s1 s2 :
    well_formed_lprog p ->
    lsem1 p s1 s2 ->
    lsem1 (tunnel_lprog_pc p fn pc) s1 s2 \/
    exists s3, lsem1 p s2 s3 /\
           lsem1 (tunnel_lprog_pc p fn pc) s1 s3.
  Proof.
    move => Hwf; move: (Hwf) => /andP [Huniq Hall]; rewrite /lsem1 /step.
    case: find_instr_tunnel_lprog_pcP =>
      [fd c l l'|fd c pe l l'|fd c l l'|fd c pe l l'|_];
      last first.
    + by case: (find_instr _ _) => // oc; rewrite eval_instr_tunnel_lprog_pc //; left.
    + move => Hgfd /eqP ? Hfindinstr; subst fn; rewrite Hfindinstr.
      have Hwfb:= (get_fundef_well_formed_funcs_body Hgfd Hwf).
      move: (Hwfb) => /andP [Huniql Hallg].
      rewrite eval_instr_tunnel_lprog_pc //; case: c Hfindinstr => ii [] //=.
      move => pe' l'' Hfindinstr [ ? ? ]; subst pe' l''.
      rewrite {1 2 4}/eval_instr /= => Hpc HSpc; t_xrbindP => b v Hv Hb.
      rewrite Hv /= Hb /=; case: ifP => [HisTb|]; last by left.
      rewrite Hgfd /=; case: pc Hpc HSpc => [//=|pc] Hpc HSpc; rewrite /= in Hpc.
      rewrite (@nth_label_find_label l (lfd_body fd) pc) //=.
      move => [?]; subst s2.
      have [] := local_goto_find_label (s := setpc s1 pc.+1) _ Hgfd Hwfb HSpc.
      - rewrite /find_instr /= Hgfd; move: HSpc.
        set Spc:= pc.+1; elim: (lfd_body fd) Spc => [|[{ii Hfindinstr} ii i] lf IHlf] Spc.
        * by rewrite nth_nil.
        by case: Spc => [|Spc] //=; apply IHlf.
      move => pc' Hfindlabel'; rewrite Hfindlabel' /=.
      rewrite /find_instr Hgfd /=.
      move: (is_goto_nth_onth HSpc) => [ii'] ->.
      rewrite /eval_instr /= Hgfd /= Hfindlabel'.
      right; by eexists.

    + move => Hgfd /eqP ? Hfindinstr; subst fn; rewrite Hfindinstr.
      have Hwfb:= (get_fundef_well_formed_funcs_body Hgfd Hwf).
      move: (Hwfb) => /andP [Huniql Hallg].
      rewrite eval_instr_tunnel_lprog_pc //; case: c Hfindinstr => ii [] //=.
      move => [fn' l''] Hfindinstr /andP [/eqP ? /eqP ?]; subst fn' l''.
      rewrite {1 2 4}/eval_instr /= => Hpc HSpc.
      rewrite Hgfd /=; case: pc Hpc HSpc => [//=|pc] Hpc HSpc; rewrite /= in Hpc.
      rewrite (@nth_label_find_label l (lfd_body fd) pc) //=.
      move => [?]; subst s2.
      have [] := local_goto_find_label (s := setpc s1 pc.+1) _ Hgfd Hwfb HSpc.
      - rewrite /find_instr /= Hgfd; move: HSpc.
        set Spc:= pc.+1; elim: (lfd_body fd) Spc => [|[{ii Hfindinstr} ii i] lf IHlf] Spc.
        * by rewrite nth_nil.
        by case: Spc => [|Spc] //=; apply IHlf.
      move => pc' Hfindlabel'; rewrite Hfindlabel' /=.
      rewrite /find_instr Hgfd /=.
      move: (is_goto_nth_onth HSpc) => [ii'] ->.
      rewrite /eval_instr /= Hgfd /= Hfindlabel' /=.
      right; by eexists.

    + move => Hgfd /eqP ? Hfindinstr; subst fn; rewrite Hfindinstr.
      have Hwfb:= (get_fundef_well_formed_funcs_body Hgfd Hwf).
      move: (Hwfb) => /andP [Huniql Hallg].
      rewrite eval_instr_tunnel_lprog_pc //; case: c Hfindinstr => ii [] //=.
      move => pe' l'' Hfindinstr [ ? ? ]; subst pe' l''.
      rewrite {1 2 4}/eval_instr /= => Hpc HSpc; t_xrbindP => b v Hv Hb.
      rewrite Hv /= Hb /=; case: ifP => [HisTb|]; last by left.
      rewrite Hgfd /=; case: pc Hpc HSpc => [//=|pc] Hpc HSpc; rewrite /= in Hpc.
      rewrite (@nth_label_find_label l (lfd_body fd) pc) //=.
      move => [?]; subst s2.
      rewrite (@nth_label_find_label l' (lfd_body fd) pc.+1) //=.
      rewrite /find_instr /= Hgfd.
      case: (is_label_nth_onth HSpc) => ii' [] ? ->.
      right; by eexists.

    move => Hgfd /eqP ? Hfindinstr; subst fn; rewrite Hfindinstr.
    have Hwfb:= (get_fundef_well_formed_funcs_body Hgfd Hwf).
    move: (Hwfb) => /andP [Huniql Hallg].
    rewrite eval_instr_tunnel_lprog_pc //; case: c Hfindinstr => ii [] //=.
    move => [fn' l''] Hfindinstr /andP [/eqP ? /eqP ?]; subst fn' l''.
    rewrite {1 2 4}/eval_instr /= => Hpc HSpc.
    rewrite Hgfd /=; case: pc Hpc HSpc => [//=|pc] Hpc HSpc; rewrite /= in Hpc.
    rewrite (@nth_label_find_label l (lfd_body fd) pc) //=.
    move => [?]; subst s2.
    rewrite (@nth_label_find_label l' (lfd_body fd) pc.+1) //=.
    rewrite /find_instr /= Hgfd.
    case: (is_label_nth_onth HSpc) => ii' [] ? ->.
    right; by eexists.
  Qed.

  Lemma lsem_tunnel_lprog_pc p s1 s2 fn pc :
    well_formed_lprog p ->
    lsem p s1 s2 ->
    exists s3, lsem p s2 s3 /\
           lsem (tunnel_lprog_pc p fn pc) s1 s3.
  Proof.
    move => Hwf Hlsem12; pattern s1, s2; set Q:= (fun _ => _); move: Hlsem12; apply: lsem_ind_r.
    + by rewrite /Q => s; exists s; split; apply Relation_Operators.rt_refl.
    rewrite /Q => {Q} s3 s4 s5 Hlsem34 Hlsem145 [s6] [Hlsem46 Htlsem36].
    case: (lsem_disj1 Hlsem145 Hlsem46) => [?| Hlsem56]; last by exists s6; split.
    subst s6; case: (lsem1_tunnel_lprog_pc fn pc Hwf Hlsem145).
    + move => Htlsem45; exists s5; split; first by apply Relation_Operators.rt_refl.
      by apply (lsem_trans Htlsem36); apply Relation_Operators.rt_step.
    move => [s7] [Hlsem157 Htlsem147]; exists s7; split; first by apply Relation_Operators.rt_step.
    by apply (lsem_trans Htlsem36); apply Relation_Operators.rt_step.
  Qed.

  Lemma lsem_tunnel_lprog_lsem p :
    well_formed_lprog p ->
    (forall s1 s2,
      lsem (tunnel_lprog p) s1 s2 ->
      lsem p s1 s2) /\
    forall s1 s2, 
      lsem p s1 s2 ->
      exists s3, lsem p s2 s3 /\
             lsem (tunnel_lprog p) s1 s3.
  Proof.
    move => Hwf; pattern p, (tunnel_lprog p); set P:= (fun _ => _).
    move: Hwf; apply tunnel_lprog_ind => //; rewrite /P => {p P}.
    + move => p; split => //; move => s1 s2 Hlsem12.
      by exists s2; split => //; apply Relation_Operators.rt_refl.
    + move => p2 p1 p3 [HP12 HQ12] [HP23 HQ23]; split.
      - by move => s1 s2 Hlsem312; apply/HP12/HP23.
      move => s1 s2 Hlsem112.
      case: (HQ12 _ _ Hlsem112) => s3 [Hlsem123 Hlsem213].
      case: (HQ23 _ _ Hlsem213) => s4 [Hlsem234 Hlsem314].
      exists s4; split => //; apply (lsem_trans Hlsem123).
      by apply HP12.
    move => p fn pc Hwf; split => s1 s2; first by apply tunnel_lprog_pc_lsem.
    by apply lsem_tunnel_lprog_pc.
  Qed.

  Lemma lsem_tunnel_lprog p s1 s2 :
    well_formed_lprog p ->
    lsem p s1 s2 ->
    exists s3, lsem p s2 s3 /\
           lsem (tunnel_lprog p) s1 s3.
  Proof. by move => Hwf; move : (lsem_tunnel_lprog_lsem Hwf) => [_ HQ]; apply HQ. Qed.

  Theorem lsem_tunnel_program p tp s1 s2 :
    tunnel_program p = ok tp ->
    lsem p s1 s2 ->
    exists s3, lsem p s2 s3 /\ lsem tp s1 s3.
  Proof. by rewrite /tunnel_program; case: ifP => // Hwf [<-]; apply lsem_tunnel_lprog. Qed.

  Corollary lsem_run_tunnel_program p tp s1 s2 :
    tunnel_program p = ok tp →
    lsem p s1 s2 →
    lsem_final p s2 →
    lsem tp s1 s2 ∧ lsem_final tp s2.
  Proof.
    move => Htp Hlsem12 Hfinal2; case: (lsem_tunnel_program Htp Hlsem12) => s3 [Hlsem23 Htlsem13].
    have ?:= (lsem_final_stutter Hlsem23 Hfinal2); subst s3; split => //.
    move: Htp Hfinal2 {Hlsem12 Htlsem13 Hlsem23}; rewrite /lsem_final.
    rewrite /tunnel_program; case: ifP => // _ [?]; subst tp.
    move => [fd] Hgfd ->. rewrite /tunnel_lprog lp_funcs_setfuncs.
    rewrite get_fundef_tunnel_funcs Hgfd; eexists; first by eauto.
    by rewrite /tunnel_lfundef lfd_body_setfb size_tunnel_lcmd.
  Qed.

  Theorem get_fundef_tunnel_program p tp fn fd :
    tunnel_program p = ok tp →
    get_fundef (lp_funcs p) fn = Some fd →
    get_fundef (lp_funcs tp) fn = Some (tunnel_lfundef fn fd).
  Proof.
    rewrite /tunnel_program; case: ifP => // Hwfp /ok_inj <-{tp} Hgfd.
    by rewrite /tunnel_lprog lp_funcs_setfuncs get_fundef_tunnel_funcs Hgfd.
  Qed.

  Lemma tunnel_program_invariants p tp :
    tunnel_program p = ok tp ->
    lp_rip   p = lp_rip   tp /\
    lp_rsp   p = lp_rsp   tp /\
    lp_globs p = lp_globs tp /\
    map fst (lp_funcs p) = map fst (lp_funcs tp) /\
    map lfd_info   (map snd (lp_funcs p)) = map lfd_info   (map snd (lp_funcs tp)) /\
    map lfd_align  (map snd (lp_funcs p)) = map lfd_align  (map snd (lp_funcs tp)) /\
    map lfd_tyin   (map snd (lp_funcs p)) = map lfd_tyin   (map snd (lp_funcs tp)) /\
    map lfd_arg    (map snd (lp_funcs p)) = map lfd_arg    (map snd (lp_funcs tp)) /\
    map lfd_tyout  (map snd (lp_funcs p)) = map lfd_tyout  (map snd (lp_funcs tp)) /\
    map lfd_res    (map snd (lp_funcs p)) = map lfd_res    (map snd (lp_funcs tp)) /\
    map lfd_export (map snd (lp_funcs p)) = map lfd_export (map snd (lp_funcs tp)).
  Proof.
    rewrite /tunnel_program; case: ifP => // _ [?]; subst tp.
    by rewrite /tunnel_lprog /setfuncs /= /tunnel_funcs -!map_comp; do!split.
  Qed.

End TunnelingProof.


End WITH_PARAMS.
