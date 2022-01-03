From mathcomp Require Import all_ssreflect all_algebra.
Require Import ZArith.
Require Import Utf8.

Require Import oseq expr compiler_util label x86_variables linear linear_sem.
(*
=======
Require Import expr compiler_util label linear linear_sem.
>>>>>>> glob_array3
*)
Import ssrZ.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope seq_scope.

Require Import seq_extra xseq_extra unionfind tunneling unionfind_proof.
Require Import linear_sem.

Section ASM_OP.

Context {pd:PointerData}.
Context {asm_op} {asmop : asmOp asm_op}.


Section LprogSemProps.

  Definition is_goto fn l c :=
    match li_i c with
    | Lgoto (fn', l') => (fn == fn') && (l == l')
    | _ => false
    end.

  Definition is_cond pe l c :=
    match li_i c with
    | Lcond pe' l' => (pe == pe') && (l == l')
    | _ => false
    end.

  Definition li_is_label c :=
    if li_i c is Llabel _ then true else false.

  Definition li_is_goto c :=
    if li_i c is Lgoto _ then true else false.

  Definition li_is_cond c :=
    if li_i c is Lcond _ _ then true else false.

  Definition li_is_local_goto fn c :=
    if li_i c is Lgoto (fn', _) then fn == fn' else false.

  Definition is_local_goto_to_label fn c c' :=
    match li_i c, li_i c' with
    | Lgoto (fn', l), Llabel l' => (fn == fn') && (l == l')
    | _, _ => false
    end.

  Definition is_cond_to_label c c' :=
    match li_i c, li_i c' with
    | Lcond _ l, Llabel l' => l == l'
    | _, _ => false
    end.

  Lemma is_label_nth_onth lf l pc :
    is_label l (nth Linstr_align lf pc) ->
    exists ii, onth lf pc = Some (MkLI ii (Llabel l)).
  Proof.
    elim: lf pc => [|[ii i] lf IHlf] pc; first by rewrite nth_nil.
    case: pc => [|pc] //=.
    + move => Hislabel; exists ii; case: i Hislabel => //= l'.
      by move => /eqP ?; subst l.
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

  Lemma get_fundef_rcons lf (fn fn' : funname) (fd : lfundef) :
    get_fundef (rcons lf (fn, fd)) fn' =
    match get_fundef lf fn' with
    | Some fd' => Some fd'
    | None => (if fn == fn'
              then Some fd
              else None)
    end.
  Proof.
    elim: lf => //= [|[fn'' fd''] lf ->].
    + by rewrite eq_sym.
    by case: ifP.
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

  Lemma get_fundef_all (T : Type) (funcs : seq (funname * T)) fn fd a :
    get_fundef funcs fn = Some fd ->
    all (fun f => a f.1 f.2) funcs ->
    a fn fd.
  Proof.
    elim: funcs => //= -[fn' fd'] tfuncs IHfuncs.
    case: ifP; first by move => /eqP ? [?] /= /andP [Ha _]; subst fn' fd'.
    by move => _ /= Hgfd /andP [_ Hall]; apply: IHfuncs.
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

  Lemma get_fundef_foldrW (A : Type) (P : A -> A -> Prop) (f : funname -> lfundef -> A -> A) lf :
    (forall x, P x x) ->
    (forall y x z, P x y -> P y z -> P x z) ->
    uniq (map fst lf) ->
    (forall fn fd x,
      get_fundef lf fn = Some fd ->
      P x (f fn fd x)) ->
    forall x,
      P x (foldr (fun p y => f p.1 p.2 y) x lf).
(*
=======
  Section MOV_OP.

  Context (mov_op : asm_op).

  Lemma get_fundef_eval_instr p' i s1 s2 :
    label_in_lprog p = label_in_lprog p' ->
    get_fundef (lp_funcs p) =1 get_fundef (lp_funcs p') ->
    eval_instr p mov_op i s1 = ok s2 ->
    eval_instr p' mov_op i s1 = ok s2.
>>>>>>> glob_array3
*)
  Proof.
    move => HPrelf HPtrans.
    elim: lf => //= -[fn fd] lf IHlf /andP [/negP Hnotin Huniq] Hlf x.
    rewrite {1}/fst {1}/snd /=; rewrite {1}/fst in Hnotin.
    set y:= (foldr _ _ _); apply: (HPtrans y); last by apply/Hlf => //; rewrite eq_refl.
    rewrite /y; apply/IHlf => // fn' fd' {y} x' Hgfd'.
    apply: Hlf => //; case: ifP => // /eqP ?; subst fn'.
    exfalso; apply: Hnotin; rewrite -get_fundef_in.
    by rewrite /isSome Hgfd'.
  Qed.

  Lemma get_fundef_exists lf fn (fd : lfundef) :
    get_fundef lf fn = Some fd ->
    List.Exists (λ p, (fn, fd) = p) lf.
(*
=======
  Lemma get_fundef_lsem1 p' s1 s2 :
    label_in_lprog p = label_in_lprog p' ->
    get_fundef (lp_funcs p) =1 get_fundef (lp_funcs p') ->
    lsem1 p mov_op s1 s2 ->
    lsem1 p' mov_op s1 s2.
>>>>>>> glob_array3
*)
  Proof.
    elim: lf => //= -[fn' fd'] lf IHlf.
    case: ifP => [/eqP ? [?]|Hneq Hgfd].
    + by subst fn' fd'; apply List.Exists_cons; left.
    by apply List.Exists_cons; right; apply IHlf.
  Qed.

  Lemma eq_from_get_fundef (lf lf' : seq (funname * lfundef)) :
    uniq (map fst lf) ->
    map fst lf = map fst lf' ->
    (forall fn, get_fundef lf fn = get_fundef lf' fn) ->
    lf = lf'.
  Proof.
    elim: lf lf' => [|[fn fd] lf IHlf] [|[fn' fd'] lf'] //=.
    move => /andP [Hnotin Huniq] [? Heqfns] Heqfd; subst fn'.
    move: (Heqfd fn); rewrite eq_refl => // -[?]; subst fd'; f_equal.
    apply IHlf => // fn'; move: (Heqfd fn'); case: ifP => //.
    move => /eqP ?; subst fn' => _; move: (Hnotin); rewrite Heqfns.
    by move: Hnotin; rewrite -!get_fundef_in; do 2!(case: (get_fundef _ _)).
  Qed.

(*
=======
  End MOV_OP.
End TunnelingSemProps.
>>>>>>> glob_array3
*)

  Lemma onth_setfunc lf fn fd i :
    onth (setfunc lf fn fd) i =
    match onth lf i with
    | Some (fn', fd') => if fn == fn' then Some (fn, fd) else Some (fn', fd')
    | None => None
    end.
  Proof.
    rewrite /setfunc onth_map; case Honth: (onth _ _) => [[fn' fd']|//].
    by rewrite /fst /snd /=; case: ifP => // /eqP ?; subst fn'.
  Qed.

  Lemma onth_goto_targets fb i x :
    oseq.onth (goto_targets fb) i = Some x ->
    exists j ii_x r, oseq.onth fb j = Some (MkLI ii_x x) /\ Lgoto r = x.
  Proof.
    elim: fb i => // -[ii_x i_x] tfb IHfb i.
    rewrite /goto_targets /=.
    case: ifP => [|_ Hoseq].
    + case: i_x => // r _; case: i => [/= [?]|i Hoseq]; first by exists 0; exists ii_x; exists r; subst x; split.
      by case: (IHfb i Hoseq) => j Hj; exists j.+1.
    by case: (IHfb i Hoseq) => j Hj; exists j.+1.
  Qed.

  Lemma map_foldr (T R : Type) (s1 : seq R) (s2 : seq T) f :
    map (fun x => foldr f x s2) s1 = foldr (fun s => map (f s)) s1 s2.
  Proof.
    elim: s2 => //= [|x2 s2 <-]; first by rewrite map_id.
    rewrite -map_comp; set f1:= (fun _ => _); set f2:= (_ \o _).
    by rewrite (@eq_map _ _ f1 f2).
  Qed.

  Lemma map_fst_map_pair1 (g : funname -> lfundef -> lfundef) lf :
    map fst (map (fun f => (f.1, g f.1 f.2)) lf) = map fst lf.
  Proof. by rewrite -map_comp; set h:= (_ \o _); rewrite (@eq_map _ _ h fst). Qed.

  Lemma map_foldr_setfunc g lf :
    uniq (map fst lf) ->
    map (fun f => (f.1, g f.1 f.2)) lf = foldr (fun f l => setfunc l f.1 (g f.1 f.2)) lf lf.
  Proof.
    move => Huniq; apply eq_from_onth => i; rewrite onth_map /setfunc -map_foldr onth_map.
    case Honth: (onth _ _) => [[fn fd]|//]; rewrite {1 2}/fst {1}/snd /=; f_equal.
    set f:= (fun _ => _); have Hfoldr1: forall lf' fn' fd', (foldr f (fn', fd') lf').1 = fn'.
    + by move => lf' fn' fd'; elim: lf'.
    elim: lf Huniq i Honth => //= -[fn' fd'] lf IHlf /andP [Hnotin Huniq].
    rewrite {1}/fst /= in Hnotin; case => [[? ?]|i Honth].
    + subst fn' fd'; rewrite {1}/f {2}/fst /=; f_equal; first by rewrite Hfoldr1.
      by rewrite Hfoldr1 eq_refl.
    rewrite {1}/f Hfoldr1; f_equal; rewrite -(IHlf Huniq _ Honth) /fst /snd /=.
    case: ifP => // /eqP ?; subst fn'; move: (onth_map fst lf i).
    rewrite Honth {2}/fst /= => {Honth} Honth; exfalso.
    by move: Hnotin => /negP Hnotin; apply/Hnotin/onth_mem; exists i.
  Qed.

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

  Lemma size_tunnel_lcmd_pc fn lc pc :
    size (tunnel_lcmd_pc fn lc pc) = size lc.
  Proof. by rewrite /tunnel_lcmd_pc size_tunnel_engine. Qed.

  Lemma size_tunnel_lcmd_fn_partial fn lc pc :
    size (tunnel_lcmd_fn_partial fn lc pc) = size lc.
  Proof. by rewrite /tunnel_lcmd_fn_partial size_tunnel_engine. Qed.

  Lemma size_tunnel_lcmd fn lc :
    size (tunnel_lcmd fn lc) = size lc.
  Proof. by rewrite /tunnel_lcmd size_tunnel_engine. Qed.

  Lemma labels_of_body_rcons lc c :
    labels_of_body (rcons lc c) =
    if li_is_label c
    then rcons (labels_of_body lc) (li_i c)
    else labels_of_body lc.
  Proof. by rewrite /labels_of_body map_rcons filter_rcons; case c => ii []. Qed.

  Lemma labels_of_body_tunnel_head fn fb uf :
    labels_of_body (tunnel_head fn uf fb) = labels_of_body fb.
  Proof.
    rewrite /labels_of_body /tunnel_head; rewrite -map_comp.
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

  Lemma labels_of_body_tunnel_lcmd_fn_partial fn fb pc :
    labels_of_body (tunnel_lcmd_fn_partial fn fb pc) = labels_of_body fb.
  Proof. by rewrite /tunnel_lcmd_fn_partial labels_of_body_tunnel_engine. Qed.

  Lemma labels_of_body_tunnel_lcmd fn fb :
    labels_of_body (tunnel_lcmd fn fb) = labels_of_body fb.
  Proof. by rewrite /tunnel_lcmd labels_of_body_tunnel_engine. Qed.

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

  Lemma funnames_tunnel_funcs_fn_partial lf fn pc :
    map fst (tunnel_funcs_fn_partial lf fn pc) = map fst lf.
  Proof.
    rewrite /tunnel_funcs_fn_partial; case Hgfd: (get_fundef _ _) => [fd|//].
    by rewrite funnames_setfunc.
  Qed.

  Lemma funnames_tunnel_funcs_fn lf fn :
    map fst (tunnel_funcs_fn lf fn) = map fst lf.
  Proof.
    rewrite /tunnel_funcs_fn; case Hgfd: (get_fundef _ _) => [fd|//].
    by rewrite funnames_setfunc.
  Qed.

  Lemma funnames_tunnel_funcs_partial lf n :
    map fst (tunnel_funcs_partial lf n) = map fst lf.
  Proof.
    rewrite /tunnel_funcs_partial map_cat /tunnel_funcs map_fst_map_pair1.
    by rewrite -map_cat cat_take_drop.
  Qed.

  Lemma funnames_tunnel_funcs lf :
    map fst (tunnel_funcs lf) = map fst lf.
  Proof. by rewrite /tunnel_funcs map_fst_map_pair1. Qed.

  Lemma get_fundef_tunnel_funcs_fn lf fn fn' :
    get_fundef (tunnel_funcs_fn lf fn) fn' =
    match get_fundef lf fn' with
    | Some fd => if fn == fn' then Some (tunnel_lfundef fn fd) else Some fd
    | None => None
    end.
  Proof.
    rewrite /tunnel_funcs_fn; case Hgfd: (get_fundef lf fn) => [fd|].
    + rewrite get_fundef_setfunc; case: ifP => [/eqP ?|].
      - by subst fn'; rewrite -get_fundef_in Hgfd.
      by case: (get_fundef _ _).
    case Hgfd': (get_fundef _ _) => [fd'|//]; case: ifP => // /eqP ?.
    by subst fn'; rewrite Hgfd in Hgfd'.
  Qed.

  Lemma get_fundef_tunnel_funcs lf fn :
    get_fundef (tunnel_funcs lf) fn =
    match get_fundef lf fn with
    | Some fd => Some (tunnel_lfundef fn fd)
    | None => None
    end.
  Proof. by rewrite /tunnel_funcs get_fundef_map2. Qed.

  Variant tunnel_chart_spec fn (uf : LUF.unionfind) : linstr -> linstr -> LUF.unionfind -> Type :=
  | TC_LabelLabel ii ii' l l' :
      tunnel_chart_spec fn uf (MkLI ii (Llabel l)) (MkLI ii' (Llabel l')) (LUF.union uf l l')

  | TC_LabelGotoEq ii ii' l l' :
      tunnel_chart_spec fn uf (MkLI ii (Llabel l)) (MkLI ii' (Lgoto (fn, l'))) (LUF.union uf l l')

  | TC_LabelGotoNEq ii ii' l l' fn' of (fn != fn') :
      tunnel_chart_spec fn uf (MkLI ii (Llabel l)) (MkLI ii' (Lgoto (fn', l'))) uf

  | TC_Otherwise c c' of (~~ ((li_is_label c && li_is_label c') || (li_is_label c && li_is_goto c'))) :
      tunnel_chart_spec fn uf c c' uf.

  Lemma tunnel_chartP fn uf c c' : tunnel_chart_spec fn uf c c' (tunnel_chart fn uf c c').
  Proof.
  case: c c' => [ii i] [ii' i']; case: i'; case: i; try by move=> *; apply: TC_Otherwise.
  + by move => l l'; apply TC_LabelLabel.
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
    Llabel l \notin labels_of_body lc ->
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
    by case: i => [? ? ?| |?|[? ?]|?|? ?|? ?]; (case: i' => [? ? ?| |?|[? ?]|?|? ?|? ?] //= _ IHlc);
    rewrite labels_of_body_rcons //= => Hnotin; (try by rewrite rcons_uniq => /andP [_]; apply IHl);
    (try by move: Hnotin; rewrite mem_rcons in_cons negb_or => /andP /= [_ Hnotin]; apply IHlc);
    rewrite rcons_uniq => /andP [_]; apply IHlc.
  Qed.

  Lemma find_tunnel_plan_id fn lc l :
    Llabel l \notin labels_of_body lc ->
    uniq (labels_of_body lc) ->
    LUF.find (tunnel_plan fn LUF.empty lc) l = l.
  Proof.
    case/lastP: lc => //= lc c /negP Hnotin; apply/find_tunnel_plan_rcons_id.
    apply/negP => Hin; apply: Hnotin; rewrite labels_of_body_rcons; case: ifP => // _.
    by rewrite mem_rcons in_cons Hin; case: (_ == _).
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
    1-3,5-6:
      by intros; apply: TBW_Otherwise.
    + move => [? ?] /=; case: ifPn => [/eqP <-|].
      - by apply: TBW_GotoEq.
      by intros; apply: TBW_Otherwise.
    by intros => /=; apply: TBW_Cond.
  Qed.

  Lemma tunnel_boreP fn uf c : tunnel_bore_spec fn uf c (tunnel_bore fn uf c).
  Proof.
    case: c => [ii i]; case: i.
    1-3,5-6:
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

  Lemma tunnel_lcmd_fn_partial_pc fn lc pc :
    uniq (labels_of_body lc) ->
    tunnel_lcmd_fn_partial fn lc pc.+1 = tunnel_lcmd_pc fn (tunnel_lcmd_fn_partial fn lc pc) pc.
  Proof.
    rewrite /tunnel_lcmd_fn_partial /tunnel_lcmd_pc /tunnel_engine => Huniq.
    have Hsubseq: subseq (labels_of_body (take pc.+1 lc)) (labels_of_body lc).
    + rewrite /labels_of_body subseq_filter; apply/andP; split.
      - by rewrite all_filter (@eq_all _ _ predT) ?all_predT //; case.
      set a := (fun _ => _); set st:= map _ _; set s:= map _ _.
      apply: (@subseq_trans _ st (filter a st) s); first by apply filter_subseq.
      by rewrite /st /s => {st s}; apply/map_subseq/take_subseq.
    move: (subseq_uniq Hsubseq Huniq) => {Hsubseq Huniq}.
    case Hsize: (pc < size lc); last first.
    + move: (negbT Hsize); rewrite -leqNgt => {Hsize} Hsize.
      rewrite !take_oversize //; last by apply/leqW.
      rewrite /pair_pc (@nth_default _ _ _ (pc.+1)) /=; last first.
      - by rewrite size_tunnel_head //; apply/leqW.
      rewrite tunnel_plan_cons_cons tunnel_plan1 /= /tunnel_chart /=.
      by case: (nth _ _ _) => _ []; rewrite tunnel_head_empty.
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
    by case i => [? ? ?| |?|[? ?]|?|? ?|? ?]; (case i' => [? ? ?| |?|[? ?]|?|? ?|? ?] //=);
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
    case Hgfd: (get_fundef _ _) => [fd|//]; case: {Hgfd} p => ? ? ? ? //=.
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
    by case: {Huniq} p => ? ? ? ?; case: (get_fundef _ _).
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
    + clear Heq Htunnel_lcmd; rewrite /goto_targets !all_filter.
      move => /allP Hall; apply/allP => i; move: (Hall i).
      case: i => //= -[fn' l''] Himp Hin.
      move: Hin => /mapP [[ii []]] //= [fn''' l'''] Hin [? ?]; subst fn''' l'''.
      move: Hin => /mapP [[ii' []]] //= [fn''' l'''] Hin [?]; subst ii'.
      have {Hin} Hin: Lgoto (fn''', l''') \in map li_i fb.
      - by apply/mapP; eexists; eauto.
      case: ifP => [/eqP ?|_] [? ?]; subst fn''' l''; last by apply/Himp.
      subst fn'; move: Himp; rewrite LUF.find_union !LUF.find_empty.
      case: ifP => [/eqP ?|_]; last by move=> Himp; apply/Himp.
      subst l'''; rewrite eq_refl /= => _ {Hpc Hall Hin ii l}.
      move: HSpc; rewrite /is_label -nth_behead /behead /=.
      case Hnth: (nth _ _ _) => [ii i] /=; case: i Hnth => //=.
      move => l Hnth /eqP ?; subst l'; move: (@mem_nth _ Linstr_align fb pc).
      case Hsize: (pc < size fb) => //; rewrite Hnth; last first.
      - move: (negbT Hsize); rewrite -leqNgt => {Hsize} Hsize.
        by rewrite nth_default in Hnth.
      move => /(_ isT) => Hin {Hnth Hsize fn pc}.
      rewrite /labels_of_body mem_filter /=.
      by apply/mapP; eexists; eauto.
    clear Heq Htunnel_lcmd; rewrite /goto_targets !all_filter.
    move => /allP Hall; apply/allP => i; move: (Hall i).
    case: i => //= -[fn' l''] Himp Hin.
    move: Hin => /mapP [[ii []]] //= [fn''' l'''] Hin [? ?]; subst fn''' l'''.
    move: Hin => /mapP [[ii' []]] //= [fn''' l'''] Hin [?]; subst ii'.
    have {Hin} Hin: Lgoto (fn''', l''') \in map li_i fb.
    + by apply/mapP; eexists; eauto.
    case: ifP => [/eqP ?|_] [? ?]; subst fn''' l''; last by apply/Himp.
    subst fn'; move: Himp; rewrite LUF.find_union !LUF.find_empty.
    case: ifP => [/eqP ?|_]; last by move=> Himp; apply/Himp.
    subst l'''; rewrite eq_refl /= => _; move: (Hall (Lgoto (fn, l'))) => /=.
    rewrite eq_refl /=; move => Himp; apply: Himp => {Hpc Hall Hin l ii}.
    move: HSpc; rewrite /is_goto -nth_behead /behead /=.
    case Hnth: (nth _ _ _) => [ii i] /=; case: i Hnth => //=.
    move => [fn' l] Hnth /andP [/eqP ? /eqP ?]; subst fn' l'.
    move: (@mem_nth _ Linstr_align fb pc).
    case Hsize: (pc < size fb) => //; rewrite Hnth; last first.
    + move: (negbT Hsize); rewrite -leqNgt => {Hsize} Hsize.
      by rewrite nth_default in Hnth.
    move => /(_ isT) => Hin {Hnth Hsize pc}.
    by apply/mapP; eexists; eauto.
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
(*
=======
  case: c c' => [ii i] [ii' i'];
    case: i'; case: i; try by move=> *; apply: TCW_Otherwise.
  move=> l [fn' l'] /=; case: ifPn => [/eqP<-|].
  - by apply: TCW_LabelGotoEq. - by move=> _; apply: TCW_Otherwise.
  Qed.

  Lemma find_plan_partial fb s ii l :
    well_formed_body fn fb ->
    prefix (rcons s (MkLI ii (Llabel l))) fb ->
    LUF.find (pairfoldl (tunnel_chart fn) LUF.empty Linstr_align (rcons s (MkLI ii (Llabel l)))) l = l.
  Proof.
    rewrite /well_formed_body => /andP [Huniqfb _] Hprefix.
    have:= (uniq_nhas Huniqfb Hprefix).
    move => /negP; move: s l (MkLI _ _) Hprefix; apply: last_ind => [|s c1 IHs] //.
    + by move => ? [] /=; rewrite LUF.find_empty.
    move => l c2 Hprefix.
    rewrite pairfoldl_rcons has_rcons last_rcons.
    move: {1 5}c1 (erefl c1) Hprefix => c1'.
    case: tunnel_chartWP; last first.
    + move=> c c' -> Hprefix Hor; apply: IHs.
      - by apply: prefix_trans (prefix_rcons _ _) Hprefix.
      - by case/negP/norP: Hor => _ /negP.
    move=> {ii} ii ii' l1 l2 -> Hprefix.
    move=> Hor; rewrite LUF.find_union; case: ifP; last first.
    + by rewrite (IHs l _ (prefix_trans (prefix_rcons _ _) Hprefix)) //;
      move => Hhas; apply: Hor; apply/orP; right.
    rewrite (IHs l _ (prefix_trans (prefix_rcons _ _) Hprefix)) //; last first.
    + by move => Hhas; apply: Hor; apply/orP; right.
    rewrite (IHs l1 _ (prefix_trans (prefix_rcons _ _) Hprefix)) //; last first.
    + by apply: (negP (uniq_nhas Huniqfb (prefix_trans (prefix_rcons _ _) Hprefix))).
    by move => /eqP ?; subst l1; exfalso; apply: Hor; apply/orP; left; rewrite /is_label /= eq_refl.
  Qed.

  Lemma prefix_rcons_find_label pfb ii l fb :
    well_formed_body fn fb ->
    prefix (rcons pfb {| li_ii := ii; li_i := Llabel l |}) fb ->
    find_label l fb = ok (size pfb).
  Proof.
    rewrite /well_formed_body => /andP [Huniqfb _].
    elim: fb pfb Huniqfb => [|hfb tfb IHfb] [|hpfb tpfb] //=; case: ifP => // /eqP ?; subst hfb.
    + by move => _ _; rewrite /find_label /find /is_label /= eq_refl.
    move => Huniqfb Hprefix; have:= (IHfb tpfb); rewrite /find_label /find.
    have:= (@uniq_nhas _ (hpfb :: tpfb) ii l Huniqfb).
    rewrite rcons_cons /= eq_refl; move => Hneg; have:= (Hneg Hprefix) => /negP Hor.
    case Hisl: (is_label _ _); first by exfalso; apply: Hor; apply/orP; left.
    have Huniqtfb: (uniq (labels_of_body tfb)).
    + move: Huniqfb; rewrite /well_formed_body /labels_of_body /=.
      by case: ifP => //; rewrite cons_uniq => _ /andP [].
    move => IHdepl; have:= (IHdepl Huniqtfb Hprefix).
    case: ifP; case: ifP => //; first by move => _ _ [->].
    by rewrite ltnS => ->.
  Qed.

  Lemma prefix_find_label pfb fb l pc:
    well_formed_body fn fb ->
    prefix pfb fb ->
    find_label l fb = ok pc ->
    exists pcf, find_label (LUF.find (tunnel_plan fn LUF.empty pfb) l) fb = ok pcf.
  Proof.
    move: pfb l pc; apply: last_ind => [|pfb c]; first by move => l pc; exists pc; rewrite /tunnel_plan /= LUF.find_empty.
    move => IHpfb l pc Hwfb Hprefix Hfindl; have:= (IHpfb _ _ Hwfb (prefix_trans (prefix_rcons _ _) Hprefix) Hfindl).
    move => -[pcf]; rewrite /tunnel_plan pairfoldl_rcons.
    set uf:= pairfoldl _ _ _ _; rewrite /tunnel_chart.
    case Hlastpfb: (last _ _) => [li_ii1 li_i1] //; case Hc: c => [li_ii2 li_i2] //.
    case: li_i1 Hlastpfb.
    (*TODO*)
    1-2,4-7:
      by intros; eexists; eauto.
    case: li_i2 Hc.
    1-3,5-7:
      by intros; eexists; eauto.
    move => [fn'' l''] ?; subst c => l' Hlastpfb Hfindpl.
    case: eqP; last by intros; eexists; eauto.
    move => ?; subst fn''; rewrite LUF.find_union.
    case: ifP; last by intros; eexists; eauto.
    move => /eqP Hfindll'; move: Hfindpl; rewrite -Hfindll' => Hpcf.
    rewrite /tunnel_plan -/uf in IHpfb.
    have: exists pc'', find_label l'' fb = ok pc''; last first.
    + move => [pc''] Hfindl''.
      by apply: (IHpfb _ _ Hwfb (prefix_trans (prefix_rcons _ _) Hprefix) Hfindl'').
    move: Hwfb; rewrite /well_formed_body.
    rewrite /well_formed_body => /andP [_].
    rewrite all_filter; move: Hprefix; case/prefixP => sfb Hfb.
    rewrite {2}Hfb map_cat map_rcons all_cat all_rcons => /andP [] /andP [/= Hl'' _ _].
    elim: fb Hl'' {Hfindl Hpcf IHpfb Hfb} => // hfb tfb.
    rewrite /labels_of_body /find_label !mem_filter /= in_cons.
    case Hhfbl'': (is_label l'' hfb) => //=.
    + by rewrite /is_label /= in Hhfbl'' => IHok Hor; exists 0.
    rewrite ltnS; move => IHok; rewrite /is_label in Hhfbl'' => Hor; move: Hor Hhfbl''.
    move => /orP [/eqP <-|]; first by rewrite eq_refl.
    move => Hin; case: (IHok Hin) => [pc''] Hif _; exists pc''.+1; move: Hif; case: ifP => //.
    by move => _ [->].
  Qed.

  Lemma find_is_label_eq l1 l2 lc :
    has (is_label l1) lc ->
    find (is_label l1) lc = find (is_label l2) lc ->
    l1 = l2.
  Proof.
    elim: lc => [|hlc tlc IHlc] //=.
    case: ifP; case: ifP => //=.
    + by rewrite /is_label; case: (li_i hlc) => // l /eqP <- /eqP.
    by move => _ _ Hhas [Heqfind]; apply: IHlc.
  Qed.

  Lemma mem_split {T : eqType} (s : seq T) (x : T) :
    x \in s -> exists s1 s2, s = s1 ++ x :: s2.
  Proof.
  move/rot_index; set i := seq.index x s; move/(congr1 (rotr i)).
  rewrite rotK {1}(_ : i = size (take i s)); last first.
  - by rewrite size_takel // index_size.
  by rewrite -cat_cons rotr_size_cat => ->; eauto.
  Qed.

  Lemma labels_of_body_nil : labels_of_body [::] = [::].
  Proof. by []. Qed.

  Lemma labels_of_body_cons c fb : labels_of_body (c :: fb) =
    if li_is_label c then c.(li_i) :: labels_of_body fb else labels_of_body fb.
  Proof. by []. Qed.

  Lemma labels_of_body_cat fb1 fb2 :
    labels_of_body (fb1 ++ fb2) = labels_of_body fb1 ++ labels_of_body fb2.
  Proof. by rewrite /labels_of_body map_cat filter_cat. Qed.

  Lemma is_labelP {l c} : reflect (c.(li_i) = Llabel l) (is_label l c).
  Proof.
  rewrite /is_label; case: c => ii [] /=; try by move=> *; constructor.
  by move=> l'; apply: (iffP eqP) => [->//|[->]].
  Qed.

  Lemma find_is_label_r fb (c : linstr) l :
        well_formed_body fn fb
     -> c \in fb
     -> is_label l c
     -> find (is_label l) fb = seq.index c fb.
  Proof.
  case/andP=> [uq _] /mem_split [fb1] [fb2] fbE lc.
  suff l_fb1: ~~ has (is_label l) fb1.
    have c_fb1: c \notin fb1.
      by apply/contra: l_fb1 => c_fb1; apply/hasP; exists c.
    rewrite fbE; rewrite find_cat (negbTE l_fb1) /= lc addn0.
    by rewrite index_cat (negbTE c_fb1) /= eqxx addn0.
  apply/hasPn=> /= c' c'_fb1; apply/contraL: uq => lc'.
  rewrite fbE labels_of_body_cat uniq_catC labels_of_body_cons.
  rewrite /li_is_label (is_labelP lc) /=; apply/nandP; left.
  rewrite negbK mem_cat; apply/orP; right.
  by rewrite mem_filter /= -(is_labelP lc'); apply/mapP; exists c'.
  Qed.

  Lemma find_is_label pfb fb c l :
    well_formed_body fn fb ->
    prefix (rcons pfb c) fb ->
    is_label l c ->
    find (is_label l) fb = size pfb.
  Proof.
  move=> wf /prefixP [fb' fbE] lc; rewrite (@find_is_label_r _ c) //.
  - rewrite fbE index_cat mem_rcons in_cons eqxx /=.
    rewrite -cats1 index_cat; case: ifP => //=; last first.
    - by move=> _; rewrite eqxx addn0.
    case/andP: wf => uq _; move: uq.
    rewrite fbE -cats1 !labels_of_body_cat -catA uniq_catC -catA.
    rewrite {1}/labels_of_body /= (is_labelP lc) /= andbC => /andP[_].
    rewrite mem_cat => /norP[_]; rewrite mem_filter /= => h.
    by move/(map_f li_i); rewrite (is_labelP lc) (negbTE h).
  - by rewrite fbE mem_cat mem_rcons in_cons eqxx.
  Qed.

  Lemma label_in_lprog_tunnel :
    forall fb,
      label_in_lprog
        ( match get_fundef (lp_funcs p) fn with
          | Some fd =>
              setfuncs p
                [seq (f.1,
                  if fn == f.1
                  then lfundef_tunnel_partial fn f.2 fb (lfd_body fd)
                  else f.2)
                | f <- lp_funcs p]
          | None => p
          end)
      = label_in_lprog p.
  Proof.
    move: wf_p => /andP; case: p => rip rsp globs funcs /= [Huniq _].
    rewrite /label_in_lprog /=; f_equal.
    case Hgfd: get_fundef => [fd|] // fb.
    rewrite lp_funcs_setfuncs -map_comp /=.
    have: get_fundef funcs fn = Some fd \/ get_fundef funcs fn = None by left.
    elim: funcs {rip globs Hgfd} Huniq => // -[fn' fd'] tfuncs IHfuncs /=.
    move => /andP [Hnotin Huniq]; case: ifP; last by move => _ Hgfd; f_equal; apply: IHfuncs.
    move => /eqP ?; subst fn'; case => [[?]|] //; subst fd'; f_equal; last first.
    + apply: IHfuncs => //; right; elim: tfuncs Hnotin {Huniq} => // -[fn' fd'] ttfuncs IHtfuncs /=.
      by rewrite in_cons Bool.negb_orb => /andP []; case: ifP.
    case: fd {tfuncs IHfuncs Hnotin Huniq} => /= _ _ _ _ lc _ _ _ _.
    set uf:= tunnel_plan _ _ _; move: uf.
    elim: lc => // -[ii []] //=; last by move => [fn'] /=; case: (fn == fn') => /=.
    by move => l lc IHlc uf; rewrite IHlc.
  Qed.

  Context (mov_op : asm_op).

  Lemma tunneling_lsem1 s1 s2 :
    lsem1 (lprog_tunnel fn p) mov_op s1 s2 -> lsem p mov_op s1 s2.
  Proof.
    rewrite /lprog_tunnel; case Hgfd: (get_fundef _ _) => [fd|];
      last by apply: Relation_Operators.rt_step.
    move: s1 s2; pattern (lfd_body fd), (lfd_body fd) at 2; apply: prefixW.
    + move => s1 s2 Hlsem1; apply: Relation_Operators.rt_step.
      have:= (@get_fundef_lsem1 _ _ _ _ _ (label_in_lprog_tunnel _)).
      rewrite Hgfd => Hgfd'; apply: (Hgfd' _ _ _ _ _ Hlsem1); clear Hgfd' Hlsem1 => fn'.
      rewrite lp_funcs_setfuncs /lfundef_tunnel_partial /tunnel_plan /= /tunnel_partial pairmap_tunnel_bore_empty.
      rewrite (get_fundef_map2 fn' (fun f1 f2 => if fn == f1 then setfb f2 (lfd_body fd) else f2) (lp_funcs p)).
      case Hgfd': (get_fundef _ _) => [fd'|] //; case: ifP => // /eqP ?; subst fn'.
      by move: Hgfd'; rewrite Hgfd => -[?]; subst fd'; rewrite setfb_lfd_body.
    move => [li_ii3 li_i3] tli.
    have:= label_in_lprog_tunnel (rcons tli {| li_ii := li_ii3; li_i := li_i3 |}).
    have:= label_in_lprog_tunnel tli.
    rewrite Hgfd /lfundef_tunnel_partial /tunnel_plan pairfoldl_rcons.
    case: (lastP tli); first by case: (lfd_body fd) => //.
    move => ttli [li_ii2 li_i2]; rewrite last_rcons /=.
    case: li_i2; case: li_i3 => //.
    move => [fn3 l3] l2; case Heqfn3: (fn == fn3) => //; move: Heqfn3 => /eqP ?; subst fn3.
    set uf := pairfoldl _ _ _ _ => Hlabel_in_lprog_tunnel Hlabel_in_lprog_tunnel_union.
    move => Hprefix Hplsem1 s1 s2; move: Hplsem1.
    rewrite /lsem1 /step /find_instr !lp_funcs_setfuncs get_fundef_union.
    case Hgfds1: (get_fundef _ _) => [fds1|] //.
    case Heqfns1: (fn == lfn s1); last first.
    + move => Hplsem1; have:= (Hplsem1 s1 s2); clear Hplsem1.
      rewrite get_fundef_partial Hgfds1 Heqfns1.
      case Honth: (oseq.onth _ _) => [[li_ii1 li_i1]|] //.
      rewrite /eval_instr /eval_jump; case: (li_i1) => //.
      - move => [fn1 l1] /=; rewrite get_fundef_partial get_fundef_union.
        case: (get_fundef _ _) => [fd1|] //; case Heqfn1: (fn == fn1) => //=.
        by rewrite !find_label_tunnel_partial.
      - move => pe1 /= Htunnel; t_xrbindP => w v Hv Hw.
        rewrite Hv /= Hw /= in Htunnel; move: Htunnel.
        rewrite Hlabel_in_lprog_tunnel Hlabel_in_lprog_tunnel_union.
        case: (decode_label _ w) => [[fn1 l1]|] //; rewrite get_fundef_partial get_fundef_union.
        case: (get_fundef _ _) => [fd1|] //; case Heqfn1: (fn == fn1) => //=.
        by rewrite !find_label_tunnel_partial.
      - by move => lv l /=; rewrite Hlabel_in_lprog_tunnel Hlabel_in_lprog_tunnel_union.
      move => pe1 l1 /= Htunnel; t_xrbindP => b v Hv Hb.
      rewrite Hv /= Hb /= in Htunnel; move: Htunnel.
      case: b {Hb} => //; rewrite get_fundef_partial get_fundef_union Heqfns1.
      by case: (get_fundef _ _) => [fd1|].
    move: s1 Heqfns1 Hgfds1 => [mem1 vm1 fn1 pc1] /= /eqP ? Hgfds1; subst fn1.
    pose s1:= Lstate mem1 vm1 fn pc1; rewrite -/s1.
    move: Hgfds1; rewrite Hgfd => -[?]; subst fds1.
    rewrite !onth_map; case Honth: (oseq.onth _ _) => [[li_ii1 li_i1]|] // Hplsem1.
    rewrite /eval_instr /eval_jump; case: li_i1 Honth => [? ? ?| |?|[fn1 l1]|pe1|lv l|pe1 l1] //=.
    1-3:
      move => Honth; have:= (Hplsem1 s1 s2); clear Hplsem1;
      by rewrite get_fundef_partial /s1 /= -/s1 Hgfd eq_refl !onth_map Honth //=.
    2:
      by move => Honth; have:= (Hplsem1 s1 s2); clear Hplsem1;
      rewrite get_fundef_partial /s1 /= -/s1 Hgfd eq_refl !onth_map Honth /eval_instr /eval_jump /=;
      move => Htunnel; t_xrbindP => w v Hv Hw; rewrite Hv /= Hw /= in Htunnel; move: Htunnel;
      rewrite Hlabel_in_lprog_tunnel Hlabel_in_lprog_tunnel_union;
      case: (decode_label _ w) => [[fn1 l1]|] //; rewrite get_fundef_partial get_fundef_union;
      case: (get_fundef _ _) => [fd1|] //; case Heqfn1: (fn == fn1) => //=;
      rewrite !find_label_tunnel_partial.
    2:
      by rewrite Hlabel_in_lprog_tunnel_union; move => Honth; have:= (Hplsem1 s1 s2); clear Hplsem1;
      rewrite get_fundef_partial /s1 /= -/s1 Hgfd eq_refl !onth_map Honth /eval_instr Hlabel_in_lprog_tunnel.
    + move => Honth.
      case Heqfn1: (fn == fn1) => //; last first.
      - have:= (Hplsem1 s1 s2); clear Hplsem1;
        rewrite get_fundef_partial /s1 /= -/s1 Hgfd eq_refl !onth_map Honth /eval_instr /eval_jump /=.
        rewrite Heqfn1 get_fundef_union // Heqfn1 get_fundef_partial.
        by case Hgfd1: (get_fundef _ _) => [fd1|] //; rewrite Heqfn1.
      move: Heqfn1 => /eqP ?; subst fn1.
      rewrite eq_refl /= LUF.find_union !LUF.find_empty.
      rewrite get_fundef_partial Hgfd eq_refl /=; t_xrbindP => pc3.
      case: ifP; last first.
      - have:= (Hplsem1 s1 s2); clear Hplsem1;
        rewrite get_fundef_partial /s1 /= -/s1 Hgfd eq_refl !onth_map Honth /eval_instr /eval_jump /=.
        rewrite eq_refl get_fundef_partial Hgfd /= eq_refl !find_label_tunnel_partial /=.
        by move => Htunnel _ Hpc13 Hs2; rewrite Hpc13 /= Hs2 /= in Htunnel; apply: Htunnel.

      rewrite find_label_tunnel_partial.
      move => Heqfind Hfindl Hsetcpc.
      pose s1':= Lstate mem1 vm1 fn (size ttli).+1.
      have:= (Hplsem1 s1' s2); have:= (Hplsem1 s1 s1'); rewrite /s1' /= -/s1'; clear Hplsem1.
      rewrite get_fundef_partial Hgfd eq_refl !onth_map Honth /= eq_refl /eval_instr /eval_jump /=.
      rewrite get_fundef_partial Hgfd eq_refl /setcpc.
      rewrite lfd_body_setfb -(eqP Heqfind) /= find_label_tunnel_partial.
      rewrite (find_plan_partial (get_fundef_wf Hgfd) (prefix_trans (prefix_rcons _ _) Hprefix)).
      rewrite (prefix_rcons_find_label (get_fundef_wf Hgfd) (prefix_trans (prefix_rcons _ _) Hprefix)).
      rewrite /= -/s1' -(prefix_onth Hprefix); last by rewrite !size_rcons.
      rewrite !onth_rcons !size_rcons eq_refl /= eq_refl get_fundef_partial Hgfd eq_refl.
      rewrite /= find_label_tunnel_partial Hfindl /=.
      move: Hsetcpc; rewrite /s1' /setcpc /= -/s1' => ->.
      by move => Hlsem11' Hlsem12'; apply: (@lsem_trans _ _ _ _ _ s1'); first apply: Hlsem11'; last apply Hlsem12'.
  move => Honth.
  t_xrbindP => b v Hv; case: b => Hb; last first.
  + have:= (Hplsem1 s1 s2); clear Hplsem1;
    rewrite get_fundef_partial /s1 /= -/s1 Hgfd eq_refl !onth_map Honth /eval_instr /eval_jump /=.
    by rewrite Hv /= Hb /=.
  rewrite get_fundef_partial Hgfd eq_refl /=; t_xrbindP => pc3.
  rewrite LUF.find_union !LUF.find_empty.
  case: ifP; last first.
  + have:= (Hplsem1 s1 s2); clear Hplsem1;
    rewrite get_fundef_partial /s1 /= -/s1 Hgfd eq_refl !onth_map Honth /eval_instr /eval_jump /=.
    rewrite Hv /= Hb /= find_label_tunnel_partial => Hpc _ Hpc3 Hs2; move: Hpc.
    rewrite get_fundef_partial Hgfd eq_refl /= find_label_tunnel_partial.
    by rewrite Hpc3 /= Hs2 /=; move => Hlsem; apply: Hlsem.
  rewrite find_label_tunnel_partial.
  move => Heqfind Hfindl Hsetcpc.
  pose s1':= Lstate mem1 vm1 fn (size ttli).+1.
  have:= (Hplsem1 s1' s2); have:= (Hplsem1 s1 s1'); rewrite /s1' /= -/s1'; clear Hplsem1.
  rewrite get_fundef_partial Hgfd eq_refl onth_map Honth /eval_instr /eval_jump /= Hv /= Hb /=.
  rewrite get_fundef_partial Hgfd eq_refl onth_map.
  rewrite -(eqP Heqfind) /= find_label_tunnel_partial.
  rewrite (find_plan_partial (get_fundef_wf Hgfd) (prefix_trans (prefix_rcons _ _) Hprefix)).
  rewrite (prefix_rcons_find_label (get_fundef_wf Hgfd) (prefix_trans (prefix_rcons _ _) Hprefix)).
  rewrite /= -/s1' -(prefix_onth Hprefix); last by rewrite !size_rcons.
  rewrite !onth_rcons !size_rcons eq_refl /= eq_refl get_fundef_partial Hgfd eq_refl.
  rewrite /= find_label_tunnel_partial Hfindl /=.
  move: Hsetcpc; rewrite /s1' /setcpc /= -/s1' => ->.
  by move => Hlsem11' Hlsem12'; apply: (@lsem_trans _ _ _ _ _ s1'); first apply: Hlsem11'; last apply Hlsem12'.
  Qed.

  Lemma tunneling_lsem s1 s2 :
    lsem (lprog_tunnel fn p) mov_op s1 s2 -> lsem p mov_op s1 s2.
  Proof.
    move: s1 s2; apply: lsem_ind; first by move => s; apply Relation_Operators.rt_refl.
    by move => s1 s2 s3 H1tp12 _ Hp23; apply: (lsem_trans (tunneling_lsem1 H1tp12)).
  Qed.

  Lemma lsem11_tunneling s1 s2 :
    lsem1 p mov_op s1 s2 ->
    lsem1 (lprog_tunnel fn p) mov_op s1 s2 \/
    exists s3, [/\ lsem1 (lprog_tunnel fn p) mov_op s2 s3 ,
               lsem1 (lprog_tunnel fn p) mov_op s1 s3 &
               exists ii l, find_instr p s2 = Some (MkLI ii (Lgoto (fn,l)))].
  Proof.
    rewrite /lprog_tunnel; case Hgfd: (get_fundef _ _) => [fd|]; last by left.
    move: s1 s2; pattern (lfd_body fd), (lfd_body fd) at 2 4 6; apply: prefixW.
    + move => s1 s2 Hlsem1; left.
      apply: (@get_fundef_lsem1 p _ _ s1 s2 _ _ Hlsem1); first by rewrite -(label_in_lprog_tunnel [::]) Hgfd.
      clear Hlsem1 => fn'.
      rewrite lp_funcs_setfuncs /lfundef_tunnel_partial /tunnel_plan /= /tunnel_partial pairmap_tunnel_bore_empty.
      rewrite (get_fundef_map2 fn' (fun f1 f2 => if fn == f1 then setfb f2 (lfd_body fd) else f2) (lp_funcs p)).
      case Hgfd': (get_fundef _ _) => [fd'|] //; case: ifP => // /eqP ?; subst fn'.
      by move: Hgfd'; rewrite Hgfd => -[?]; subst fd'; rewrite setfb_lfd_body.
    move => [li_ii4 li_i4] tli.
    have:= label_in_lprog_tunnel (rcons tli {| li_ii := li_ii4; li_i := li_i4 |}).
    have:= label_in_lprog_tunnel tli.
    rewrite Hgfd /lfundef_tunnel_partial /tunnel_plan pairfoldl_rcons.
    case: (lastP tli); first by case: (lfd_body fd) => //.
    move => ttli [li_ii3 li_i3]; rewrite last_rcons /=.
    case: li_i3; case: li_i4 => //.
    move => [fn4 l4] l3; case Heqfn4: (fn == fn4) => //; move: Heqfn4 => /eqP ?; subst fn4.
    set uf := pairfoldl _ _ _ _ => Hlabel_in_lprog_tunnel Hlabel_in_lprog_tunnel_union Hprefix Hplsem1 s1 s2.
    move: Hplsem1; rewrite /lsem1 /step /find_instr !lp_funcs_setfuncs get_fundef_union //.
    case Hgfds1: (get_fundef _ _) => [fds1|] //.
    case Heqfns1: (fn == lfn s1); last first.
    + move => Hplsem1; have:= (Hplsem1 s1 s2); clear Hplsem1; rewrite Hgfds1.
      case Honth1: (oseq.onth _ _) => [[li_ii1 li_i1]|] //.
      rewrite get_fundef_partial Hgfds1 Heqfns1 Honth1.
      move => _ Hevalinstr; left; move: Hevalinstr.
      rewrite /eval_instr /eval_jump; case: (li_i1) => //=.
      - move => [fn1 l1] /=; rewrite get_fundef_union.
        case Heqfn1: (fn == fn1); last by case Hgfd1: (get_fundef _ _) => [fd1|].
        move: Heqfn1 => /eqP ?; subst fn1; rewrite Hgfd.
        by rewrite /= !find_label_tunnel_partial.
      - move => pe1; t_xrbindP => w v Hv Hw; rewrite Hv /= Hw /=.
        rewrite Hlabel_in_lprog_tunnel_union.
        case: (decode_label _ w) => [[fn1 l1]|] //; rewrite get_fundef_union.
        case Heqfn1: (fn == fn1); last by case Hgfd1: (get_fundef _ _) => [fd1|].
        move: Heqfn1 => /eqP ?; subst fn1; rewrite Hgfd.
        by rewrite /= !find_label_tunnel_partial.
      - by move => lv l; rewrite Hlabel_in_lprog_tunnel_union.
      move => pe1 l1; t_xrbindP => b v Hv Hb; rewrite Hv /= Hb /=.
      case: b {Hb} => //; rewrite get_fundef_union Heqfns1.
      by case: get_fundef.
    move: s1 Heqfns1 Hgfds1 => [mem1 vm1 fn1 pc1] /= /eqP ?; subst fn1.
    rewrite Hgfd => -[?]; subst fds1.
    pose s1:= Lstate mem1 vm1 fn pc1; rewrite /= -/s1.
    move: s2 => [mem2 vm2 fn2 pc2]; pose s2:= Lstate mem2 vm2 fn2 pc2; rewrite /= -/s2.
    rewrite get_fundef_partial !onth_map.
    case Honth1: (oseq.onth _ pc1) => [[li_ii1 li_i1]|] //.
    rewrite /eval_instr /eval_jump; case: li_i1 Honth1 => [? ? ?| |?|[fn1 l1]|pe1|lv l|pe1 l1] //=.
    1-3:
      by move => Honth1 Hplsem1;
      have:= (Hplsem1 s1 s2); clear Hplsem1;
      rewrite /s1 /= -/s1 Hgfd Honth1 /=;
      move => _ Htunnel; left.
    2:
      by move => Honth1 Hplsem1;
      have:= (Hplsem1 s1 s2); clear Hplsem1;
      rewrite /s1 /= -/s1 Hgfd Honth1 /=;
      move => _ Htunnel; left;
      move: Htunnel; t_xrbindP => w v Hv Hw; rewrite Hv /= Hw /=;
      rewrite Hlabel_in_lprog_tunnel_union;
      case: (decode_label _ w) => [[fn1 l1]|] //; rewrite get_fundef_union;
      case Hgfd1: (get_fundef _ _) => [fd1|] //;
      case Heqfn1: (fn == fn1) => //; move: Heqfn1 => /eqP ?; subst fn1;
      move: Hgfd1; rewrite Hgfd => -[?]; subst fd1;
      rewrite /= !find_label_tunnel_partial.
    2:
      by move => Honth1 Hplsem1;
      have:= (Hplsem1 s1 s2); clear Hplsem1;
      rewrite /s1 /= -/s1 Hgfd Honth1 /=;
      move => _ Htunnel; left;
      rewrite Hlabel_in_lprog_tunnel_union.
    + rewrite !get_fundef_union eq_refl Hgfd => Honth1 Hplsem1.
      case Heqfn1: (fn == fn1) => //; last first.
      - have:= (Hplsem1 s1 s2); clear Hplsem1.
        rewrite /s1 /= -/s1 Hgfd Honth1 /=.
        move => _ Htunnel; left.
        rewrite Heqfn1 get_fundef_union Heqfn1.
        by move: Htunnel; case: (get_fundef _ _) => [fd1|].
      move: Heqfn1 => /eqP ?; subst fn1.
      rewrite Hgfd eq_refl /= LUF.find_union !LUF.find_empty get_fundef_union Hgfd eq_refl.
      t_xrbindP => pcf1 Hpcf1 ? ? ? ?; subst mem2 vm2 fn2 pc2.
      rewrite /= !find_label_tunnel_partial.
      have:= (Hplsem1 s1 s2).
      rewrite /s1 /= -/s1 Hgfd Honth1 /= Hgfd /= Hpcf1 /= get_fundef_partial Hgfd eq_refl.
      rewrite lfd_body_setfb onth_map Honth1 /= eq_refl get_fundef_partial Hgfd eq_refl.
      rewrite lfd_body_setfb /= !find_label_tunnel_partial !onth_map.
      move => -[//| |[s3]].
      - clear Hplsem1; case: ifP => //; last by left.
        rewrite (find_plan_partial (get_fundef_wf Hgfd) (prefix_trans (prefix_rcons _ _) Hprefix)).
        move => /eqP Hfindl; t_xrbindP => pcf1' Hpcf1' ?; subst pcf1'.
        move: Hpcf1 Hpcf1'; rewrite {1 2}/find_label -!has_find; do 2! case : ifP => //.
        move => _ Hhas [Hpcf1] [Hpcf1']; have:= (@find_is_label_eq _ (LUF.find uf l1) _ Hhas).
        rewrite Hpcf1 -{1}Hpcf1' -Hfindl => Heqfind; rewrite Heqfind // in Hpcf1.
        have Hfindislabel:= (@find_is_label _ _ _ l3 (get_fundef_wf Hgfd) (prefix_trans (prefix_rcons _ _) Hprefix)).
        move: (Hpcf1); rewrite Hfindislabel; last by rewrite /is_label //=.
        (*TODO: Can I be more directive with subst?*)
        move => Hpcf1''; move: Hpcf1 Hpcf1'; subst pcf1 => Hpcf1 Hpcf1'.
        rewrite -(prefix_onth Hprefix); last by rewrite !size_rcons.
        rewrite onth_rcons !size_rcons eq_refl {1}/tunnel_bore eq_refl /=.
        rewrite get_fundef_union Hgfd eq_refl LUF.find_union /=.
        rewrite !find_label_tunnel_partial.
        have:= (get_fundef_wf Hgfd); rewrite /well_formed_body => /andP [_ Hall].
        move: Hall; rewrite /goto_targets all_filter all_map => Hall.
        have:= (prefix_all Hprefix Hall); rewrite all_rcons => /andP [Hl4 _]; clear Hall.
        rewrite /= mem_filter /= in Hl4; have:= mapP Hl4 => -[[li_ii5 li_i5]] /= Hin ?.
        clear Hl4; subst li_i5; have Hhas4: has (is_label l4) (lfd_body fd).
        * by apply/hasP; eexists; first exact Hin; rewrite /is_label /= eq_refl.
        have: exists pc4, find_label l4 (lfd_body fd) = ok pc4.
        * by rewrite /find_label -has_find Hhas4; eexists.
        clear li_ii5 Hin Hhas => -[pc4] Hpc4.
        have:= (prefix_find_label (get_fundef_wf Hgfd) (prefix_trans (prefix_rcons _ _) Hprefix) Hpc4).
        rewrite /tunnel_plan -/uf => -[pcf4] Hpcf4; rewrite Hpcf4 /=.
        pose s3:= Lstate mem1 vm1 fn pcf4.+1; right; exists s3; split.
        * by case: ifP => _; rewrite Hpcf4 /= /setcpc /s2 /s3 /=.
        * by rewrite /setcpc /s1 /s3.
        by eexists; eauto.
      clear Hplsem1; move => -[]; case: ifP => //; last first.
      - move => Hfindl Hmatch Hs3; right; exists s3; split => //; move: Hmatch.
        case Honthp1: (oseq.onth _ _) => [[li_ii5 li_i5]|] //.
        case: li_i5 Honthp1 => //=.
        * move => [fn5 l5] /=; case: ifP => // Heqfn; rewrite get_fundef_union get_fundef_partial Heqfn //.
          move: Heqfn => /eqP ?; subst fn5; rewrite Hgfd LUF.find_union /= !find_label_tunnel_partial.
          case: ifP => // Hfindl' _; move: Hs3; t_xrbindP => pcff1 Hfindlabel1 ?; subst s3.
          move => ? Hfindlabel1'; rewrite /setcpc /s1 /s2 /= => -[?]; subst; exfalso.
          move: Hfindl => /eqP Hfindl; apply: Hfindl; move: Hfindl' Hfindlabel1 Hfindlabel1' => /eqP <-.
          rewrite /find_label; case: ifP; case: ifP => //; rewrite -has_find => Hhas _ [<-] [Hfind].
          by apply: (find_is_label_eq Hhas Hfind).
        * move => pe5 Honth5; t_xrbindP => w v Hv Hw; rewrite Hv /= Hw /=.
          rewrite Hlabel_in_lprog_tunnel Hlabel_in_lprog_tunnel_union.
          case: (decode_label _ w) => //.
          move => [fn5 l5] /=; rewrite get_fundef_union get_fundef_partial.
          case Heqfn: (fn == fn5) => //; move: Heqfn => /eqP ?; subst fn5.
          by rewrite Hgfd /= !find_label_tunnel_partial.
        * by move => lv l; rewrite Hlabel_in_lprog_tunnel Hlabel_in_lprog_tunnel_union.
        move => pe5 l5 Honth5; t_xrbindP => b v Hv Hb; rewrite Hv /= Hb /=; case: b {Hb} => //.
        rewrite !find_label_tunnel_partial LUF.find_union; case: ifP => // Hfindl'.
        move: Hs3; t_xrbindP => pcff1 Hfindlabel1 ?; subst s3.
        move => ? Hfindlabel1'; rewrite /setcpc /s1 /s2 /= => -[?]; subst; exfalso.
        move: Hfindl => /eqP Hfindl; apply: Hfindl; move: Hfindl' Hfindlabel1 Hfindlabel1' => /eqP <-.
        rewrite /find_label; case: ifP; case: ifP => //; rewrite -has_find => Hhas _ [<-] [Hfind].
        by apply: (find_is_label_eq Hhas Hfind).
      rewrite (find_plan_partial (get_fundef_wf Hgfd) (prefix_trans (prefix_rcons _ _) Hprefix)).
      move => /eqP Hfindl Hmatch; t_xrbindP => pcf1' Hpcf1'.
      move: s3 Hmatch => [mem3 vm3 fn3 pc3]; pose s3:= Lstate mem3 vm3 fn3 pc3; rewrite /= -/s3.
      move => Hmatch; rewrite /setcpc => -[? ? ? ?]; subst mem3 vm3 fn3 pc3; rewrite /s1 /= -/s1.
      move => [li_ii5] [l5] Honth5; right; move: Hpcf1' Hmatch; rewrite -Hfindl => Hpcf1'.
      have:= (prefix_rcons_find_label (get_fundef_wf Hgfd) (prefix_trans (prefix_rcons _ _) Hprefix)).
      rewrite Hpcf1' => -[?]; subst pcf1'.
      have:= (get_fundef_wf Hgfd); rewrite /well_formed_body => /andP[_ Hall].
      move: Hall; rewrite /goto_targets all_filter all_map => Hall.
      have:= (prefix_all Hprefix Hall); rewrite all_rcons => /andP [Hl4 _]; clear Hall.
      rewrite /= mem_filter /= in Hl4; have:= mapP Hl4 => -[[li_ii6 li_i6]] /= Hin ?.
      clear Hl4; subst li_i6; have Hhas4: has (is_label l4) (lfd_body fd).
      - by apply/hasP; eexists; first exact Hin; rewrite /is_label /= eq_refl.
      have: exists pc4, find_label l4 (lfd_body fd) = ok pc4.
      - by rewrite /find_label -has_find Hhas4; eexists.
      clear li_ii6 Hin Hhas4 => -[pc4] Hpc4.
      have:= (prefix_find_label (get_fundef_wf Hgfd) (prefix_trans (prefix_rcons _ _) Hprefix) Hpc4).
      rewrite /tunnel_plan -/uf => -[pcf4] Hpcf4; rewrite Hpcf4 /= => Hmatch.
      pose s4:= Lstate mem1 vm1 fn pcf4.+1; exists s4; split => //; last by eexists; eauto.
      move: Hmatch; rewrite Honth5 /= eq_refl get_fundef_union get_fundef_partial Hgfd eq_refl.
      rewrite /= LUF.find_union !find_label_tunnel_partial; case: ifP; first by rewrite Hpcf4 /s4.
      move => /negP Hfindl'; t_xrbindP => pcf5 Hpcf5 ?; subst pcf5; exfalso; apply: Hfindl'; apply/eqP.
      rewrite -(find_plan_partial (get_fundef_wf Hgfd) (prefix_trans (prefix_rcons _ _) Hprefix)) -/uf in Hpcf1'.
      move: Hpcf1' Hpcf5; rewrite /find_label; case: ifP; case: ifP => //.
      by rewrite -has_find => Hhas _ [<-] [Hfind]; rewrite (find_is_label_eq Hhas Hfind).
    rewrite !get_fundef_union eq_refl Hgfd => Honth1 Hplsem1.
    t_xrbindP => b v Hv Hb; rewrite Hv /= Hb /=; case: b Hb => Hb; last by left.
    t_xrbindP => pcf1 Hpcf1 ? ? ? ?; subst mem2 vm2 fn2 pc2.
    rewrite !find_label_tunnel_partial LUF.find_union !LUF.find_empty.
    have:= (Hplsem1 s1 s2); clear Hplsem1.
    rewrite /s1 /= -/s1 Hgfd Honth1 /= Hpcf1 /= Hv /= Hb /= /setcpc /s1 /s2 /= -/s1 -/s2.
    rewrite get_fundef_partial Hgfd eq_refl lfd_body_setfb onth_map Honth1 /= Hv /= Hb /=.
    rewrite !find_label_tunnel_partial !onth_map.
    move => -[//| |[s3]].
    + case: ifP => //; last by left.
      rewrite (find_plan_partial (get_fundef_wf Hgfd) (prefix_trans (prefix_rcons _ _) Hprefix)).
      move => /eqP Hfindl; t_xrbindP => pcf1' Hpcf1' ?; subst pcf1'.
      move: Hpcf1 Hpcf1'; rewrite {1 2}/find_label -!has_find; do 2! case : ifP => //.
      move => _ Hhas [Hpcf1] [Hpcf1']; have:= (@find_is_label_eq _ (LUF.find uf l1) _ Hhas).
      rewrite Hpcf1 -{1}Hpcf1' -Hfindl => Heqfind; rewrite Heqfind // in Hpcf1.
      have Hfindislabel:= (@find_is_label _ _ _ l3 (get_fundef_wf Hgfd) (prefix_trans (prefix_rcons _ _) Hprefix)).
      move: (Hpcf1); rewrite Hfindislabel; last by rewrite /is_label //=.
      (*TODO: Can I be more directive with subst?*)
      move => Hpcf1''; move: Hpcf1 Hpcf1'; subst pcf1 => Hpcf1 Hpcf1'.
      rewrite -(prefix_onth Hprefix); last by rewrite !size_rcons.
      rewrite onth_rcons !size_rcons eq_refl {1}/tunnel_bore eq_refl /=.
      rewrite get_fundef_union Hgfd eq_refl LUF.find_union /=.
      rewrite !find_label_tunnel_partial.
      have:= (get_fundef_wf Hgfd); rewrite /well_formed_body => /andP[_ Hall].
      move: Hall; rewrite /goto_targets all_filter all_map => Hall.
      have:= (prefix_all Hprefix Hall); rewrite all_rcons => /andP [Hl4 _]; clear Hall.
      rewrite /= mem_filter /= in Hl4; have:= mapP Hl4 => -[[li_ii5 li_i5]] /= Hin ?.
      clear Hl4; subst li_i5; have Hhas4: has (is_label l4) (lfd_body fd).
      - by apply/hasP; eexists; first exact Hin; rewrite /is_label /= eq_refl.
      have: exists pc4, find_label l4 (lfd_body fd) = ok pc4.
      - by rewrite /find_label -has_find Hhas4; eexists.
      clear li_ii5 Hin Hhas => -[pc4] Hpc4.
      have:= (prefix_find_label (get_fundef_wf Hgfd) (prefix_trans (prefix_rcons _ _) Hprefix) Hpc4).
      rewrite /tunnel_plan -/uf => -[pcf4] Hpcf4; rewrite Hpcf4 /=.
      pose s3:= Lstate mem1 vm1 fn pcf4.+1; right; exists s3; split.
      - by case: ifP => _; rewrite Hpcf4 /= /setcpc /s2 /s3 /=.
      - by rewrite /setcpc /s1 /s3.
      by eexists; eauto.
    move => -[]; case: ifP => //; last first.
    + move => Hfindl Hmatch Hs3; right; exists s3; split => //; move: Hmatch.
      case Honthp1: (oseq.onth _ _) => [[li_ii5 li_i5]|] //.
      case: li_i5 Honthp1 => //=.
      - move => [fn5 l5] /=; case: ifP => // Heqfn; rewrite get_fundef_union get_fundef_partial Heqfn //.
        move: Heqfn => /eqP ?; subst fn5; rewrite Hgfd LUF.find_union /= !find_label_tunnel_partial.
        case: ifP => // Hfindl' _; move: Hs3; t_xrbindP => pcff1 Hfindlabel1 ?; subst s3.
        move => ? Hfindlabel1'; rewrite /setcpc /s1 /s2 /= => -[?]; subst; exfalso.
        move: Hfindl => /eqP Hfindl; apply: Hfindl; move: Hfindl' Hfindlabel1 Hfindlabel1' => /eqP <-.
        rewrite /find_label; case: ifP; case: ifP => //; rewrite -has_find => Hhas _ [<-] [Hfind].
        by apply: (find_is_label_eq Hhas Hfind).
      - move => pe5 Honth5; t_xrbindP => w5 v5 Hv5 Hw5; rewrite Hv5 /= Hw5 /=.
        rewrite Hlabel_in_lprog_tunnel Hlabel_in_lprog_tunnel_union.
        case: (decode_label _ w5) => //.
        move => [fn5 l5] /=; rewrite get_fundef_union get_fundef_partial.
        case Heqfn: (fn == fn5) => //; move: Heqfn => /eqP ?; subst fn5.
        by rewrite Hgfd /= !find_label_tunnel_partial.
      - by move => lv l; rewrite Hlabel_in_lprog_tunnel Hlabel_in_lprog_tunnel_union.
      move => pe5 l5 Honth5; t_xrbindP => b5 v5 Hv5 Hb5; rewrite Hv5 /= Hb5 /=; case: b5 {Hb5} => //.
      rewrite !find_label_tunnel_partial LUF.find_union; case: ifP => // Hfindl'.
      move: Hs3; t_xrbindP => pcff1 Hfindlabel1 ?; subst s3.
      move => ? Hfindlabel1'; rewrite /setcpc /s1 /s2 /= => -[?]; subst; exfalso.
      move: Hfindl => /eqP Hfindl; apply: Hfindl; move: Hfindl' Hfindlabel1 Hfindlabel1' => /eqP <-.
      rewrite /find_label; case: ifP; case: ifP => //; rewrite -has_find => Hhas _ [<-] [Hfind].
      by apply: (find_is_label_eq Hhas Hfind).
    rewrite (find_plan_partial (get_fundef_wf Hgfd) (prefix_trans (prefix_rcons _ _) Hprefix)).
    move => /eqP Hfindl Hmatch; t_xrbindP => pcf1' Hpcf1'.
    move: s3 Hmatch => [mem3 vm3 fn3 pc3]; pose s3:= Lstate mem3 vm3 fn3 pc3; rewrite /= -/s3.
    move => Hmatch; rewrite /setcpc => -[? ? ? ?]; subst mem3 vm3 fn3 pc3; rewrite /s1 /= -/s1.
    move => [li_ii5] [l5] Honth5; right; move: Hpcf1' Hmatch; rewrite -Hfindl => Hpcf1'.
    have:= (prefix_rcons_find_label (get_fundef_wf Hgfd) (prefix_trans (prefix_rcons _ _) Hprefix)).
    rewrite Hpcf1' => -[?]; subst pcf1'.
    have:= (get_fundef_wf Hgfd); rewrite /well_formed_body => /andP[_ Hall].
    move: Hall; rewrite /goto_targets all_filter all_map => Hall.
    have:= (prefix_all Hprefix Hall); rewrite all_rcons => /andP [Hl4 _]; clear Hall.
    rewrite /= mem_filter /= in Hl4; have:= mapP Hl4 => -[[li_ii6 li_i6]] /= Hin ?.
    clear Hl4; subst li_i6; have Hhas4: has (is_label l4) (lfd_body fd).
    + by apply/hasP; eexists; first exact Hin; rewrite /is_label /= eq_refl.
    have: exists pc4, find_label l4 (lfd_body fd) = ok pc4.
    + by rewrite /find_label -has_find Hhas4; eexists.
    clear li_ii6 Hin Hhas4 => -[pc4] Hpc4.
    have:= (prefix_find_label (get_fundef_wf Hgfd) (prefix_trans (prefix_rcons _ _) Hprefix) Hpc4).
    rewrite /tunnel_plan -/uf => -[pcf4] Hpcf4; rewrite Hpcf4 /= => Hmatch.
    pose s4:= Lstate mem1 vm1 fn pcf4.+1; exists s4; split => //; last by eexists; eauto.
    move: Hmatch; rewrite Honth5 /= eq_refl get_fundef_union get_fundef_partial Hgfd eq_refl.
    rewrite /= LUF.find_union !find_label_tunnel_partial; case: ifP; first by rewrite Hpcf4 /s4.
    move => /negP Hfindl'; t_xrbindP => pcf5 Hpcf5 ?; subst pcf5; exfalso; apply: Hfindl'; apply/eqP.
    rewrite -(find_plan_partial (get_fundef_wf Hgfd) (prefix_trans (prefix_rcons _ _) Hprefix)) -/uf in Hpcf1'.
    move: Hpcf1' Hpcf5; rewrite /find_label; case: ifP; case: ifP => //.
    by rewrite -has_find => Hhas _ [<-] [Hfind]; rewrite (find_is_label_eq Hhas Hfind).
  Qed.

  Lemma lsem1_tunneling s1 s2 :
    lsem1 p mov_op s1 s2 ->
    exists s3, lsem (lprog_tunnel fn p) mov_op s2 s3
               /\ lsem1 (lprog_tunnel fn p) mov_op s1 s3.
  Proof.
    move => H1p12; case: (lsem11_tunneling H1p12) => [H1tp12|[s3] [H1tp23 H1tp13 _]].
    + by exists s2; split => //; apply: Relation_Operators.rt_refl.
    by exists s3; split => //; apply: Relation_Operators.rt_step.
  Qed.

  Theorem lsem_tunneling s1 s2 :
    lsem p mov_op s1 s2 ->
    exists s3, lsem p mov_op s2 s3
               /\ lsem (lprog_tunnel fn p) mov_op s1 s3.
  Proof.
    have Ht: (lsem p mov_op s1 s2 →
              ∃ s3 : lstate, lsem (lprog_tunnel fn p) mov_op s2 s3
                             ∧ lsem (lprog_tunnel fn p) mov_op s1 s3);
      last first.
    + by move => Hp12; case: (Ht Hp12) => s3 [Hp23 Htp13]; exists s3; split => //; apply: tunneling_lsem.
    move: s1 s2; apply lsem_ind_r; first by move => s; exists s; split; apply Relation_Operators.rt_refl.
    move => s1 s2 s3 Hp12 H1p23 [s4 [Htp24 Htp14]].
    case: (lsem1_tunneling H1p23) => [s4' [Hp34' H1tp24']].
    case (lsem_disj1 H1tp24' Htp24) => [Heq24|Htp44'].
    + by exists s4'; split => //; apply: (lsem_trans Htp14); rewrite -Heq24; apply: Relation_Operators.rt_step.
    by exists s4; split => //; apply: (lsem_trans Hp34' _).
>>>>>>> glob_array3
*)
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

  Lemma well_formed_tunnel_funcs lf :
    well_formed_funcs lf ->
    well_formed_funcs (tunnel_funcs lf).
  Proof.
    rewrite tunnel_funcs_partial_eq => Hwf.
    elim: (size lf) => [|n IHwf]; first by rewrite tunnel_funcs_partial0.
    rewrite tunnel_funcs_partial_fn; last first.
    + by move: Hwf; rewrite /well_formed_funcs => /andP [].
    case Honth: (onth _ _) => [[fn fd]|//].
    by apply/well_formed_tunnel_funcs_fn.
  Qed.

  Lemma well_formed_tunnel_lprog_pc p fn pc :
    well_formed_lprog p ->
    well_formed_lprog (tunnel_lprog_pc p fn pc).
  Proof.
    case: p => rip rsp globs lf; rewrite /well_formed_lprog /=.
    by apply well_formed_tunnel_funcs_pc.
  Qed.

  Lemma well_formed_tunnel_lprog_fn p fn :
    well_formed_lprog p ->
    well_formed_lprog (tunnel_lprog_fn p fn).
  Proof.
    case: p => rip rsp globs lf; rewrite /well_formed_lprog /=.
    by apply well_formed_tunnel_funcs_fn.
  Qed.

  Lemma well_formed_tunnel_lprog p :
    well_formed_lprog p ->
    well_formed_lprog (tunnel_lprog p).
  Proof.
    case: p => rip rsp globs lf; rewrite /well_formed_lprog /=.
    by apply well_formed_tunnel_funcs.
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
      case: i Honth => [? ? ?| |?|[fn l'']|?|? ?|pe l''] /= Honth Hpc HSpc /=.
      1-3,5-6:
        by apply FT_Otherwise; rewrite Hgfd eq_refl.
      - case: ifP => [/eqP ?|Hneq]; last first.
        * apply FT_Otherwise; rewrite Hgfd eq_refl //=.
          rewrite /is_local_goto_to_label /= Hneq /=; move: Hpc HSpc.
          set c:= nth _ _ _; set c':= nth _ _ _; move: c c' => [? i] [? i'].
          by case: i; case: i'.
        subst fn; rewrite LUF.find_union !LUF.find_empty.
        case: ifP => [/eqP ?|Hneq]; last first.
        * apply FT_Otherwise; rewrite Hgfd eq_refl //=.
          rewrite /is_local_goto_to_label /=; move: Hpc HSpc.
          set c:= nth _ _ _; set c':= nth _ _ _; move: c c' => [? i] [? i'].
          case: i; case: i' => //= l''' l'''' /eqP ? /eqP ?; subst l''' l''''.
          by rewrite eq_sym in Hneq; rewrite Hneq Bool.andb_false_r.
        subst l''; set c:= MkLI _ _.
        move: (@FT_GotoLabelLabel p s (lfn s) pc (Some c) fd c l l' Hgfd).
        by rewrite eq_refl /= => HFT; apply HFT => //; rewrite /c /is_goto /= !eq_refl.
      rewrite LUF.find_union !LUF.find_empty.
      case: ifP => [/eqP ?|Hneq]; last first.
      * apply FT_Otherwise; rewrite Hgfd eq_refl //=.
        rewrite /is_cond_to_label /=; move: Hpc HSpc.
        set c:= nth _ _ _; set c':= nth _ _ _; move: c c' => [? i] [? i'].
        case: i; case: i' => //= l''' l'''' /eqP ? /eqP ?; subst l''' l''''.
        by rewrite eq_sym in Hneq; rewrite Hneq Bool.andb_false_r.
      subst l''; set c:= MkLI _ _.
      move: (@FT_CondLabelLabel p s (lfn s) pc (Some c) fd c pe l l').
      by rewrite eq_refl /= => HFT; apply HFT => //; rewrite /c /is_cond /= !eq_refl.
    + rewrite /tunnel_head onth_map; case Honth: (onth _ _) => [[ii i]|]; last first.
      - by move => Hpc HSpc; apply FT_Otherwise; rewrite Hgfd eq_refl.
      case: i Honth => [? ? ?| |?|[fn l'']|?|? ?|pe l''] /= Honth Hpc HSpc /=.
      1-3,5-6:
        by apply FT_Otherwise; rewrite Hgfd eq_refl.
      - case: ifP => [/eqP ?|Hneq]; last first.
        * apply FT_Otherwise; rewrite Hgfd eq_refl //=.
          rewrite /is_local_goto_to_label /= Hneq /=; move: Hpc HSpc.
          set c:= nth _ _ _; set c':= nth _ _ _; move: c c' => [? i] [? i'].
          by case: i; case: i'.
        subst fn; rewrite LUF.find_union !LUF.find_empty.
        case: ifP => [/eqP ?|Hneq]; last first.
        * apply FT_Otherwise; rewrite Hgfd eq_refl //=.
          rewrite /is_local_goto_to_label /=; move: Hpc HSpc.
          set c:= nth _ _ _; set c':= nth _ _ _; move: c c' => [? i] [? i'].
          case: i; case: i' => //= -[fn l'''] l'''' /eqP ? /andP [/eqP ? /eqP ?]; subst fn l''' l''''.
          by rewrite eq_sym in Hneq; rewrite Hneq Bool.andb_false_r.
        subst l''; set c:= MkLI _ _.
        move: (@FT_GotoLabelGoto p s (lfn s) pc (Some c) fd c l l' Hgfd).
        by rewrite eq_refl /= => HFT; apply HFT => //; rewrite /c /is_goto /= !eq_refl.
      rewrite LUF.find_union !LUF.find_empty.
      case: ifP => [/eqP ?|Hneq]; last first.
      * apply FT_Otherwise; rewrite Hgfd eq_refl //=.
        rewrite /is_cond_to_label /=; move: Hpc HSpc.
        set c:= nth _ _ _; set c':= nth _ _ _; move: c c' => [? i] [? i'].
        case: i; case: i' => //= -[fn l'''] l'''' /eqP ? /andP [/eqP ? /eqP ?]; subst fn l''' l''''.
        by rewrite eq_sym in Hneq; rewrite Hneq Bool.andb_false_r.
      subst l''; set c:= MkLI _ _.
      move: (@FT_CondLabelGoto p s (lfn s) pc (Some c) fd c pe l l').
      by rewrite eq_refl /= => HFT; apply HFT => //; rewrite /c /is_cond /= !eq_refl.
    + apply FT_Otherwise; rewrite Hgfd eq_refl /=; move: Hpc HSpc => /=.
      set c:= nth _ _ _; set c':= nth _ _ _; move: c c' => [ii i] [ii' i'].
      case: i => //= l'' /eqP ?; subst l''.
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
    by case: i => [| | |[]| | | ]; (case: i' => [| | |[]| | | ]);
    (case: i'' => [| | |[]| | | ] => //=); intros; rewrite Bool.orb_false_r Bool.andb_false_r.
  Qed.

  Lemma find_label_tunnel_lcmd_pc l fn lc pc :
    find_label l (tunnel_lcmd_pc fn lc pc) = find_label l lc.
  Proof.
    rewrite /find_label /tunnel_lcmd_pc /tunnel_engine /tunnel_head.
    rewrite size_map seq.find_map; set p:= preim _ _.
    rewrite (@eq_in_find _ p (is_label l) lc) //.
    move => [ii i] _; rewrite /p => {p} /=.
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

  Lemma eval_instr_tunnel_lprog_pc p fn pc :
    uniq (map fst (lp_funcs p)) ->
    eval_instr (tunnel_lprog_pc p fn pc) =2 eval_instr p.
  Proof.
    move => Huniq [ii i] s; case: i => [ | | |[fn' l]|pe|lv l|pe l] //=.
    + rewrite /eval_instr /= /tunnel_funcs_pc; case Hgfd: (get_fundef (lp_funcs p) fn) => [fd|//].
      rewrite get_fundef_setfunc -get_fundef_in Hgfd /=; case: ifP => // /eqP ?; subst fn'.
      by rewrite Hgfd /tunnel_lfundef_pc lfd_body_setfb /= find_label_tunnel_lcmd_pc.
    + rewrite /eval_instr /= label_in_lprog_tunnel_lprog_pc //.
      apply bind_eq => // u. case: (decode_label _ _) => // r.
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
    + rewrite ltn0Sn; move: Hislabel; case: i => //= l'.
      move => {IHlc} /eqP ?; subst l' => /andP [/negP Hnotin _].
      case: pc => // pc /= Hislabel; exfalso; apply: Hnotin.
      rewrite mem_filter /=; move: Hislabel.
      elim: lc pc => [|[{ii} ii i] lc IHlc] pc //=; first by rewrite nth_nil.
      rewrite in_cons; case: pc => [|pc] //=.
      - by case: i => //= l' /eqP ?; subst l'; rewrite eq_refl.
      by move => Hislabel; rewrite (IHlc _ Hislabel); apply/orP; right.
    case: pc => [|pc] //=; first by rewrite Hislabel.
    move => Huniq {Hislabel} Hislabel.
    rewrite -(addn1 (find _ _)) -(addn1 (size _)) ltn_add2r.
    move: (IHlc pc) => {IHlc}; rewrite Hislabel => {Hislabel}.
    case: ifP; last first.
    + move => _; have ->: uniq (labels_of_body lc); last by move => /(_ isT isT).
      by move: Huniq; case: i => [? ? ?| |l'|[? ?]|?|? ?|? ?] //= /andP [].
    move => Hfind /(_ _ isT) IHlc; f_equal; rewrite addn1; f_equal.
    have {Huniq} Huniq: uniq (labels_of_body lc); last by case: (IHlc Huniq).
    by move: Huniq {Hfind IHlc}; case: i => //= l' /andP [].
  Qed.

  Lemma local_goto_find_label p s c fd l :
    find_instr p s = Some c ->
    get_fundef (lp_funcs p) (lfn s) = Some fd ->
    well_formed_body (lfn s) (lfd_body fd) ->
    is_goto (lfn s) l c ->
    exists pc, find_label l (lfd_body fd) = ok pc.
  Proof.
    case: c => ii [] //= -[fn l'] Hfindinstr Hgfd /andP [_ Hall].
    move => /andP [/eqP ? /eqP ?]; subst fn l'.
    move: Hfindinstr; rewrite /find_instr Hgfd => Honth.
    move: Hall => /allP /(_ (Lgoto (lfn s, l))); rewrite mem_filter /=.
    set c:= MkLI _ _ in Honth; have: c \in lfd_body fd.
    + by apply/onth_mem; exists (lpc s).
    rewrite /c; rewrite /c in Honth => {c} Hin.
    move: (map_f li_i Hin) => /= {Hin} Hin /(_ Hin).
    move => /andP [_ {Hin Honth Hgfd}].
    rewrite /find_label; case: ifP; first by intros; eexists; eauto.
    move => /negP Hnfind Hin; exfalso; apply: Hnfind; move: Hin.
    rewrite /labels_of_body mem_filter /=.
    elim: (lfd_body fd) => //= -[{ii fd} ii i] lc IHlc /=.
    rewrite -(addn1 (find _ _)) -(addn1 (size _)) in_cons.
    case: ifP; last by rewrite ltn_add2r; case: i => //= l' /eqP Hneq /orP [/eqP [?]|//]; subst l'.
    by move => _ _; rewrite addn1 ltn0Sn.
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
      move => pe' l'' Hfindinstr /andP [/eqP ? /eqP ?]; subst pe' l''.
      rewrite {1 2 3}/eval_instr /= => Hpc HSpc; t_xrbindP => b v Hv Hb.
      rewrite Hv /= Hb /=; case: ifP => [HisTb|]; last by left.
      rewrite Hgfd /=; case: pc Hpc HSpc => [//=|pc] Hpc HSpc; rewrite /= in Hpc.
      rewrite (@nth_label_find_label l (lfd_body fd) pc) //=.
      t_xrbindP => pc' Hfindlabel'; move => ?; subst s2.
      case: s1 Hgfd Hwfb Hallg Hfindinstr Hv HSpc.
      move => mem vm fn pc1; rewrite /setcpc; set c:= nth _ _ _ => //=.
      set s1:= {| lmem := mem; lvm := vm; lfn := fn; lpc := pc1 |}.
      set s2:= {| lmem := mem; lvm := vm; lfn := fn; lpc := pc.+1 |}.
      move => Hgfd Hwfb Hallg Hfindinstr Hv HSpc; right; exists s2; split => //.
      rewrite /find_instr Hgfd /s2 /= -/s2; case: (is_goto_nth_onth HSpc) => ii' ->.
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
      case: s1 Hgfd Hwfb Hallg Hfindinstr HSpc.
      move => mem vm fn pc1; rewrite /setcpc; set c:= nth _ _ _ => //=.
      set s1:= {| lmem := mem; lvm := vm; lfn := fn; lpc := pc1 |}.
      set s2:= {| lmem := mem; lvm := vm; lfn := fn; lpc := pc.+1 |}.
      move => Hgfd Hwfb Hallg Hfindinstr HSpc; right; exists s2; split => //.
      rewrite /find_instr Hgfd /s2 /= -/s2; case: (is_goto_nth_onth HSpc) => ii' ->.
      by rewrite /eval_instr /= Hgfd /= Hfindlabel' /=.
    + move => Hgfd /eqP ? Hfindinstr; subst fn; rewrite Hfindinstr.
      have Hwfb:= (get_fundef_well_formed_funcs_body Hgfd Hwf).
      move: (Hwfb) => /andP [Huniql Hallg].
      rewrite eval_instr_tunnel_lprog_pc //; case: c Hfindinstr => ii [] //=.
      move => pe' l'' Hfindinstr /andP [/eqP ? /eqP ?]; subst pe' l''.
      rewrite {1 2 3}/eval_instr /= => Hpc HSpc; t_xrbindP => b v Hv Hb.
      rewrite Hv /= Hb /=; case: ifP => [HisTb|]; last by left.
      rewrite Hgfd /=; case: pc Hpc HSpc => [//=|pc] Hpc HSpc; rewrite /= in Hpc.
      rewrite (@nth_label_find_label l (lfd_body fd) pc) //=.
      rewrite (@nth_label_find_label l' (lfd_body fd) pc.+1) //=.
      move => [?]; subst s2; case: s1 Hgfd Hwfb Hallg Hfindinstr Hv HSpc.
      move => mem vm fn pc1; rewrite /setcpc; set c:= nth _ _ _ => //=.
      set s1:= {| lmem := mem; lvm := vm; lfn := fn; lpc := pc1 |}.
      set s2:= {| lmem := mem; lvm := vm; lfn := fn; lpc := pc.+1 |}.
      move => Hgfd Hwfb Hallg Hfindinstr Hv HSpc; right; exists s2; split => //.
      rewrite /find_instr Hgfd /s2 /= -/s2; case: (is_label_nth_onth HSpc) => ii' ->.
      by rewrite /eval_instr.
    move => Hgfd /eqP ? Hfindinstr; subst fn; rewrite Hfindinstr.
    have Hwfb:= (get_fundef_well_formed_funcs_body Hgfd Hwf).
    move: (Hwfb) => /andP [Huniql Hallg].
    rewrite eval_instr_tunnel_lprog_pc //; case: c Hfindinstr => ii [] //=.
    move => [fn' l''] Hfindinstr /andP [/eqP ? /eqP ?]; subst fn' l''.
    rewrite {1 2 3}/eval_instr /= => Hpc HSpc.
    rewrite Hgfd /=; case: pc Hpc HSpc => [//=|pc] Hpc HSpc; rewrite /= in Hpc.
    rewrite (@nth_label_find_label l (lfd_body fd) pc) //=.
    rewrite (@nth_label_find_label l' (lfd_body fd) pc.+1) //=.
    move => [?]; subst s2; case: s1 Hgfd Hwfb Hallg Hfindinstr HSpc.
    move => mem vm fn pc1; rewrite /setcpc; set c:= nth _ _ _ => //=.
    set s1:= {| lmem := mem; lvm := vm; lfn := fn; lpc := pc1 |}.
    set s2:= {| lmem := mem; lvm := vm; lfn := fn; lpc := pc.+1 |}.
    move => Hgfd Hwfb Hallg Hfindinstr HSpc; right; exists s2; split => //.
    rewrite /find_instr Hgfd /s2 /= -/s2; case: (is_label_nth_onth HSpc) => ii' ->.
    by rewrite /eval_instr.
  Qed.

  Lemma tunnel_lprog_pc_lsem p fn pc s1 s2 :
    well_formed_lprog p ->
    lsem (tunnel_lprog_pc p fn pc) s1 s2 ->
    lsem p s1 s2.
(*
=======
  Section MOV_OP.
  Context
    (mov_op: asm_op).

  Lemma partial_tunnel_program_lsem fns p s1 s2 :
    well_formed_lprog p ->
    lsem (foldr lprog_tunnel p fns) mov_op s1 s2 ->
    lsem p mov_op s1 s2.
>>>>>>> glob_array3
*)
  Proof.
    move => Hwf Htlsem12; pattern s1, s2; set Q:= (fun _ => _); move: Htlsem12; apply: lsem_ind_r.
    + by rewrite /Q => s; apply Relation_Operators.rt_refl.
    rewrite /Q => {Q} s3 s4 s5 Htlsem34 Htlsem145 Hlsem34.
    apply (lsem_trans Hlsem34); case: (tunnel_lprog_pc_lsem1 Hwf Htlsem145).
    + by move => Hlsem145; apply Relation_Operators.rt_step.
    by case => s6 [Hlsem146 Hlsem165]; apply (@lsem_trans p s6); apply Relation_Operators.rt_step.
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
      move => pe' l'' Hfindinstr /andP [/eqP ? /eqP ?]; subst pe' l''.
      rewrite {1 2 4}/eval_instr /= => Hpc HSpc; t_xrbindP => b v Hv Hb.
      rewrite Hv /= Hb /=; case: ifP => [HisTb|]; last by left.
      rewrite Hgfd /=; case: pc Hpc HSpc => [//=|pc] Hpc HSpc; rewrite /= in Hpc.
      rewrite (@nth_label_find_label l (lfd_body fd) pc) //=.
      move => [?]; subst s2; case : s1 Hgfd Hwfb Hallg Hfindinstr Hv HSpc.
      move => mem vm fn pc1; rewrite /setcpc; set c:= nth _ _ _ => //=.
      set s1:= {| lmem := mem; lvm := vm; lfn := fn; lpc := pc1 |}.
      set s2:= {| lmem := mem; lvm := vm; lfn := fn; lpc := pc.+1 |}.
      move => Hgfd Hwfb Hallg Hfindinstr Hv HSpc.
      move: (@local_goto_find_label p s2 c fd l').
      rewrite /s2 /= -/s2 => /(_ _ Hgfd Hwfb HSpc); case.
      - rewrite /find_instr /s2 /= Hgfd; move: HSpc; rewrite /c.
        set Spc:= pc.+1; elim: (lfd_body fd) Spc => [|[{ii Hfindinstr} ii i] lf IHlf] Spc.
        * by rewrite nth_nil.
        by case: Spc => [|Spc] //=; apply IHlf.
      move => pc' Hfindlabel'; rewrite Hfindlabel' /=.
      set s3:= {| lmem := mem; lvm := vm; lfn := fn; lpc := pc'.+1 |}.
      rewrite /find_instr /s2 /= -/s2 Hgfd /=.
      rewrite /c in HSpc; move: (is_goto_nth_onth HSpc) => [ii'] ->.
      rewrite /eval_instr /= Hgfd /= Hfindlabel'.
      by right; exists s3.
    + move => Hgfd /eqP ? Hfindinstr; subst fn; rewrite Hfindinstr.
      have Hwfb:= (get_fundef_well_formed_funcs_body Hgfd Hwf).
      move: (Hwfb) => /andP [Huniql Hallg].
      rewrite eval_instr_tunnel_lprog_pc //; case: c Hfindinstr => ii [] //=.
      move => [fn' l''] Hfindinstr /andP [/eqP ? /eqP ?]; subst fn' l''.
      rewrite {1 2 4}/eval_instr /= => Hpc HSpc.
      rewrite Hgfd /=; case: pc Hpc HSpc => [//=|pc] Hpc HSpc; rewrite /= in Hpc.
      rewrite (@nth_label_find_label l (lfd_body fd) pc) //=.
      move => [?]; subst s2; case : s1 Hgfd Hwfb Hallg Hfindinstr HSpc.
      move => mem vm fn pc1; rewrite /setcpc; set c:= nth _ _ _ => //=.
      set s1:= {| lmem := mem; lvm := vm; lfn := fn; lpc := pc1 |}.
      set s2:= {| lmem := mem; lvm := vm; lfn := fn; lpc := pc.+1 |}.
      move => Hgfd Hwfb Hallg Hfindinstr HSpc.
      move: (@local_goto_find_label p s2 c fd l').
      rewrite /s2 /= -/s2 => /(_ _ Hgfd Hwfb HSpc); case.
      - rewrite /find_instr /s2 /= Hgfd; move: HSpc; rewrite /c.
        set Spc:= pc.+1; elim: (lfd_body fd) Spc => [|[{ii Hfindinstr} ii i] lf IHlf] Spc.
        * by rewrite nth_nil.
        by case: Spc => [|Spc] //=; apply IHlf.
      move => pc' Hfindlabel'; rewrite Hfindlabel' /=.
      set s3:= {| lmem := mem; lvm := vm; lfn := fn; lpc := pc'.+1 |}.
      rewrite /find_instr /s2 /= -/s2 Hgfd /=.
      rewrite /c in HSpc; move: (is_goto_nth_onth HSpc) => [ii'] ->.
      rewrite /eval_instr /= Hgfd /= Hfindlabel'.
      by right; exists s3.
    + move => Hgfd /eqP ? Hfindinstr; subst fn; rewrite Hfindinstr.
      have Hwfb:= (get_fundef_well_formed_funcs_body Hgfd Hwf).
      move: (Hwfb) => /andP [Huniql Hallg].
      rewrite eval_instr_tunnel_lprog_pc //; case: c Hfindinstr => ii [] //=.
      move => pe' l'' Hfindinstr /andP [/eqP ? /eqP ?]; subst pe' l''.
      rewrite {1 2 4}/eval_instr /= => Hpc HSpc; t_xrbindP => b v Hv Hb.
      rewrite Hv /= Hb /=; case: ifP => [HisTb|]; last by left.
      rewrite Hgfd /=; case: pc Hpc HSpc => [//=|pc] Hpc HSpc; rewrite /= in Hpc.
      rewrite (@nth_label_find_label l (lfd_body fd) pc) //=.
      move => [?]; subst s2; case : s1 Hgfd Hwfb Hallg Hfindinstr Hv HSpc.
      move => mem vm fn pc1; rewrite /setcpc; set c:= nth _ _ _ => //=.
      set s1:= {| lmem := mem; lvm := vm; lfn := fn; lpc := pc1 |}.
      set s2:= {| lmem := mem; lvm := vm; lfn := fn; lpc := pc.+1 |}.
      move => Hgfd Hwfb Hallg Hfindinstr Hv HSpc.
      rewrite (@nth_label_find_label l' (lfd_body fd) pc.+1) //=.
      rewrite /find_instr /s2 /= Hgfd; case: (is_label_nth_onth HSpc) => ii' ->.
      by rewrite /eval_instr /=; right; eexists; eauto.
    move => Hgfd /eqP ? Hfindinstr; subst fn; rewrite Hfindinstr.
    have Hwfb:= (get_fundef_well_formed_funcs_body Hgfd Hwf).
    move: (Hwfb) => /andP [Huniql Hallg].
    rewrite eval_instr_tunnel_lprog_pc //; case: c Hfindinstr => ii [] //=.
    move => [fn' l''] Hfindinstr /andP [/eqP ? /eqP ?]; subst fn' l''.
    rewrite {1 2 4}/eval_instr /= => Hpc HSpc.
    rewrite Hgfd /=; case: pc Hpc HSpc => [//=|pc] Hpc HSpc; rewrite /= in Hpc.
    rewrite (@nth_label_find_label l (lfd_body fd) pc) //=.
    move => [?]; subst s2; case : s1 Hgfd Hwfb Hallg Hfindinstr HSpc.
    move => mem vm fn pc1; rewrite /setcpc; set c:= nth _ _ _ => //=.
    set s1:= {| lmem := mem; lvm := vm; lfn := fn; lpc := pc1 |}.
    set s2:= {| lmem := mem; lvm := vm; lfn := fn; lpc := pc.+1 |}.
    move => Hgfd Hwfb Hallg Hfindinstr HSpc.
    rewrite (@nth_label_find_label l' (lfd_body fd) pc.+1) //=.
    rewrite /find_instr /s2 /= Hgfd; case: (is_label_nth_onth HSpc) => ii' ->.
    by rewrite /eval_instr /=; right; eexists; eauto.
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
(*
=======
    lprog_tunnel fn p = tp ->
    size (lp_funcs p) = size (lp_funcs tp) /\
    forall n ,
      omap (fun p => size (lfd_body p.2)) (oseq.onth (lp_funcs p) n) =
      omap (fun p => size (lfd_body p.2)) (oseq.onth (lp_funcs tp) n).
  Proof.
    rewrite /lprog_tunnel /well_formed_lprog => /andP [Huniq _].
    case Hgfd: (get_fundef _ _) => [l|] <- //.
    split => [/=|n /=]; first by rewrite size_map.
    rewrite onth_map.
    case Heqn: (oseq.onth (lp_funcs p) n) => [[fn' l']|] //=.
    f_equal; case: ifP => [/eqP ?|//]; subst fn'.
    rewrite /lfundef_tunnel_partial lfd_body_setfb -tunnel_partial_size.
    case: (assoc_onth Hgfd) => m Heqm.
    rewrite oseq.onth_nth in Heqm.
    case: (le_lt_dec (size (lp_funcs p)) m) => [/leP Hlem|/ltP Hltm].
    + by rewrite nth_default in Heqm => //; rewrite size_map.
    rewrite (@nth_map _ (fn, l) _ None (fun x => Some x) m (lp_funcs p) Hltm) in Heqm.
    rewrite oseq.onth_nth in Heqn.
    case: (le_lt_dec (size (lp_funcs p)) n) => [/leP Hlen|/ltP Hltn].
    + by rewrite nth_default in Heqn => //; rewrite size_map.
    rewrite (@nth_map _ (fn, l) _ None (fun x => Some x) n (lp_funcs p) Hltn) in Heqn.
    move: Heqm Heqn => [Heqm] [Heqn].
    have:= (@nth_map _ (fn, l) _ fn fst m (lp_funcs p) Hltm); rewrite Heqm /= => Heqm1.
    have:= (@nth_map _ (fn, l) _ fn fst n (lp_funcs p) Hltn); rewrite Heqn /= => Heqn1.
    have := (@nth_uniq _ fn _ m n _ _ Huniq); rewrite !size_map Hltm Hltn Heqm1 Heqn1 => Heq.
    have Heq': (m = n) by apply/eqP; rewrite -Heq //.
    by rewrite Heq' Heqn in Heqm; move: Heqm => [->].
  Qed.

  Lemma tunnel_program_size p tp :
    tunnel_program p = ok tp ->
    size (lp_funcs p) = size (lp_funcs tp) /\
    forall n ,
      omap (fun p => size (lfd_body p.2)) (oseq.onth (lp_funcs p) n) =
      omap (fun p => size (lfd_body p.2)) (oseq.onth (lp_funcs tp) n).
  Proof.
    rewrite /tunnel_program; case: ifP => // Hwfp [].
    elim: (funnames p) tp => [tp <- //|] fn fns Hfns tp /= Heq.
    have [<- Ho1]:= (lprog_tunnel_size (well_formed_partial_tunnel_program fns Hwfp) Heq).
    have Hrefl: foldr lprog_tunnel p fns = foldr lprog_tunnel p fns by trivial.
    have [<- Ho2]:= (Hfns (foldr lprog_tunnel p fns) Hrefl).
    by split => // n; rewrite Ho2 Ho1.
  Qed.

  Lemma lprog_tunnel_invariants fn p tp :
    lprog_tunnel fn p = tp ->
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
    rewrite /lprog_tunnel => <-; case: (get_fundef _ _) => [x|//].
    rewrite /setfuncs /=; split => //; split => //; split => //.
    rewrite -!map_comp.
    split; first by apply: eq_map => -[fn' l'].
    split; first by apply: eq_map => -[fn' l'] /=; case: ifP.
    split; first by apply: eq_map => -[fn' l'] /=; case: ifP.
    split; first by apply: eq_map => -[fn' l'] /=; case: ifP.
    split; first by apply: eq_map => -[fn' l'] /=; case: ifP.
    split; first by apply: eq_map => -[fn' l'] /=; case: ifP.
    split; first by apply: eq_map => -[fn' l'] /=; case: ifP.
    by apply: eq_map => -[fn' l'] /=; case: ifP.
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
    rewrite /tunnel_program; case: ifP => // _ [].
    elim: (funnames p) tp => [tp <-|] //= fn fns Hfns tp.
    pose fp:= (foldr lprog_tunnel p fns); rewrite -/fp.
    move => Heq; have:= (lprog_tunnel_invariants Heq).
    move => [<-] [<-] [<-] [<-] [<-] [<-] [<-] [<-] [<-] [<-] <-.
    by apply Hfns.
  Qed.

  Lemma get_fundef_foldr_lprog_tunnel p fn fns fd :
    uniq fns ->
    get_fundef (lp_funcs p) fn = Some fd →
    get_fundef (lp_funcs (foldr lprog_tunnel p fns)) fn =
    if fn \in fns
    then Some (lfundef_tunnel_partial fn fd fd.(lfd_body) fd.(lfd_body))
    else Some fd.
  Proof.
    elim: fns => //= fn' fns Hfns /andP [Hnotin Huniq] Hgfd.
    move: (Hfns Huniq Hgfd) => {Hfns} {Hgfd} Hfns.
    rewrite get_fundef_lprog_tunnel Hfns {Hfns} in_cons.
    case: ifP; case: ifP => //=.
    + by move => /eqP ?; subst fn' => Hin; rewrite Hin /= in Hnotin.
    + by rewrite eq_sym => -> .
    + by move => /eqP ?; subst fn'; rewrite eq_refl.
    by rewrite eq_sym => ->.
  Qed.

  Definition tunnel_fd fn fd :=
    lfundef_tunnel_partial fn fd (lfd_body fd) (lfd_body fd).

  Lemma get_fundef_tunnel_program p tp fn fd :
    tunnel_program p = ok tp →
    get_fundef (lp_funcs p) fn = Some fd →
    get_fundef (lp_funcs tp) fn = Some (tunnel_fd fn fd).
>>>>>>> glob_array3
*)
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

  Lemma tunnel_lprog_lsem p s1 s2:
    well_formed_lprog p ->
    lsem (tunnel_lprog p) s1 s2 -> lsem p s1 s2.
  Proof. by move => Hwf; move : (lsem_tunnel_lprog_lsem Hwf) => [HP _]; apply HP. Qed.

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
(*
=======
    lsem p mov_op s1 s2 ->
    exists s3, lsem p mov_op s2 s3 /\ lsem tp mov_op s1 s3.
  Proof.
    rewrite /tunnel_program; case: ifP => // wfp [<-].
    elim: funnames => [|hfns tfns IHfns /=]; first by exists s2; split => //; apply: Relation_Operators.rt_refl.
    move => Hlsem12; case: (IHfns Hlsem12) => s3 [Hlsem23 Hplsem13].
    case: (lsem_tunneling hfns (well_formed_partial_tunnel_program _ wfp) Hplsem13) => s4 [Hplsem34 Hpplsem14].
    exists s4; split => //; apply: (lsem_trans Hlsem23).
    by apply: (partial_tunnel_program_lsem wfp Hplsem34).
  Qed.
>>>>>>> glob_array3
*)

  Corollary lsem_run_tunnel_program p tp s1 s2 :
    tunnel_program p = ok tp →
    lsem p mov_op s1 s2 →
    lsem_final p s2 →
    lsem tp mov_op s1 s2 ∧ lsem_final tp s2.
  Proof.
    move => Htp Hlsem12 Hfinal2; case: (lsem_tunnel_program Htp Hlsem12) => s3 [Hlsem23 Htlsem13].
    have ?:= (lsem_final_stutter Hlsem23 Hfinal2); subst s3; split => //.
    move: Htp Hfinal2 {Hlsem12 Htlsem13 Hlsem23}; rewrite /lsem_final.
    rewrite /tunnel_program; case: ifP => // _ [?]; subst tp.
    move => [fd] Hgfd ->. rewrite /tunnel_lprog lp_funcs_setfuncs.
    rewrite get_fundef_tunnel_funcs Hgfd; eexists; first by eauto.
    by rewrite /tunnel_lfundef lfd_body_setfb size_tunnel_lcmd.
  Qed.

End TunnelingProof.
(*
=======
End MOV_OP.

End TunnelingCompilerProof.

End ASM_OP.
>>>>>>> glob_array3
*)
