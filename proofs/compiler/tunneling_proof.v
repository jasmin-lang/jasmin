From mathcomp Require Import all_ssreflect all_algebra.
Require Import ZArith.
Require Import Utf8.

Require Import oseq expr compiler_util label x86_variables linear linear_sem.
Import ssrZ.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope seq_scope.

Require Import tunneling_misc unionfind tunneling unionfind_proof.
Require Import linear_sem.



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

  Lemma onth_mem (T : eqType) (x : T) (s : seq T) :
    reflect (exists i, onth s i = Some x) (x \in s).
  Proof.
    elim: s => [//=|y s IHs].
    + by rewrite in_nil; apply ReflectF => -[].
    rewrite in_cons /=; case Heq: (x == y) => /=.
    + by apply ReflectT; exists 0; move: Heq => /eqP ->.
    elim: IHs => [Hexists|Hnexists].
    + by apply ReflectT; case: Hexists => i Honth; exists (i.+1).
    apply ReflectF => -[i] Hmatch; apply Hnexists.
    case: i Hmatch => [[?]|i Honth]; last by exists i.
    by subst y; rewrite eq_refl in Heq.
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

  Lemma get_fundef_foldrW (A : Type) (P : A -> A -> Prop) (f : funname -> lfundef -> A -> A) lf :
    (forall x, P x x) ->
    (forall y x z, P x y -> P y z -> P x z) ->
    uniq (map fst lf) ->
    (forall fn fd x,
      get_fundef lf fn = Some fd ->
      P x (f fn fd x)) ->
    forall x,
      P x (foldr (fun p y => f p.1 p.2 y) x lf).
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

  Variant tunnel_chart_weak_spec fn (uf : LUF.unionfind) : linstr -> linstr -> LUF.unionfind -> Type :=
  | TCW_LabelLabel ii ii' l l' :
      tunnel_chart_weak_spec
        fn uf (MkLI ii (Llabel l)) (MkLI ii' (Llabel l')) (LUF.union uf l l')

  | TCW_LabelGotoEq ii ii' l l' :
      tunnel_chart_weak_spec
        fn uf (MkLI ii (Llabel l)) (MkLI ii' (Lgoto (fn, l'))) (LUF.union uf l l')

  | TCW_Otherwise c c' :
      tunnel_chart_weak_spec fn uf c c' uf.

  Variant tunnel_chart_spec fn (uf : LUF.unionfind) : linstr -> linstr -> LUF.unionfind -> Type :=
  | TC_LabelLabel ii ii' l l' :
      tunnel_chart_spec fn uf (MkLI ii (Llabel l)) (MkLI ii' (Llabel l')) (LUF.union uf l l')

  | TC_LabelGotoEq ii ii' l l' :
      tunnel_chart_spec fn uf (MkLI ii (Llabel l)) (MkLI ii' (Lgoto (fn, l'))) (LUF.union uf l l')

  | TC_LabelGotoNEq ii ii' l l' fn' of (fn != fn') :
      tunnel_chart_spec fn uf (MkLI ii (Llabel l)) (MkLI ii' (Lgoto (fn', l'))) uf

  | TC_Otherwise c c' of (~~ ((li_is_label c && li_is_label c') || (li_is_label c && li_is_goto c'))) :
      tunnel_chart_spec fn uf c c' uf.

  Lemma tunnel_chartWP fn uf c c' : tunnel_chart_weak_spec fn uf c c' (tunnel_chart fn uf c c').
  Proof.
  case: c c' => [ii i] [ii' i'];
    case: i'; case: i; try by move=> *; apply: TCW_Otherwise.
  + by move => l l'; apply TCW_LabelLabel.
  move=> l [fn' l'] /=; case: ifPn => [/eqP<-|].
  + by apply: TCW_LabelGotoEq.
  by move=> _; apply: TCW_Otherwise.
  Qed.

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

  Inductive tunnel_plan_weak_spec fn uf : lcmd -> LUF.unionfind -> Type :=
  | TPW_Nil:
      tunnel_plan_weak_spec fn uf [::] uf
  | TPW_One c :
      tunnel_plan_weak_spec fn uf [:: c] uf
  | TPW_LabelLabel uf' fb ii ii' l l' :
      tunnel_plan_weak_spec fn uf (rcons fb (MkLI ii (Llabel l))) uf' ->
      tunnel_plan_weak_spec fn uf (rcons (rcons fb (MkLI ii (Llabel l))) (MkLI ii' (Llabel l'))) (LUF.union uf' l l')
  | TPW_LabelGotoEq uf' fb ii ii' l l' :
      tunnel_plan_weak_spec fn uf (rcons fb (MkLI ii (Llabel l))) uf' ->
      tunnel_plan_weak_spec fn uf (rcons (rcons fb (MkLI ii (Llabel l))) (MkLI ii' (Lgoto (fn, l')))) (LUF.union uf' l l')
  | TPW_Otherwise uf' fb c c' :
      tunnel_plan_weak_spec fn uf (rcons fb c) uf' ->
      tunnel_plan_weak_spec fn uf (rcons (rcons fb c) c') uf'.

  Inductive tunnel_plan_spec fn uf : lcmd -> LUF.unionfind -> Type :=
  | TP_Nil:
      tunnel_plan_spec fn uf [::] uf
  | TP_One c :
      tunnel_plan_spec fn uf [:: c] uf
  | TP_LabelLabel uf' fb ii ii' l l' :
      tunnel_plan_spec fn uf (rcons fb (MkLI ii (Llabel l))) uf' ->
      tunnel_plan_spec fn uf (rcons (rcons fb (MkLI ii (Llabel l))) (MkLI ii' (Llabel l'))) (LUF.union uf' l l')
  | TP_LabelGotoEq uf' fb ii ii' l l' :
      tunnel_plan_spec fn uf (rcons fb (MkLI ii (Llabel l))) uf' ->
      tunnel_plan_spec fn uf (rcons (rcons fb (MkLI ii (Llabel l))) (MkLI ii' (Lgoto (fn, l')))) (LUF.union uf' l l')
  | TP_LabelGotoNEq uf' fb ii ii' l l' fn' of (fn != fn') :
      tunnel_plan_spec fn uf (rcons fb (MkLI ii (Llabel l))) uf' ->
      tunnel_plan_spec fn uf (rcons (rcons fb (MkLI ii (Llabel l))) (MkLI ii' (Lgoto (fn', l')))) uf'
  | TP_Otherwise uf' fb c c' of (~~ ((li_is_label c && li_is_label c') || (li_is_label c && li_is_goto c'))):
      tunnel_plan_spec fn uf (rcons fb c) uf' ->
      tunnel_plan_spec fn uf (rcons (rcons fb c) c') uf'.

  Lemma tunnel_planWP fn uf fb : tunnel_plan_weak_spec fn uf fb (tunnel_plan fn uf fb).
  Proof.
    elim/last_ind: fb => [|fb c']; first by apply: TPW_Nil.
    case/lastP: fb => [/= HTP|fb c HTP].
    + by rewrite tunnel_plan1; apply: TPW_One.
    rewrite tunnel_plan_rcons_rcons; move: HTP; set uf':= (tunnel_plan _ _ _).
    (*TODO: any  way to do this with the case: in ssreflect?*)
    ecase tunnel_chartWP.
    + by apply: TPW_LabelLabel.
    + by apply: TPW_LabelGotoEq.
    by apply:  TPW_Otherwise.
  Qed.

  Lemma tunnel_planP fn uf fb : tunnel_plan_spec fn uf fb (tunnel_plan fn uf fb).
  Proof.
    elim/last_ind: fb => [|fb c']; first by apply: TP_Nil.
    case/lastP: fb => [/= HTP|fb c HTP].
    + by rewrite tunnel_plan1; apply: TP_One.
    rewrite tunnel_plan_rcons_rcons; move: HTP; set uf':= (tunnel_plan _ _ _).
    ecase tunnel_chartP.
    + by apply: TP_LabelLabel.
    + by apply: TP_LabelGotoEq.
    + by apply: TP_LabelGotoNEq.
    by apply:  TP_Otherwise.
  Qed.

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

  (*
  Lemma tunnel_bore_proj fn uf c :
    tunnel_bore fn uf (tunnel_bore fn uf c) = (tunnel_bore fn uf c).
  Proof.
    case: (tunnel_boreP _ _ c) => [ii l|ii pe l|ii pe l|c'] //=.
    + by rewrite eq_refl LUF.find_find.
    + by case: ifP => //; rewrite LUF.find_find.
    + by rewrite LUF.find_find.
    by case: tunnel_boreP.
  Qed.
  *)

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

  Lemma lsem11_tunnel_lprog_pc p fn pc s1 s2 :
    well_formed_lprog p ->
    lsem1 p s1 s2 ->
    lsem1 (tunnel_lprog_pc p fn pc) s1 s2 \/
    exists s3, lsem1 (tunnel_lprog_pc p fn pc) s1 s3 /\
           lsem1 (tunnel_lprog_pc p fn pc) s2 s3.
  Proof.
    move => Hwf; move: (Hwf) => /andP [Huniq Hall]; rewrite /lsem1 /step.
    case: find_instr_tunnel_lprog_pcP =>
      [fd c l l'|fd c pe l l'|fd c l l'|fd c pe l l'|_];
      last first.
    + by case: (find_instr _ _) => // oc; rewrite eval_instr_tunnel_lprog_pc //; left.
    + move => Hgfd /eqP ? Hfindinstr; subst fn; rewrite Hfindinstr.
      rewrite eval_instr_tunnel_lprog_pc //; case: c Hfindinstr => ii [] //=.
      move => pe' l'' Hfindinstr /andP [/eqP ? /eqP ?]; subst pe' l''.
      rewrite {1 2 3}/eval_instr /= => Hpc HSpc; t_xrbindP => b v Hv Hb.
      rewrite Hv /= Hb /=; case: ifP => [HisTb|]; last by left.
      rewrite Hgfd /=; case: pc Hpc HSpc => [//=|pc] Hpc HSpc; rewrite /= in Hpc.
      rewrite (@nth_label_find_label l (lfd_body fd) pc) //=; last first.
      - by move: (get_fundef_well_formed_funcs_body Hgfd Hwf) => /andP [].
      move => [?]; subst s2; case : s1 Hgfd Hfindinstr Hv HSpc.
      move => mem vm fn pc1; rewrite /setcpc; set c:= nth _ _ _ => //=.
      set s1:= {| lmem := mem; lvm := vm; lfn := fn; lpc := pc1 |}.
      set s2:= {| lmem := mem; lvm := vm; lfn := fn; lpc := pc.+1 |}.
      move => Hgfd Hfindinstr Hv HSpc; move: (@local_goto_find_label p s2 c fd l').
      have Hwfb:= (get_fundef_well_formed_funcs_body Hgfd Hwf).
      rewrite /s2 /= -/s2 => /(_ _ Hgfd Hwfb HSpc); case.
      - rewrite /find_instr /s2 /= Hgfd; move: HSpc; rewrite /c.
        set Spc:= pc.+1; elim: (lfd_body fd) Spc => [|[{ii Hfindinstr} ii i] lf IHlf] Spc.
        * by rewrite nth_nil.
        by case: Spc => [|Spc] //=; apply IHlf.
      move => pc' Hfindlabel'; rewrite Hfindlabel' /=.
      set s3:= {| lmem := mem; lvm := vm; lfn := fn; lpc := pc'.+1 |}.
      case: find_instr_tunnel_lprog_pcP =>
        [fd' c' l'' l'''|fd' c' pe' l'' l'''|fd' c' l'' l'''|fd' c' pe' l'' l'''|].
      1-2:
        by rewrite Hgfd => -[?] _; subst fd' => _ _ _;
        move: HSpc; rewrite /c; set Spc:= pc.+1; move: Spc => Spc /=;
        set c'':= nth _ _ _; case: c'' => [ii'' []].
      - rewrite Hgfd => -[?] _; subst fd' => Hfindinstr' Hisgoto Hpc' HSpc'.
        rewrite /= in Hpc'.
        have ?: l = l''; last subst l'' => {Hpc'}.
        * by move: Hpc Hpc'; case: (nth _ _ _) => ? [] //= l'''' /eqP ? /eqP ?; subst l'' l''''.
        have ?: l' = l'''; last subst l''' => {HSpc'}.
        * have: is_goto fn l''' c by rewrite /c; move: HSpc' => //=.
          move: HSpc; case: c => [ii' []] //= -[fn' l''''].
          move => /andP [/eqP ? /eqP ?]; subst fn' l''''.
          by move => /andP [_ /eqP ?]; subst l'''.
        rewrite eval_instr_tunnel_lprog_pc /eval_instr //= Hgfd /=.
        by rewrite Hfindlabel' /=; right; exists s3; split.
      - rewrite Hgfd => -[?] _; subst fd' => Hfindinstr' Hisgoto Hpc' HSpc'.
        rewrite /= in Hpc'; exfalso; move: Hfindinstr' Hisgoto HSpc'.
        rewrite /find_instr Hgfd => /(@onthP _ Linstr_align).
        move => /andP [_ /eqP <-]; rewrite /s2 /=.
        by case: (lfd_body fd) => // _ l''''; case: (nth _ _ _) => ? [].
      rewrite Hgfd => _; rewrite /find_instr Hgfd /s2 /= -/s2.
      have ->: onth (lfd_body fd) pc.+1 = Some c.
      - move: HSpc; rewrite /c; elim: (lfd_body fd) {Hpc c s2} pc => [|c lf IHlf] pc //=.
        case: pc => [|pc]; last by apply/IHlf.
        by case: {IHlf} lf.
      rewrite eval_instr_tunnel_lprog_pc //; right; exists s3; split => //.
      move: HSpc; case: c => {ii Hfindinstr} ii [] //= -[fn' l''].
      move => /andP [/eqP ? /eqP ?]; subst fn' l''.
      by rewrite /eval_instr /= Hgfd /= Hfindlabel'.
    + move => Hgfd /eqP ? Hfindinstr; subst fn; rewrite Hfindinstr.
      rewrite eval_instr_tunnel_lprog_pc //; case: c Hfindinstr => ii [] //=.
      move => [fn l''] Hfindinstr /andP [/eqP ? /eqP ?]; subst fn l''.
      rewrite {1 2 3}/eval_instr /= => Hpc HSpc.
      rewrite Hgfd /=; case: pc Hpc HSpc => [//=|pc] Hpc HSpc; rewrite /= in Hpc.
      rewrite (@nth_label_find_label l (lfd_body fd) pc) //=; last first.
      - by move: (get_fundef_well_formed_funcs_body Hgfd Hwf) => /andP [].
      move => [?]; subst s2; case : s1 Hgfd Hfindinstr HSpc.
      move => mem vm fn pc1; rewrite /setcpc; set c:= nth _ _ _ => //=.
      set s1:= {| lmem := mem; lvm := vm; lfn := fn; lpc := pc1 |}.
      set s2:= {| lmem := mem; lvm := vm; lfn := fn; lpc := pc.+1 |}.
      move => Hgfd Hfindinstr HSpc; move: (@local_goto_find_label p s2 c fd l').
      have Hwfb:= (get_fundef_well_formed_funcs_body Hgfd Hwf).
      rewrite /s2 /= -/s2 => /(_ _ Hgfd Hwfb HSpc); case.
      - rewrite /find_instr /s2 /= Hgfd; move: HSpc; rewrite /c.
        set Spc:= pc.+1; elim: (lfd_body fd) Spc => [|[{ii Hfindinstr} ii i] lf IHlf] Spc.
        * by rewrite nth_nil.
        by case: Spc => [|Spc] //=; apply IHlf.
      move => pc' Hfindlabel'; rewrite Hfindlabel' /=.
      set s3:= {| lmem := mem; lvm := vm; lfn := fn; lpc := pc'.+1 |}.
      case: find_instr_tunnel_lprog_pcP =>
        [fd' c' l'' l'''|fd' c' pe' l'' l'''|fd' c' l'' l'''|fd' c' pe' l'' l'''|].
      1-2:
        by rewrite Hgfd => -[?] _; subst fd' => _ _ _;
        move: HSpc; rewrite /c; set Spc:= pc.+1; move: Spc => Spc /=;
        set c'':= nth _ _ _; case: c'' => [ii'' []].
      - rewrite Hgfd => -[?] _; subst fd' => Hfindinstr' Hisgoto Hpc' HSpc'.
        rewrite /= in Hpc'.
        have ?: l = l''; last subst l'' => {Hpc'}.
        * by move: Hpc Hpc'; case: (nth _ _ _) => ? [] //= l'''' /eqP ? /eqP ?; subst l'' l''''.
        have ?: l' = l'''; last subst l''' => {HSpc'}.
        * have: is_goto fn l''' c by rewrite /c; move: HSpc' => //=.
          move: HSpc; case: c => [ii' []] //= -[fn' l''''].
          move => /andP [/eqP ? /eqP ?]; subst fn' l''''.
          by move => /andP [_ /eqP ?]; subst l'''.
        rewrite eval_instr_tunnel_lprog_pc /eval_instr //= Hgfd /=.
        by rewrite Hfindlabel' /=; right; exists s3; split.
      - rewrite Hgfd => -[?] _; subst fd' => Hfindinstr' Hisgoto Hpc' HSpc'.
        rewrite /= in Hpc'; exfalso; move: Hfindinstr' Hisgoto HSpc'.
        rewrite /find_instr Hgfd => /(@onthP _ Linstr_align).
        move => /andP [_ /eqP <-]; rewrite /s2 /=.
        by case: (lfd_body fd) => // _ l''''; case: (nth _ _ _) => ? [].
      rewrite Hgfd => _; rewrite /find_instr Hgfd /s2 /= -/s2.
      have ->: onth (lfd_body fd) pc.+1 = Some c.
      - move: HSpc; rewrite /c; elim: (lfd_body fd) {Hpc c s2} pc => [|c lf IHlf] pc //=.
        case: pc => [|pc]; last by apply/IHlf.
        by case: {IHlf} lf.
      rewrite eval_instr_tunnel_lprog_pc //; right; exists s3; split => //.
      move: HSpc; case: c => {ii Hfindinstr} ii [] //= -[fn' l''].
      move => /andP [/eqP ? /eqP ?]; subst fn' l''.
      by rewrite /eval_instr /= Hgfd /= Hfindlabel'.
    + move => Hgfd /eqP ? Hfindinstr; subst fn; rewrite Hfindinstr.
      rewrite eval_instr_tunnel_lprog_pc //; case: c Hfindinstr => ii [] //=.
      move => pe' l'' Hfindinstr /andP [/eqP ? /eqP ?]; subst pe' l''.
      rewrite {1 2 3}/eval_instr /= => Hpc HSpc; t_xrbindP => b v Hv Hb.
      rewrite Hv /= Hb /=; case: ifP => [HisTb|]; last by left.
      rewrite Hgfd /=; case: pc Hpc HSpc => [//=|pc] Hpc HSpc; rewrite /= in Hpc.
      rewrite (@nth_label_find_label l (lfd_body fd) pc) //=; last first.
      - by move: (get_fundef_well_formed_funcs_body Hgfd Hwf) => /andP [].
      move => [?]; subst s2; case : s1 Hgfd Hfindinstr Hv HSpc.
      move => mem vm fn pc1; rewrite /setcpc; set c:= nth _ _ _ => //=.
      set s1:= {| lmem := mem; lvm := vm; lfn := fn; lpc := pc1 |}.
      set s2:= {| lmem := mem; lvm := vm; lfn := fn; lpc := pc.+1 |}.
      move => Hgfd Hfindinstr Hv HSpc.
      rewrite (@nth_label_find_label l' (lfd_body fd) pc.+1) //=; last first.
      - by move: (get_fundef_well_formed_funcs_body Hgfd Hwf) => /andP [].
      set s3:= {| lmem := mem; lvm := vm; lfn := fn; lpc := pc.+2 |}.
      case: find_instr_tunnel_lprog_pcP =>
        [fd' c' l'' l'''|fd' c' pe' l'' l'''|fd' c' l'' l'''|fd' c' pe' l'' l'''|].
      - rewrite Hgfd => -[?] _; subst fd' => Hfindinstr' Hisgoto Hpc' HSpc'.
        rewrite /= in Hpc'.
        have ?: l = l''; last subst l'' => {Hpc'}.
        * by move: Hpc Hpc'; case: (nth _ _ _) => ? [] //= l'''' /eqP ? /eqP ?; subst l'' l''''.
        have ?: l' = l'''; last subst l''' => {HSpc'}.
        * have: is_label l''' c by rewrite /c; move: HSpc' => //=.
          move: HSpc; case: c => [ii' []] //= l''''.
          by move => /eqP ? /eqP ?; subst l''' l''''.
        rewrite eval_instr_tunnel_lprog_pc /eval_instr //= Hgfd /=.
        rewrite (@nth_label_find_label l' (lfd_body fd) pc.+1) //=; last first.
        * by move: (get_fundef_well_formed_funcs_body Hgfd Hwf) => /andP [].
        by right; exists s3; split.
      - rewrite Hgfd => -[?] _; subst fd' => Hfindinstr' Hisgoto Hpc' HSpc'.
        rewrite /= in Hpc'; exfalso; move: Hfindinstr' Hisgoto HSpc'.
        rewrite /find_instr Hgfd => /(@onthP _ Linstr_align).
        move => /andP [_ /eqP <-]; rewrite /s2 /=.
        by case: (lfd_body fd) => // _ l''''; case: (nth _ _ _) => ? [].
      - rewrite Hgfd => -[?] _; subst fd' => Hfindinstr' Hisgoto Hpc' HSpc'.
        rewrite /= in Hpc'; exfalso; move: HSpc HSpc'.
        by rewrite /c /=; case: (lfd_body fd) => //= _ l''''; case: (nth _ _ _) => ? [].
      - rewrite Hgfd => -[?] _; subst fd' => Hfindinstr' Hisgoto Hpc' HSpc'.
        rewrite /= in Hpc'; exfalso; move: Hfindinstr' Hisgoto HSpc'.
        rewrite /find_instr Hgfd => /(@onthP _ Linstr_align).
        move => /andP [_ /eqP <-]; rewrite /s2 /=.
        by case: (lfd_body fd) => // _ l''''; case: (nth _ _ _) => ? [].
      rewrite Hgfd => _; rewrite /find_instr Hgfd /s2 /= -/s2.
      have ->: onth (lfd_body fd) pc.+1 = Some c.
      - move: HSpc; rewrite /c; elim: (lfd_body fd) {Hpc c s2 s3} pc => [|c lf IHlf] pc //=.
        case: pc => [|pc]; last by apply/IHlf.
        by case: {IHlf} lf.
      rewrite eval_instr_tunnel_lprog_pc //; right; exists s3; split => //.
      by move: HSpc; case: c => {ii Hfindinstr} ii [] //= -[fn' l''].
    move => Hgfd /eqP ? Hfindinstr; subst fn; rewrite Hfindinstr.
    rewrite eval_instr_tunnel_lprog_pc //; case: c Hfindinstr => ii [] //=.
    move => [fn' l''] Hfindinstr /andP [/eqP ? /eqP ?]; subst fn' l''.
    rewrite {1 2 3}/eval_instr /= => Hpc HSpc.
    rewrite Hgfd /=; case: pc Hpc HSpc => [//=|pc] Hpc HSpc; rewrite /= in Hpc.
    rewrite (@nth_label_find_label l (lfd_body fd) pc) //=; last first.
    + by move: (get_fundef_well_formed_funcs_body Hgfd Hwf) => /andP [].
    move => [?]; subst s2; case : s1 Hgfd Hfindinstr  HSpc.
    move => mem vm fn pc1; rewrite /setcpc; set c:= nth _ _ _ => //=.
    set s1:= {| lmem := mem; lvm := vm; lfn := fn; lpc := pc1 |}.
    set s2:= {| lmem := mem; lvm := vm; lfn := fn; lpc := pc.+1 |}.
    move => Hgfd Hfindinstr HSpc.
    rewrite (@nth_label_find_label l' (lfd_body fd) pc.+1) //=; last first.
    + by move: (get_fundef_well_formed_funcs_body Hgfd Hwf) => /andP [].
    set s3:= {| lmem := mem; lvm := vm; lfn := fn; lpc := pc.+2 |}.
    case: find_instr_tunnel_lprog_pcP =>
      [fd' c' l'' l'''|fd' c' pe' l'' l'''|fd' c' l'' l'''|fd' c' pe' l'' l'''|].
    + rewrite Hgfd => -[?] _; subst fd' => Hfindinstr' Hisgoto Hpc' HSpc'.
      rewrite /= in Hpc'.
      have ?: l = l''; last subst l'' => {Hpc'}.
      - by move: Hpc Hpc'; case: (nth _ _ _) => ? [] //= l'''' /eqP ? /eqP ?; subst l'' l''''.
      have ?: l' = l'''; last subst l''' => {HSpc'}.
      - have: is_label l''' c by rewrite /c; move: HSpc' => //=.
        move: HSpc; case: c => [ii' []] //= l''''.
        by move => /eqP ? /eqP ?; subst l''' l''''.
      rewrite eval_instr_tunnel_lprog_pc /eval_instr //= Hgfd /=.
      rewrite (@nth_label_find_label l' (lfd_body fd) pc.+1) //=; last first.
      - by move: (get_fundef_well_formed_funcs_body Hgfd Hwf) => /andP [].
      by right; exists s3; split.
    + rewrite Hgfd => -[?] _; subst fd' => Hfindinstr' Hisgoto Hpc' HSpc'.
      rewrite /= in Hpc'; exfalso; move: Hfindinstr' Hisgoto HSpc'.
      rewrite /find_instr Hgfd => /(@onthP _ Linstr_align).
      move => /andP [_ /eqP <-]; rewrite /s2 /=.
      by case: (lfd_body fd) => // _ l''''; case: (nth _ _ _) => ? [].
    + rewrite Hgfd => -[?] _; subst fd' => Hfindinstr' Hisgoto Hpc' HSpc'.
      rewrite /= in Hpc'; exfalso; move: HSpc HSpc'.
      by rewrite /c /=; case: (lfd_body fd) => //= _ l''''; case: (nth _ _ _) => ? [].
    + rewrite Hgfd => -[?] _; subst fd' => Hfindinstr' Hisgoto Hpc' HSpc'.
      rewrite /= in Hpc'; exfalso; move: Hfindinstr' Hisgoto HSpc'.
      rewrite /find_instr Hgfd => /(@onthP _ Linstr_align).
      move => /andP [_ /eqP <-]; rewrite /s2 /=.
      by case: (lfd_body fd) => // _ l''''; case: (nth _ _ _) => ? [].
    rewrite Hgfd => _; rewrite /find_instr Hgfd /s2 /= -/s2.
    have ->: onth (lfd_body fd) pc.+1 = Some c.
    + move: HSpc; rewrite /c; elim: (lfd_body fd) {Hpc c s2 s3} pc => [|c lf IHlf] pc //=.
      case: pc => [|pc]; last by apply/IHlf.
      by case: {IHlf} lf.
    rewrite eval_instr_tunnel_lprog_pc //; right; exists s3; split => //.
    by move: HSpc; case: c => {ii Hfindinstr} ii [] //= -[fn' l''].
  Qed.

  Lemma lsem1_tunnel_lprog_pc p s1 s2 fn pc :
    well_formed_lprog p ->
    lsem1 p s1 s2 ->
    exists s3, lsem1 (tunnel_lprog_pc p fn pc) s1 s3 /\
           lsem (tunnel_lprog_pc p fn pc) s2 s3.
  Proof.
    move => Hwf Hlsem1.
    case: (lsem11_tunnel_lprog_pc fn pc Hwf Hlsem1).
    + by exists s2; split => //; apply Relation_Operators.rt_refl.
    move => [s3] {Hlsem1} [Hlsem1 Hlsem1'].
    by exists s3; split => //; apply/Relation_Operators.rt_step.
  Qed.

  Lemma lsem_tunnel_lprog_pc p s1 s2 fn pc :
    well_formed_lprog p ->
    lsem p s1 s2 ->
    exists s3, lsem (tunnel_lprog_pc p fn pc) s1 s3 /\
           lsem (tunnel_lprog_pc p fn pc) s2 s3.
  Proof.
    move => Hwf Hlsem; pattern s1, s2; set Q:= (fun _ => _); move: Hlsem; apply: lsem_ind_r.
    + by rewrite /Q => s; exists s; split; apply Relation_Operators.rt_refl.
    rewrite /Q => {Q} s3 s4 s5 Hlsem34 Hlsem1 [s6] [Hlsem36 Hlsem46].
    case: (lsem1_tunnel_lprog_pc fn pc Hwf Hlsem1) => s7 {Hlsem1} [Hlsem1 Hlsem57].
    case: (lsem_disj1 Hlsem1 Hlsem46) => [?| Hlsem76].
    + subst s6; exists s7; split => //.
      apply/lsem_trans; first by apply/Hlsem36.
      by apply Relation_Operators.rt_step.
    exists s6; split => //; apply/lsem_trans; last by apply/Hlsem76.
    by apply/Hlsem57.
  Qed.

  (*TODO: either lsem tp -> lsem p or do proof directly.*)

  Lemma lsem_tunnel_lprog p s1 s2 :
    lsem p s1 s2 ->
    exists s3, lsem p s2 s3 /\ lsem (tunnel_lprog p) s1 s3.
  Proof.
  Qed.

  Theorem lsem_tunnel_program p tp s1 s2 :
    tunnel_program p = ok tp ->
    lsem p s1 s2 ->
    exists s3, lsem p s2 s3 /\ lsem tp s1 s3.
  Proof.
    rewrite /tunnel_program; case: ifP => // wfp [<-].
    elim: funnames => [|hfns tfns IHfns /=]; first by exists s2; split => //; apply: Relation_Operators.rt_refl.
    move => Hlsem12; case: (IHfns Hlsem12) => s3 [Hlsem23 Hplsem13].
    case: (lsem_tunneling hfns (well_formed_partial_tunnel_program _ wfp) Hplsem13) => s4 [Hplsem34 Hpplsem14].
    exists s4; split => //; apply: (lsem_trans Hlsem23).
    by apply: (partial_tunnel_program_lsem wfp Hplsem34).
  Qed.

  Corollary lsem_run_tunnel_program p tp s1 s2 :
    tunnel_program p = ok tp →
    lsem p s1 s2 →
    lsem_final p s2 →
    lsem tp s1 s2 ∧ lsem_final tp s2.
  Proof.
    move => Htp Hlsem12 Hfinal.
    case: (lsem_tunnel_program Htp Hlsem12) => s3 [Hlsem23 Hlsem13].
    have ?:= (lsem_final_stutter Hlsem23 Hfinal); subst s3.
    split => //; case: Hfinal => fd Hgfd Heq.
    exists (lfundef_tunnel_partial (lfn s2) fd (lfd_body fd) (lfd_body fd)) => //.
    + by rewrite (get_fundef_tunnel_program Htp Hgfd).
    by rewrite /lfundef_tunnel_partial lfd_body_setfb -tunnel_partial_size.
  Qed.

End TunnelingProof.

fail.


Section TunnelingCompilerProof.

  Lemma all_if (T : Type) (a b c : pred T) (s : seq T) :
    all a (filter c s) ->
    all b (filter (negb \o c) s) ->
    all (fun x => if c x then a x else b x) s.
  Proof.
    elim: s => //= hs ts IHs.
    by case: ifP => [Hchs /= /andP [Hahs Hats] Hbts|Hchs /= Hats /andP [Hbhs Hbts]];
    apply/andP; split => //; apply: IHs.
  Qed.

  Lemma all_filtered (T : Type) (a b : pred T) (s : seq T) :
    all a s -> all a (filter b s).
  Proof.
    by elim: s => //= hs ts IHs; case: ifP => /= _ /andP; case => Hahs Hths; first (apply/andP; split => //); apply: IHs.
  Qed.

  Lemma all_eq_filter (T : Type) (a b c : pred T) (s : seq T) :
    (forall x, c x -> a x = b x) ->
    all a (filter c s) ->
    all b (filter c s).
  Proof.
    move => Hcab; elim: s => //= hs ts IHs; case: ifP => //= Hchs /andP [Hahs Hats].
    by apply/andP; split; first rewrite -Hcab; last apply IHs.
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

  Lemma map_filter (T1 T2 : Type) (a : pred T2) (b : T1 -> T2) (s : seq T1) :
    filter a (map b s) = map b (filter (fun x => a (b x)) s).
  Proof.
    by elim: s => //= hs ts ->; case: ifP.
  Qed.

  Lemma labels_of_body_tunnel_partial fn uf lc :
    labels_of_body lc =
    labels_of_body (tunnel_partial fn uf lc).
  Proof.
    rewrite /labels_of_body; elim: lc => //= -[ii []] //=; first by move => ? ? ->.
    by move => [fn' l'] tlc /=; case: ifP => //; case: ifP.
  Qed.

  Lemma all_onthP (T : Type)  (a : pred T) (s : seq T) :
    reflect (forall i x , oseq.onth s i = Some x -> a x) (all a s).
  Proof.
    apply: (iffP idP).
    + move => /all_nthP Hnth i x.
      have:= Hnth x i.
      elim: s i {Hnth} => //= hs ts IHs [/= Ha [<-]|i /= Ha]; first by apply: Ha.
      by apply: IHs => Hisizets; apply: Ha.
    elim: s => //= hs ts IHs Honth.
    apply/andP; split; first by apply: (Honth 0).
    by apply: IHs => i x ?; apply: (Honth (i.+1)).
  Qed.

  Lemma assoc_onth (T : eqType) (U : Type) (s : seq (T * U)) (x : T) (y : U) :
    assoc s x = Some y ->
    exists i, oseq.onth s i = Some (x,y).
  Proof.
    elim: s => //= -[hsx hsy] ts IHs.
    case: ifP => [/eqP ? [?]|_ Hassoc]; first by subst hsx hsy; exists 0.
    by case: (IHs Hassoc) => i Honth; exists i.+1.
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

  Lemma labels_of_body_tunnel_plan_partial l fn pfb fb :
    well_formed_body fn fb ->
    prefix pfb fb ->
    Llabel l \in labels_of_body fb ->
    Llabel (LUF.find (tunnel_plan fn LUF.empty pfb) l) \in labels_of_body fb.
  Proof.
    rewrite /tunnel_plan => Hwfb.
    elim/last_ind: pfb l => //=.
    move => pfb c IHfb l Hprefix Hlabelin.
    have Hprefix':= (prefix_trans (@prefix_rcons _ pfb c) Hprefix).
    have:= (IHfb _ Hprefix' Hlabelin) => {Hlabelin}.
    rewrite pairfoldl_rcons; move: IHfb.
    set uf:= pairfoldl _ _ _ _ => IHfb.
    case: last => ii []; case: c Hprefix => li_ii [] //=.
    + move => l' Hprefix l''; rewrite LUF.find_union.
      case: ifP => // _ _; apply: IHfb => //.
      apply: (@mem_prefix _ (labels_of_body (rcons pfb {| li_ii := li_ii; li_i := Llabel l' |}))).
      - by apply/prefix_filter/prefix_map.
      by rewrite /labels_of_body map_rcons filter_rcons /= mem_rcons mem_head.
    move => [fn' l'] Hprefix l''.
    case: ifP => // /eqP ?; subst fn'; rewrite LUF.find_union.
    case: ifP => // _ _; apply: IHfb.
    move: Hwfb => /andP [_ Hall].
    have:= (@prefix_all _ (goto_targets (rcons pfb {| li_ii := ii; li_i := Lgoto (fn, l') |})) _ _ _ Hall) => {Hall}.
    rewrite /goto_targets {2}map_rcons filter_rcons /= all_rcons => Hall.
    have:= andP (Hall _) => {Hall} -[] //.
    + apply: prefix_filter.
      move: (prefix_map li_i Hprefix).
      by rewrite !map_rcons.
    move: Hwfb => /andP [_] /allP /(_ (Lgoto (fn, l'))).
    rewrite eq_refl /= => Himp; apply Himp.
    have:= (@mem_prefix _ _ _ Hprefix {| li_ii := li_ii; li_i := Lgoto (fn, l') |} _).
    rewrite -cats1 mem_cat mem_seq1 eq_refl orbT => /(_ isT) => Hin.
    rewrite /goto_targets mem_filter /=.
    by apply/mapP; exists {| li_ii := li_ii; li_i := Lgoto (fn, l') |}.
  Qed.

  Lemma labels_of_body_tunnel_plan l fn fb :
    well_formed_body fn fb ->
    Llabel l \in labels_of_body fb ->
    Llabel (LUF.find (tunnel_plan fn LUF.empty fb) l) \in labels_of_body fb.
  Proof. by move => Hwfb; move: (prefix_refl fb); apply labels_of_body_tunnel_plan_partial. Qed.

  Lemma goto_targets_tunnel_partial fn fb l:
    well_formed_body fn fb ->
    Lgoto (fn, l) \in goto_targets (tunnel_partial fn (tunnel_plan fn LUF.empty fb) fb) ->
    Llabel l \in labels_of_body fb.
  Proof.
    rewrite /tunnel_plan => Hwfb.
    pattern fb, fb at 2 3.
    apply: prefixW => //=.
    + rewrite /tunnel_partial (@eq_map _ _ _ idfun); last first.
      - by move => ?; rewrite tunnel_bore_empty.
      rewrite map_id.
      move: Hwfb; rewrite /well_formed_body => /andP [_ /allP] Hall Hin.
      by move: (Hall _ Hin); rewrite eq_refl.
    move => c pfb Hprefix; rewrite pairfoldl_rcons.
    set uf:= pairfoldl _ _ _ _ => IHfb.
    case Hlast: last => [ii [ | |l'| | | | ]]; case: c Hprefix => ii' [] //=; auto.
    + move => l'' Hprefix; rewrite mem_filter => /andP [_].
      case/mapP => -[ii'' []] // [fn''' l'''] /= Hin'' [? ?]; subst fn''' l'''; move: Hin''.
      case/mapP => -[ii''' []] // [fn''' l'''] /= Hin''' [?]; subst ii'''.
      case: ifP => [/eqP ? [_]|Hneq -[?]]; last first.
      - by subst; move: Hneq; rewrite eq_refl.
      subst fn'''; rewrite LUF.find_union.
      move: IHfb Hprefix Hlast; rewrite /uf; clear uf; case: (lastP pfb) => // {pfb} pfb [iii ll].
      set uf:= pairfoldl _ _ _ _ => IHfb Hprefix; rewrite last_rcons => -[? ?]; subst iii ll.
      rewrite (find_plan_partial Hwfb (prefix_trans (prefix_rcons _ _) Hprefix)).
      case: ifP => [/eqP Heqfind|/negP Hneqfind] ?; subst l; last first.
      - apply/IHfb; rewrite mem_filter /=; apply/mapP.
        exists {| li_ii := ii''; li_i := Lgoto (fn, LUF.find uf l''') |} => //=.
        by apply/mapP; exists {| li_ii := ii''; li_i := Lgoto (fn, l''') |} => //=; rewrite eqxx.
      have Hprefix':= (prefix_rcons (rcons pfb {| li_ii := ii; li_i := Llabel l' |}) {| li_ii := ii'; li_i := Llabel l'' |}).
      have Hprefix'':= (prefix_trans Hprefix' Hprefix).
      move: (@labels_of_body_tunnel_plan_partial l'' _ _ _ Hwfb Hprefix'').
      rewrite /tunnel_plan -/uf => Himp; apply Himp; rewrite mem_filter /=.
      apply/mapP; exists {| li_ii := ii'; li_i := Llabel (l'') |} => //=.
      by apply/(mem_prefix Hprefix); rewrite -cats1 mem_cat mem_seq1 eq_refl orbT.
    move => [fn'' l''] Hprefix; case: ifP; last by auto.
    move => /eqP ?; subst fn''; rewrite mem_filter => /andP [_].
    case/mapP => -[ii'' []] // [fn''' l'''] /= Hin'' [? ?]; subst fn''' l'''; move: Hin''.
    case/mapP => -[ii''' []] // [fn''' l'''] /= Hin''' [?]; subst ii'''.
    case: ifP => [/eqP ? [_]|Hneq -[?]]; last first.
    + by subst; move: Hneq; rewrite eq_refl.
    subst fn'''; rewrite LUF.find_union.
    move: IHfb Hprefix Hlast; rewrite /uf; clear uf; case: (lastP pfb) => // {pfb} pfb [iii ll].
    set uf:= pairfoldl _ _ _ _ => IHfb Hprefix; rewrite last_rcons => -[? ?]; subst iii ll.
    rewrite (find_plan_partial Hwfb (prefix_trans (prefix_rcons _ _) Hprefix)).
    case: ifP => [/eqP Heqfind|/negP Hneqfind] ?; subst l; last first.
    + apply/IHfb; rewrite mem_filter /=; apply/mapP.
      exists {| li_ii := ii''; li_i := Lgoto (fn, LUF.find uf l''') |} => //=.
      by apply/mapP; exists {| li_ii := ii''; li_i := Lgoto (fn, l''') |} => //=; rewrite eqxx.
    apply/IHfb; rewrite mem_filter /=; apply/mapP.
    exists {| li_ii := ii'; li_i := Lgoto (fn, LUF.find uf l'') |} => //=.
    apply/mapP; exists {| li_ii := ii'; li_i := Lgoto (fn, l'') |} => //=; last by rewrite eqxx.
    move: Hprefix => /prefixP [sfb] ->; rewrite mem_cat mem_rcons in_cons.
    by apply/orP; left; apply/orP; left; apply/eqP.
  Qed.

  Lemma onthP {T : eqType} (s : seq T) (x : T) :
    reflect (exists2 i , i < size s & oseq.onth s i = Some x) (x \in s).
  Proof.
    apply: (iffP (nthP x)); case => i Hsize Hnth; exists i => //.
    + by rewrite -Hnth; apply: oseq.onth_nth_size.
    by apply/eqP; rewrite -oseq.onth_sizeP // Hnth.
  Qed.

  Lemma well_formed_lprog_tunnel fn p :
    well_formed_lprog p ->
    well_formed_lprog (lprog_tunnel fn p).
  Proof.
    rewrite /well_formed_lprog /lprog_tunnel; case: p => /= rip rsp globs funcs.
    move => /andP [Huniq Hall]; apply/andP; split.
    + move: Huniq {Hall}; case Hgfd: (get_fundef _ _) => [fd|] //=.
      by rewrite -map_comp (@eq_map _ _ _ fst).
    move: Hall; move => /all_onthP Hwfb; apply/all_onthP => i [fn' fd'] /=.
    case Hgfd: get_fundef => [fd|] /= {rip globs}; last by apply: Hwfb.
    rewrite onth_map; case Honth: oseq.onth => [[fn'' fd'']|] //= [?]; subst fn''.
    case: ifP => [/eqP ? ?|_ ?]; last by subst fd''; apply: (Hwfb _ _ Honth).
    subst fn' fd'; rewrite /lfundef_tunnel_partial /= => {i fd'' Honth}.
    case: (assoc_onth Hgfd) => i Honth; have:= (Hwfb _ _ Honth) => /= {Hwfb Hgfd Honth} Hwf.
    move: (Hwf); move => /andP [Huniql Hall]; move: (Hall) => /all_onthP Hlocalgotos.
    apply/andP; split; rewrite -labels_of_body_tunnel_partial //.
    apply/all_onthP => {i} i x /onth_goto_targets [j] [ii_x] [[fn' l']] [Honth ?]; subst x.
    move: Honth => /oseq.onthP /andP Hnth; have:= (Hnth Linstr_align) => {Hnth} -[Hsize /eqP Hnth].
    have:= (mem_nth Linstr_align Hsize); move: Hnth => -> Hin {Hsize}.
    have:= (map_f li_i Hin) => {Hin} /= Hin.
    have: Lgoto (fn', l') \in goto_targets (tunnel_partial fn (tunnel_plan fn LUF.empty (lfd_body fd)) (lfd_body fd)).
    + by rewrite /goto_targets mem_filter.
    move => {Hin} Hin; move: (Hin); rewrite /goto_targets mem_filter => /andP [_].
    case/mapP => -[ii'' []] // [fn''' l'''] /= Hin'' [? ?]; subst fn''' l'''; move: Hin''.
    case/mapP => -[ii''' []] // [fn''' l'''] /= Hin''' [?]; subst ii'''.
    case: ifP => [/eqP ? [? ?]|Hneq [? ?]].
    + subst fn''' fn'; apply/andP; split; first by apply/eqP.
      by move/(goto_targets_tunnel_partial Hwf): Hin.
    subst fn''' l'''; rewrite Hneq /=;  move: Hall => /allP /(_ (Lgoto (fn', l'))).
    rewrite /goto_targets mem_filter Hneq /= => -> //.
    by apply/mapP; exists {| li_ii := ii''; li_i := Lgoto (fn', l') |}.
  Qed.

  Lemma well_formed_partial_tunnel_program fns p :
    well_formed_lprog p ->
    well_formed_lprog (foldr lprog_tunnel p fns).
  Proof.
    by elim: fns => //= hfns tfns IHfns wfp; apply: well_formed_lprog_tunnel; apply: IHfns.
  Qed.

  Lemma partial_tunnel_program_lsem fns p s1 s2 :
    well_formed_lprog p ->
    lsem (foldr lprog_tunnel p fns) s1 s2 ->
    lsem p s1 s2.
  Proof.
    elim: fns => //= hfns tfns IHfns wfp Hpplsem12; apply: (IHfns wfp).
    apply: (tunneling_lsem (well_formed_partial_tunnel_program _ wfp)).
    by apply: Hpplsem12.
  Qed.

  Lemma tunnel_partial_size fn uf l :
    size l = size (tunnel_partial fn uf l).
  Proof. by rewrite /tunnel_partial size_map. Qed.

  Lemma lprog_tunnel_size fn p tp :
    well_formed_lprog p ->
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

  Lemma get_fundef_tunnel_program p tp fn fd :
    tunnel_program p = ok tp →
    get_fundef (lp_funcs p) fn = Some fd →
    get_fundef (lp_funcs tp) fn = Some (lfundef_tunnel_partial fn fd fd.(lfd_body) fd.(lfd_body)).
  Proof.
    rewrite /tunnel_program; case: ifP => // Hwfp /ok_inj <-{tp} Hgfd.
    rewrite (get_fundef_foldr_lprog_tunnel _ Hgfd).
    + by rewrite ifT //; apply/in_map; exists (fn, fd) => //=; apply get_fundef_in'.
    by move: Hwfp; rewrite /well_formed_lprog /funnames => /andP [].
  Qed.

  Theorem lsem_tunnel_program p tp s1 s2 :
    tunnel_program p = ok tp ->
    lsem p s1 s2 ->
    exists s3, lsem p s2 s3 /\ lsem tp s1 s3.
  Proof.
    rewrite /tunnel_program; case: ifP => // wfp [<-].
    elim: funnames => [|hfns tfns IHfns /=]; first by exists s2; split => //; apply: Relation_Operators.rt_refl.
    move => Hlsem12; case: (IHfns Hlsem12) => s3 [Hlsem23 Hplsem13].
    case: (lsem_tunneling hfns (well_formed_partial_tunnel_program _ wfp) Hplsem13) => s4 [Hplsem34 Hpplsem14].
    exists s4; split => //; apply: (lsem_trans Hlsem23).
    by apply: (partial_tunnel_program_lsem wfp Hplsem34).
  Qed.

  Corollary lsem_run_tunnel_program p tp s1 s2 :
    tunnel_program p = ok tp →
    lsem p s1 s2 →
    lsem_final p s2 →
    lsem tp s1 s2 ∧ lsem_final tp s2.
  Proof.
    move => Htp Hlsem12 Hfinal.
    case: (lsem_tunnel_program Htp Hlsem12) => s3 [Hlsem23 Hlsem13].
    have ?:= (lsem_final_stutter Hlsem23 Hfinal); subst s3.
    split => //; case: Hfinal => fd Hgfd Heq.
    exists (lfundef_tunnel_partial (lfn s2) fd (lfd_body fd) (lfd_body fd)) => //.
    + by rewrite (get_fundef_tunnel_program Htp Hgfd).
    by rewrite /lfundef_tunnel_partial lfd_body_setfb -tunnel_partial_size.
  Qed.

End TunnelingCompilerProof.
