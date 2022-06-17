(* ** Imports and settings *)
From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp.word Require Import ssrZ.
Require Import psem array_expansion compiler_util ZArith.
Import Utf8.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope vmap.
Local Open Scope seq_scope.

Definition wf_t (m : t) :=
  forall x ai, Mvar.get m.(sarrs) x = Some ai ->
    [/\ ~ Sv.mem x m.(svars), is_sarr (vtype x) &
    forall i xi, Mi.get ai.(ai_elems) i = Some xi ->
      [/\ ~ Sv.mem xi m.(svars), xi.(vtype) == sword ai.(ai_ty),
      (0 <= i < ai_len ai)%Z &
      forall x' ai' i' xi',
        Mvar.get m.(sarrs) x' = Some ai' ->
        Mi.get ai'.(ai_elems) i' = Some xi' ->
        x <> x' \/ i <> i' -> xi != xi']].

Definition eval_array ws v i :=
  if v is Varr _ t
  then ok (rdflt undef_w (rmap (@Vword _) (WArray.get AAscale ws t i)))
  else type_error.

Lemma eval_arrayP ws v i w : eval_array ws v i = ok w ->
  is_sarr (type_of_val v) /\ (w = undef_w \/ exists ww, w = @Vword ws ww).
Proof.
  by case: v => //= > [<-]; split=> //; case: WArray.get; auto; right; eexists.
Qed.

Definition eq_alloc_vm (m : t) vm1 vm2 :=
  vm1 =[m.(svars)] vm2 /\
  forall x ai i xi,
    Mvar.get m.(sarrs) x = Some ai ->
    Mi.get ai.(ai_elems) i = Some xi ->
    eval_array ai.(ai_ty) vm1.[x] i = ok vm2.[xi].

Definition eq_alloc {_: PointerData} {syscall_state : Type} {sc_sem : syscall_sem syscall_state} (m : t) (s1 s2 : estate) :=
  [/\ eq_alloc_vm m s1.(evm) s2.(evm),
    s1.(escs) = s2.(escs) & s1.(emem) = s2.(emem)].

Definition expand_v expd v :=
  match expd with
  | Some (ws, len) => mapM (eval_array ws v) (ziota 0 len)
  | None => ok [:: v]
  end.

Lemma expand_vP n a ws l :
  mapM (eval_array ws (@Varr n a)) l =
    ok (map (fun i => rdflt undef_w (rmap (@Vword _) (WArray.get AAscale ws a i)))
    l).
Proof. by elim: l => // *; simpl map; rewrite -mapM_cons. Qed.

Definition expand_vs := mapM2 ErrType expand_v.

Section Section.

Context {pd: PointerData} {syscall_state : Type} {sc_sem : syscall_sem syscall_state}.
Context `{asmop:asmOp}.
Variable (fi : funname -> ufundef -> expand_info).
Variable (entries : seq funname).
Variable p1 p2:uprog.

Local Notation gd := (p_globs p1).

Section Expr.

Context (m : t) (valid : wf_t m).

Lemma check_var_get s1 s2 x :
  Sv.mem x (svars m) -> eq_alloc m s1 s2 -> (evm s1).[x] = (evm s2).[x].
Proof. by move=> h [][/(_ _ (Sv_memP _ _ h))->]. Qed.

Lemma check_gvar_get s1 s2 x :
  check_gvar m x ->
  eq_alloc m s1 s2 ->
  get_gvar gd s1.(evm) x = get_gvar gd s2.(evm) x.
Proof.
  by rewrite /get_gvar /check_gvar; case: is_lvar => // /check_var_get h/h ->.
Qed.

Lemma eq_alloc_mem s1 s2 : eq_alloc m s1 s2 -> emem s1 = emem s2.
Proof. by case. Qed.

Lemma eq_alloc_scs s1 s2 : eq_alloc m s1 s2 -> escs s1 = escs s2.
Proof. by case. Qed.

Lemma expand_esP_aux (s1 s2 : estate) es1 es2 :
  eq_alloc m s1 s2 ->
  expand_es m es1 = ok es2 ->
  (∀ e, List.In e es1 ->
   ∀ e2, expand_e m e = ok e2 ->
   ∀ v, sem_pexpr gd s1 e = ok v -> sem_pexpr gd s2 e2 = ok v) ->
  forall vs, sem_pexprs gd s1 es1 = ok vs -> sem_pexprs gd s2 es2 = ok vs.
Proof.
  move=> h; rewrite /sem_pexprs /expand_es.
  elim: es1 es2 => [ | e1 es1 hrec] es' /=; first by move=> [<-] _ ? [<-].
  t_xrbindP=> e2 he1 es2 /hrec hes1 <- he ?? se1 ? /hes1 hes2 <- /=.
  rewrite (he _ _ _ he1 _ se1); last by left.
  by rewrite /= hes2 // => e he'; apply: he; right.
Qed.

Lemma expand_eP (s1 s2: estate) :
  eq_alloc m s1 s2 ->
  forall e1 e2, expand_e m e1 = ok e2 -> 
  forall v, sem_pexpr gd s1 e1 = ok v ->
            sem_pexpr gd s2 e2 = ok v.
Proof.
  move=> h; elim=> /=.
  + by move=> z _ [<-] _ [<-].
  + by move=> b _ [<-] _ [<-].
  + by move=> n _ [<-] _ [<-].
  + by move=> x e2; t_xrbindP=> /check_gvar_get -/(_ _ _ h) -> <-.
  + move=> aa sz x e hrec e2.
    case: ifP => [/check_gvar_get /(_ h)|/norP/proj1/negbNE hlv].
    + t_xrbindP=> -> e1 /hrec he <- v /=.
      apply: on_arr_gvarP => n t hty ->.
      by t_xrbindP=> i vi /he -> /= -> /= w -> <-.
    case hgetx : Mvar.get => //; case: is_constP => // i.
    t_xrbindP=> /eqP <- /eqP ->; case hgeti : Mi.get => [xi|//] -[<-] v.
    apply: on_arr_gvarP => n t /eqP hty.
    rewrite /get_gvar hlv{hlv} => -[hx1] /=.
    t_xrbindP=> ? hw <-; case: h => -[_ /(_ _ _ _ _ hgetx hgeti)].
    by rewrite hx1 /= hw /get_gvar => -[<-] //.
  + move=> aa sz len x e hrec e2.
    t_xrbindP=> he e1 /hrec hrec1 <- /=.
    rewrite (check_gvar_get he h) => v.
    apply: on_arr_gvarP => n t hty -> /=.
    by t_xrbindP=> i vi /hrec1 -> /= -> t' /= -> <-.
  + move=> sz x e hrec e2; t_xrbindP=> hin e1 /hrec hrec1 <- >.
    rewrite (check_var_get hin h) => /= -> > /hrec1 -> /= -> ?.
    by rewrite (eq_alloc_mem h) => /= -> <-.
  + by move=> o e1 hrec e2; t_xrbindP=> e1' /hrec he1 <- /= ?? /he1 -> /= ->.
  + move=> o e1 hrec1 e2 hrec2 e'.
    by t_xrbindP=> e1' /hrec1 he1 e2' /hrec2 he2 <- /= ?? /he1 -> /= ? /he2 ->.
  + move=> op es hrec e'; t_xrbindP=> es' hes' <- ?? h1 h2 /=.
    by have := expand_esP_aux h hes' hrec h1; rewrite /sem_pexprs => ->.
  move=> t b hrecb e1 hrec1 e2 hrec2 e'.
  t_xrbindP=> b' /hrecb hb e1' /hrec1 he1 e2'  /hrec2 he2 <- /=.
  by move=> ??? /hb -> /= -> /= ?? /he1 -> /= -> ?? /he2 -> /= -> /= <-.
Qed.

Lemma expand_esP (s1 s2 : estate) :
  eq_alloc m s1 s2 ->
  forall es1 es2, expand_es m es1 = ok es2 -> 
  forall vs, sem_pexprs gd s1 es1 = ok vs ->
             sem_pexprs gd s2 es2 = ok vs.
Proof.
  move=> h es1 es2 hex; apply (expand_esP_aux h hex) => e _; exact: expand_eP.
Qed.

Lemma expand_paramsP (s1 s2 : estate) e expdin :
  eq_alloc m s1 s2 ->
  forall es1 es2 vs, mapM2 e (expand_param m) expdin es1 = ok es2 ->
    sem_pexprs gd s1 es1 = ok vs ->
    exists2 vs', expand_vs expdin vs = ok vs' &
      sem_pexprs gd s2 (flatten es2) = ok (flatten vs').
Proof.
  move=> h ?? + H; elim: {H}(mapM2_Forall3 H) => [?[<-]|]; first by eexists.
  case=> [[??] [] g c|] //= >; last by t_xrbindP=> ? /(expand_eP h){h}h <- ?
    hrec > /h{h} /= -> ? /hrec{hrec}[? + ->] <- /= => ->; eexists.
  case: Option.oappP => // ? hga; case: ifP => //
    /and3P[/eqP? /eqP? hloc] + _; subst; rewrite /get_gvar hloc{hloc} /=.
  t_xrbindP=> + hrec ? z0 /hrec{hrec}+ <- => + [? ->].
  case: h (valid hga) => -[_ /(_ _ _ _ _ hga){hga}hgai _ _] [_ /is_sarrP[? htg hmi]].
  have /(typerel_undef_compat vm_subcomp) /compat_typeEl := Vmap.get_varP (evm s1) (gv g).
  rewrite htg{htg} => /type_of_valI[? /[dup]hg->].
  rewrite /sem_pexprs mapM_cat -/(sem_pexprs _ _ (flatten _)) => + -> /=.
  elim/ziota_ind: (ziota _ _) c; first by move=> ? [] <-; eexists.
  simpl=> > _ hrec; t_xrbindP=> >; case: Option.oappP => // a
    /[dup]/hmi{hmi}[_ /eqP hta _ _] /hgai{hgai}.
  rewrite hg{hg} /=; t_xrbindP=> -> ?? /hrec{hrec}[?]; subst.
  t_xrbindP=> ? -> ??; subst=> + /= /cat_inj_tail ??; subst=> /= ->.
  by eexists.
Qed.

Lemma eq_alloc_write_var s1 s2 (x: var_i) v s1':
   eq_alloc m s1 s2 ->
   Sv.mem x (svars m) ->
   write_var x v s1 = ok s1' ->
   exists2 s2' : estate, write_var x v s2 = ok s2' & eq_alloc m s1' s2'.
Proof.
  move=> h; case: (h) => -[heq ha] hscs hmem /=.
  move=> /Sv_memP hin hw.
  have [vm2 heq2 hw2]:= write_var_eq_on hw heq.
  exists (with_vm s1' vm2).
  + by have -> : s2 = with_vm s1 (evm s2) by case: (s2) hscs hmem => ??? /= <- <-.
  split=> //; split; first by apply: eq_onI heq2; SvD.fsetdec.
  move=> x' ai i xi hai hxi.
  have [/negP /Sv_memP hnx' _ /(_ _ _ hxi) [] /negP /Sv_memP hnxi _ _]:= valid hai.
  rewrite -(vrvP_var hw); last by SvD.fsetdec.
  rewrite -(vrvP_var hw2) => [_|]; last by SvD.fsetdec.
  exact: ha.
Qed.

Lemma expand_lvP (s1 s2 : estate) :
  eq_alloc m s1 s2 ->
  forall x1 x2, expand_lv m x1 = ok x2 ->
  forall v s1',
    write_lval gd x1 v s1 = ok s1' ->
    exists2 s2', write_lval gd x2 v s2 = ok s2' & eq_alloc m s1' s2'.
Proof.
  move=> h; case: (h) => -[heq ha] hscs hmem [] /=.
  + by move=> ii ty _ [<-] /= ??; case: ifP => // _ [<-]; eexists.
  + by move=> x; t_xrbindP=> _ ? <- /= v1 s1'; apply eq_alloc_write_var.
  + move=> ws x e x2; t_xrbindP=> hin e' he <- v s1' vx.
    rewrite (check_var_get hin h) => /= -> > /(expand_eP h he) -> /= -> ? -> ?.
    by rewrite -hmem => /= -> <-; eexists.
  + move=> aa ws x e x2.
    case: ifPn => [/[dup] hin /Sv_memP/heq->/= | hnin].
    + t_xrbindP=> e' he <- v s1' /=.
      apply: on_arr_varP => n t hty ->.
      t_xrbindP=> i vi /(expand_eP h he) -> /= -> /= ? -> /= t' -> hw /=.
      exact: (eq_alloc_write_var h hin hw).
    case hai: Mvar.get => //; case: is_constP => // i.
    t_xrbindP=> /eqP <- /eqP ->; case hxi: Mi.get => [xi|//] [<-] v s1'.
    apply: on_arr_varP => n t /eqP hty hget /=; rewrite /write_var.
    t_xrbindP=> w /to_wordI[? [wi -> hw]] t' ht' vm' hs <- /=.
    have [_ _ /(_ _ _ hxi)[hnmem /eqP htxi _ hd]] := valid hai.
    case: (@Vmap.set_var_ok _ (evm s2) xi (Vword wi)).
    + rewrite /typerel_undef /Basics.flip /= htxi /truncate_defined_val /= hw.
      exact: subtype_refl.
    move=> ? /[dup] ht2 ->; eexists=> //; split=> //; split=> /=.
    + move=> y H; rewrite (Vmap.set_varP_neq hs);
        last by apply/eqP => ?; subst; apply: (negP hnin (SvD.F.mem_1 H)).
      rewrite (Vmap.set_varP_neq ht2); first exact: heq H.
      by apply/eqP => ?; subst; exact: hnmem (SvD.F.mem_1 H).
    move=> x' ? i' >.
    rewrite (Vmap.set_varP _ hs).
    case: ((v_var x) =P x') => [<- | hxx'].
    + rewrite hai => -[<-].
      rewrite -hty truncate_defined_val_arr /= (WArray.setP _ ht').
      case: (i =P i') => [<- /= | hii' hxi'].
      + by rewrite hxi => -[<-]; rewrite (Vmap.set_varP_eq ht2) htxi
        /truncate_defined_val /= hw; eexists.
      rewrite (Vmap.set_varP_neq ht2).
      + by have := ha _ _ _ _ hai hxi'; rewrite hget.
      by apply: (hd _ _ _ _ hai hxi'); auto.
    move=> hai' hxi'; rewrite (Vmap.set_varP_neq ht2); first by apply: ha hai' hxi'.
    by apply: (hd _ _ _ _ hai' hxi'); auto.
  move=> aa ws len x e x2; t_xrbindP=> hin e' he <- /= v s1'.
  apply: on_arr_varP => n t hty.
  rewrite (check_var_get hin h) => -> /=.
  t_xrbindP=> i vi /(expand_eP h he) -> /= -> /= ? -> /= t' -> /= hw.
  exact: (eq_alloc_write_var h hin hw).
Qed.

Lemma expand_lvsP (s1 s2 : estate) :
  eq_alloc m s1 s2 ->
  forall x1 x2, expand_lvs m x1 = ok x2 ->
  forall vs s1',
    write_lvals gd s1 x1 vs = ok s1' ->
    exists2 s2', write_lvals gd s2 x2 vs = ok s2' & eq_alloc m s1' s2'.
Proof.
  move=> heqa x1 x2 hex; elim: x1 x2 hex s1 s2 heqa => /=.
  + by move=> ? [<-] s1 s2 ? [ | //] ? [<-]; exists s2.
  move=> x1 xs1 hrec ?; t_xrbindP=> x2 hx xs2 hxs <- s1 s2 heqa [//|v vs] s1'.
  t_xrbindP=> s1'' /(expand_lvP heqa hx) [s2'' hw heqa'] /(hrec _ hxs _ _ heqa') [s2' ??].
  by exists s2' => //=; rewrite hw.
Qed.

Lemma expand_returnsP (s1 s2 : estate) e expdout :
  eq_alloc m s1 s2 ->
  forall xs1 xs2, mapM2 e (expand_return m) expdout xs1 = ok xs2 ->
  forall vs vs' s1',
    write_lvals gd s1 xs1 vs = ok s1' ->
    expand_vs expdout vs = ok vs' ->
    exists2 s2', write_lvals gd s2 (flatten xs2) (flatten vs') = ok s2' &
      eq_alloc m s1' s2'.
Proof.
  move=> + > H; elim: {H}(mapM2_Forall3 H) s1 s2.
  + by move=> ??? [] // ?? [<-] [<-]; eexists.
  case=> [[? len] [? t > [<-] _ h > /h{h}hrec [] // |vi c|||]|] //= >; first 2 last.
  + t_xrbindP=> ? /expand_lvP hlv <- ? hrec > /hlv{hlv}hlv [] //.
    t_xrbindP=> > /hlv{hlv}[? + /hrec{hrec}h] /h{h}h?/h{h}[?+?] <- => /= -> /= ->.
    by eexists.
  + t_xrbindP=> ?; case: ifP => // ? [?].
    subst=> /hrec{hrec}h z1 hm ? /h{h}[? hlv ?] <-; eexists; last by eassumption.
    rewrite -(size_ziota 0) -map_const_nseq.
    elim/ziota_ind: (ziota _ _) z1 hm; first by move=> ? [<-].
    by simpl=> > ? hrec; t_xrbindP=> > /eval_arrayP[/is_sarrP[? /type_of_valI[??]]
      [?|[?->]]] ? /[dup]/hrec{hrec}?; subst; rewrite expand_vP => -[?] ?; subst.
  case: Option.oappP => // ai hga; have [hnin htvi hgi] := valid hga.
  case: ifP => // /andP[/eqP? /eqP?] + _.
  subst=> hexc hrec s1 s2 heqa []//; rewrite /write_var.
  t_xrbindP=> va ???? vm1 hsv <- /hrec{hrec}hrec z1 hexv ? /hrec{hrec} hrec ?; subst.
  have [vm2] : exists vm, write_lvals gd s2 c z1 = ok (with_vm s2 vm).
  + elim/ziota_ind: (ziota _ _) s2 {heqa hrec} c z1 hexc hexv => >.
    + by case=> <- [<-]; eexists; erewrite with_vm_same.
    simpl=> ? hrec; case: Option.oappP => //= a.
    by t_xrbindP=> + s2 _ _ > /hrec{hrec}hrec <- v
      /eval_arrayP/proj2[?|[??]] ? /hrec{hrec} + <-;
      rewrite /= /write_var => /hgi{hgi}[? /eqP hta _ _];
      (case: (@Vmap.set_var_ok _ (evm s2) a v); last by move=> ? ->; exact);
      subst; apply: compat_typerel_undef; rewrite hta.
  move: hrec => /[swap]; rewrite /write_lvals => hf1 /(_ (with_vm s2 vm2)) []; last first.
  + by move=> ? hf2; move: (cat_fold2 hf1 hf2) => /= ->; eexists.
  case: heqa => -[heq heva] hcs hm; split=> //; split=> [|vi' ai' i xi] {hcs hm}.
  + move=> ? /Sv_memP hin; rewrite (Vmap.set_varP_neq hsv) ?heq; last first.
    + by apply/eqP => ?; subst; exact: hnin.
    + exact/Sv_memP.
    elim/ziota_ind: (ziota _ _) c z1 s2 {heq heva hexv} hexc hf1
      => [?[]>[<-]//[<-]//|> _ hrec ?[]/=]; t_xrbindP=> >;
      case: Option.oappP => // ? /hgi{hgi}[??? _] [?] ? /hrec{hrec}hrec ?;
      subst=> //=; rewrite /write_var.
    t_xrbindP=> _ > /Vmap.set_varP_neq+ <- /hrec{hrec} <- => -> //=.
    by apply/eqP=> ?; subst; exact: hnin.
  case: (vi' =P vi) => [{heva}->|]; last first.
  + move=> /nesym/[dup]hneq/eqP/(Vmap.set_varP_neq hsv){hsv} /= ->
      /[dup]/heva{heva}h hga' /[dup]/h{h}-> hgi'.
    elim/ziota_ind: (ziota _ _) c z1 hexv hexc vm2 s2 {2}s2{heq} hf1
      => [>[<-][<-]>[->]|> _ hrec] //=.
    t_xrbindP=> > ?? /hrec{hrec}h ??+?/h{h}h?>; subst=> /=.
    case: Option.oappP => // ? /hgi{hgi}[_ _ _
      /(_ _ _ _ _ hga' hgi' (or_introl _ hneq)){hga' hgi' hneq}?] [<-] /=.
    t_xrbindP=> ? + /h{h}<-; rewrite /write_var.
    by t_xrbindP=> ? /Vmap.set_varP_neq <- // <-.
  move: htvi (Vmap.get_varP vm1 vi) (Vmap.set_varP_eq hsv) => /is_sarrP[?->]
    /(typerel_undef_compat vm_subcomp) /compat_typeEl/type_of_valI[t ->] /= he.
  have ? : va = t by case: Result.rdfltP he => // ? /[swap] <- /truncate_defined_valI[].
  rewrite hga => -[?]; subst=> /[dup]/hgi{hgi}[_ /eqP htxi [hp hle] hne] hgi.
  move: c z1 hexc hexv hf1.
  have := ziota_cat 0 hp (Zle_minus_le_0 _ _ (Z.lt_le_incl _ _ hle)).
  rewrite Zplus_minus => /= <-.
  have := ziotaS_cons i (Zle_minus_le_0 _ _ (Zlt_le_succ _ _ hle)).
  rewrite Zminus_succ_l Z.sub_succ_l Z.sub_succ_r Z.succ_pred !mapM_cat => ->.
  rewrite /= hgi /=; t_xrbindP=> > hc1 ? c2 hc2 ??? hz1 ? z2 hz2 ??; subst.
  move: {hc1 hz1} (size_mapM hc1) (size_mapM hz1) => -> /(fold2_cat _) + hf
    => /(_ _ _ _ _ _ _ _ _ hf){hf}[?] _.
  rewrite /= /write_var /=; t_xrbindP=> ? vm /Vmap.set_varP_eq hrw ? hf; subst.
  suff : vm2.[xi] = vm.[xi].
  + rewrite {}hrw htxi => ->; case: WArray.get => //= ?.
    by rewrite /truncate_defined_val /= truncate_word_u.
  elim/ziota_ind: (ziota _ _) c2 z2 vm vm2 {hrw} hc2 hz2 hf
    => [> [<-] [<-] [_ _ <-] | > hbnd hrec] //=; t_xrbindP=> >.
  case: Option.oappP => //? /(hne _ _ _ _ hga){hne}hne [?]?{}/hrec h ??/h{h}h ?.
  subst; rewrite /= /write_var /=; t_xrbindP=> > /Vmap.set_varP_neq hrw ?.
  subst; rewrite with_vm_idem => /h{h} ->; rewrite hrw // neq_sym.
  by apply: hne; Psatz.lia.
Qed.

End Expr.

Hypothesis Hcomp : expand_prog fi entries p1 = ok p2.

Local Notation ev := tt.

Section Step1.

Context step1
  (Hstep1 : map_cfprog_name (expand_fsig fi entries) (p_funcs p1) = ok step1).

Definition fsigs := 
  let (fnames, fexpd) := unzip12 step1 in
  foldr (fun x y => Mfn.set y x.1 x.2) (Mfn.empty _) (zip fnames (unzip2 fexpd)).

Lemma eq_globs : p_globs p2 = gd.
Proof.
  move: Hcomp; rewrite /expand_prog; t_xrbindP=> z ?.
  rewrite 2!(surjective_pairing (unzip12 _)).
  by t_xrbindP=> ?? <-.
Qed.

Lemma all_checked fn fd1 :
  get_fundef (p_funcs p1) fn = Some fd1 ->
  exists fd2 fd2' m g, [/\ get_fundef (p_funcs p2) fn = Some fd2,
    Mfn.get fsigs fn = Some g,
    expand_fsig fi entries fn fd1 = ok (fd2', m, g) &
    expand_fbody fsigs fn (fd2', m) = ok fd2].
Proof.
  move=> /(get_map_cfprog_name_gen Hstep1)[[fd2' fex'] hex' hfd'].
  move: Hcomp; rewrite /expand_prog Hstep1 /= 2!(surjective_pairing (unzip12 _)).
  t_xrbindP=> pf2 hpf2 ?; subst.
  have hfd2' : get_fundef (zip (unzip12 step1).1 (unzip12 (unzip12 step1).2).1) fn = Some fd2'.
  + elim: step1 hfd' => //= a > hrec.
    rewrite (surjective_pairing a) (surjective_pairing a.2).
    by case: ifP => /= [-> [<-]|-> /hrec].
  have [[>]] := get_map_cfprog_name_gen hpf2 hfd2'.
  case: fd2' hex' hfd' hfd2' => > ? hfd' ? heb ?.
  eexists _, _, _, _; split; eauto.
  + rewrite /fsigs (surjective_pairing (unzip12 _)).
    elim: step1 hfd' => //= -[] > hrec /=.
    by case: ifP => [+[?]|+/hrec]; rewrite eq_sym Mfn.setP => ->; subst.
  move: heb.
  by rewrite /expand_fbody /fsigs {3}(surjective_pairing (unzip12 _)) -unzip122.
Qed.

Let Pi_r s1 (i1:instr_r) s2:=
  forall ii m ii' i2 s1',
    wf_t m -> eq_alloc m s1 s1' ->
    expand_i fsigs m (MkI ii i1) = ok (MkI ii' i2) ->
  exists2 s2', eq_alloc m s2 s2' & sem_i p2 ev s1' i2 s2'.

Let Pi s1 (i1:instr) s2:=
  forall m i2 s1',
    wf_t m -> eq_alloc m s1 s1' ->
    expand_i fsigs m i1 = ok i2 ->
  exists2 s2', eq_alloc m s2 s2' & sem_I p2 ev s1' i2 s2'.

Let Pc s1 (c1:cmd) s2 :=
  forall m c2 s1',
    wf_t m -> eq_alloc m s1 s1' ->
    mapM (expand_i fsigs m) c1 = ok c2 ->
  exists2 s2', eq_alloc m s2 s2' & sem p2 ev s1' c2 s2'.

Let Pfor (i1:var_i) vs s1 c1 s2 :=
  forall m c2 s1',
    wf_t m -> eq_alloc m s1 s1' -> Sv.mem i1 m.(svars) ->
    mapM (expand_i fsigs m) c1 = ok c2 ->
  exists2 s2', eq_alloc m s2 s2' & sem_for p2 ev i1 vs s1' c2 s2'.

Let Pfun scs m fn vargs scs' m' vres :=
  forall expdin expdout, Mfn.get fsigs fn = Some (expdin, expdout) ->
  forall vargs', expand_vs expdin vargs = ok vargs' ->
  exists2 vres', expand_vs expdout vres = ok vres' &
    sem_call p2 ev scs m fn (flatten vargs') scs' m' (flatten vres').

Local Lemma Hskip : sem_Ind_nil Pc.
Proof.
  by move=> s1 m c2 s1' hwf heqa /= [<-]; exists s1'=> //; constructor.
Qed.

Local Lemma Hcons : sem_Ind_cons p1 ev Pc Pi.
Proof.
  move=> s1 s2 s3 i c _ Hi _ Hc m c2 s1' hwf heqa1 /=.
  t_xrbindP=> i' /Hi -/(_ _ hwf heqa1) [s2' heqa2 hsemi].
  move=> c' /Hc -/(_ _ hwf heqa2) [s3' heqa3 hsemc] <-; exists s3' => //.
  by econstructor; eauto.
Qed.

Local Lemma HmkI : sem_Ind_mkI p1 ev Pi_r Pi.
Proof.
  move=> ii i s1 s2 _ Hi m [ii' i2] s1' hwf heqa /Hi -/(_ _ hwf heqa) [s2' heqa' hsemi].
  by exists s2'.
Qed.

Local Lemma Hassgn : sem_Ind_assgn p1 Pi_r.
Proof.
  move=> s1 s2 x tag ty e v v' hse htr hw ii m ii' i2 s1' hwf heqa /=.
  t_xrbindP=> x' hx e' he _ <-.
  have ? := expand_eP heqa he hse.
  have [s2' hw' heqa'] := expand_lvP hwf heqa hx hw.
  by exists s2' => //; econstructor; rewrite ?eq_globs; eauto.
Qed.

Local Lemma Hopn : sem_Ind_opn p1 Pi_r.
Proof.
  move=> s1 s2 t o xs es; rewrite /sem_sopn; t_xrbindP=> vs ves hse ho hws.
  move=> ii m ii' e2 s1' hwf heqa /=; t_xrbindP=> xs' hxs es' hes _ <-.
  have := expand_esP heqa hes hse.
  have := expand_lvsP hwf heqa hxs hws.
  rewrite -eq_globs => -[s2' hws' ?] hse'; exists s2' => //.
  by constructor; rewrite /sem_sopn hse' /= ho.
Qed.

Local Lemma Hsyscall : sem_Ind_syscall p1 Pi_r.
Proof.
  move=> s1 scs2 m2 s2 o xs es vs ves hse ho hws.
  move=> ii m ii' e2 s1' hwf heqa /=; t_xrbindP=> xs' hxs es' hes _ <-.
  have := expand_esP heqa hes hse.
  have heqa': eq_alloc m (with_scs (with_mem s1 m2) scs2) (with_scs (with_mem s1' m2) scs2) by case: heqa.
  have := expand_lvsP hwf heqa' hxs hws.
  rewrite -eq_globs => -[s2' hws' ?] hse'; exists s2' => //.
  by econstructor; eauto; rewrite -(eq_alloc_mem heqa) -(eq_alloc_scs heqa).
Qed.

Local Lemma Hif_true : sem_Ind_if_true p1 ev Pc Pi_r.
Proof.
  move=> s1 s2 e c1 c2 hse hs hrec ii m ii' ? s1' hwf heqa /=.
  t_xrbindP=> e' he c1' hc1 c2' hc2 _ <-.
  have := expand_eP heqa he hse; rewrite -eq_globs => hse'.
  have [s2' ??] := hrec _ _ _ hwf heqa hc1.
  by exists s2' => //; apply Eif_true.
Qed.

Local Lemma Hif_false : sem_Ind_if_false p1 ev Pc Pi_r.
Proof.
  move=> s1 s2 e c1 c2 hse hs hrec ii m ii' ? s1' hwf heqa /=.
  t_xrbindP=> e' he c1' hc1 c2' hc2 _ <-.
  have := expand_eP heqa he hse; rewrite -eq_globs => hse'.
  have [s2' ??] := hrec _ _ _ hwf heqa hc2.
  by exists s2' => //; apply Eif_false.
Qed.

Local Lemma Hwhile_true : sem_Ind_while_true p1 ev Pc Pi_r.
Proof.
  move=> s1 s2 s3 s4 a c1 e c2 _ hrec1 hse _ hrec2 _ hrecw ii m ii' ? s1' hwf heqa /=.
  t_xrbindP=> e' he c1' hc1 c2' hc2 hii <-.
  have [sc1 heqa1 hs1]:= hrec1 _ _ _ hwf heqa hc1.
  have := expand_eP heqa1 he hse; rewrite -eq_globs => hse'.
  have [sc2 heqa2 hs2]:= hrec2 _ _ _ hwf heqa1 hc2.
  have [| s2' ? hsw]:= hrecw ii m ii' (Cwhile a c1' e' c2') _ hwf heqa2.
  + by rewrite /= he hc1 hc2 hii.
  exists s2' => //; apply: Ewhile_true hsw; eauto.
Qed.

Local Lemma Hwhile_false : sem_Ind_while_false p1 ev Pc Pi_r.
Proof.
  move=> s1 s2 a c e c' _ hrec1 hse ii m ii' ? s1' hwf heqa /=.
  t_xrbindP=> e' he c1' hc1 c2' hc2 hii <-.
  have [s2' heqa1 hs1]:= hrec1 _ _ _ hwf heqa hc1.
  have := expand_eP heqa1 he hse; rewrite -eq_globs => hse'.
  by exists s2' => //; apply: Ewhile_false; eauto.
Qed.

Local Lemma Hfor : sem_Ind_for p1 ev Pi_r Pfor.
Proof.
  move=> s1 s2 i d lo hi c vlo vhi hslo hshi _ hfor ii m ii' ? s1' hwf heqa /=.
  t_xrbindP=> hin lo' hlo hi' hhi c' hc ? <-.
  have := expand_eP heqa hlo hslo.
  have := expand_eP heqa hhi hshi; rewrite -eq_globs => hshi' hslo'.
  have [s2' ??]:= hfor _ _ _ hwf heqa hin hc.
  exists s2' => //; econstructor; eauto.
Qed.

Local Lemma Hfor_nil : sem_Ind_for_nil Pfor.
Proof.
  by move=> s i c i2 c' s1' hwf heqa _; exists s1' => //; constructor.
Qed.

Local Lemma Hfor_cons : sem_Ind_for_cons p1 ev Pc Pfor.
Proof.
  move=> s1 s1w s2 s3 i w ws c Hwi _ Hc _ Hfor m c' s1' hwf heqa hin hc.
  have [s1w' ? heqa1']:= eq_alloc_write_var hwf heqa hin Hwi.
  have [s2' heqa2 ?]:= Hc _ _ _ hwf heqa1' hc.
  have [s3' ??]:= Hfor _ _ _ hwf heqa2 hin hc.
  by exists s3' => //; econstructor; eauto.
Qed.

Local Lemma Hcall : sem_Ind_call p1 ev Pi_r Pfun.
Proof.
  move=> s1 scs2 m2 s2 ii xs fn args vargs vs Hes Hsc Hfun Hw ii1 m ii2 i2 s1' hwf heqa /=.
  case hgfn: Mfn.get => [[ei eo]|//].
  t_xrbindP=> xs' sxs' hxs <- es' ses' hes <- _.
  have [? heva]:= expand_paramsP hwf heqa hes Hes.
  have heqa': eq_alloc m (with_scs (with_mem s1 m2) scs2) (with_scs (with_mem s1' m2) scs2) by case: heqa.
  case: {Hfun}(Hfun ei eo hgfn _ heva) => ? hevr.
  have [s2' ]:= expand_returnsP hwf heqa' hxs Hw hevr.
  rewrite -eq_globs => ???? <-; exists s2' => //; econstructor; eauto.
  by case: heqa => _ <- <-.
Qed.

Lemma wf_init_map ffi m fcc : init_map ffi = ok (m, fcc) -> wf_t m.
Proof.
  rewrite /init_map; t_xrbindP.
  set svars_ := of_list _.
  pose wf_st svm :=
    [/\ wf_t {| svars := svars_; sarrs := svm.2 |},
      Sv.Subset svars_ svm.1 &
      (forall x ai i xi,
        Mvar.get svm.2 x = Some ai ->
        Mi.get (ai_elems ai) i = Some xi ->
        Sv.In xi svm.1)].
  suff : forall l svm svm', wf_st svm -> foldM init_array_info svm l = ok svm' -> wf_st svm'.
  + move=> h svm' /h []; first by split.
    by move=> ? _ _ <-.
  elim=> /= [ ??? [<-] // | vi vis hrec svm svm' hwf].
  t_xrbindP=> svm1 heq; apply: hrec.
  move: heq; rewrite /init_array_info; t_xrbindP=> ?.
  case: svm hwf => sv1 m1 hwf; t_xrbindP=> /Sv_memP hin [[sv2 m2] b].
  set ty := sword _.
  have hcsz : forall l t t',
    foldM (init_elems ty) t l = ok t' -> Z.of_nat (size l) = (t'.2 - t.2)%Z.
  + elim=> [> [->]|> hrec] /=; first by rewrite Z.sub_diag.
    t_xrbindP=> -[[??]?] ? [[]]> /=; t_xrbindP=> ???? /hrec; subst=> /=.
    Psatz.lia.
  pose wf_sm (svmp : _ * _ * Z) :=
    let '(sv,mi,_) := svmp in
    Sv.Subset sv1 sv /\
    (forall i xi, Mi.get mi i = Some xi ->
      [/\ ~Sv.In xi sv1, Sv.In xi sv,
        vtype xi == ty, (0 <= i < b)%Z &
        forall j xj, i <> j -> Mi.get mi j = Some xj -> xi <> xj]).
  have : forall ids svmp svmp',
    (Z.of_nat (size ids) <= b)%Z -> (Z.of_nat (size ids) = b - svmp.2)%Z ->
    wf_sm svmp -> foldM (init_elems ty) svmp ids = ok svmp' -> wf_sm svmp'.
  + elim => /= [?????[<-]//| id ids hrec] [[sv mi] i] svmp' hbsz hsz hwfsm.
    t_xrbindP=> svmp'' hsvmp''; apply: hrec; first Psatz.lia; move: hsvmp'';
      rewrite /init_elems; t_xrbindP=> /Sv_memP hnin <- /=.
    + by simpl in hsz; Psatz.lia.
    simpl in hsz; case: hwfsm => h1 h2; split; first by SvD.fsetdec.
    move=> i1 xi1; rewrite Mi.setP; case: eqP => ?.
    + subst i1 => -[<-]; split => //; try SvD.fsetdec.
      + Psatz.lia.
      move=> j xj hji; rewrite Mi.setP_neq; last by apply/eqP.
      by move=> /h2 [hj1 hj2 _ _ _] heq; apply hnin; rewrite heq.
    move=> /h2 [] hi1 hi2 hi3 hi4 hi5; split => //; first by SvD.fsetdec.
    move=> j xj ji; rewrite Mi.setP; case: eqP => _; last by apply: hi5.
    by move=> [<-] heq; apply hnin; rewrite -heq.
  move=> h /[dup]/hcsz{hcsz}hsz /h{h}h [<-].
  have /h{h}[|//|hsub hmi] : wf_sm (sv1, Mi.empty var, 0%Z) by split.
  + by rewrite hsz /= Z.sub_0_r; reflexivity.
  case: hwf => /= hwf hsub' hget; split=> /=; first last.
  + move=> /= x ai i xi; rewrite Mvar.setP; case: eqP.
    + by move=> ? [<-]; subst x => /hmi [].
    by move=> ? h1 h2; have /= := hget _ _ _ _ h1 h2; SvD.fsetdec.
  + by rewrite /=; SvD.fsetdec.
  move=> x ai /=; rewrite Mvar.setP; case: eqP.
  + move=> <- [<-]; split=> //; first by apply/negP/Sv_memP; SvD.fsetdec.
    move=> i xi /= hgeti; have [/= hnin heqt ht hdbnd hj] := hmi _ _ hgeti; split=> //.
    + by apply/negP/Sv_memP; SvD.fsetdec.
    move=> x' ai' i' xi'; rewrite Mvar.setP; case: eqP => [<- [<-] /= hgeti' hd| hne].
    + by case: (hmi _ _ hgeti) => ???? h; apply/eqP/(h i') => //; case: hd.
    move=> h1 h2 ?; have /= ?:= hget _ _ _ _ h1 h2; apply/eqP => heq.
    by apply hnin; rewrite heq.
  move=> /eqP hne /[dup] hgetx /hwf /= [?? hgeti]; split=> //.
  move=> i xi /[dup] hi /hgeti [??? h]; split=> //.
  move=> x' ai' i' xi'; rewrite Mvar.setP; case: eqP.
  + move=> ? [<-]; subst x' => /= hi' ?.
    have /= ? := hget _ _ _ _ hgetx hi.
    by have [hnin ????]:= hmi _ _ hi'; apply/eqP => heq; apply hnin; rewrite -heq.
  by move=> ? hgetx'; have [?? /(_ _ _ hi) [???] /=]:= hwf _ _ hgetx; apply.
Qed.

Local Lemma Hproc : sem_Ind_proc p1 ev Pc Pfun.
Proof.
  move=> scs1 m1 scs2 m2 fn f vargs vargs' s0 s1 s2 vres Hget Hca [].
  set sempty := {| evm := Vmap.empty |}.
  move=> ? Hw _ Hc Hres ??; subst.
  have [? [? [m [? [Hget2 hsigs /=]]]] {Hget}]:= all_checked Hget.
  rewrite /expand_fsig; t_xrbindP=> -[??].
  case: f Hca Hw Hc Hres => finfo ftyin fparams fbody ftyout fres fextra /=.
  set fd := {| f_info := finfo |} => Hca Hw Hc Hres hinit.
  t_xrbindP=> -[ip ie] iz hparams hiz.
  rewrite /= (surjective_pairing (unzip12 _)).
  t_xrbindP=> -[op oe] oz hres hoz.
  rewrite /= (surjective_pairing (unzip12 _)) => -[???].
  subst; t_xrbindP=> fbody' hbody ?; subst.
  rewrite /Pfun hsigs => exin exout [??] vargs'' hargs; subst.
  have hwf := wf_init_map hinit.
  have heqa : eq_alloc m sempty sempty.
  + split=> //; split=> //.
    move=> x ai i xi hai hxi.
    rewrite /eval_array /= !Vmap.get_var0.
    have [_ /is_sarrP[p ->] /(_ _ _ hxi) [_ /eqP -> _ _] /=]:= hwf _ _ hai.
    case heq : (WArray.get AAscale (ai_ty ai) (WArray.empty p) i) => [w | ]; last first.
    + by rewrite /undef_v (undef_x_vundef (_ _)).
    have []:= WArray.get_bound heq; rewrite /mk_scale => ???.
    have h : ((0 <= 0%N)%Z ∧ (0%N < wsize_size (ai_ty ai)))%Z.
    + by move=> /=; have := wsize_size_pos (ai_ty ai); Psatz.lia.
    have [_ /(_ 0 h)] := read_read8 heq.
    by rewrite WArray.get0 //= WArray.addE; have := wsize_size_pos (ai_ty ai); Psatz.lia.
  (* some parts may remind you of expand_returnsP proof,
    in fact they are almost the same except with write_vars instead of write_lvals *)
  have [vargs''' [s1' [htrs hparams' heqa1]]]: exists vargs''' s1', [/\
    mapM2 ErrType truncate_val (flatten (unzip1 ip)) (flatten vargs'') = ok vargs''',
    write_vars (flatten (unzip2 ip)) vargs''' sempty = ok s1' &
    eq_alloc m s1 s1'].
  + elim: ftyin fparams vargs' iz ip exin vargs vargs'' sempty {1 3}sempty
      {hinit fd Hget2 hsigs} hparams hiz hargs Hca heqa Hw
      => [[]//[]//> [<-][<-<-][<-][<-]?[<-]|ty? h[]//x?[]//v?????? ss2 ss1 /=].
    + by eexists _, _.
    t_xrbindP=> -[[tys xs] ei] htyv ? /h{h}h <- [??]; subst=> /=.
    t_xrbindP=> vs hev ? /(h _ _ _ _ _ _ _ (surjective_pairing _)){h}h
      <- vt htr ? /h{h}h <-.
    rewrite /write_var; t_xrbindP=> heqa ss1' vm hsv ?; subst.
    suff [? [? [htrs hvs /h{h}h]]]: exists vts ss2',
      [/\ mapM2 ErrType truncate_val tys vs = ok vts,
        write_vars xs vts ss2 = ok ss2' & eq_alloc m (with_vm ss1 vm) ss2'].
    + case/h => {h}? [? [/(cat_mapM2 htrs)-> /(cat_fold2 hvs) hwvs ?]].
      by eexists _, _; split=> //; first by rewrite /write_vars hwvs.
    move: htyv hev.
    (rewrite /expand_tyv; case hmg: Mvar.get => [ai|]; t_xrbindP)
      => [b z hmm|hin <-<-<-[<-]/=]; last first.
    + rewrite /write_var htr; case: heqa => -[heq hmi]??.
      have [? hrw] := Vmap.set_set (evm ss2) hsv.
      eexists _, _; split=> //=; first by rewrite hrw.
      split=> //=; split=> [y/heq|y ?? xi /[dup]/hwf[hnin ? h']/hmi{hmi}h
        /[dup]/h'{h'}[hnin' _ [hlb hhb] _]/h{h}].
      + by rewrite (Vmap.set_varP _ hsv) (Vmap.set_varP _ hrw); case: eqP.
      by have [/nesym/eqP/(Vmap.set_varP_neq hsv)-> /nesym/eqP/(Vmap.set_varP_neq hrw)->]
        : ~ y = x /\ ~ xi = x by split; move=> ?; subst.
    have [hnin htx hgi] := hwf _ _ hmg.
    rewrite (surjective_pairing (unzip12 _)) => -[<-<-<-] /=.
    rewrite unzip121 unzip122 size_unzip2 -(size_mapM hmm)
      size_ziota /ziota Nat2Z.id -/(ziota _ _) => hmm'.
    have [vts htrs [vm' hwvs]] : exists2 vts,
      mapM2 ErrType truncate_val (unzip2 z) vs = ok vts &
      exists vm, write_vars (unzip1 z) vts ss2 = ok (with_vm ss2 vm).
    + elim/ziota_ind: (ziota _ _) vs ss2 z {heqa} hmm hmm' => [> [<-][<-]|> hbnd hrec/=].
      + by eexists=> //=; eexists (evm _); erewrite with_vm_same.
      t_xrbindP=> vs ss2 >; case: Option.oappP
        => // vi hmi [<-]? /hrec{hrec}h <- vvi hea ? /h{h} /[swap]<-/=.
      have [_ /eqP hty _ _] := hgi _ _ hmi.
      suff [? -> [vm' hwv']]: exists2 vtvi, truncate_val (vtype vi) vvi = ok vtvi &
        exists vm', write_var {| v_var := vi; v_info := v_info x |} vtvi ss2 = ok (with_vm ss2 vm').
      + case/(_ (with_vm ss2 vm')) => ? -> [? hwvs].
        by eexists=> //=; rewrite hwv' /= hwvs with_vm_idem; eexists.
      rewrite /write_var hty.
      have [_ [|[w]]->/=]:= eval_arrayP hea.
      + have [|? hv] := Vmap.set_var_ok (evm ss2) (@compat_typerel_undef (vtype vi) undef_w _).
        + by rewrite hty.
        by eexists=> //; rewrite hv; eexists.
      case: truncate_word => /= [w'|?].
      + have [|? hv] := Vmap.set_var_ok (evm ss2) (@compat_typerel_undef (vtype vi) (Vword w') _).
        + by rewrite hty.
        by eexists=> //; rewrite hv; eexists.
      have [|? hv] := Vmap.set_var_ok (evm ss2) (@compat_typerel_undef (vtype vi) (Vword w) _).
      + by rewrite hty.
      by eexists=> //; rewrite hv; eexists.
    rewrite htrs; eexists _, _; split=> //; first by rewrite hwvs.
    case: heqa => heqa hsc hm; split=> // {hsc hm}.
    case: heqa => heq heva; split=> [|vi' ai' i xi].
    + move=> ? /Sv_memP hin; rewrite (Vmap.set_varP_neq hsv) ?heq; last first.
      + by apply/eqP => ?; subst; exact: hnin.
      + exact/Sv_memP.
      elim/ziota_ind: (ziota _ _) z vts ss2 {htrs heq heva} hmm hwvs
        => [?[]>[<-]//[<-]//|> _ hrec ?[]/=]; t_xrbindP=> >;
        case: Option.oappP => // ? /hgi{hgi}[? ? ? _] [?] ? /hrec{hrec}hrec ?;
        subst=> //=; rewrite /write_var.
      t_xrbindP=> _ > /Vmap.set_varP_neq+ <- /hrec{hrec} <- => -> //=.
      by apply/eqP=> ?; subst; exact: hnin.
    case: (vi' =P x) => [{heva}->|]; last first.
    + move=> /nesym/[dup]hneq/eqP/(Vmap.set_varP_neq hsv){hsv} /= ->
        /[dup]/heva{heva}h hga' /[dup]/h{h}-> hgi'.
      elim/ziota_ind: (ziota _ _) z vs vts hmm' hmm htrs vm' ss2 {2}ss2 {heq} hwvs
        => [>[<-][<-][<-]>[->]|> _ hrec] //=.
      t_xrbindP=> > ?? /hrec{hrec}h ??+?/h{h}h?>; subst=> /=.
      case: Option.oappP => // ? /hgi{hgi}[_ _ _
        /(_ _ _ _ _ hga' hgi' (or_introl _ hneq)){hga' hgi' hneq}?] [<-] /=.
      t_xrbindP=> ??? /h{h}h ?; subst; t_xrbindP=> > + /h{h}<-; rewrite /write_var.
      by t_xrbindP=> ? /Vmap.set_varP_neq <- // <-.
    move: {h} htx (Vmap.get_varP vm x) (Vmap.set_varP_eq hsv) => /is_sarrP[?->]
      /(typerel_undef_compat vm_subcomp) /compat_typeEl/type_of_valI[t ->] /= he.
    have ? : vt = t by case: Result.rdfltP he => // ? /[swap]<- /truncate_defined_valI[].
    rewrite hmg => -[?]; subst=> /[dup]/hgi{hgi}[_ /eqP htxi [hp hle] hne] hgi.
    have {htr}? := proj2 (truncate_valI htr); subst.
    move: z vs vts hmm' hmm htrs hwvs.
    have := ziota_cat 0 hp (Zle_minus_le_0 _ _ (Z.lt_le_incl _ _ hle)).
    rewrite Zplus_minus => /= <-.
    have := ziotaS_cons i (Zle_minus_le_0 _ _ (Zlt_le_succ _ _ hle)).
    rewrite Zminus_succ_l Z.sub_succ_l Z.sub_succ_r Z.succ_pred !mapM_cat => ->.
    rewrite /= hgi /=; t_xrbindP=> > hz1 ? z2 hz2 ??? hc1 ? c2 hc2 ??.
    subst; rewrite unzip2_cat /=.
    move: (size_mapM hc1) (size_mapM hz1); rewrite -size_unzip2
      => -> /(mapM2_cat _) + ht => /(_ _ _ _ _ _ _ _ ht){ht}[? [? [ht1 /=]]].
    t_xrbindP=> ? ht t2 ht2 ??; subst; rewrite unzip1_cat /write_vars.
    move: (proj2 (size_mapM2 ht1)); rewrite size_unzip2 -size_unzip1
      => /(fold2_cat _) + hwv => /(_ _ _ _ _ _ _ _ _ hwv){hwv}[?] _.
    rewrite /= /write_var /=; t_xrbindP=> ? svm /Vmap.set_varP_eq hrw ? hf; subst.
    suff : vm'.[xi] = svm.[xi].
    + move: ht; rewrite hrw htxi => /[swap]->; case: WArray.get => [?|?[<-]//].
      rewrite /= truncate_word_u => -[<-].
      by rewrite /truncate_defined_val /= truncate_word_u.
    elim/ziota_ind: (ziota _ _) c2 z2 t2 svm vm' {hrw hsv} hc2 hz2 ht2 hf
      => [>[<-][<-][<-][_ _ <-]| > hbnd hrec] //=; t_xrbindP=> >.
    case: Option.oappP => //? /(hne _ _ _ _ hmg){hne}hne [?]?/hrec{hrec}h ??/h{h}h ?.
    subst=> /=; t_xrbindP=> > ?? /h{h}h?.
    subst; t_xrbindP=> > /Vmap.set_varP_neq hrw ?.
    subst; rewrite with_vm_idem => /h{h} ->; rewrite hrw // neq_sym.
    by apply: hne; Psatz.lia.
  have [s2' heqa2 hsem]:= Hc _ _ _ hwf heqa1 hbody.
  suff [???] : exists2 vres', expand_vs exout vres = ok vres' &
    mapM2 ErrType (λ (ty : stype) (x : var_i), truncate_val ty (evm s2').[x])
      (flatten (unzip1 op)) (flatten (unzip2 op)) = ok (flatten vres').
  + eexists; first by eassumption.
    by eexists; eauto; rewrite ?(unzip121, unzip122); eauto=> //; case: heqa2.
  elim: ftyout fres oz op exout vres {hinit fd Hget2 hsigs} hres hoz Hres
    => [[]//> [<-][<-<-][<-]|ty? hrec []//= x>]; first by eexists.
  t_xrbindP=> -[[tys xs] ei] htyv ? /hrec{hrec}h <- [??] v htr ?+?; subst.
  case/(h _ _ _ (surjective_pairing _)) => {h}? /= -> /(cat_mapM2 _)h.
  suff [? -> /h{h}->] : exists2 vs, expand_v ei v = ok vs &
    mapM2 ErrType (fun ty (x : var_i) => truncate_val ty (evm s2').[x]) tys xs = ok vs.
  + by eexists.
  move: {h htrs} htyv.
  (rewrite /expand_tyv; case hmg: Mvar.get => [ai|]; t_xrbindP)
    => [b z|hin <-<-<-]/=; last first.
  + by case: heqa2 htr => -[/(_ _ (Sv_memP _ _ hin))<- hmi]?? ->; eexists.
  rewrite (surjective_pairing (unzip12 _)) => /[dup]/size_mapM ++ [<- <- <-].
  rewrite /expand_v unzip122 size_unzip2 size_ziota /ziota => <-.
  rewrite Nat2Z.id -/(ziota _ _).
  elim/ziota_ind: (ziota _ _) z => [?[<-]|> _ hrec /=]; first by eexists.
  t_xrbindP; case: Option.oappP => // ? hmi > [?] ?+?.
  subst=> /hrec{hrec}[? /= -> -> /=].
  rewrite (truncate_val_u (Vmap.get_varP (vmr:= vmr_subtype) _ _)).
  eexists=> //; case: heqa2 htr => -[_ /(_ _ _ _ _ hmg hmi){hmg hmi}+] _ _.
  by move=> /[dup]/eval_arrayP/proj1/is_sarrP[? /type_of_valI[? ->]]
    /[swap] /truncate_valE/proj2-> ->.
Qed.

Lemma expand_callP_aux f scs mem scs' mem' va vr:
  sem_call p1 ev scs mem f va scs' mem' vr ->
  (* exactly Pfun *)
  forall expdin expdout, Mfn.get fsigs f = Some (expdin, expdout) ->
  forall vas, expand_vs expdin va = ok vas ->
  exists2 vrs, expand_vs expdout vr = ok vrs &
  sem_call p2 ev scs mem f (flatten vas) scs' mem' (flatten vrs).
Proof.
  exact: (@sem_call_Ind _ _ _ _ _ _ _ _ p1 ev Pc Pi_r Pi Pfor Pfun Hskip Hcons HmkI Hassgn Hopn Hsyscall
          Hif_true Hif_false Hwhile_true Hwhile_false Hfor Hfor_nil Hfor_cons Hcall Hproc).
Qed.

End Step1.

Lemma expand_callP f scs mem scs' mem' va vr:
  sem_call p1 ev scs mem f va scs' mem' vr ->
  f \in entries ->
  sem_call p2 ev scs mem f va scs' mem' vr.
Proof.
  apply: (rbindP _ Hcomp) => s1 /[dup]Hs1/expand_callP_aux h _ /[dup]+/h{h}.
  rewrite /fsigs (surjective_pairing (unzip12 _)).
  set fsigs := foldr _ _ _
    => -[???? {}f fd {}va va' ??? {}vr hgf htri _ _ _ htro _ _] h b.
  have {htro}hso := proj2 (size_mapM2 htro).
  suff /h{h}h : Mfn.get fsigs f =
    Some (map (fun=> None) (f_tyin fd), map (fun=> None) (f_tyout fd)).
  + have /h{h}[?] :
     expand_vs (map (fun=> None) (f_tyin fd)) va' = ok [seq [:: x] | x <- va'].
    + elim: (f_tyin fd) va' va htri {h} => [[]|> hrec []]//=.
      by t_xrbindP=> > _ ? /hrec{hrec}->.
    have : expand_vs (map (fun=> None) (f_tyout fd)) vr = ok [seq [:: x] | x <- vr].
    + by elim: (f_tyout fd) vr hso => [[]|> hrec []//>[/hrec{hrec}/=->]].
    by move=> -> [<-]; rewrite 2!flatten_seq1.
  move: Hs1 fd hgf {h htri hso}; rewrite {}/fsigs; elim: (p_funcs p1) s1
    => [> [<-]|[?[? fti fp ? fto fr]]> hrec] //=.
  t_xrbindP=> > +?? /hrec{hrec}h ?; subst=> /=.
  case: ifP => [{h}/eqP<- + [?] _ _ _ _ _ _ [<-<-<-<-<-<-<-]
    | /eqP/nesym/eqP/(Mfn.setP_neq _ _)-> + /h] //=.
  rewrite Mfn.setP_eq /expand_fsig b /=; t_xrbindP=> -[??] _; t_xrbindP=> ? z1 hz1 ?.
  rewrite (surjective_pairing (unzip12 _)); t_xrbindP=> ? z2 hz2 ?.
  rewrite (surjective_pairing (unzip12 _)) => -[?]; subst=> /=.
  do 2 f_equal.
  + elim: fti fp z1 hz1 => [[]//?[<-]|> hrec []]//=.
    t_xrbindP=> > +? /hrec{hrec}+ ?; subst=> /= + ->.
    by rewrite /expand_tyv; case: Mvar.get => //; t_xrbindP=> ? <-.
  elim: fto fr z2 hz2 => [[]//?[<-]|> hrec []]//=.
  t_xrbindP=> > +? /hrec{hrec}+ ?; subst=> /= + ->.
  by rewrite /expand_tyv; case: Mvar.get => //; t_xrbindP=> ? <-.
Qed.

End Section.
