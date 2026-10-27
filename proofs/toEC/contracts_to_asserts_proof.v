(* * Correctness of the pass contracts_to_asserts.

   The transformed program, run with its assertions evaluated but its contracts
   not ([withassert_nocontract]), behaves as the source run with its contracts
   evaluated ([withassert]): same results, same failures. Each assertion added
   checks, on the same values, a condition that the semantics of the contracts
   checks at a call; the copies added write variables that the functions do
   not otherwise use ([check_contract], the freshness checks).

   The relation [wiequiv_f] only constrains the runs of its first program
   that do not fail: the two directions are stated separately. *)

From ITree Require Import ITree ITreeFacts.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype seq ssrnat.
Require Import compiler_util psem psem_facts.
Require Import contracts_to_asserts normalize_calls_proof.

#[local] Existing Instance progUnit.
#[local] Existing Instance nosubword.
#[local] Existing Instance indirect_c.

Section SYNTAX.

Context (fresh_var_ident : v_kind -> instr_info -> string -> atype -> Ident.ident).

Lemma fresh_cvarP ii X acc x acc' y :
  fresh_cvar fresh_var_ident ii X acc x = ok (acc', y) ->
  [/\ vtype y = vtype x, ~ Sv.In y X, ~ Sv.In y acc & acc' = Sv.add y acc].
Proof.
rewrite /fresh_cvar; t_xrbindP => /Sv_memP hnin <- <- /=.
by split => //; SvD.fsetdec.
Qed.

Lemma vars_lP (x : var) xs : Sv.In x (vars_l xs) <-> x \in [seq v_var y | y <- xs].
Proof.
elim: xs => [ | y xs ih] /=; first by split => //; SvD.fsetdec.
rewrite in_cons SvD.F.add_iff ih; split.
+ by move=> [-> | ->]; rewrite ?eqxx ?orbT.
by case/orP => [/eqP -> | ->]; auto.
Qed.

Lemma fresh_cvarsP ii X acc xs acc' ys :
  fresh_cvars fresh_var_ident ii X acc xs = ok (acc', ys) ->
  [/\ [seq vtype (v_var y) | y <- ys] = [seq vtype (v_var x) | x <- xs],
      uniq [seq v_var y | y <- ys],
      (forall y, Sv.In y (vars_l ys) -> ~ Sv.In y X /\ ~ Sv.In y acc)
    & Sv.Equal acc' (Sv.union (vars_l ys) acc)].
Proof.
elim: xs acc acc' ys => [ | x xs ih] acc acc' ys /=.
+ by move=> [<- <-] /=; split => //; SvD.fsetdec.
t_xrbindP => -[acc1 y] /fresh_cvarP [hty hX hacc ->] -[acc2 ys'] /ih [htys huniq hfresh heq] <- <- /=.
split.
+ by rewrite hty htys.
+ rewrite huniq andbT; apply/negP => /vars_lP /hfresh /= [_]; SvD.fsetdec.
+ move=> z /SvD.F.add_iff [<- | /hfresh /=]; [done | SvD.fsetdec].
rewrite heq /=; SvD.fsetdec.
Qed.

(* How a destination of a call is rewritten: itself when it is a variable,
   a fresh variable when it is [_]. *)
Definition dest_of (X acc : Sv.t) (lv : lval) (d : var_i) :=
  lv = Lvar d \/ [/\ exists vi, lv = Lnone vi (vtype d), ~ Sv.In d X & ~ Sv.In d acc].

Lemma call_destsP ii X acc lvs ires acc' ds :
  call_dests fresh_var_ident ii X acc lvs ires = ok (acc', ds) ->
  [seq vtype (v_var d) | d <- ds] = [seq vtype (v_var y) | y <- ires] /\
  List.Forall2 (dest_of X acc) lvs ds.
Proof.
elim: lvs ires acc acc' ds => [ | lv lvs ih] [ | y ires] acc acc' ds //=.
+ by move=> [_ <-].
t_xrbindP => -[acc1 d] hd -[acc2 ds'] /ih [htys hall] _ <- /=.
have hw : forall acc0, Sv.Subset acc acc0 -> List.Forall2 (dest_of X acc0) lvs ds' -> List.Forall2 (dest_of X acc) lvs ds'.
+ move=> acc0 hsub; apply List.Forall2_impl => lv' d' [-> | [h1 h2 h3]]; [by left | right; split => //; SvD.fsetdec].
case: lv hd => //.
+ move=> vi ty; t_xrbindP => /eqP -> /fresh_cvarP [hty hX hacc ?]; subst acc1.
  rewrite hty htys; split => //; constructor; last by apply: hw hall => /=; SvD.fsetdec.
  by right; split => //; exists vi; rewrite hty.
move=> x; t_xrbindP => /eqP hty ??; subst acc1 d.
by rewrite hty htys; split => //; constructor => //; left.
Qed.

Lemma dest_of_vrvs X a lvs ds :
  List.Forall2 (dest_of X a) lvs ds ->
  forall z, Sv.In z (vrvs [seq Lvar x | x <- ds]) -> Sv.In z (vrvs lvs) \/ ~ Sv.In z X.
Proof.
elim => [ | lv d lvs' ds' hd _ ih] z /=; first by rewrite /vrvs /=; SvD.fsetdec.
rewrite !vrvs_cons => /Sv.union_spec [ | /ih]; last by SvD.fsetdec.
by case: hd => [-> | [_ hX _]] /=; [left; SvD.fsetdec | move=> ?; right; SvD.fsetdec].
Qed.

Context {asm_op : Type} {asmop : asmOp asm_op}.

Lemma write_c_copy_es ii xs tys es :
  Sv.Subset (write_c (copy_es ii xs tys es)) (vars_l xs).
Proof.
elim: xs tys es => [ | x xs ih] [ | ty tys] [ | e es] /=; try by rewrite /write_c /=; SvD.fsetdec.
rewrite /copy_es /= write_c_cons -/(copy_es ii xs tys es) write_Ii write_i_assgn.
have := ih tys es; rewrite /vrv /=; SvD.fsetdec.
Qed.

Lemma write_c_assert_all ii a_s : Sv.Equal (write_c (assert_all ii a_s)) Sv.empty.
Proof.
elim: a_s => [ | a a_s ih] /=; first by rewrite /write_c.
by rewrite write_c_cons ih write_Ii /=; SvD.fsetdec.
Qed.

(* The shape of the code around a call to a function with a contract. *)
Lemma call_with_contractP ii X acc lvs f es tyin ci acc' c' :
  call_with_contract fresh_var_ident ii X acc lvs f es tyin ci = ok (acc', c') ->
  exists ip ds,
  [/\ c' = copy_es ii ip tyin es
           ++ assert_all ii (map (rename_assertion (rename_map ci.(f_iparams) ip)) ci.(f_pre))
           ++ MkI ii (Ccall [seq Lvar x | x <- ds] f [seq Plvar x | x <- ip])
           :: assert_all ii (map (rename_assertion (rename_map (ci.(f_iparams) ++ ci.(f_ires)) (ip ++ ds))) ci.(f_post)),
      size es = size ci.(f_iparams),
      [seq vtype (v_var y) | y <- ip] = [seq vtype (v_var x) | x <- ci.(f_iparams)],
      (forall y, Sv.In y (vars_l ip) -> ~ Sv.In y X),
      [seq vtype (v_var d) | d <- ds] = [seq vtype (v_var y) | y <- ci.(f_ires)],
      List.Forall2 (dest_of X (vars_l ip)) lvs ds
    & Sv.Subset (vrvs lvs) X -> uniq [seq v_var x | x <- ip ++ ds]].
Proof.
rewrite /call_with_contract; t_xrbindP => /eqP hsize -[acc1 ip] /fresh_cvarsP [htyip huip hfip heq1] -[acc2 ds] /call_destsP [htyds hds] huds _ <- /=.
have {}hds : List.Forall2 (dest_of X (vars_l ip)) lvs ds.
+ apply: List.Forall2_impl hds => lv d [-> | [h1 h2 h3]]; [by left | right; split => //; SvD.fsetdec].
exists ip, ds; split => //.
+ by move=> y /hfip [].
move=> hsub; rewrite map_cat cat_uniq huip huds andbT /=.
elim: hds hsub {huds} => //= lv d lvs' ds' [-> | [_ hX hip]] _ ih hsub.
+ rewrite vrvs_cons /= in hsub; rewrite negb_or ih; last by SvD.fsetdec.
  rewrite andbT; apply/negP => /vars_lP /hfip [] ?; SvD.fsetdec.
rewrite vrvs_cons /= in hsub; rewrite negb_or ih; last by SvD.fsetdec.
by rewrite andbT; apply/negP => /vars_lP.
Qed.

Context (p : _uprog).

(* The transformed code writes the variables of the source code and
   auxiliary variables, which are not in [X]. *)
Let Pi (i : instr) := forall X acc acc' c', c2a_i fresh_var_ident p X acc i = ok (acc', c') ->
  forall z, Sv.In z (write_c c') -> Sv.In z (write_I i) \/ ~ Sv.In z X.
Let Pr (ir : instr_r) := forall ii, Pi (MkI ii ir).
Let Pc (c : cmd) := forall X acc acc' c', c2a_c (c2a_i fresh_var_ident p X) acc c = ok (acc', c') ->
  forall z, Sv.In z (write_c c') -> Sv.In z (write_c c) \/ ~ Sv.In z X.

Lemma c2a_write : forall c, Pc c.
Proof.
apply (cmd_rect (Pr := Pr) (Pi := Pi) (Pc := Pc)).
+ done.
+ by move=> X acc acc' c' [_ <-] z; rewrite /write_c /=; auto.
+ move=> i c hi hc X acc acc' c' /=; t_xrbindP => -[acc1 ci] /hi {}hi -[acc2 cc] /hc {}hc _ <- z.
  rewrite write_c_app write_c_cons => /Sv.union_spec [/hi | /hc]; [SvD.fsetdec | SvD.fsetdec].
1-4: by move=> > [_ <-] z; rewrite write_c_cons /write_c /=; left; SvD.fsetdec.
+ move=> e c1 c2 hc1 hc2 ii X acc acc' c' /=; t_xrbindP => -[acc1 c1'] /hc1 {}hc1 -[acc2 c2'] /hc2 {}hc2 _ <- z.
  rewrite write_c_cons /= write_Ii write_i_if write_Ii write_i_if.
  move=> /Sv.union_spec [/Sv.union_spec [/hc1 | /hc2] | ]; [SvD.fsetdec | SvD.fsetdec | rewrite /write_c /=; SvD.fsetdec].
+ move=> v dir lo hi c hc ii X acc acc' c' /=; t_xrbindP => -[acc1 c1'] /hc {}hc _ <- z.
  rewrite write_c_cons /= !write_Ii !write_i_for.
  move=> /Sv.union_spec [/Sv.union_spec [ | /hc] | ]; [SvD.fsetdec | SvD.fsetdec | rewrite /write_c /=; SvD.fsetdec].
+ move=> a c e info c2 hc hc2 ii X acc acc' c' /=; t_xrbindP => -[acc1 c1'] /hc {}hc -[acc2 c2'] /hc2 {}hc2 _ <- z.
  rewrite write_c_cons /= !write_Ii !write_i_while.
  move=> /Sv.union_spec [/Sv.union_spec [/hc | /hc2] | ]; [SvD.fsetdec | SvD.fsetdec | rewrite /write_c /=; SvD.fsetdec].
move=> xs f es ii X acc acc' c' /=.
case: get_fundef => [fd | //].
case: f_contract => [ci | ]; last by move=> [_ <-] z; rewrite write_c_cons /write_c /=; left; SvD.fsetdec.
move=> /call_with_contractP [ip [ds [-> _ _ hip _ hds _]]] z.
rewrite !write_c_app write_c_cons !write_c_assert_all write_Ii write_i_call.
have hcp := @write_c_copy_es ii ip (f_tyin fd) es.
move=> /Sv.union_spec [/hcp /hip | ]; first by auto.
move=> /Sv.union_spec [ | /Sv.union_spec [h | ]]; [SvD.fsetdec | | SvD.fsetdec].
by case: (dest_of_vrvs hds h); auto.
Qed.

End SYNTAX.


Section RENAME.

Context
  {asm_op syscall_state : Type} {ep : EstateParams syscall_state}
  {spp : SemPexprParams} {sip : SemInstrParams asm_op syscall_state}.

(* [vt] holds, in the variables renamed by [r], the values of [vs] in the
   variables of [R]. *)
Definition ren_on (r : Mvar.t var) (R : Sv.t) (vt vs : Vm.t) :=
  forall z, Sv.In z R ->
    vtype (odflt z (Mvar.get r z)) = vtype z /\
    Vm.get (sm := partial) vt (odflt z (Mvar.get r z)) = Vm.get (sm := partial) vs z.

Lemma rename_eassertP r gd (t s : estate) R a :
  emem t = emem s -> ren_on r R (evm t) (evm s) -> Sv.Subset (read_eassert a) R ->
  sem_eassert gd t (rename_eassert r a) = sem_eassert gd s a.
Proof using sip.
move=> hmem hR.
have hR' : forall z, Sv.In z R -> Vm.get (sm := total) (evm t) (odflt z (Mvar.get r z)) = Vm.get (sm := total) (evm s) z.
+ by move=> z /hR [hty heq]; apply Vm.get_eq_mode.
have [he hes] := rename_e_esP (wa := withassert) (sm := total) true gd hmem hR'.
elim: a => /=.
+ by move=> e; rewrite read_eassert_Pexpr => /he ->.
+ by move=> o es; rewrite read_eassert_PappN => /hes; rewrite /sem_pexprs => ->.
+ move=> x; rewrite read_eassert_Pis_var_init => hsub.
  have [_ ] := hR x ltac:(SvD.fsetdec).
  by rewrite /is_var_init /normalize_calls.rename_var; case: Mvar.get => [y|] /= ->.
+ move=> e1 e2; rewrite read_eassert_Pis_mem_init => hsub.
  rewrite (he e1); last by SvD.fsetdec.
  by rewrite (he e2) ?hmem //; SvD.fsetdec.
move=> a1 ih1 a2 ih2; rewrite read_eassert_Pand => hsub.
by rewrite ih1 ?ih2 //; SvD.fsetdec.
Qed.

Lemma rename_map_write_aux xs ys vs m (s t s' t' : estate) :
  [seq vtype (v_var y) | y <- ys] = [seq vtype (v_var x) | x <- xs] ->
  uniq [seq v_var y | y <- ys] ->
  (forall z y, Mvar.get m z = Some y ->
     vtype y = vtype z /\ Vm.get (sm := partial) (evm t) y = Vm.get (sm := partial) (evm s) z) ->
  (forall z y, Mvar.get m z = Some y -> y \notin [seq v_var y | y <- ys]) ->
  write_vars true xs vs s = ok s' -> write_vars true ys vs t = ok t' ->
  forall z y,
    Mvar.get (foldl (fun m xy => Mvar.set m (v_var xy.1) (v_var xy.2)) m (zip xs ys)) z = Some y ->
    vtype y = vtype z /\ Vm.get (sm := partial) (evm t') y = Vm.get (sm := partial) (evm s') z.
Proof.
elim: xs ys vs m s t => [ | x xs ih] [ | y ys] [ | v vs] //= m s t.
+ by move=> _ _ hm _ [<-] [<-].
move=> [hty htys] /andP [hy huniq] hm hnin.
t_xrbindP => s1 /write_varP [-> _ htrx] hxs t1 /write_varP [-> _ htry] hys.
apply: (ih _ _ _ _ _ htys huniq _ _ hxs hys).
+ move=> z y0; rewrite Mvar.setP; case: eqP => [<- [<-] | hne /[dup] /hm [hty0 heq] /hnin].
  + by rewrite /= !Vm.setP_eq hty.
  rewrite in_cons negb_or => /andP [hy0 _] /=.
  by rewrite !Vm.setP_neq //; [apply/eqP | rewrite eq_sym].
move=> z y0; rewrite Mvar.setP; case: eqP => [_ [<-] // | _ /hnin].
by rewrite in_cons negb_or => /andP [].
Qed.

Lemma rename_map_dom_aux xs ys m z :
  size xs = size ys ->
  (Sv.In z (vars_l xs) \/ Mvar.get m z <> None) ->
  Mvar.get (foldl (fun m xy => Mvar.set m (v_var xy.1) (v_var xy.2)) m (zip xs ys)) z <> None.
Proof.
elim: xs ys m => [ | x xs ih] [ | y ys] //= m.
+ by move=> _ [ | //]; clear; SvD.fsetdec.
move=> [hsize] h; apply ih => //.
case: h => [/SvD.F.add_iff [<- | hin] | hm]; [right | by left | right].
+ by rewrite Mvar.setP_eq.
by rewrite Mvar.setP; case: eqP.
Qed.

(* Writing the same values in the variables [xs] of one state and in their
   renamings [ys] in another: the renamed variables hold the values of the
   original ones. *)
Lemma rename_map_write xs ys vs (s t s' t' : estate) :
  [seq vtype (v_var y) | y <- ys] = [seq vtype (v_var x) | x <- xs] ->
  uniq [seq v_var y | y <- ys] ->
  write_vars true xs vs s = ok s' -> write_vars true ys vs t = ok t' ->
  ren_on (rename_map xs ys) (vars_l xs) (evm t') (evm s').
Proof.
move=> hty hu hxs hys z hz.
have hsz : size xs = size ys by rewrite -(size_map (fun x : var_i => vtype x) xs) -hty size_map.
rewrite /rename_map.
case h : Mvar.get => [y | ]; last by have := rename_map_dom_aux (m := Mvar.empty var) hsz (or_introl hz); rewrite h.
have := rename_map_write_aux hty hu _ _ hxs hys h.
by apply => ??; rewrite Mvar.get0.
Qed.

Context {wa : WithAssert} {sm : SemMode}.

(* The copies [xs := es] write in [xs] the values of [es] truncated. *)
Lemma copy_esP (p : uprog) ev ii xs tys es (t t1 : estate) :
  (forall x, Sv.In x (vars_l xs) -> ~ Sv.In x (read_es es)) ->
  size xs = size es -> size tys = size es ->
  esem p ev (copy_es ii xs tys es) t = ok t1 ->
  exists2 vs, sem_pexprs true (p_globs p) t es = ok vs &
    exists2 vargs, mapM2 ErrType truncate_val (map eval_atype tys) vs = ok vargs &
      write_vars true xs vargs t = ok t1.
Proof.
elim: xs tys es t => [ | x xs ih] [ | ty tys] [ | e es] // t hdisj.
+ by move=> _ _ [<-]; exists [::] => //; exists [::].
move=> /succn_inj hsx /succn_inj hst.
have -> : copy_es ii (x :: xs) (ty :: tys) (e :: es) = MkI ii (Cassgn (Lvar x) AT_none ty e) :: copy_es ii xs tys es by [].
rewrite esem_cons /= /sem_assgn; t_xrbindP => t' v he v' htr hw hc.
have [ | vs hvs [vargs hvargs hws]] := ih _ _ _ _ hsx hst hc.
+ move=> z hz hin; apply: (hdisj z).
  + by rewrite /=; SvD.fsetdec.
  by rewrite read_es_cons; SvD.fsetdec.
have hes : sem_pexprs true (p_globs p) t es = ok vs.
+ rewrite -hvs; move: hw => /write_varP [-> _ _].
  apply: eq_on_sem_pexprs.
  + done.
  move=> z hz /=.
  apply: Vm.get_eq_mode => //; rewrite Vm.setP_neq //; apply/eqP => ?; subst z.
  by apply: (hdisj x); [rewrite /=; SvD.fsetdec | rewrite read_es_cons; SvD.fsetdec].
rewrite he hes /=; eexists; first reflexivity.
rewrite /= htr hvargs /=; eexists; first reflexivity.
by rewrite /= hw.
Qed.

(* Conversely, the copies run when the values of [es] can be truncated to
   the types of [xs]. *)
Lemma copy_es_ok (p : uprog) ev ii xs tys es vs vargs (t : estate) :
  (forall x, Sv.In x (vars_l xs) -> ~ Sv.In x (read_es es)) ->
  [seq vtype (v_var x) | x <- xs] = tys ->
  sem_pexprs true (p_globs p) t es = ok vs ->
  mapM2 ErrType truncate_val (map eval_atype tys) vs = ok vargs ->
  exists2 t1, esem p ev (copy_es ii xs tys es) t = ok t1 & write_vars true xs vargs t = ok t1.
Proof.
move=> hdisj <-.
elim: xs es vs vargs t hdisj => [ | x xs ih] [ | e es] vs vargs t hdisj.
+ by move=> [<-] [<-]; exists t.
+ by rewrite /=; t_xrbindP => v _ vs' _ <-.
+ by move=> [<-].
have -> : copy_es ii (x :: xs) [seq vtype (v_var x) | x <- x :: xs] (e :: es) = MkI ii (Cassgn (Lvar x) AT_none (vtype x) e) :: copy_es ii xs [seq vtype (v_var x) | x <- xs] es by [].
rewrite /=; t_xrbindP => v he vs' hes.
move=> <-; t_xrbindP => v' htr vargs' hvargs <-.
rewrite he /= htr /=.
have hw : write_var true x v' t = ok (with_vm t (evm t).[x <- v']).
+ apply write_var_truncate; first by apply: truncate_val_DB htr.
  by rewrite -(truncate_val_has_type htr); apply truncatable_type_of.
rewrite hw /=.
apply: ih _ hvargs.
+ move=> z hz hin; apply: (hdisj z).
  + by rewrite /=; SvD.fsetdec.
  by rewrite read_es_cons; SvD.fsetdec.
rewrite -hes; apply: eq_on_sem_pexprs => // z hz /=.
apply: Vm.get_eq_mode => //; rewrite Vm.setP_neq //; apply/eqP => ?; subst z.
by apply: (hdisj x); [rewrite /=; SvD.fsetdec | rewrite read_es_cons; SvD.fsetdec].
Qed.

(* The destinations of a call written in the target, each a variable or a
   fresh variable for [_], and in the source. *)
Lemma dests_write_ts gd X Y a lvs ds vs (t s t' : estate) :
  Sv.Subset Y X ->
  List.Forall2 (dest_of X a) lvs ds ->
  st_eq_on Y t s ->
  write_lvals true gd t [seq Lvar x | x <- ds] vs = ok t' ->
  exists2 s', write_lvals true gd s lvs vs = ok s' & st_eq_on Y t' s'.
Proof.
move=> hYX hds; elim: hds vs t s => [ | lv d lvs' ds' hd _ ih] [ | v vs] t s hts //=.
+ by move=> [<-]; exists s.
t_xrbindP => t1 hw1 hws.
case: hd => [-> | [[vi ->] hdX _]] /=.
+ move: hw1 => /write_varP [? hdb htr]; subst t1.
  rewrite (write_var_truncate hdb htr) /=.
  apply: ih hws; case: hts => h1 h2 h3; split => //= z hz.
  by rewrite !Vm.setP; case: eqP => // _; apply h3.
move: hw1 => /write_varP [? hdb htr]; subst t1.
rewrite /write_none hdb htr /=.
apply: ih hws; case: hts => h1 h2 h3; split => //= z hz.
rewrite Vm.setP_neq; first by apply h3.
apply/eqP => ?; subst z; move: hz hYX hdX; clear; SvD.fsetdec.
Qed.

Lemma dests_write_st gd X Y a lvs ds vs (s t s' : estate) :
  Sv.Subset Y X ->
  List.Forall2 (dest_of X a) lvs ds ->
  st_eq_on Y s t ->
  write_lvals true gd s lvs vs = ok s' ->
  exists2 t', write_lvals true gd t [seq Lvar x | x <- ds] vs = ok t' & st_eq_on Y s' t'.
Proof.
move=> hYX hds; elim: hds vs t s => [ | lv d lvs' ds' hd _ ih] [ | v vs] t s hts //=.
+ by move=> [<-]; exists t.
t_xrbindP => s1 hw1 hws.
case: hd hw1 => [-> | [[vi ->] hdX _]] /=.
+ move=> /write_varP [? hdb htr]; subst s1.
  rewrite (write_var_truncate hdb htr) /=.
  apply: ih hws; case: hts => h1 h2 h3; split => //= z hz.
  by rewrite !Vm.setP; case: eqP => // _; apply h3.
rewrite /write_none; t_xrbindP => htr hdb ?; subst s1.
rewrite (write_var_truncate hdb htr) /=.
apply: ih hws; case: hts => h1 h2 h3; split => //= z hz.
rewrite Vm.setP_neq; first by apply h3.
apply/eqP => ?; subst z; move: hz hYX hdX; clear; SvD.fsetdec.
Qed.

Lemma write_vars_eq_on2 xs vs (s1 s2 s1' s2' : estate) Z :
  write_vars true xs vs s1 = ok s1' -> write_vars true xs vs s2 = ok s2' ->
  evm s1 =[Z] evm s2 -> evm s1' =[Sv.union (vars_l xs) Z] evm s2'.
Proof.
elim: xs vs s1 s2 Z => [ | x xs ih] [ | v vs] //= s1 s2 Z.
+ by move=> [<-] [<-] h z hz; apply h; clear -hz; SvD.fsetdec.
t_xrbindP => t1 /write_varP [-> _ _] h1 t2 /write_varP [-> _ _] h2 heq.
have := ih _ _ _ (Sv.add x Z) h1 h2.
move=> h; apply: eq_onI (h _); first by clear; SvD.fsetdec.
move=> z hz /=; rewrite !Vm.setP; case: eqP => // hne; apply heq; clear -hz hne; SvD.fsetdec.
Qed.

Lemma write_vars_scs_mem wdb xs vs (s s' : estate) :
  write_vars wdb xs vs s = ok s' -> escs s' = escs s /\ emem s' = emem s.
Proof.
elim: xs vs s => [ | x xs ih] [ | v vs] //= s; first by move=> [<-].
by t_xrbindP => s1 /write_varP [-> _ _] /ih [-> ->].
Qed.

Lemma write_vars_rename_ok xs ys vs (s s' t : estate) :
  [seq vtype (v_var y) | y <- ys] = [seq vtype (v_var x) | x <- xs] ->
  write_vars true xs vs s = ok s' -> exists t', write_vars true ys vs t = ok t'.
Proof.
elim: xs ys vs s t => [ | x xs ih] [ | y ys] [ | v vs] //= s t; first by move=> _ _; exists t.
move=> [hty htys]; t_xrbindP => s1 /write_varP [-> hdb htr] /(ih _ _ _ (with_vm t (evm t).[y <- v]) htys) [t' ht'].
by rewrite write_var_truncate ?hty //=; exists t'.
Qed.

Lemma get_var_is_partial wdb vm xs vs :
  get_var_is (sm := partial) wdb vm xs = ok vs -> List.forallb is_defined vs ->
  get_var_is (sm := sm) wdb vm xs = ok vs.
Proof.
elim: xs vs => [ | x xs ih] vs /=; first by move=> [<-].
t_xrbindP => v hv vs' /ih{}ih <- /= /andP [hd /ih ->].
move: hv; rewrite /get_var; t_xrbindP => _ hv.
have heq : Vm.get (sm := sm) vm x = v by rewrite Vm.get_modeE hv hd andbF.
by rewrite heq hd orbT.
Qed.

(* The variables written read back the values written, when they are
   pairwise distinct and the values are defined and of their types. *)
Lemma write_vars_read gd xs vs (s s' : estate) :
  uniq [seq v_var x | x <- xs] ->
  List.map type_of_val vs = [seq eval_atype (vtype (v_var x)) | x <- xs] ->
  List.forallb is_defined vs ->
  write_vars true xs vs s = ok s' ->
  sem_pexprs true gd s' [seq Plvar x | x <- xs] = ok vs.
Proof.
move=> hu htys hdef hw; rewrite sem_pexprs_get_var; apply get_var_is_partial => //.
elim: xs vs s hu htys hdef hw => [ | x xs ih] [ | v vs] //= s.
move=> /andP [hx hu] [htv htvs] /andP [hdv hdvs]; t_xrbindP => s1 /write_varP [-> hdb htr] hw.
rewrite (write_vars_get_varP_neq _ _ hw); last first.
+ move: hx; elim: (xs) => //= y ys ihy; rewrite in_cons negb_or => /andP [h1 /ihy ->]; rewrite eq_sym h1.
  done.
rewrite /= get_var_eq //= hdv /= (ih _ _ hu htvs hdvs hw) /= vm_truncate_val_eq //.
Qed.

Lemma mapM2_truncate_defined tys vs vargs :
  mapM2 ErrType truncate_val tys vs = ok vargs -> List.forallb is_defined vargs.
Proof.
elim: tys vs vargs => [ | ty tys ih] [ | v vs] vargs //=; first by move=> [<-].
by t_xrbindP => v' /truncate_val_defined hd vargs' /ih hds <- /=; rewrite hd.
Qed.

Lemma mapM2_truncate_idem tys vs vargs :
  mapM2 ErrType truncate_val tys vs = ok vargs -> mapM2 ErrType truncate_val tys vargs = ok vargs.
Proof.
elim: tys vs vargs => [ | ty tys ih] [ | v vs] vargs //=; first by move=> [<-].
by t_xrbindP => v' /truncate_val_idem hv vargs' /ih hvs <- /=; rewrite hv hvs.
Qed.

End RENAME.

Lemma all2_vtype (xs : seq var_i) tys :
  all2 (fun (x : var_i) ty => vtype x == ty) xs tys -> [seq vtype (v_var x) | x <- xs] = tys.
Proof. by elim: xs tys => [ | x xs ih] [ | ty tys] //= /andP [/eqP -> /ih ->]. Qed.

Section CHECK.

Context {asm_op : Type} {asmop : asmOp asm_op}.

Lemma check_contractP (fd : ufundef) ci :
  check_contract fd = ok tt -> f_contract fd = Some ci ->
  [/\ [seq vtype (v_var x) | x <- f_iparams ci] = f_tyin fd,
      [seq vtype (v_var x) | x <- f_ires ci] = f_tyout fd,
      [seq vtype (v_var x) | x <- f_params fd] = f_tyin fd,
      uniq [seq v_var x | x <- f_params fd],
      size (f_ires ci) = size (f_res fd),
      (forall a, List.In a (f_pre ci) -> Sv.Subset (read_eassert a.2) (vars_l (f_iparams ci))),
      (forall a, List.In a (f_post ci) -> Sv.Subset (read_eassert a.2) (contract_vars ci))
    & disjoint (contract_vars ci) (vars_fd fd)].
Proof.
move=> + hci; rewrite /check_contract hci; t_xrbindP.
have hread : forall X (l : seq assertion), Sv.subset (read_easserts [seq a.2 | a <- l]) X ->
  forall a, List.In a l -> Sv.Subset (read_eassert a.2) X.
+ move=> X; elim => [ | a l ih] //= /Sv.subset_spec; rewrite read_easserts_cons => hsub a' [<- | hin].
  + by clear -hsub; SvD.fsetdec.
  by apply: ih hin; apply/Sv.subset_spec; clear -hsub; SvD.fsetdec.
move=> /and5P [/all2_vtype -> /all2_vtype -> /all2_vtype -> -> /and5P [_ /eqP -> /hread hpre /hread hpost ->]].
by split.
Qed.

Context (fresh_var_ident : v_kind -> instr_info -> string -> atype -> Ident.ident) (p : _uprog).

(* The variables the pass treats as the variables of a function. *)
Definition c2a_X (fd : ufundef) := Sv.union (vars_fd fd) (oapp contract_vars Sv.empty fd.(f_contract)).

Lemma c2a_fdP (fd fd' : ufundef) :
  contracts_to_asserts_fd fresh_var_ident p fd = ok fd' ->
  exists acc body',
  [/\ c2a_c (c2a_i fresh_var_ident p (c2a_X fd)) Sv.empty (f_body fd) = ok (acc, body'),
      [/\ f_info fd' = f_info fd, f_contract fd' = f_contract fd, f_tyin fd' = f_tyin fd,
          f_params fd' = f_params fd, f_tyout fd' = f_tyout fd, f_res fd' = f_res fd
        & f_extra fd' = f_extra fd]
    & exists ii,
      f_body fd' =
        if f_contract fd is Some ci then
          copy_es ii ci.(f_iparams) fd.(f_tyin) (map Plvar fd.(f_params))
          ++ assert_all ii ci.(f_pre)
          ++ body'
          ++ copy_es ii ci.(f_ires) fd.(f_tyout) (map Plvar fd.(f_res))
          ++ assert_all ii ci.(f_post)
        else body'].
Proof.
rewrite /contracts_to_asserts_fd; t_xrbindP => -[acc body'] hc hfd.
exists acc, body'; split => //.
+ by case hci: f_contract hfd => [ci | ] [<-]; split => //=; rewrite hci.
case hci: f_contract hfd => [ci | ] [<-] /=; last by exists dummy_instr_info.
by eexists; reflexivity.
Qed.

Context (p' : _uprog) (Hp : contracts_to_asserts_prog fresh_var_ident p = ok p').

Lemma c2a_prog_inv :
  [/\ map_cfprog (contracts_to_asserts_fd fresh_var_ident p) (p_funcs p) = ok (p_funcs p'),
      p_globs p' = p_globs p, p_extra p' = p_extra p
    & forall fn fd, get_fundef (p_funcs p) fn = Some fd -> check_contract fd = ok tt].
Proof using Hp.
move: Hp; rewrite /contracts_to_asserts_prog; t_xrbindP => hall funcs hfuncs <-; split => //.
move=> fn fd hfd.
have := allMP (get_fundef_in' hfd) hall.
by rewrite /add_funname /add_finfo /=; case: check_contract => [[] | ].
Qed.

Lemma c2a_get_fundef fn :
  if get_fundef (p_funcs p) fn is Some fd then
    exists2 fd', contracts_to_asserts_fd fresh_var_ident p fd = ok fd' & get_fundef (p_funcs p') fn = Some fd'
  else get_fundef (p_funcs p') fn = None.
Proof using Hp.
apply: get_map_cfprog_name_gen_aux.
by case: c2a_prog_inv => H _ _ _; exact H.
Qed.

End CHECK.

Section CONTRACT_SEM.

Context
  {asm_op syscall_state : Type} {ep : EstateParams syscall_state}
  {spp : SemPexprParams} {sip : SemInstrParams asm_op syscall_state}.

Lemma mapM_sem_assertP gd (s : estate) (l : seq assertion) :
  (exists vs, mapM (sem_assert (wa := withassert) gd s) l = ok vs) <->
  (forall a, List.In a l -> sem_eassert gd s a.2 = ok true).
Proof.
elim: l => [ | a l ih] /=; first by split => // _; exists [::].
rewrite /sem_assert /=; split.
+ move=> [vs]; t_xrbindP.
  move=> b hb hbt _ vs' hvs _ a' [<- | hin]; first by case: b hb hbt.
  by apply ih => //; exists vs'.
move=> h; have [vs hvs] := ih.2 (fun a' ha' => h a' (or_intror ha')).
move: hvs; rewrite /sem_assert /= => ->.
by rewrite (h a (or_introl erefl)) /=; eexists.
Qed.

Lemma sem_preE (P : uprog) fn fs fd ci :
  get_fundef (p_funcs P) fn = Some fd -> f_contract fd = Some ci ->
  sem_pre (wa := withassert) P fn fs = ok tt <->
  exists vargs Sp,
    [/\ mapM2 ErrType truncate_val (map eval_atype (f_tyin fd)) (fvals fs) = ok vargs,
        write_vars true (f_iparams ci) vargs (Estate (fscs fs) (fmem fs) Vm.init) = ok Sp
      & forall a, List.In a (f_pre ci) -> sem_eassert (p_globs P) Sp a.2 = ok true].
Proof.
rewrite /sem_pre /= => -> -> /=; split.
+ rewrite /dc_truncate_val /=; t_xrbindP => vargs hvargs Sp hSp vs hvs _.
  by exists vargs, Sp; split => //; apply mapM_sem_assertP; exists vs.
move=> [vargs [Sp [hvargs hSp hpre]]].
rewrite /dc_truncate_val /= hvargs /= hSp /=.
by have [vs ->] := (mapM_sem_assertP _ _ _).2 hpre.
Qed.

Lemma sem_postE (P : uprog) fn vs fr fd ci :
  get_fundef (p_funcs P) fn = Some fd -> f_contract fd = Some ci ->
  sem_post (wa := withassert) P fn vs fr = ok tt <->
  exists vargs Sp Sq,
    [/\ mapM2 ErrType truncate_val (map eval_atype (f_tyin fd)) vs = ok vargs,
        write_vars true (f_iparams ci) vargs (Estate (fscs fr) (fmem fr) Vm.init) = ok Sp,
        write_vars true (f_ires ci) (fvals fr) Sp = ok Sq
      & forall a, List.In a (f_post ci) -> sem_eassert (p_globs P) Sq a.2 = ok true].
Proof.
rewrite /sem_post /= => -> -> /=; split.
+ rewrite /dc_truncate_val /=; t_xrbindP => vargs hvargs Sp hSp Sq hSq vs' hvs _.
  by exists vargs, Sp, Sq; split => //; apply mapM_sem_assertP; exists vs'.
move=> [vargs [Sp [Sq [hvargs hSp hSq hpost]]]].
rewrite /dc_truncate_val /= hvargs /= hSp /= hSq /=.
by have [vs' ->] := (mapM_sem_assertP _ _ _).2 hpost.
Qed.

End CONTRACT_SEM.

Section TGT_SRC.

Context
  {asm_op syscall_state : Type} {ep : EstateParams syscall_state}
  {spp : SemPexprParams} {sip : SemInstrParams asm_op syscall_state} {sm : SemMode}
  {E E0 : Type -> Type} {wE : with_Error E E0} {rE : EventRels E0}.

Context (fresh_var_ident : v_kind -> instr_info -> string -> atype -> Ident.ident).
Context (p p' : prog) (ev : extra_val_t).
Hypothesis Hp : contracts_to_asserts_prog fresh_var_ident p = ok p'.

(* The target receives the arguments of the source, or their truncations; on
   the source side, the precondition of the callee holds. *)
Definition pre_ts (fn : funname) (ft fs : fstate) :=
  [/\ fscs ft = fscs fs, fmem ft = fmem fs &
      forall fd, get_fundef (p_funcs p) fn = Some fd ->
        mapM2 ErrType truncate_val (map eval_atype (f_tyin fd)) (fvals ft) =
        mapM2 ErrType truncate_val (map eval_atype (f_tyin fd)) (fvals fs) /\
        sem_pre (wa := withassert) p fn fs = ok tt].

Definition spec_ts : EquivSpec :=
  {| rpreF_ := fun fn1 fn2 ft fs => fn1 = fn2 /\ pre_ts fn1 ft fs
   ; rpostF_ := fun fn1 fn2 ft fs frt frs =>
       frt = frs /\ sem_post (wa := withassert) p fn1 (fvals fs) frs = ok tt |}.

Lemma eq_globs_ts : p_globs p' = p_globs p.
Proof using Hp. by case: (c2a_prog_inv Hp). Qed.

#[local] Lemma checker_st_eq_onP_ts : Checker_eq p' p checker_st_eq_on.
Proof using Hp. by apply checker_st_eq_onP; rewrite eq_globs_ts. Qed.

#[local] Lemma checker_a_st_eq_onP_ts : Checker_a_eq p' p checker_a_st_eq_on.
Proof using Hp. by apply checker_a_st_eq_onP; rewrite eq_globs_ts. Qed.

#[local] Hint Resolve checker_st_eq_onP_ts checker_a_st_eq_onP_ts : core.

(* The arguments of a call: [es] in the source, their truncated copies [ip]
   in the target. *)
Definition args_ts (es : pexprs) (tyin : seq atype) (ip : seq var_i) (t s : estate) vs vargs :=
  [/\ sem_pexprs true (p_globs p) s es = ok vs,
      mapM2 ErrType truncate_val (map eval_atype tyin) vs = ok vargs
    & sem_pexprs true (p_globs p') t [seq Plvar x | x <- ip] = ok vargs].

Definition copied_ts Y es tyin (ci : fun_contract) ip (t s : estate) :=
  st_eq_on Y t s /\ exists vs vargs, args_ts es tyin ip t s vs vargs /\
    exists2 Sp, write_vars true (f_iparams ci) vargs (Estate (escs s) (emem s) Vm.init) = ok Sp &
      ren_on (rename_map (f_iparams ci) ip) (vars_l (f_iparams ci)) (evm t) (evm Sp).

Definition checked_ts Y f es tyin ip (t s : estate) :=
  st_eq_on Y t s /\ exists vs vargs, args_ts es tyin ip t s vs vargs /\
    sem_pre (wa := withassert) p f (mk_fstate vs s) = ok tt.

Lemma c2a_call_ts X Y ii lvs f es fd ci acc acc' c' :
  get_fundef (p_funcs p) f = Some fd -> f_contract fd = Some ci ->
  Sv.Subset (vars_I (MkI ii (Ccall lvs f es))) Y -> Sv.Subset Y X ->
  call_with_contract fresh_var_ident ii X acc lvs f es (f_tyin fd) ci = ok (acc', c') ->
  wequiv_rec (wa1 := withassert_nocontract) (wa2 := withassert) p' p ev ev spec_ts
    (st_eq_on Y) c' [:: MkI ii (Ccall lvs f es)] (st_eq_on Y).
Proof using Hp.
move=> hfd hci hsub hYX /call_with_contractP [ip [ds [-> hsize htyip hipX htyds hds huniq]]].
have [_ _ _ hchk] := c2a_prog_inv Hp.
have [htyi htyo htyp hup _ hpre hpost hdisj] := check_contractP (hchk _ _ hfd) hci.
rewrite vars_I_call in hsub.
have huniq' := huniq ltac:(rewrite /vars_lvals in hsub; clear -hsub hYX; SvD.fsetdec).
rewrite -[[:: MkI ii (Ccall lvs f es)]]cat0s.
apply wequiv_cat with (copied_ts Y es (f_tyin fd) ci ip).
+ apply wequiv_basic_esem.
  + rewrite /copy_es; elim: (ip) (zip _ _) => [ | ? ? ih] [ | ? ?] //=.
  move=> t s t1 hts hcp.
  have hdis : forall x, Sv.In x (vars_l ip) -> ~ Sv.In x (read_es es).
  + by move=> x /hipX hx hx'; apply hx; clear -hx' hsub hYX; SvD.fsetdec.
  have hsip : size ip = size es by rewrite hsize -(size_map (fun x : var_i => vtype x)) htyip size_map.
  have hsty : size (f_tyin fd) = size es by rewrite hsize -htyi size_map.
  have [vs hvs [vargs hvargs hw]] := copy_esP hdis hsip hsty hcp.
  have hout : evm t =[Y] evm t1.
  + move=> z hz; apply: (write_vars_eq_ex hw); move=> /sv_of_listP /vars_lP /hipX; apply.
    by clear -hz hYX; SvD.fsetdec.
  have [hscs hmem] := write_vars_scs_mem hw.
  case: (hts) => hts1 hts2 hts3.
  have hes : sem_pexprs true (p_globs p) s es = ok vs.
  + rewrite -hvs eq_globs_ts; apply: eq_on_sem_pexprs => //.
    apply/eq_on_mode.
    by move=> z hz; symmetry; apply hts3; clear -hz hsub; SvD.fsetdec.
  exists s => //; split.
  + split; [by rewrite hscs | by rewrite hmem | move=> z hz; rewrite -(hout z hz); exact: hts3].
  have hui : uniq [seq v_var x | x <- ip] by move: huniq'; rewrite map_cat cat_uniq => /andP [].
  exists vs, vargs; split; first split => //.
  + apply: write_vars_read hui _ (mapM2_truncate_defined hvargs) hw.
    rewrite (mapM2_truncate_val_has_type hvargs) -htyi.
    by rewrite -htyip -map_comp.
  have [Sp hSp] := write_vars_rename_ok (Estate (escs s) (emem s) Vm.init) (esym htyip) hw.
  by exists Sp => //; apply: rename_map_write htyip hui hSp hw.
rewrite -[[:: MkI ii (Ccall lvs f es)]]cat0s.
apply wequiv_cat with (checked_ts Y f es (f_tyin fd) ip).
+ apply wequiv_asserts_left => // t s [hts [vs [vargs [hargs [Sp hSp hren]]]]] hasserts.
  split => //; exists vs, vargs; split => //.
  apply (sem_preE _ hfd hci); exists vargs, Sp; split => //; first by case: hargs.
  move=> a ha; have := hasserts _ (List.in_map (rename_assertion (rename_map (f_iparams ci) ip)) _ _ ha).
  rewrite eq_globs_ts /=.
  rewrite (rename_eassertP _ _ hren (hpre _ ha)) //.
  by case: hts => _ -> _; have [_ ->] := write_vars_scs_mem hSp.
rewrite -[[:: MkI ii (Ccall lvs f es)]]cats0 -cat1s.
apply wequiv_cat with (st_eq_on Y); last by apply wequiv_asserts_left.
apply: wkequiv_eq_pred => t0 s0 [hts [vs [vargs [[hes hvargs hip] hpre_s]]]].
apply wequiv_call_wa with (Pf := rpreF (eS := spec_ts)) (Qf := rpostF (eS := spec_ts))
  (Rv := fun vs1 vs2 => vs1 = vargs /\ vs2 = vs).
+ by move=> _ _ vs1 [-> ->] /=; rewrite hip => -[<-]; exists vs.
+ by move=> _ _ _ _ [-> ->] [-> ->].
+ move=> _ _ _ _ [-> ->] [-> ->]; split => //; split => //=.
  1,2: by case: hts.
  move=> fd0; rewrite hfd => -[<-]; split => //.
  by rewrite hvargs (mapM2_truncate_idem hvargs).
+ by move=> fs1 fs2 fr1 fr2 _ [_ ->].
+ exact: (@wequiv_fun_rec _ _ _ _ _ _ _ _ _ _ p' p ev ev spec_ts ii ii f f).
move=> fs1 fs2 fr1 fr2 _ [<- _] t s t' [-> ->]; rewrite /upd_estate /= eq_globs_ts => hw.
apply: (dests_write_ts hYX hds _ hw).
by case: hts => h1 h2 h3; split.
Qed.

Lemma c2a_call_nc_ts Y ii lvs f es fd :
  get_fundef (p_funcs p) f = Some fd -> f_contract fd = None ->
  Sv.Subset (vars_I (MkI ii (Ccall lvs f es))) Y ->
  wequiv_rec (wa1 := withassert_nocontract) (wa2 := withassert) p' p ev ev spec_ts
    (st_eq_on Y) [:: MkI ii (Ccall lvs f es)] [:: MkI ii (Ccall lvs f es)] (st_eq_on Y).
Proof using Hp.
move=> hfd hci; rewrite vars_I_call /vars_lvals => hsub.
have hpre : forall vs (s : estate), sem_pre (wa := withassert) p f (mk_fstate vs s) = ok tt.
+ by move=> vs s; rewrite /sem_pre /= hfd hci.
apply wequiv_call_wa with (Pf := rpreF (eS := spec_ts)) (Qf := rpostF (eS := spec_ts)) (Rv := eq).
+ rewrite eq_globs_ts; apply read_es_st_eq_on; clear -hsub; SvD.fsetdec.
+ by move=> *; apply hpre.
+ move=> t s vs _ [h1 h2 _] <-; split => //; split => //= fd0 hfd0; split => //; exact: hpre.
+ by move=> > _ [_ ->].
+ exact: (@wequiv_fun_rec _ _ _ _ _ _ _ _ _ _ p' p ev ev spec_ts ii ii f f).
move=> fs1 fs2 fr1 fr2 _ [<- _]; rewrite /upd_estate eq_globs_ts => t s t' [h1 h2 h3] hw.
have hrd : Sv.Subset (read_rvs lvs) Y by clear -hsub; SvD.fsetdec.
have [|s' hs' hst] := write_lvals_st_eq_on hrd (i1 := with_scs (with_mem t (fmem fr1)) (fscs fr1)) (i2 := with_scs (with_mem s (fmem fr1)) (fscs fr1)) _ hw.
+ by split.
exists s' => //; apply: st_rel_weaken hst => ??; apply eq_onI; clear; SvD.fsetdec.
Qed.

Let Pi_ts (i : instr) :=
  forall X Y acc acc' c', Sv.Subset (vars_I i) Y -> Sv.Subset Y X ->
  c2a_i fresh_var_ident p X acc i = ok (acc', c') ->
  wequiv_rec (wa1 := withassert_nocontract) (wa2 := withassert) p' p ev ev spec_ts
    (st_eq_on Y) c' [:: i] (st_eq_on Y).

Let Pr_ts (ir : instr_r) := forall ii, Pi_ts (MkI ii ir).

Let Pc_ts (c : cmd) :=
  forall X Y acc acc' c', Sv.Subset (vars_c c) Y -> Sv.Subset Y X ->
  c2a_c (c2a_i fresh_var_ident p X) acc c = ok (acc', c') ->
  wequiv_rec (wa1 := withassert_nocontract) (wa2 := withassert) p' p ev ev spec_ts
    (st_eq_on Y) c' c (st_eq_on Y).

Lemma c2a_body_ts : forall c, Pc_ts c.
Proof using Hp.
apply (cmd_rect (Pr := Pr_ts) (Pi := Pi_ts) (Pc := Pc_ts)).
+ done.
+ by move=> X Y acc acc' c' _ _ [_ <-]; apply wequiv_nil.
+ move=> i c Hi Hc X Y acc acc' c' hsub hYX /=.
  t_xrbindP => -[acc1 ci] hci -[acc2 cc] hcc _ <-.
  rewrite vars_c_cons in hsub.
  rewrite -cat1s; apply wequiv_cat with (st_eq_on Y).
  + by apply: (Hi _ _ _ _ _ _ hYX hci); clear -hsub; SvD.fsetdec.
  by apply: (Hc _ _ _ _ _ _ hYX hcc); clear -hsub; SvD.fsetdec.
{ move=> x tg ty e ii X Y acc acc' c' hsub _ [_ <-].
  rewrite vars_I_assgn /vars_lval in hsub.
  apply wequiv_assgn_rel_eq with checker_st_eq_on Y => //.
  all: by split; try done; rewrite /read_es /read_rvs /=; clear -hsub; SvD.fsetdec. }
{ move=> xs tg o es ii X Y acc acc' c' hsub _ [_ <-].
  rewrite vars_I_opn /vars_lvals in hsub.
  apply wequiv_opn_rel_eq with checker_st_eq_on Y => //.
  all: by split; try done; clear -hsub; SvD.fsetdec. }
{ move=> xs o es ii X Y acc acc' c' hsub _ [_ <-].
  rewrite vars_I_syscall /vars_lvals in hsub.
  apply wequiv_syscall_rel_eq_core with (ce := checker_st_eq_on) (d := Y) (de := Y).
  + exact: checker_st_eq_onP_ts.
  1,2: by split; try done; clear -hsub; SvD.fsetdec.
  exact: wrequiv_eq. }
{ move=> a ii X Y acc acc' c' hsub _ [_ <-].
  rewrite vars_I_assert in hsub.
  apply wequiv_assert_rel_eq with (ca := checker_a_st_eq_on) (d := Y) (de := Y) => //.
  by split; try done; clear -hsub; SvD.fsetdec. }
{ move=> e c1 c2 Hc1 Hc2 ii X Y acc acc' c' hsub hYX /=.
  t_xrbindP => -[acc1 c1'] hc1 -[acc2 c2'] hc2 _ <-.
  rewrite vars_I_if in hsub.
  apply wequiv_if_rel_eq with checker_st_eq_on Y Y Y => //.
  + by split; try done; clear -hsub; SvD.fsetdec.
  + by apply: (Hc1 _ _ _ _ _ _ hYX hc1); clear -hsub; SvD.fsetdec.
  by apply: (Hc2 _ _ _ _ _ _ hYX hc2); clear -hsub; SvD.fsetdec. }
{ move=> v dir lo hi c Hc ii X Y acc acc' c' hsub hYX /=.
  t_xrbindP => -[acc1 c1'] hc _ <-.
  rewrite vars_I_for in hsub.
  apply wequiv_for_rel_eq with checker_st_eq_on Y Y => //.
  + by split => //; rewrite /read_es /= read_eE; clear -hsub; SvD.fsetdec.
  + by split; try done; clear -hsub; SvD.fsetdec.
  by apply: (Hc _ _ _ _ _ _ hYX hc); clear -hsub; SvD.fsetdec. }
{ move=> a c e info c2 Hc Hc2 ii X Y acc acc' c'' hsub hYX /=.
  t_xrbindP => -[acc1 c1'] hc -[acc2 c2'] hc2 _ <-.
  rewrite vars_I_while in hsub.
  apply wequiv_while_rel_eq with checker_st_eq_on Y => //.
  + by split; try done; clear -hsub; SvD.fsetdec.
  + by apply: (Hc _ _ _ _ _ _ hYX hc); clear -hsub; SvD.fsetdec.
  by apply: (Hc2 _ _ _ _ _ _ hYX hc2); clear -hsub; SvD.fsetdec. }
move=> xs f es ii X Y acc acc' c' hsub hYX /=.
case hfd: get_fundef => [fd | //]; case hci: f_contract => [ci | ].
+ exact: c2a_call_ts hfd hci hsub hYX.
by move=> [_ <-]; apply: c2a_call_nc_ts hfd hci hsub.
Qed.

Lemma c2a_init_ts fn (fd fd' : ufundef) ft fs s :
  contracts_to_asserts_fd fresh_var_ident p fd = ok fd' ->
  get_fundef (p_funcs p) fn = Some fd -> pre_ts fn ft fs ->
  initialize_funcall p' ev fd' ft = ok s -> initialize_funcall p ev fd fs = ok s.
Proof using Hp.
move=> /c2a_fdP [_ [_ [_ [_ _ htyin hparams _ _ hextra] _]]] hfd [hscs hmem /(_ _ hfd) [htr _]].
rewrite /initialize_funcall htyin hparams hextra /estate0 hscs hmem /dc_truncate_val /= htr.
by [].
Qed.

Lemma finalize_eq_on (fd1 fd2 : ufundef) (t s : estate) fr :
  f_tyout fd1 = f_tyout fd2 -> f_res fd1 = f_res fd2 ->
  st_eq_on (vars_l (f_res fd1)) t s ->
  finalize_funcall fd1 t = ok fr -> finalize_funcall fd2 s = ok fr.
Proof.
move=> htyo hres [h1 h2 h3]; rewrite /finalize_funcall -htyo -hres; t_xrbindP => vs hvs vs' htr <-.
have -> : get_var_is (~~ direct_call) (evm s) (f_res fd1) = ok vs.
+ rewrite -hvs; elim: (f_res fd1) h3 => //= x xs ih h3.
  rewrite ih; last by move=> z hz; apply h3; rewrite /=; clear -hz; SvD.fsetdec.
  have hx : Vm.get (sm := sm) (evm s) x = Vm.get (sm := sm) (evm t) x.
  + by apply Vm.get_eq_mode => //; symmetry; apply h3; rewrite /=; clear; SvD.fsetdec.
  by rewrite /get_var hx.
by rewrite /= htr h1 h2.
Qed.

Lemma c2a_fun_ts fn :
  wiequiv_f (wa1 := withassert_nocontract) (wa2 := withassert) p' p ev ev
    (rpreF (eS := spec_ts)) fn fn (rpostF (eS := spec_ts)).
Proof using Hp.
apply wequiv_fun_ind_wa => {}fn _ ft fs [<- hpre] fd' hfd'.
move: (c2a_get_fundef Hp fn); case hfd: get_fundef => [fd | ]; last by rewrite hfd'.
move=> [fd'_ hc2a]; rewrite hfd' => -[?]; subst fd'_.
exists fd => // _.
have [_ _ /(_ _ hfd) [_ hpre_s]] := hpre.
split => // s hinit; exists s; first exact: c2a_init_ts hc2a hfd hpre hinit.
have [acc [body' [hbody [_ hcontr htyin hparams htyout hres hextra] [ii hb]]]] := c2a_fdP hc2a.
have [_ _ _ hchk] := c2a_prog_inv Hp.
move: hb hbody hcontr; rewrite /c2a_X; case hci: (f_contract fd) => [ci | ] /= hb hbody hcontr; last first.
+ exists (st_eq_on (vars_fd (pT := progUnit) fd)), (st_eq_on (vars_fd (pT := progUnit) fd)); split => //.
  + rewrite hb; apply: (c2a_body_ts _ _ hbody); rewrite /vars_fd; clear; SvD.fsetdec.
  + move=> t s0 fr hts hf; exists fr; last by split => //; rewrite /sem_post /= hfd hci.
    have hfin := finalize_eq_on htyout hres; apply: hfin hf; rewrite hres.
    by apply: st_rel_weaken hts => ??; apply eq_onI; rewrite /vars_fd; clear; SvD.fsetdec.
  by move=> ?? [].
have [htyi htyo htyp hup hsres hpreC hpostC hdisj] := check_contractP (hchk _ _ hfd) hci.
have [vargs [Sp [hvargs hSp hpreSp]]] := (sem_preE _ hfd hci).1 hpre_s.
have [_ _ /(_ _ hfd) [htr _]] := hpre.
move: hinit; rewrite /initialize_funcall htyin hparams /dc_truncate_val /= htr hvargs /= => hinit.
have hdz : forall z, Sv.In z (contract_vars ci) -> ~ Sv.In z (vars_fd (pT := progUnit) fd) by apply/disjointP.
exists (fun t s' => t = s /\ s' = s),
  (fun t s' => st_eq_on (vars_fd (pT := progUnit) fd) t s' /\
     forall fr, finalize_funcall fd' t = ok fr -> sem_post (wa := withassert) p fn (fvals fs) fr = ok tt).
split => //; last by move=> ?? [].
2: { move=> t s0 fr [hts hpo] hf; exists fr; last by split => //; apply hpo.
     have hfin := finalize_eq_on htyout hres; apply: hfin hf; rewrite hres.
     by apply: st_rel_weaken hts => ??; apply eq_onI; rewrite /vars_fd; clear; SvD.fsetdec. }
rewrite hb -[f_body fd]cat0s catA.
apply wequiv_cat with (fun t s' => st_eq_on (vars_fd (pT := progUnit) fd) t s' /\ evm t =[vars_l (f_iparams ci)] evm Sp).
+ rewrite -[[::]]cat0s.
  apply wequiv_cat with (fun t s' => st_eq_on (vars_fd (pT := progUnit) fd) t s' /\ evm t =[vars_l (f_iparams ci)] evm Sp); last by apply wequiv_asserts_left.
  apply wequiv_basic_esem.
  + rewrite /copy_es; elim: (f_iparams ci) (zip _ _) => [ | ? ? ih] [ | ? ?] //=.
  move=> t s0 t1 [-> ->] hcp.
  have hdis : forall x, Sv.In x (vars_l (f_iparams ci)) -> ~ Sv.In x (read_es [seq Plvar i | i <- f_params fd]).
  + move=> x hx; rewrite vars_l_read_es => hx'.
    apply: (hdz x); rewrite /contract_vars /vars_fd; clear -hx hx'; SvD.fsetdec.
  have hs1 : size (f_iparams ci) = size [seq Plvar i | i <- f_params fd].
  + by rewrite size_map -(size_map (fun x : var_i => vtype x)) htyi -htyp size_map.
  have hs2 : size (f_tyin fd) = size [seq Plvar i | i <- f_params fd] by rewrite size_map -htyp size_map.
  have [vs hvs [vargs' hvargs' hw]] := copy_esP hdis hs1 hs2 hcp.
  have hrd : sem_pexprs true (p_globs p') s [seq Plvar i | i <- f_params fd] = ok vargs.
  + apply: write_vars_read hup _ (mapM2_truncate_defined hvargs) hinit.
    by rewrite (mapM2_truncate_val_has_type hvargs) -htyp -map_comp.
  move: hvs; rewrite hrd => -[?]; subst vs.
  move: hvargs'; rewrite (mapM2_truncate_idem hvargs) => -[?]; subst vargs'.
  exists s => //; split.
  + have [h1 h2] := write_vars_scs_mem hw.
    split => // z hz.
    rewrite -(write_vars_eq_ex hw) // => /sv_of_listP /vars_lP hz'.
    by apply: (hdz z) hz; rewrite /contract_vars; clear -hz'; SvD.fsetdec.
  have := write_vars_eq_on2 (Z := Sv.empty) hw hSp.
  move=> /(_ ltac:(by move=> ?; clear; SvD.fsetdec)) h z hz; apply h; clear -hz; SvD.fsetdec.
rewrite -[f_body fd]cats0.
apply wequiv_cat with (fun t s' => st_eq_on (vars_fd (pT := progUnit) fd) t s' /\ evm t =[vars_l (f_iparams ci)] evm Sp).
+ have hb' := c2a_body_ts (c := f_body fd) (X := Sv.union (vars_fd (pT := progUnit) fd) (contract_vars ci)) (Y := vars_fd (pT := progUnit) fd) ltac:(rewrite /vars_fd; clear; SvD.fsetdec) ltac:(clear; SvD.fsetdec) hbody.
  have hwr := c2a_write hbody.
  apply: wkequiv_eq_pred => t0 s0 [h0 hIP].
  have := wequiv_write1 hb' (s1_ := t0).
  move=> h; eapply wkequiv_weaken; last exact h.
  1,2: by [].
  + by move=> ?? [-> ->].
  move=> _ _ o1 o2 _ [hex hst]; split => // z hz.
  rewrite -hIP // hex //.
  move=> /hwr [hw | hX].
  + by apply: (hdz z); rewrite /contract_vars /vars_fd /vars_c; clear -hz hw; SvD.fsetdec.
  by apply: hX; rewrite /contract_vars; clear -hz; SvD.fsetdec.
rewrite -[[::]]cat0s.
apply wequiv_cat with (fun t s' => st_eq_on (vars_fd (pT := progUnit) fd) t s' /\
  forall fr, finalize_funcall fd' t = ok fr -> exists Sp' Sq,
    [/\ write_vars true (f_iparams ci) vargs (Estate (fscs fr) (fmem fr) Vm.init) = ok Sp',
        write_vars true (f_ires ci) (fvals fr) Sp' = ok Sq,
        emem t = emem Sq & evm t =[contract_vars ci] evm Sq]).
+ apply wequiv_basic_esem.
  + rewrite /copy_es; elim: (f_ires ci) (zip _ _) => [ | ? ? ih] [ | ? ?] //=.
  move=> t s0 t3 [hts hIP] hcp.
  have hdis : forall x, Sv.In x (vars_l (f_ires ci)) -> ~ Sv.In x (read_es [seq Plvar i | i <- f_res fd]).
  + move=> x hx; rewrite vars_l_read_es => hx'.
    apply: (hdz x); rewrite /contract_vars /vars_fd; clear -hx hx'; SvD.fsetdec.
  have hs1 : size (f_ires ci) = size [seq Plvar i | i <- f_res fd] by rewrite size_map.
  have hs2 : size (f_tyout fd) = size [seq Plvar i | i <- f_res fd].
  + by rewrite size_map -hsres -htyo size_map.
  have [vsr hvsr [vres hvres hw]] := copy_esP hdis hs1 hs2 hcp.
  have hout : forall z, ~ Sv.In z (vars_l (f_ires ci)) -> Vm.get (sm := partial) (evm t3) z = Vm.get (sm := partial) (evm t) z.
  + move=> z hz; symmetry; apply: (write_vars_eq_ex hw) => /sv_of_listP /vars_lP; exact hz.
  have [hscs3 hmem3] := write_vars_scs_mem hw.
  exists s0 => //; split.
  + case: hts => h1 h2 h3; split; [by rewrite hscs3 | by rewrite hmem3 | move=> z hz].
    rewrite hout; first by apply h3.
    by move=> hz'; apply: (hdz z) hz; rewrite /contract_vars; clear -hz'; SvD.fsetdec.
  have hvs3 : sem_pexprs true (p_globs p') t3 [seq Plvar i | i <- f_res fd] = ok vsr.
  + rewrite -hvsr; apply: eq_on_sem_pexprs => //; apply/eq_on_mode => z hz; apply hout.
    move: hz; rewrite vars_l_read_es => hz hz'.
    by apply: (hdz z); rewrite /contract_vars /vars_fd; clear -hz hz'; SvD.fsetdec.
  move: hvs3; rewrite sem_pexprs_get_var => hvs3.
  move=> fr; rewrite /finalize_funcall hres htyout hvs3 /dc_truncate_val /= hvres /= => -[<-] /=.
  have [Sp' hSp'] := write_vars_rename_ok (Estate (escs t3) (emem t3) Vm.init) erefl hSp.
  have [Sq hSq] := write_vars_rename_ok Sp' erefl hw.
  exists Sp', Sq; split => //.
  + by have [_ ->] := write_vars_scs_mem hSq; have [_ ->] := write_vars_scs_mem hSp'.
  have hpp : evm t =[vars_l (f_iparams ci)] evm Sp'.
  + have := write_vars_eq_on2 (Z := Sv.empty) hSp hSp'.
    move=> /(_ ltac:(by move=> ?; clear; SvD.fsetdec)) h z hz.
    by rewrite hIP // h //; clear -hz; SvD.fsetdec.
  have := write_vars_eq_on2 hw hSq hpp.
  by move=> h z hz; apply h; rewrite /contract_vars in hz; clear -hz; SvD.fsetdec.
apply wequiv_asserts_left => // t s0 [hts hR] hasserts; split => // fr hf.
have [Sp' [Sq [h1 h2 h3 h4]]] := hR fr hf.
apply (sem_postE (fvals fs) fr hfd hci); exists vargs, Sp', Sq; split => // a ha.
have := hasserts a ha; rewrite eq_globs_ts (eq_on_sem_eassert _ h3) //.
by move=> z hz; apply h4; apply: hpostC ha _ hz.
Qed.

Lemma esem_asserts_errorP {wa : WithAssert} {sem_F : sem_Fun E} (P : prog) ii l (s : estate) e :
  esem P ev (assert_all ii l) s = Error e -> isem_cmd_ P ev (assert_all ii l) s ≈ iresult (Error e).
Proof.
elim: l s => [ | a l ih] s //=.
rewrite /isem_assert; case: sem_assert => [[] | e'] /=.
+ by rewrite !bind_ret_l; apply ih.
by move=> [<-]; rewrite bind_bind /iresult /= bind_throw; reflexivity.
Qed.

Lemma esem_assertsP {wa : WithAssert} (P : prog) ii l (s s' : estate) :
  esem P ev (assert_all ii l) s = ok s' ->
  forall a, List.In a l -> sem_eassert (p_globs P) s a.2 = ok true.
Proof.
elim: l s => [ | a l ih] s //= ; rewrite /esem /=; t_xrbindP => s1 [].
move=> ha <- hl a' [<- | hin]; last by apply: ih hl _ hin.
by move: ha; rewrite /sem_assert; t_xrbindP => _ b -> hb; case: b hb.
Qed.

Lemma c2a_pre_ts fn (fd fd' : ufundef) ci fs ii s1 t1 t2 :
  get_fundef (p_funcs p) fn = Some fd ->
  contracts_to_asserts_fd fresh_var_ident p fd = ok fd' -> f_contract fd = Some ci ->
  initialize_funcall p' ev fd' fs = ok s1 ->
  esem (wa := withassert_nocontract) p' ev
    (copy_es ii (f_iparams ci) (f_tyin fd) [seq Plvar i | i <- f_params fd]) s1 = ok t1 ->
  esem (wa := withassert_nocontract) p' ev (assert_all ii (f_pre ci)) t1 = ok t2 ->
  sem_pre (wa := withassert) p fn fs = ok tt.
Proof using Hp.
move=> hfd hc2a hci hinit hcp has.
have [acc [body' [hbody [_ hcontr htyin hparams htyout hres hextra] _]]] := c2a_fdP hc2a.
have [_ _ _ hchk] := c2a_prog_inv Hp.
have [htyi htyo htyp hup hsres hpreC hpostC hdisj] := check_contractP (hchk _ _ hfd) hci.
have hdz : forall z, Sv.In z (contract_vars ci) -> ~ Sv.In z (vars_fd (pT := progUnit) fd) by apply/disjointP.
move: hinit; rewrite /initialize_funcall htyin hparams /dc_truncate_val /=.
t_xrbindP => vargs hvargs hinit.
have hdis : forall x, Sv.In x (vars_l (f_iparams ci)) -> ~ Sv.In x (read_es [seq Plvar i | i <- f_params fd]).
+ move=> x hx; rewrite vars_l_read_es => hx'.
  apply: (hdz x); rewrite /contract_vars /vars_fd; clear -hx hx'; SvD.fsetdec.
have hs1 : size (f_iparams ci) = size [seq Plvar i | i <- f_params fd].
+ by rewrite size_map -(size_map (fun x : var_i => vtype x)) htyi -htyp size_map.
have hs2 : size (f_tyin fd) = size [seq Plvar i | i <- f_params fd] by rewrite size_map -htyp size_map.
have [vs hvs [vargs' hvargs' hw]] := copy_esP hdis hs1 hs2 hcp.
have hrd : sem_pexprs true (p_globs p') s1 [seq Plvar i | i <- f_params fd] = ok vargs.
+ apply: write_vars_read hup _ (mapM2_truncate_defined hvargs) hinit.
  by rewrite (mapM2_truncate_val_has_type hvargs) -htyp -map_comp.
move: hvs; rewrite hrd => -[?]; subst vs.
move: hvargs'; rewrite (mapM2_truncate_idem hvargs) => -[?]; subst vargs'.
have [Sp hSp] := write_vars_rename_ok (Estate (fscs fs) (fmem fs) Vm.init) erefl hw.
apply (sem_preE fs hfd hci); exists vargs, Sp; split => // a ha.
have hmem : emem t1 = emem Sp.
+ have [_ ->] := write_vars_scs_mem hw; have [_ ->] := write_vars_scs_mem hinit.
  by have [_ ->] := write_vars_scs_mem hSp.
have := esem_assertsP has ha; rewrite eq_globs_ts (eq_on_sem_eassert _ hmem) //.
have := write_vars_eq_on2 (Z := Sv.empty) hw hSp.
move=> /(_ ltac:(by move=> ?; clear; SvD.fsetdec)) h z hz; apply h.
by have := hpreC _ ha; clear -hz; SvD.fsetdec.
Qed.

(* The transformed program, its contracts not evaluated, behaves as the source,
   its contracts evaluated: when the precondition of the source does not
   hold, the assertions of the transformed function fail. *)
Lemma c2a_tgt_src fn :
  wiequiv_f (wa1 := withassert_nocontract) (wa2 := withassert) p' p ev ev
    (rpreF (eS := eq_spec)) fn fn (rpostF (eS := eq_spec)).
Proof using Hp.
move=> fs _ [_ <-].
have hgen : pre_ts fn fs fs -> xrutt.xrutt (core_logics.errcutoff (is_error wE)) core_logics.nocutoff EPreRel EPostRel
   (rpostF (eS := eq_spec) fn fn fs fs)
   (isem_fun (wa := withassert_nocontract) p' ev fn fs) (isem_fun (wa := withassert) p ev fn fs).
+ move=> h; have := c2a_fun_ts (conj erefl h).
  by apply xrutt_facts.xrutt_weaken => // > [].
case hfd: (get_fundef (p_funcs p) fn) => [fd | ]; last by apply hgen; split => // ?; rewrite hfd.
case hpre: (sem_pre (wa := withassert) p fn fs) => [[] | e].
+ by apply hgen; split => // ? [<-]; split.
move: (c2a_get_fundef Hp fn); rewrite hfd => -[fd' hc2a hfd'].
rewrite isem_call_unfold /isem_fun_body /kget_fundef hfd' /= bind_ret_l.
rewrite /isem_pre /sem_pre /= bind_ret_l.
case hinit: initialize_funcall => [s1 | e1] /=; last first.
+ rewrite bind_throw; apply xrutt.xrutt_CutL => //.
  by rewrite /core_logics.errcutoff /is_error /Subevent.subevent /CategoryOps.resum /fromErr mid12.
rewrite bind_ret_l.
have [acc [body' [hbody [_ hcontr htyin hparams htyout hres hextra] [ii hb]]]] := c2a_fdP hc2a.
case hci: (f_contract fd) hb => [ci | ] hb; last by move: hpre; rewrite /sem_pre /= hfd hci.
rewrite hb isem_cmd_cat bind_bind.
have hbc : all basic_i (copy_es ii (f_iparams ci) (f_tyin fd) [seq Plvar i | i <- f_params fd]).
+ rewrite /copy_es; elim: (f_iparams ci) (zip _ _) => [ | ? ? ih] [ | ? ?] //=.
case hcp: (esem (wa := withassert_nocontract) p' ev (copy_es ii (f_iparams ci) (f_tyin fd) [seq Plvar i | i <- f_params fd]) s1) => [t1 | e2]; last first.
+ rewrite (esem_basic_errorP hbc hcp) /iresult bind_throw; apply xrutt.xrutt_CutL => //.
  by rewrite /core_logics.errcutoff /is_error /Subevent.subevent /CategoryOps.resum /fromErr mid12.
rewrite (esem_i_bodyP hcp) /= bind_ret_l isem_cmd_cat bind_bind.
case has: (esem (wa := withassert_nocontract) p' ev (assert_all ii (f_pre ci)) t1) => [t2 | e3].
+ by have := c2a_pre_ts hfd hc2a hci hinit hcp has; rewrite hpre.
rewrite (esem_asserts_errorP has) /iresult bind_throw; apply xrutt.xrutt_CutL => //.
by rewrite /core_logics.errcutoff /is_error /Subevent.subevent /CategoryOps.resum /fromErr mid12.
Unshelve. all: exact _.
Qed.

End TGT_SRC.


(* When the transformed program runs without failure, its assertions
   evaluated, the source runs with the same results, its contracts
   evaluated. *)
Theorem contracts_to_asserts_tgt_src :
  forall {asm_op syscall_state : Type} {ep : EstateParams syscall_state}
    {spp : SemPexprParams} {sip : SemInstrParams asm_op syscall_state} {sm : SemMode}
    {E E0 : Type -> Type} {wE : with_Error E E0} {rE : EventRels E0}
    (fresh_var_ident : v_kind -> instr_info -> string -> atype -> Ident.ident)
    (p p' : prog) (ev : extra_val_t),
  contracts_to_asserts_prog fresh_var_ident p = ok p' ->
  forall fn,
  wiequiv_f (wa1 := withassert_nocontract) (wa2 := withassert)
    p' p ev ev (rpreF (eS := eq_spec)) fn fn (rpostF (eS := eq_spec)).
Proof. by move=> > hp fn; exact: (c2a_tgt_src _ hp (fn := fn)). Qed.

(* When the source runs without failure, its contracts evaluated, the
   transformed program runs with the same results, its assertions
   evaluated. *)
Axiom contracts_to_asserts_src_tgt :
  forall {asm_op syscall_state : Type} {ep : EstateParams syscall_state}
    {spp : SemPexprParams} {sip : SemInstrParams asm_op syscall_state} {sm : SemMode}
    {E E0 : Type -> Type} {wE : with_Error E E0} {rE : EventRels E0}
    (fresh_var_ident : v_kind -> instr_info -> string -> atype -> Ident.ident)
    (p p' : prog) (ev : extra_val_t),
  contracts_to_asserts_prog fresh_var_ident p = ok p' ->
  forall fn,
  wiequiv_f (wa1 := withassert) (wa2 := withassert_nocontract)
    p p' ev ev (rpreF (eS := eq_spec)) fn fn (rpostF (eS := eq_spec)).
