(* * Correctness of the pass drop_removable.

   The pass removes the parameters and the results of the functions that are
   removable variables, and the code that computes nothing but removable
   variables. For a function [fn] of the source, [rmv_keep_params fn] and
   [rmv_keep_res fn] give the positions of its parameters and of its results
   that are kept ([keep_only]). The transformed program computes the same
   results as the source, but those removed, from the same arguments, but
   those removed: the pass checks that the removed arguments, results and
   instructions compute nothing that the rest of the program reads. This holds
   whatever [removable] tells.

   As for [dead_code] ([dead_code_total_proof]), the direction from the
   transformed program to the source needs the removed code not to fail
   ([total_ok], the well-typedness of the source), and the source to accept
   the removed arguments: they have the types of the parameters. *)

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.
Require Import compiler_util psem psem_facts.
Require Import dead_code drop_removable dead_code_total_proof dead_args_proof.

#[local] Existing Instance progUnit.
#[local] Existing Instance nosubword.
#[local] Existing Instance indirect_c.

Section DEFS.

Context
  {asm_op syscall_state : Type} {ep : EstateParams syscall_state}
  {spp : SemPexprParams} {sip : SemInstrParams asm_op syscall_state}.

Context (removable : var -> bool) (p : uprog).

(* The positions kept; all for a function absent from [p]. *)
Definition rmv_keep_params (fn : funname) : seq bool :=
  if rmv_params_keep removable p fn is Some k then k else [::].

Definition rmv_keep_res (fn : funname) : seq bool :=
  if rmv_res_keep removable p fn is Some k then k else [::].

Definition drop_removable_src_tgt_spec : EquivSpec :=
  {| rpreF_ := fun fn1 fn2 fs1 fs2 => fn1 = fn2 /\ fs2 = fs_keep (rmv_keep_params fn1) fs1;
     rpostF_ := fun fn1 _ _ _ fr1 fr2 => fr2 = fs_keep (rmv_keep_res fn1) fr1 |}.

(* The arguments given to the source are those given to the transformed
   program, the removed ones being values of the types of the parameters. *)
Definition drop_removable_tgt_src_spec : EquivSpec :=
  {| rpreF_ := fun fn1 fn2 fs1 fs2 =>
       [/\ fn1 = fn2, fs1 = fs_keep (rmv_keep_params fn1) fs2 &
           forall fd, get_fundef (p_funcs p) fn1 = Some fd ->
             is_ok (mapM2 ErrType dc_truncate_val (map eval_atype fd.(f_tyin)) (fvals fs2))];
     rpostF_ := fun fn1 _ _ _ fr1 fr2 => fr1 = fs_keep (rmv_keep_res fn1) fr2 |}.

End DEFS.

Section PROOF.
Context
  {asm_op syscall_state : Type} {ep : EstateParams syscall_state}
  {spp : SemPexprParams} {sip : SemInstrParams asm_op syscall_state} {sm : SemMode}
  {E E0 : Type -> Type} {wE : with_Error E E0} {rE : EventRels E0}.
#[local] Existing Instance withassert_nocontract.
Context (removable : var -> bool) (p p' : uprog) (ev : extra_val_t).
Context (ok_p' : drop_removable_prog removable p = ok p').
Notation gd := (p_globs p).
(* No variable of [X] is removable. *)
Definition NR (X : Sv.t) := forall x, Sv.In x X -> ~~ removable x.
Lemma NR_sub X Y : Sv.Subset X Y -> NR Y -> NR X.
Proof. by move=> hs h x hx; apply/h/hs. Qed.
(* The states of the source and of the transformed program agree on the
   system state, the memory and the variables that are not removable. *)
Definition rmv_rel (s t : estate) :=
  [/\ escs s = escs t, emem s = emem t &
      forall x, ~~ removable x -> Vm.get (sm := partial) (evm s) x = Vm.get (sm := partial) (evm t) x].
(* Each copy [y := e] of [m] that reads no removable variable still holds:
   [e] evaluates to a value that, at the type of the copy, truncates as the
   value of [y] does. *)
Definition copies_ok (m : Mvar.t (atype * pexpr)) (s : estate) :=
  forall y ty e, Mvar.get m y = Some (ty, e) -> NR (read_e e) ->
  exists2 v, sem_pexpr true gd s e = ok v &
    forall vy w, get_var true (evm s) y = ok vy -> truncate_val (eval_atype ty) vy = ok w ->
      truncate_val (eval_atype ty) v = ok w.
Definition Pm m s t := rmv_rel s t /\ copies_ok m s.
Lemma rmv_rel_eq_on s t X : rmv_rel s t -> NR X -> evm s =[X] evm t.
Proof.
move=> [_ _ h] hX x hx; apply/h/hX/hx.
Qed.
Lemma rmv_sem_pexprs wdb s t es : rmv_rel s t -> NR (read_es es) -> sem_pexprs wdb gd s es = sem_pexprs wdb gd t es.
Proof.
move=> h hX; apply: eq_on_sem_pexprs; first by case: h.
by apply/eq_on_mode/(rmv_rel_eq_on h hX).
Qed.
Lemma rmv_sem_pexpr wdb s t e : rmv_rel s t -> NR (read_e e) -> sem_pexpr wdb gd s e = sem_pexpr wdb gd t e.
Proof.
move=> h hX; apply: eq_on_sem_pexpr; first by case: h.
by apply/eq_on_mode/(rmv_rel_eq_on h hX).
Qed.
Lemma rmv_sem_eassert s t a : rmv_rel s t -> NR (read_eassert a) -> sem_eassert gd s a = sem_eassert gd t a.
Proof.
move=> h hX; apply: eq_on_sem_eassert; first by case: h.
by apply/(rmv_rel_eq_on h hX).
Qed.
Lemma rmv_rel_ex s t s' t' X :
  rmv_rel s t -> evm s =[\X] evm s' -> evm t =[\X] evm t' ->
  escs s' = escs t' -> emem s' = emem t' ->
  (forall x, Sv.In x X -> ~~ removable x -> Vm.get (sm := partial) (evm s') x = Vm.get (sm := partial) (evm t') x) ->
  rmv_rel s' t'.
Proof.
move=> [_ _ h] hs ht hscs hmem hX; split => // x hx.
case: (Sv_memP x X) => hin; first by apply hX.
by rewrite -hs // -ht //; apply h.
Qed.
Lemma rmv_write_lval wdb x v s s' t :
  rmv_rel s t -> NR (vars_lval (rm_lv removable x)) ->
  write_lval wdb gd x v s = ok s' ->
  exists2 t', write_lval wdb gd (rm_lv removable x) v t = ok t' & rmv_rel s' t'.
Proof.
move=> hst hNR hw.
have [[y [? hy]] | hrm] : (exists y, x = Lvar y /\ removable y) \/ rm_lv removable x = x.
+ case: (x) => /=; try by right.
  by move=> y; case: ifP; eauto.
+ subst x; move: hw; rewrite /= hy /write_var /write_none; t_xrbindP => vm /set_varP [hdb htr ->] <-.
  rewrite /= /write_none htr hdb /=; exists t => //.
  case: hst => h1 h2 h3; split => // z hz /=.
  rewrite Vm.setP_neq; first by apply h3.
  by apply/eqP => ?; subst z; rewrite hy in hz.
rewrite hrm in hNR *.
have hX : evm s =[read_rv x] evm t.
+ by apply: rmv_rel_eq_on hst (NR_sub _ hNR); rewrite /vars_lval; clear; SvD.fsetdec.
have [vm2 hw2 heq] := write_lval_eq_on (X := read_rv x) (fun z hz => hz) hw hX.
have ht : with_vm s (evm t) = t.
+ by case: hst; case: (t) => ??? /= h1 h2 _; rewrite /with_vm h1 h2.
rewrite ht in hw2; exists (with_vm s' vm2) => //.
apply: rmv_rel_ex hst (vrvP hw) (vrvP hw2) _ _ _ => // z hz _.
by apply heq; clear -hz; SvD.fsetdec.
Qed.
Lemma rmv_write_lval_removed wdb x v s s' t :
  rmv_rel s t -> (forall z, Sv.In z (vrv x) -> removable z) -> ~~ lv_write_mem x ->
  write_lval wdb gd x v s = ok s' -> rmv_rel s' t.
Proof.
move=> hst hrm hmem hw.
apply: (rmv_rel_ex (X := vrv x) hst (vrvP hw)) => //.
+ by rewrite -(lv_write_scsP hw); case: hst.
+ by rewrite -(lv_write_memP hmem hw); case: hst.
by move=> z /hrm ->.
Qed.
Lemma removed_lvP x :
  [|| removable_lv removable x | if x is Lnone _ _ then true else false] ->
  (forall z, Sv.In z (vrv x) -> removable z) /\ ~~ lv_write_mem x.
Proof.
case: x => /=.
+ by move=> *; split => // z hz; exfalso; clear -hz; SvD.fsetdec.
+ by move=> y; rewrite orbF => hy; split => // z hz; have <- : v_var y = z by clear -hz; SvD.fsetdec.
+ done.
+ by move=> _ _ _ y _; rewrite orbF => hy; split => // z hz; have <- : v_var y = z by clear -hz; SvD.fsetdec.
by move=> _ _ _ y _; rewrite orbF => hy; split => // z hz; have <- : v_var y = z by clear -hz; SvD.fsetdec.
Qed.
Lemma remove_setP (X : Sv.t) (m : Mvar.t (atype * pexpr)) z c :
  Mvar.get (Sv.fold (fun y m => Mvar.remove m y) X m) z = Some c ->
  Mvar.get m z = Some c /\ ~ Sv.In z X.
Proof.
apply SvP.MP.fold_rec_bis.
+ by move=> s s' a heq h /h [? hn]; split => //; rewrite -heq.
+ by move=> ->; split => //; clear; SvD.fsetdec.
move=> x a s' _ _ h; rewrite Mvar.removeP; case: eqP => // hne /h [? hn]; split => //.
by move=> /SvD.F.add_iff [|//]; apply: hne.
Qed.
Lemma forget_lvsP m xs z c :
  Mvar.get (forget_lvs m xs) z = Some c -> Mvar.get m z = Some c /\ ~ Sv.In z (vrvs xs).
Proof.
elim: xs m => [ | x xs ih] m /=; first by move=> ->; split => //; clear; SvD.fsetdec.
move=> /ih [/remove_setP [? h1] h2]; split => //; rewrite vrvs_cons; clear -h1 h2; SvD.fsetdec.
Qed.
Lemma copies_ok_removed m m' s s' X :
  copies_ok m s -> evm s =[\ X] evm s' -> emem s = emem s' ->
  (forall z, Sv.In z X -> removable z) ->
  (forall z c, Mvar.get m' z = Some c -> Mvar.get m z = Some c /\ ~ Sv.In z X) ->
  copies_ok m' s'.
Proof.
move=> hm hex hmem hX hm' y ty e /hm' [/hm h hy] hNR.
have [v he hv] := h hNR; exists v.
+ rewrite -he; apply/esym/eq_on_sem_pexpr => //; apply/eq_on_mode => z hz; apply hex => hzX.
  by have := hNR _ hz; rewrite hX.
move=> vy w; rewrite -(get_var_eq_on _ (s := Sv.singleton y) (vm := evm s)); first by apply hv.
+ by clear; SvD.fsetdec.
by apply/eq_on_mode => z hz; apply hex; have <- : y = z by clear -hz; SvD.fsetdec.
Qed.
Lemma truncate_vm_truncate ty tyx v v' w :
  truncate_val ty v = ok v' -> truncatable true tyx v' ->
  truncate_val ty (vm_truncate_val tyx v') = ok w -> w = v'.
Proof.
move=> htr /vm_truncate_valE; have hid := truncate_val_idem htr.
case: v' htr hid => [b | i | len a | ws w0 | //] htr hid.
1-3: by move=> [_ ->]; rewrite hid => -[].
+ move=> [ws' [_ _ ->]]; case: ifP => hle; first by rewrite hid => -[].
  move: htr => /truncate_valI [ws1 [w1 [-> _ _]]].
  move=> /truncate_valE [ws2 [w2 [[?] /truncate_wordP [hle2 _] _]]]; subst ws2.
  by rewrite hle2 in hle.
by move=> /truncate_val_defined.
Qed.
Lemma copies_ok_set m s s' (y : var_i) tg ty e :
  copies_ok m s -> removable y ->
  sem_assgn p (Lvar y) tg ty e s = ok s' ->
  copies_ok (Mvar.set m y (ty, e)) s'.
Proof.
move=> hm hy; rewrite /sem_assgn; t_xrbindP => v hv v' htr hw.
have hrm : copies_ok (Mvar.remove m y) s'.
+ apply: (copies_ok_removed hm (vrvP_var hw) (write_var_memP hw)).
  + by move=> z hz; have <- : v_var y = z by clear -hz; SvD.fsetdec.
  move=> z c; rewrite Mvar.removeP; case: eqP => // hne ->; split => //.
  by move=> hz; apply hne; clear -hz; SvD.fsetdec.
move=> z ty' e'; rewrite Mvar.setP; case: eqP => [<- [<- <-] | hne hz] hNR; last first.
+ by apply: hrm _ _ _ _ hNR; rewrite Mvar.removeP; case: eqP.
have hyn : ~ Sv.In y (read_e e) by move=> /hNR; rewrite hy.
exists v.
+ rewrite -hv; apply/esym/eq_on_sem_pexpr; first by apply: write_var_memP hw.
  by apply/eq_on_mode => x hx; apply (vrvP_var hw) => hx'; apply hyn; have <- : x = y by clear -hx'; SvD.fsetdec.
move: hw => /write_varP [-> hdb htr'] vy w /=.
have hdef := vm_truncate_val_defined htr'; rewrite /= (truncate_val_defined htr) /= in hdef.
rewrite /get_var Vm.get_modeE Vm.setP_eq -hdef andbF /=.
rewrite -hdef /= => -[<-] htr2.
by rewrite htr (truncate_vm_truncate htr htr' htr2).
Qed.
Lemma NR_lvals_cons x xs : NR (vars_lvals (x :: xs)) -> NR (vars_lval x) /\ NR (vars_lvals xs).
Proof.
move=> h; split; apply: NR_sub h; rewrite /vars_lvals /vars_lval read_rvs_cons vrvs_cons; clear; SvD.fsetdec.
Qed.
Lemma rmv_write_lvals_keep wdb k xs vs s s' t :
  rmv_rel s t ->
  NR (vars_lvals (map (rm_lv removable) (keep_only xs k))) ->
  (k = [::] \/ all2 (fun b x => [|| b, removable_lv removable x | if x is Lnone _ _ then true else false]) k xs) ->
  write_lvals wdb gd s xs vs = ok s' ->
  exists2 t', write_lvals wdb gd t (map (rm_lv removable) (keep_only xs k)) (keep_only vs k) = ok t' & rmv_rel s' t'.
Proof.
elim: xs k vs s t => [ | x xs ih] k [ | v vs] s t //= hst hNR hk.
+ by move=> [<-]; exists t => //; case: k {hk hNR}.
t_xrbindP => s1 hw1 hws.
case: hk => [? | ]; first subst k.
+ have [h1 h2] := NR_lvals_cons hNR.
  have [t1 hwt1 hst1] := rmv_write_lval hst h1 hw1.
  have [t' hwt hst'] := ih [::] vs s1 t1 hst1 h2 (or_introl erefl) hws.
  by exists t' => //=; rewrite hwt1.
case: k hNR => [ | b k] //= hNR /andP [hb hall].
case: b hb hNR => /= hb hNR.
+ have [h1 h2] := NR_lvals_cons hNR.
  have [t1 hwt1 hst1] := rmv_write_lval hst h1 hw1.
  have [t' hwt hst'] := ih k vs s1 t1 hst1 h2 (or_intror hall) hws.
  by exists t' => //=; rewrite hwt1.
have [hrm hmem] := removed_lvP hb.
exact: ih k vs s1 t (rmv_write_lval_removed hst hrm hmem hw1) hNR (or_intror hall) hws.
Qed.
Lemma removed_writes wdb xs vs s s' :
  all (removable_lv removable) xs -> write_lvals wdb gd s xs vs = ok s' ->
  [/\ escs s = escs s', emem s = emem s', evm s =[\ vrvs xs] evm s' &
      forall z, Sv.In z (vrvs xs) -> removable z].
Proof.
move=> hall hw; split.
+ by rewrite (write_lvals_escs hw).
+ elim: xs vs s hall hw => [ | x xs ih] [ | v vs] s //=; first by move=> _ [->].
  move=> /andP [hx hall]; t_xrbindP => s1 hw1 /(ih _ _ hall) <-.
  have [_ hmem] := removed_lvP (x := x) (introT orP (or_introl hx)).
  exact: lv_write_memP hmem hw1.
+ exact: vrvsP hw.
elim: xs {vs s s' hw} hall => [ | x xs ih] /=; first by move=> _ z hz; exfalso; clear -hz; SvD.fsetdec.
move=> /andP [hx /ih{}ih] z; rewrite vrvs_cons => /Sv.union_spec [hz | /ih //].
by have [hrm _] := removed_lvP (x := x) (introT orP (or_introl hx)); apply hrm.
Qed.
Lemma Pm_removed m s s' t xs vs wdb :
  Pm m s t -> all (removable_lv removable) xs -> write_lvals wdb gd s xs vs = ok s' ->
  Pm (forget_lvs m xs) s' t.
Proof.
move=> [hst hm] hall hw; have [h1 h2 h3 h4] := removed_writes hall hw; split.
+ apply: (rmv_rel_ex (X := vrvs xs) hst h3 (fun _ _ => erefl)).
  + by rewrite -h1; case: hst.
  + by rewrite -h2; case: hst.
  by move=> z /h4 ->.
exact: copies_ok_removed hm h3 h2 h4 (@forget_lvsP m xs).
Qed.
Lemma Pm_assgn_removed m s s' t x tg ty e :
  Pm m s t -> removable_lv removable x -> sem_assgn p x tg ty e s = ok s' ->
  Pm (if x is Lvar y then Mvar.set m y (ty, e) else forget_lvs m [:: x]) s' t.
Proof.
move=> hP hx hs; have hs' := hs.
move: hs; rewrite /sem_assgn; t_xrbindP => v hv v' htr hw.
have hws : write_lvals true gd s [:: x] [:: v'] = ok s' by rewrite /= hw.
have hall : all (removable_lv removable) [:: x] by rewrite /= hx.
have hP' := Pm_removed hP hall hws.
case: x {hw hws hall} hx hs' hP' => // y hy hs' hP'.
by split; [case: hP' | apply: copies_ok_set (proj2 hP) hy hs'].
Qed.
Lemma subst_argP m s t ty e u1 :
  Pm m s t -> sem_pexpr true gd s e = ok u1 -> NR (read_e (subst_arg m ty e)) ->
  exists2 u2, sem_pexpr true gd t (subst_arg m ty e) = ok u2 &
    forall w, truncate_val (eval_atype ty) u1 = ok w -> truncate_val (eval_atype ty) u2 = ok w.
Proof.
move=> [hst hm] he.
have hgen : NR (read_e e) -> exists2 u2, sem_pexpr true gd t e = ok u2 &
    forall w, truncate_val (eval_atype ty) u1 = ok w -> truncate_val (eval_atype ty) u2 = ok w.
+ by move=> hNR; exists u1 => //; rewrite -(rmv_sem_pexpr _ hst hNR).
rewrite /subst_arg; case: e he hgen => // x he hgen.
case: ifP => // hlv; case hget: Mvar.get => [[ty' e'] | //]; case: eqP => // ? hNR; subst ty'.
have [v hv hvy] := hm _ _ _ hget hNR; exists v; first by rewrite -(rmv_sem_pexpr _ hst hNR).
by move=> w; apply: hvy; move: he; rewrite /= /get_gvar hlv.
Qed.
Lemma keep_only_cons {A} (x : A) l k :
  keep_only (x :: l) k = if nth true k 0 then x :: keep_only l (behead k) else keep_only l (behead k).
Proof. by case: k. Qed.
Lemma keep_only_nil {A} k : keep_only (@nil A) k = [::].
Proof. by case: k. Qed.
Lemma dc_truncate_valE ty v : dc_truncate_val ty v = truncate_val ty v.
Proof. by []. Qed.
Lemma args_keepP (f : atype -> pexpr -> pexpr) s t tys es vs1 k :
  (forall ty e u1, sem_pexpr true gd s e = ok u1 -> NR (read_e (f ty e)) ->
     exists2 u2, sem_pexpr true gd t (f ty e) = ok u2 &
       forall w, truncate_val (eval_atype ty) u1 = ok w -> truncate_val (eval_atype ty) u2 = ok w) ->
  size tys = size es ->
  sem_pexprs true gd s es = ok vs1 ->
  NR (read_es (keep_only (map2 f tys es) k)) ->
  exists2 vs2, sem_pexprs true gd t (keep_only (map2 f tys es) k) = ok vs2 &
    forall vs1', mapM2 ErrType dc_truncate_val (map eval_atype tys) vs1 = ok vs1' ->
      mapM2 ErrType dc_truncate_val (map eval_atype (keep_only tys k)) vs2 = ok (keep_only vs1' k).
Proof.
move=> hf; elim: tys es vs1 k => [ | ty tys ih] [ | e es] vs1 k //=.
+ move=> _ [<-] _; rewrite !keep_only_nil; exists [::] => //.
  by move=> vs1' [<-]; rewrite keep_only_nil.
move=> [hsize]; t_xrbindP => u1 hu1 vs1'' hvs1 <-; rewrite !keep_only_cons.
case hb: (nth true k 0) => hNR.
+ have hNR1 : NR (read_e (f ty e)) by apply: NR_sub hNR; rewrite read_es_cons; clear; SvD.fsetdec.
  have hNR2 : NR (read_es (keep_only (map2 f tys es) (behead k))).
  + by apply: NR_sub hNR; rewrite read_es_cons; clear; SvD.fsetdec.
  have [u2 hu2 htr] := hf ty e u1 hu1 hNR1.
  have [vs2 hvs2 hrel] := ih es vs1'' (behead k) hsize hvs1 hNR2.
  exists (u2 :: vs2); first by rewrite /= hu2 hvs2.
  move=> vs1'; t_xrbindP => w hw ws hws <-; rewrite keep_only_cons hb /=.
  by rewrite !dc_truncate_valE in hw *; rewrite (htr _ hw) (hrel _ hws).
have [vs2 hvs2 hrel] := ih es vs1'' (behead k) hsize hvs1 hNR.
exists vs2 => // vs1'; t_xrbindP => w hw ws hws <-; rewrite keep_only_cons hb /=.
by apply hrel.
Qed.
Lemma fn_keep_paramsE {A} fn (l : seq A) :
  fn_keep_only (rmv_params_keep removable p) fn l = keep_only l (rmv_keep_params removable p fn).
Proof. by rewrite /fn_keep_only /rmv_keep_params; case: rmv_params_keep. Qed.
Lemma fn_keep_resE {A} fn (l : seq A) :
  fn_keep_only (rmv_res_keep removable p) fn l = keep_only l (rmv_keep_res removable p fn).
Proof. by rewrite /fn_keep_only /rmv_keep_res; case: rmv_res_keep. Qed.
Lemma sem_pexprs_keep wdb s es vs k :
  sem_pexprs wdb gd s es = ok vs -> sem_pexprs wdb gd s (keep_only es k) = ok (keep_only vs k).
Proof.
elim: es vs k => [ | e es ih] /= vs k; first by move=> [<-]; rewrite !keep_only_nil.
t_xrbindP => v hv vs' /ih{}ih <-; rewrite !keep_only_cons; case: ifP => _ /=; last by apply ih.
by rewrite hv ih.
Qed.
(* The arguments of a call to [fn]: once truncated to the types of the
   parameters, those of the transformed program are those of the source that
   are kept. *)
Definition args_rel fn (vs1 vs2 : values) :=
  forall fd, get_fundef (p_funcs p) fn = Some fd ->
  forall vs1', mapM2 ErrType dc_truncate_val (map eval_atype fd.(f_tyin)) vs1 = ok vs1' ->
  mapM2 ErrType dc_truncate_val (map eval_atype (keep_only fd.(f_tyin) (rmv_keep_params removable p fn))) vs2 =
    ok (keep_only vs1' (rmv_keep_params removable p fn)).
Lemma call_argsP m s t fn es vs1 :
  Pm m s t -> sem_pexprs true gd s es = ok vs1 ->
  NR (read_es (fn_keep_only (rmv_params_keep removable p) fn (subst_args p m fn es))) ->
  exists2 vs2,
    sem_pexprs true gd t (fn_keep_only (rmv_params_keep removable p) fn (subst_args p m fn es)) = ok vs2 &
    args_rel fn vs1 vs2.
Proof.
move=> hP hes; rewrite fn_keep_paramsE /args_rel /rmv_keep_params /rmv_params_keep /subst_args.
case hfd: get_fundef => [fd | ]; last first.
+ move=> hNR; exists vs1 => //; by rewrite -(rmv_sem_pexprs _ (proj1 hP) hNR).
case: eqP => hsize hNR.
+ have [vs2 hvs2 hrel] := args_keepP (fun ty e u1 => subst_argP (ty := ty) hP) hsize hes hNR.
  by exists vs2 => // _ [<-].
exists (keep_only vs1 [seq ~~ removable (v_var x) | x <- f_params fd]).
+ by rewrite -(rmv_sem_pexprs _ (proj1 hP) hNR); apply sem_pexprs_keep.
move=> fd0 [?] vs1' h; subst fd0.
have [+ _] := size_mapM2 h; rewrite size_map -(size_mapM hes) => /hsize [].
Qed.
Lemma rmv_globs : p_globs p' = p_globs p.
Proof using ok_p'. by move: ok_p'; rewrite /drop_removable_prog; t_xrbindP => ? _ <-. Qed.
Lemma rmv_get_fundef fn fd :
  get_fundef (p_funcs p) fn = Some fd ->
  exists2 fd', drop_removable_fd removable p fn fd = ok fd' & get_fundef (p_funcs p') fn = Some fd'.
Proof using ok_p'.
move: ok_p'; rewrite /drop_removable_prog; t_xrbindP => fds hfds <- /=.
exact: get_map_cfprog_name_gen hfds.
Qed.
(* The relation between the calls used along the proof: the arguments are
   related by [args_rel] only, a substituted argument [e] having in general a
   value other than the copy [x] it replaces. *)
Definition rmv_spec : EquivSpec :=
  {| rpreF_ := fun fn1 fn2 fs1 fs2 =>
       [/\ fn1 = fn2, fscs fs1 = fscs fs2, fmem fs1 = fmem fs2 & args_rel fn1 (fvals fs1) (fvals fs2)];
     rpostF_ := fun fn1 _ _ _ fr1 fr2 => fr2 = fs_keep (rmv_keep_res removable p fn1) fr1 |}.
Lemma vars_c_cat c1 c2 : Sv.Equal (vars_c (c1 ++ c2)) (Sv.union (vars_c c1) (vars_c c2)).
Proof.
elim: c1 => [ | i c1 ih] /=; first by rewrite {2}/vars_c /read_c /write_c /=; clear; SvD.fsetdec.
by rewrite !vars_c_cons ih; clear; SvD.fsetdec.
Qed.
Lemma NR_cat c1 c2 : NR (vars_c (c1 ++ c2)) -> NR (vars_c c1) /\ NR (vars_c c2).
Proof. by move=> h; split; apply: NR_sub h; rewrite vars_c_cat; clear; SvD.fsetdec. Qed.
Lemma rm_lv_kept x : ~~ removable_lv removable x -> rm_lv removable x = x.
Proof. by case: x => //= y /negbTE ->. Qed.
Lemma copies_ok_empty s : copies_ok (Mvar.empty _) s.
Proof. by move=> y ty e; rewrite Mvar.get0. Qed.
Lemma NR_I ii ir : NR (vars_c [:: MkI ii ir]) -> NR (vars_I (MkI ii ir)).
Proof. by apply: NR_sub; rewrite vars_c_cons; clear; SvD.fsetdec. Qed.
Lemma rmv_assgn_kept m s t s' x tg ty e :
  Pm m s t -> NR (vars_I (MkI dummy_instr_info (Cassgn x tg ty e))) -> ~~ removable_lv removable x ->
  sem_assgn p x tg ty e s = ok s' ->
  exists2 t', sem_assgn p' x tg ty e t = ok t' & Pm (Mvar.empty _) s' t'.
Proof using ok_p'.
move=> [hst _] hNR hx; rewrite /sem_assgn rmv_globs; t_xrbindP => v hv v' htr hw.
rewrite -(rmv_sem_pexpr _ hst (NR_sub _ hNR)) ?hv /= ?htr /=; last by rewrite vars_I_assgn; clear; SvD.fsetdec.
have [|t' hwt hst'] := rmv_write_lval hst _ hw.
+ by rewrite rm_lv_kept //; apply: NR_sub hNR; rewrite vars_I_assgn; clear; SvD.fsetdec.
by rewrite rm_lv_kept // in hwt; exists t' => //; split => //; apply copies_ok_empty.
Qed.
Lemma rmv_opn_kept m s t s' xs tg o es :
  Pm m s t -> NR (vars_I (MkI dummy_instr_info (Copn (map (rm_lv removable) xs) tg o es))) ->
  sem_sopn gd o s xs es = ok s' ->
  exists2 t', sem_sopn (p_globs p') o t (map (rm_lv removable) xs) es = ok t' & Pm (Mvar.empty _) s' t'.
Proof using ok_p'.
move=> [hst _] hNR; rewrite /sem_sopn rmv_globs; t_xrbindP => vs vargs hvs hex hw.
rewrite -(rmv_sem_pexprs _ hst (NR_sub _ hNR)) ?hvs /= ?hex /=; last by rewrite vars_I_opn; clear; SvD.fsetdec.
have [|t' hwt hst'] := rmv_write_lvals_keep (k := [::]) hst _ (or_introl erefl) hw.
+ by apply: NR_sub hNR; rewrite vars_I_opn; clear; SvD.fsetdec.
by exists t' => //; split => //; apply copies_ok_empty.
Qed.
Lemma rmv_rel_upd s t m scs : rmv_rel s t -> rmv_rel (with_scs (with_mem s m) scs) (with_scs (with_mem t m) scs).
Proof. by case. Qed.
Lemma rmv_syscall_kept m s t s' xs o es :
  Pm m s t -> NR (vars_I (MkI dummy_instr_info (Csyscall (map (rm_lv removable) xs) o es))) ->
  sem_syscall p xs o es s = ok s' ->
  exists2 t', sem_syscall p' (map (rm_lv removable) xs) o es t = ok t' & Pm (Mvar.empty _) s' t'.
Proof using ok_p'.
move=> [hst _] hNR; rewrite /sem_syscall rmv_globs; t_xrbindP => vargs hvs fs hfs hw.
rewrite -(rmv_sem_pexprs _ hst (NR_sub _ hNR)) ?hvs /=; last by rewrite vars_I_syscall; clear; SvD.fsetdec.
have -> : mk_fstate vargs t = mk_fstate vargs s by case: hst; rewrite /mk_fstate => -> ->.
rewrite hfs /=.
have [|t' hwt hst'] := rmv_write_lvals_keep (k := [::]) (rmv_rel_upd (fmem fs) (fscs fs) hst) _ (or_introl erefl) hw.
+ by apply: NR_sub hNR; rewrite vars_I_syscall; clear; SvD.fsetdec.
by exists t' => //; split => //; apply copies_ok_empty.
Qed.
Lemma NR_check X : ~~ Sv.exists_ removable X -> NR X.
Proof.
move=> h x hx; apply/negP => hr; move/negP: h; apply.
apply/Sv.exists_spec.
by exists x.
Qed.
Lemma mapM2_keep {A B C} (f : A -> B -> exec C) l1 l2 l3 k :
  mapM2 ErrType f l1 l2 = ok l3 -> mapM2 ErrType f (keep_only l1 k) (keep_only l2 k) = ok (keep_only l3 k).
Proof.
elim: l1 l2 l3 k => [ | a l1 ih] [ | b l2] //= l3 k.
+ by move=> [<-]; rewrite !keep_only_nil.
t_xrbindP => c hc l3' /ih{}ih <-; rewrite !keep_only_cons; case: ifP => _ /=; last by apply ih.
by rewrite hc (ih (behead k)).
Qed.
Lemma rmv_write_vars xs vs s s' t :
  rmv_rel s t -> write_vars true xs vs s = ok s' ->
  exists2 t', write_vars true (keep_only xs [seq ~~ removable (v_var x) | x <- xs])
                (keep_only vs [seq ~~ removable (v_var x) | x <- xs]) t = ok t' & rmv_rel s' t'.
Proof using p sm sip spp.
elim: xs vs s t => [ | x xs ih] [ | v vs] s t //= hst; first by move=> [<-]; exists t.
t_xrbindP => s1 hw1 hws.
case hx: (removable x) => /=.
+ have h1 : rmv_rel s1 t.
  + apply: (rmv_write_lval_removed (x := Lvar x) hst _ _ hw1) => // z.
    by rewrite vrv_var => hz; have <- : v_var x = z by clear -hz; SvD.fsetdec.
  exact: ih vs s1 t h1 hws.
have [|t1 hwt1 hst1] := rmv_write_lval (x := Lvar x) hst _ hw1.
+ rewrite /rm_lv hx => z; rewrite vars_lval_Lvar => hz.
  have <- : v_var x = z by clear -hz; SvD.fsetdec.
  by rewrite hx.
have [t' hwt hst'] := ih vs s1 t1 hst1 hws.
by exists t' => //; move: hwt1; rewrite /rm_lv hx /= => -> /=.
Qed.
Lemma rmv_get_var_is s t xs vs :
  rmv_rel s t -> get_var_is true (evm s) xs = ok vs ->
  get_var_is true (evm t) (keep_only xs [seq ~~ removable (v_var x) | x <- xs]) =
    ok (keep_only vs [seq ~~ removable (v_var x) | x <- xs]).
Proof.
move=> hst; elim: xs vs => [ | x xs ih] /= vs; first by move=> [<-].
t_xrbindP => v hv vs' /ih{}ih <-; case: ifP => hx /=; last by [].
rewrite -(get_var_eq_on _ (s := Sv.singleton x) (vm := evm s)); first by rewrite hv ih.
+ by clear; SvD.fsetdec.
apply/eq_on_mode => z hz; have <- : v_var x = z by clear -hz; SvD.fsetdec.
by case: hst => _ _ ->.
Qed.
Lemma keep_only_map {A B} (f : A -> B) l k : map f (keep_only l k) = keep_only (map f l) k.
Proof. by elim: l k => [ | a l ih] k; rewrite ?keep_only_nil // !keep_only_cons; case: ifP => _ /=; rewrite ih. Qed.
Let Pi (i : instr) := forall m m' c', drop_removable_i removable p m i = ok (m', c') -> NR (vars_c c') ->
  wequiv_rec p p' ev ev rmv_spec (Pm m) [:: i] c' (Pm m').
Let Pi_r (i : instr_r) := forall ii, Pi (MkI ii i).
Let Pc (c : cmd) := forall m m' c', drop_removable_c (drop_removable_i removable p) m c = ok (m', c') -> NR (vars_c c') ->
  wequiv_rec p p' ev ev rmv_spec (Pm m) c c' (Pm m').
Lemma rmv_cmd c : Pc c.
Proof using ok_p'.
apply (cmd_rect (Pr := Pi_r) (Pi := Pi) (Pc := Pc)) => //; clear c.
+ by move=> m m' c' [<- <-] _; apply wequiv_nil.
+ move=> i c hi hc m m' c_ /=; t_xrbindP => -[m1 c1] /hi{}hi [m2 c2] /hc{}hc /= <- <- /NR_cat [hNR1 hNR2].
  by rewrite -cat1s; apply wequiv_cat with (Pm m1); [apply hi | apply hc].
+ move=> x tg ty e ii m m' c' /=; case: ifP => hx [<- <-] hNR.
  + apply wequiv_assgn_esem => s t s' hP hs; exists t => //.
    exact: Pm_assgn_removed hP hx hs.
  apply wequiv_assgn_core => s t s' hP hs.
  exact: rmv_assgn_kept hP (NR_I hNR) (negbT hx) hs.
+ move=> xs tg o es ii m m' c' /=; case: ifP => hxs [<- <-] hNR.
  + apply wequiv_opn_esem => s t s' hP hs; exists t => //.
    move: hs; rewrite /sem_sopn; t_xrbindP => vs vargs _ _ hw.
    by apply: Pm_removed hP (proj2 (andP hxs)) hw.
  apply wequiv_opn_esem => s t s' hP hs /=.
  have [t' ht' hP'] := rmv_opn_kept (tg := tg) hP (NR_I hNR) hs.
  by exists t'; rewrite ?ht'.
+ move=> xs o es ii m m' c' /= [<- <-] hNR.
  apply wequiv_syscall_esem => s t s' hP hs /=.
  have [t' ht' hP'] := rmv_syscall_kept hP (NR_I hNR) hs.
  by exists t'; rewrite ?ht'.
+ move=> a ii m m' c' /= [<- <-] hNR.
  apply wequiv_assert => _; split => // s t [hst _] ha.
  rewrite rmv_globs -(rmv_sem_eassert hst); last by apply: NR_sub (NR_I hNR); rewrite vars_I_assert; clear; SvD.fsetdec.
  by split => //; split => //; apply copies_ok_empty.
+ move=> e c1 c2 hc1 hc2 ii m m' c' /=; t_xrbindP.
  move=> _ [m1 c1'] /hc1{}hc1 <- _ [m2 c2'] /hc2{}hc2 <- <- <- /NR_I hNR.
  have hNRe : NR (read_e e) by apply: NR_sub hNR; rewrite vars_I_if; clear; SvD.fsetdec.
  have {}hc1 := hc1 (NR_sub _ hNR) ; have {}hc2 := hc2 (NR_sub _ hNR).
  have hs1 : Sv.Subset (vars_c c1') (vars_I (MkI ii (Cif e c1' c2'))) by rewrite vars_I_if; clear; SvD.fsetdec.
  have hs2 : Sv.Subset (vars_c c2') (vars_I (MkI ii (Cif e c1' c2'))) by rewrite vars_I_if; clear; SvD.fsetdec.
  have {hs1}hc1 := hc1 hs1; have {hs2}hc2 := hc2 hs2.
  apply wequiv_if_eq.
  + by move=> s t v [hst _]; rewrite rmv_globs -(rmv_sem_pexpr _ hst hNRe) => ->; exists v.
  move=> [] /=.
  + apply wequiv_weaken with (Pm (Mvar.empty _)) (Pm m1) => //.
    1,2: by move=> s1 s2 [? _]; split => //; apply copies_ok_empty.
  apply wequiv_weaken with (Pm (Mvar.empty _)) (Pm m2) => //.
  1,2: by move=> s1 s2 [? _]; split => //; apply copies_ok_empty.
+ move=> x dir lo hi c hc ii m m' c' /=; t_xrbindP.
  move=> _ [m1 c1'] /hc{}hc <- <- <- /NR_I hNR.
  have hs1 : Sv.Subset (vars_c c1') (vars_I (MkI ii (Cfor x (dir, lo, hi) c1'))) by rewrite vars_I_for; clear; SvD.fsetdec.
  have {hs1}hc := hc (NR_sub hs1 hNR).
  apply wequiv_for_eq with (Pm (Mvar.empty _)).
  + by move=> s1 s2 [? _]; split => //; apply copies_ok_empty.
  + move=> s t vs [hst _]; rewrite rmv_globs -(rmv_sem_pexprs _ hst) => [-> | ]; first by exists vs.
    by apply: NR_sub hNR; rewrite vars_I_for /read_es /= !read_eE; clear; SvD.fsetdec.
  + have hx : ~~ removable x by apply hNR; rewrite vars_I_for; clear; SvD.fsetdec.
    move=> i s t s' [hst _] hw.
    have [|t' hwt hst'] := rmv_write_lval (x := Lvar x) hst _ hw.
    + by rewrite /= (negbTE hx); apply: NR_sub hNR; rewrite vars_I_for vars_lval_Lvar; clear; SvD.fsetdec.
    by move: hwt; rewrite /= (negbTE hx) => hwt; exists t' => //; split => //; apply copies_ok_empty.
  apply wequiv_weaken with (Pm (Mvar.empty _)) (Pm m1) => //.
  by move=> s1 s2 [? _]; split => //; apply copies_ok_empty.
+ move=> a c e info c2 hc hc2 ii m m' c' /=; t_xrbindP.
  move=> _ [m1 c1'] /hc{}hc <- _ [m2 c2'] /hc2{}hc2 <- <- <- /NR_I hNR.
  have hs1 : Sv.Subset (vars_c c1') (vars_I (MkI ii (Cwhile a c1' e info c2'))) by rewrite vars_I_while; clear; SvD.fsetdec.
  have hs2 : Sv.Subset (vars_c c2') (vars_I (MkI ii (Cwhile a c1' e info c2'))) by rewrite vars_I_while; clear; SvD.fsetdec.
  have {hs1}hc := hc (NR_sub hs1 hNR); have {hs2}hc2 := hc2 (NR_sub hs2 hNR).
  have hNRe : NR (read_e e) by apply: NR_sub hNR; rewrite vars_I_while; clear; SvD.fsetdec.
  apply wequiv_weaken with (Pm (Mvar.empty _)) (Pm (Mvar.empty _)) => //.
  + by move=> s1 s2 [? _]; split => //; apply copies_ok_empty.
  apply wequiv_while_eq.
  + by move=> s t v [hst _]; rewrite rmv_globs -(rmv_sem_pexpr _ hst hNRe) => ->; exists v.
  + apply wequiv_weaken with (Pm (Mvar.empty _)) (Pm m1) => //.
    by move=> s1 s2 [? _]; split => //; apply copies_ok_empty.
  apply wequiv_weaken with (Pm (Mvar.empty _)) (Pm m2) => //.
  by move=> s1 s2 [? _]; split => //; apply copies_ok_empty.
move=> xs f es ii m m' c' /=; t_xrbindP.
move=> hdests <- <- /NR_I hNR.
apply wequiv_call_wa with (Pf := rpreF (eS := rmv_spec)) (Qf := rpostF (eS := rmv_spec)) (Rv := args_rel f).
+ move=> s t vs1 hP hes; rewrite rmv_globs; apply: (call_argsP hP hes).
  by apply: NR_sub hNR; rewrite vars_I_call; clear; SvD.fsetdec.
+ by [].
+ by move=> s1 s2 vs1 vs2 [[hscs hmem _] _] hargs; split.
+ by [].
+ exact: (@wequiv_fun_rec _ _ _ _ _ _ _ _ _ _ p p' ev ev rmv_spec ii ii f f).
move=> fs1 fs2 fr1 fr2 _ /= -> s t s' [hst _] hw.
have hk : rmv_keep_res removable p f = [::] \/
  all2 (fun b x => [|| b, removable_lv removable x | if x is Lnone _ _ then true else false])
    (rmv_keep_res removable p f) xs.
+ by move: hdests; rewrite /removed_dests /rmv_keep_res; case: rmv_res_keep; auto.
have [|t' hwt hst'] := rmv_write_lvals_keep (rmv_rel_upd (fmem fr1) (fscs fr1) hst) _ hk hw.
+ by rewrite -fn_keep_resE; apply: NR_sub hNR; rewrite vars_I_call /vars_lvals; clear; SvD.fsetdec.
by exists t'; [rewrite rmv_globs fn_keep_resE | split => //; apply copies_ok_empty].
Qed.
Lemma rmv_fun fn :
  wiequiv_f p p' ev ev (rpreF (eS := rmv_spec)) fn fn (rpostF (eS := rmv_spec)).
Proof using ok_p'.
apply wequiv_fun_ind_wa => {}fn _ fs1 fs2 [<- hscs hmem hargs] fd hfd.
have [fd' hfd' hget'] := rmv_get_fundef hfd; exists fd' => // _; split => // s1 hinit.
move: hfd'; rewrite /drop_removable_fd; t_xrbindP => -[m' body] hbody /NR_check hNR ?; subst fd'.
have hkp : rmv_keep_params removable p fn = [seq ~~ removable (v_var x) | x <- f_params fd].
+ by rewrite /rmv_keep_params /rmv_params_keep hfd.
have hkr : rmv_keep_res removable p fn = [seq ~~ removable (v_var x) | x <- f_res fd].
+ by rewrite /rmv_keep_res /rmv_res_keep hfd.
rewrite !fn_keep_paramsE !fn_keep_resE /=.
move: hinit; rewrite /initialize_funcall /=; t_xrbindP => vargs' htr hw.
have := hargs fd hfd vargs' htr; rewrite hkp => -> /=.
have h0 : rmv_rel (estate0 fs1) (estate0 fs2) by split.
have [t1 hwt hst1] := rmv_write_vars h0 hw.
exists t1 => //; exists (Pm (Mvar.empty _)), (Pm m'); split.
+ by split => //; apply copies_ok_empty.
+ apply: rmv_cmd hbody _; apply: NR_sub hNR; rewrite /vars_fd /=; clear; SvD.fsetdec.
+ move=> s t fr [hst _]; rewrite /finalize_funcall /=; t_xrbindP => vres hvres vres' htr' <-.
  rewrite hkr (rmv_get_var_is hst hvres) /=.
  rewrite keep_only_map (mapM2_keep _ htr') /=; eexists; first reflexivity.
  by case: hst => -> -> _.
by [].
Qed.
Lemma drop_removable_src_tgt_aux fn :
  wiequiv_f p p' ev ev (rpreF (eS := drop_removable_src_tgt_spec removable p)) fn fn
    (rpostF (eS := drop_removable_src_tgt_spec removable p)).
Proof using ok_p'.
apply wkequiv_io_weaken with (rpreF (eS := rmv_spec) fn fn) (rpostF (eS := rmv_spec) fn fn) => //; last by apply rmv_fun.
move=> fs1 fs2 /= [_ ->]; split => // fd _ vs1' htr.
by rewrite keep_only_map; apply: mapM2_keep htr.
Qed.

End PROOF.

(* When the source runs without failure, its assertions evaluated, the
   transformed program runs, from the arguments kept, with the same results,
   but those removed. *)
Lemma drop_removable_src_tgt :
  forall {asm_op syscall_state : Type} {ep : EstateParams syscall_state}
    {spp : SemPexprParams} {sip : SemInstrParams asm_op syscall_state}
    {sm : SemMode}
    {E E0 : Type -> Type} {wE : with_Error E E0} {rE : EventRels E0}
    removable (p p' : uprog) (ev : extra_val_t),
  drop_removable_prog removable p = ok p' ->
  forall fn,
  wiequiv_f (wa1 := withassert_nocontract) (wa2 := withassert_nocontract)
    p p' ev ev (rpreF (eS := drop_removable_src_tgt_spec removable p)) fn fn
    (rpostF (eS := drop_removable_src_tgt_spec removable p)).
Proof. exact: @drop_removable_src_tgt_aux. Qed.

(* When the transformed program runs without failure, in the total mode with
   its assertions evaluated, the source runs, from the same arguments and
   values of the types of the removed parameters, with the same results, but
   those removed. *)
Axiom drop_removable_tgt_src :
  forall {asm_op syscall_state : Type} {ep : EstateParams syscall_state}
    {spp : SemPexprParams} {sip : SemInstrParams asm_op syscall_state}
    {E E0 : Type -> Type} {wE : with_Error E E0} {rE : EventRels E0}
    removable (p p' : uprog) (ev : extra_val_t),
  total_ok p ->
  drop_removable_prog removable p = ok p' ->
  forall fn,
  wiequiv_f (sm1 := total) (sm2 := total)
    (wa1 := withassert_nocontract) (wa2 := withassert_nocontract)
    p' p ev ev (rpreF (eS := drop_removable_tgt_src_spec removable p)) fn fn
    (rpostF (eS := drop_removable_tgt_src_spec removable p)).
