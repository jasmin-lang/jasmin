From mathcomp Require Import all_ssreflect all_algebra.
Require Import psem x86_variables.
Import Utf8.
Import compiler_util x86_sem.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* -------------------------------------------------------------------- *)
Lemma xreg_of_varI ii x y :
  xreg_of_var ii x = ok y →
  match y with
  | Reg r => register_of_var x = Some r
  | XReg r => xmm_register_of_var x = Some r
  | _ => False
  end.
Proof.
  rewrite /xreg_of_var.
  case: xmm_register_of_var; last case: register_of_var; last by [].
  all: by move => r [<-].
Qed.

(* -------------------------------------------------------------------- *)
Lemma inj_rflag_of_var ii x y v :
     rflag_of_var ii x = ok v
  -> rflag_of_var ii y = ok v
  -> v_var x = y.
Proof.
case: x y => -[] xt xn xi [] [] yt yn yi; rewrite /rflag_of_var /=.
t_xrbindP => _ /assertP /eqP ->.
case Ex: (rflag_of_string xn) => [vx|] // -[?]; subst vx.
move=> _ /assertP /eqP ->.
case Ey: (rflag_of_string yn) => [vy|] // -[?]; subst vy.
by f_equal; apply: (inj_rflag_of_string Ex Ey).
Qed.

(* -------------------------------------------------------------------- *)
Definition of_rbool (v : rflagv) :=
  if v is Def b then Vbool b else undef_b.

(* -------------------------------------------------------------------- *)
Definition eqflags (m: estate) (rf: rflagmap) : Prop :=
  ∀ f v, get_var (evm m) (var_of_flag f) = ok v → value_uincl v (of_rbool (rf f)).

Variant disj_rip rip := 
  | Drip of
    (∀ r, var_of_register r <> rip) &
    (∀ r, var_of_xmm_register r <> rip) &
    (∀ f, var_of_flag f <> rip).

Variant lom_eqv rip (m : estate) (lom : x86_mem) :=
  | MEqv of
         emem m = asm_mem lom
    & get_var (evm m) rip = ok (Vword lom.(asm_rip)) 
    & disj_rip rip 
    & (∀ r v, get_var (evm m) (var_of_register r) = ok v → value_uincl v (Vword (asm_reg lom r)))
    & (∀ r v, get_var (evm m) (var_of_xmm_register r) = ok v → value_uincl v (Vword (asm_xreg lom r)))
    & eqflags m (asm_flag lom).

(* -------------------------------------------------------------------- *)
Definition value_of_bool (b: exec bool) : exec value :=
  match b with
  | Ok b => ok (Vbool b)
  | Error ErrAddrUndef => ok undef_b
  | Error e => Error e
  end.

(* -------------------------------------------------------------------- *)
Lemma xgetreg_ex rip x r v s xs :
  lom_eqv rip s xs →
  register_of_var x = Some r →
  get_var s.(evm) x = ok v →
  value_uincl v (Vword (xs.(asm_reg) r)).
Proof. case => _ _ _ eqv _ _ /var_of_register_of_var <-{x}; exact: eqv. Qed.

(* -------------------------------------------------------------------- *)
Lemma xxgetreg_ex rip x r v s xs :
  lom_eqv rip s xs →
  xmm_register_of_var x = Some r →
  get_var (evm s) x = ok v →
  value_uincl v (Vword (asm_xreg xs r)).
Proof. by case => _ _ _ _ eqr _ /xmm_register_of_varI ?; subst x; auto. Qed.

(* -------------------------------------------------------------------- *)
Lemma xgetflag_ex ii m rf x f v :
  eqflags m rf →
  rflag_of_var ii x = ok f →
  get_var (evm m) x = ok v →
  value_uincl v (of_rbool (rf f)).
Proof.
move: (@var_of_flag_of_var x).
move => h eqm; case: x h => -[] xt xn xi /=.
rewrite /rflag_of_var /flag_of_var /= => h.
t_xrbindP => _ /assertP /eqP ?; subst xt.
case: rflag_of_string h => //= fl /(_ _ erefl) <- [<-] /= ok_v.
apply (eqm _ _ ok_v).
Qed.

Lemma gxgetflag_ex ii m rf (x:gvar) f v :
  eqflags m rf →
  rflag_of_var ii x.(gv) = ok f →
  get_gvar [::] (evm m) x = ok v →
  value_uincl v (of_rbool (rf f)).
Proof.
  by rewrite /get_gvar; case: ifP => // ?; apply: xgetflag_ex.   
Qed.

Corollary xgetflag ii m rf x f v b :
  eqflags m rf →
  rflag_of_var ii x = ok f →
  get_var (evm m) x = ok v →
  to_bool v = ok b →
  rf f = Def b.
Proof.
move => eqm ok_f ok_v ok_b.
have := xgetflag_ex eqm ok_f ok_v.
case: {ok_v} v ok_b => //.
- by move => b' [<-]; case: (rf _) => // ? ->.
by case.
Qed.

Corollary gxgetflag ii m rf (x:gvar) f v b :
  eqflags m rf →
  rflag_of_var ii x.(gv) = ok f →
  get_gvar [::] (evm m) x = ok v →
  to_bool v = ok b →
  rf f = Def b.
Proof.
  by rewrite /get_gvar; case: ifP => // ?; apply: xgetflag. 
Qed.

(* -------------------------------------------------------------------- *)
Lemma eq_get_gvar m x y vx vy: 
  v_var (gv x) = v_var (gv y) -> get_gvar [::] m x = ok vx -> get_gvar [::] m y = ok vy -> vx = vy.
Proof.
  by rewrite /get_gvar; case:ifP => //; case: ifP => // ?? -> -> [->].
Qed.

Lemma not_condtP (c:condt) rf b : 
  eval_cond rf c = ok b -> eval_cond rf (not_condt c) = ok (negb b).
Proof.
  case: c => /=.
  1,3,5,9,11: by case: (rf _) => //= ? [->].
  1,2,3,6,7: by case: (rf _) => //= ? [<-]; rewrite negbK.
  + by case: (rf CF) => //= ?; case: (rf _) => //= ? [<-]; rewrite negb_or.
  + by case: (rf CF) => //= ?; case: (rf _) => //= ? [<-]; rewrite -negb_or negbK.
  + by case: (rf SF) => //= ?; case: (rf _) => //= ? [<-]; rewrite negbK.
  + by case: (rf SF) => //= ?; case: (rf _) => //= ? [<-].
  + by case: (rf ZF) => //= ?; case: (rf SF) => //= ?; case: (rf _) => //= ? [<-]; rewrite negb_or negbK.
  by case: (rf ZF) => //= ?; case: (rf SF) => //= ?; case: (rf _) => //= ? [<-]; rewrite negb_and negbK.
Qed.

Lemma or_condtP ii e c1 c2 c rf b1 b2: 
  or_condt ii e c1 c2 = ok c ->  
  eval_cond rf c1 = ok b1 ->
  eval_cond rf c2 = ok b2 ->
  eval_cond rf c  = ok (b1 || b2).
Proof.
  case: c1 => //; case: c2 => //= -[<-] /=.
  + by case: (rf _) => // ? [->]; case: (rf _) => // ? [->].
  + by case: (rf _) => // ? [->]; case: (rf _) => // ? [->] /=; rewrite orbC.
  + by case: (rf ZF) => // ? [->]; case: (rf SF) => //= ?; case: (rf _) => //= ? [<-].
  by case: (rf SF) => //= ?; case: (rf _) => //= ? [<-]; case: (rf _) => //= ? [->]; rewrite orbC.
Qed.

Lemma and_condtP ii e c1 c2 c rf b1 b2: 
  and_condt ii e c1 c2 = ok c ->  
  eval_cond rf c1 = ok b1 ->
  eval_cond rf c2 = ok b2 ->
  eval_cond rf c  = ok (b1 && b2).
Proof.
  case: c1 => //; case: c2 => //= -[<-] /=.
  + by case: (rf _) => // ? [<-]; case: (rf _) => // ? [<-].
  + by case: (rf _) => // ? [<-]; case: (rf _) => // ? [<-] /=; rewrite andbC.
  + by case: (rf ZF) => // ? [<-]; case: (rf SF) => //= ?; case: (rf _) => //= ? [<-].
  by case: (rf SF) => //= ?; case: (rf _) => //= ? [<-]; case: (rf _) => //= ? [->]; rewrite andbC.
Qed.

Lemma value_of_bool_uincl vb ve (b:bool) : 
  to_bool vb = ok b ->
  (∃ v' : value, value_of_bool ve = ok v' ∧ value_uincl vb v') ->
  ve = ok b.
Proof.
  move=> h [v' [] hvb /(value_uincl_bool) -/(_ _ h) [??]]; subst vb v'.
  by case: ve hvb => /= [ ? [->] | []].
Qed.

Lemma eval_assemble_cond_r ii m rf e c v:
  eqflags m rf →
  assemble_cond_r ii e = ok c →
  sem_pexpr [::] m e = ok v →
  let get x :=
    if rf x is Def b then ok b else undef_error in
  ∃ v', value_of_bool (eval_cond get c) = ok v' ∧ value_uincl v v'.
Proof.
move=> eqv; elim: e c v => //.
+ move => x c v /=; t_xrbindP => r ok_r ok_ct ok_v.
  have := gxgetflag_ex eqv ok_r ok_v.
  by case: {ok_r ok_v} r ok_ct => // -[<-] {c} /= h; eexists; split; eauto; case: (rf _).
+ case => //= e hrec; t_xrbindP => c v ce hce <- ve hve.
  rewrite /sem_sop1 /=; t_xrbindP => b hb <-.
  have /(value_of_bool_uincl hb) -/not_condtP -> := hrec _ _ hce hve.
  by exists (~~b).
+ case => //=.
  + move=> e1 _ e2 _ c v.
    case: e1 => //= x1; case: e2 => //= x2; t_xrbindP => f1 ok_f1 f2 ok_f2.
    case: ifP => // /orP hor [<-] v1 /(gxgetflag eqv ok_f1) hv1 v2 /(gxgetflag eqv ok_f2) hv2.
    move=> /sem_sop2I /= [b1 [b2 [b3 [hb1 hb2 [<-] ->]]]].
    move: (hv1 _ hb1) (hv2 _ hb2) => hfb1 hfb2.
    exists (b1 == b2); split => //.
    by case: hor => /andP [] /eqP ? /eqP ?; subst f1 f2; rewrite hfb1 hfb2 //= eq_sym.
  + move=> e1 hrec1 e2 hrec2 c v; t_xrbindP => c1 hc1 c2 hc2 hand v1 hv1 v2 hv2.
    move=> /sem_sop2I /= [b1 [b2 [b3 [hb1 hb2 [<-] ->]]]].
    have /(value_of_bool_uincl hb1) hec1 := hrec1 _ _ hc1 hv1.
    have /(value_of_bool_uincl hb2) hec2 := hrec2 _ _ hc2 hv2.
    have -> := and_condtP hand hec1 hec2.
    by exists (b1 && b2).
  move=> e1 hrec1 e2 hrec2 c v; t_xrbindP => c1 hc1 c2 hc2 hor v1 hv1 v2 hv2.
  move=> /sem_sop2I /= [b1 [b2 [b3 [hb1 hb2 [<-] ->]]]].
  have /(value_of_bool_uincl hb1) hec1 := hrec1 _ _ hc1 hv1.
  have /(value_of_bool_uincl hb2) hec2 := hrec2 _ _ hc2 hv2.
  have -> := or_condtP hor hec1 hec2.
  by exists (b1 || b2).
move=> t e _ e1 _ e2 _ c v /=.
case: e => //= v1; case: e1 => //= [v2 | [] //= e2'].
+ case: e2 => //= -[] // [] //= vn2; t_xrbindP => f1 hf1 f2 hf2 fn2 hfn2.
  case: ifP => // /orP hor [<-] b1 vv1 /(gxgetflag eqv hf1) hvb1/hvb1{hvb1}hvb1.
  move=> vv2 vv2' /(gxgetflag eqv hf2) hvb2 ht2.
  move=> ?? vvn2 /(gxgetflag eqv hfn2) hvnb2 /sem_sop1I /= [nb2 /hvnb2{hvnb2}hvnb2 ->].
  move=> /truncate_val_bool [??] ?; subst.
  move: ht2; rewrite /truncate_val /=; t_xrbindP => b2 /hvb2{hvb2}hvb2 ?; subst.
  exists (if b1 then Vbool b2 else ~~ nb2); split => //.
  by case: hor => /and3P [/eqP ? /eqP ? /eqP ?]; subst; move: hvnb2; rewrite hvb1 hvb2 => -[<-] /=;
    case: (b1); case: (b2).
case: e2' => //= v2; case: e2 => // vn2; t_xrbindP => f1 hf1 f2 hf2 fn2 hfn2.
case: ifP => // /orP hor [<-] b1 vv1 /(gxgetflag eqv hf1) hvb1/hvb1{hvb1}hvb1.
move=> ? vv2 vv2' /(gxgetflag eqv hf2) hvb2 /sem_sop1I /= [b2 /hvb2{hvb2}hvb2 ->].
move=> /truncate_val_bool [??] ?; subst.
move=> vvn2 /(gxgetflag eqv hfn2) hvnb2.
rewrite /truncate_val /=; t_xrbindP => nb2 /hvnb2{hvnb2}hvnb2 ??; subst.
exists (if b1 then Vbool (~~b2) else nb2); split => //.
by case: hor => /and3P [/eqP ? /eqP ? /eqP ?]; subst; move: hvnb2; rewrite hvb1 hvb2 => -[<-] /=;
    case: (b1); case: (b2).
Qed.
   
Lemma eval_assemble_cond ii m rf e c v:
  eqflags m rf →
  assemble_cond ii e = ok c →
  sem_pexpr [::] m e = ok v →
  let get x :=
    if rf x is Def b then ok b else undef_error in
  ∃ v', value_of_bool (eval_cond get c) = ok v' ∧ value_uincl v v'.
Proof. apply eval_assemble_cond_r. Qed.

(* -------------------------------------------------------------------- *)
Lemma xscale_ok ii z sc :
  scale_of_z' ii z = ok sc ->
  z = word_of_scale sc.
Proof.
  rewrite /scale_of_z' -[X in _ -> X = _]wrepr_unsigned.
  case: (wunsigned z) => //.
  do! (case=> //; try by move=> <-).
Qed.
