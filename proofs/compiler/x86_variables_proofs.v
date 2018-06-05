From mathcomp Require Import all_ssreflect all_algebra.
Require Import x86_variables.
Import Utf8.
Import compiler_util psem x86_sem.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* -------------------------------------------------------------------- *)
Lemma inj_rflag_of_var ii x y v :
     rflag_of_var ii x = ok v
  -> rflag_of_var ii y = ok v
  -> x = y.
Proof.
case: x y => -[]// x [] []// y /=.
case Ex: (rflag_of_string x) => [vx|] // -[?]; subst vx.
case Ey: (rflag_of_string y) => [vy|] // -[?]; subst vy.
by f_equal; apply: (inj_rflag_of_string Ex Ey).
Qed.

(* -------------------------------------------------------------------- *)
Definition of_rbool (v : RflagMap.rflagv) :=
  if v is Def b then Vbool b else Vundef sbool.

(* -------------------------------------------------------------------- *)
Definition eqflags (m: estate) (rf: rflagmap) : Prop :=
  ∀ f v, get_var (evm m) (var_of_flag f) = ok v → value_uincl v (of_rbool (rf f)).

Variant lom_eqv (m : estate) (lom : x86_mem) :=
  | MEqv of
         emem m = xmem lom
    & (∀ r v, get_var (evm m) (var_of_register r) = ok v → value_uincl v (Vword (xreg lom r)))
    & (∀ r v, get_var (evm m) (var_of_xmm_register r) = ok v → value_uincl v (Vword (xxreg lom r)))
    & eqflags m (xrf lom).

(* -------------------------------------------------------------------- *)
Definition value_of_bool (b: exec bool) : exec value :=
  match b with
  | Ok b => ok (Vbool b)
  | Error ErrAddrUndef => ok (Vundef sbool)
  | Error e => Error e
  end.

(* -------------------------------------------------------------------- *)
Lemma xgetreg_ex ii x r v s xs :
  lom_eqv s xs →
  reg_of_var ii x = ok r →
  get_var s.(evm) x = ok v →
  value_uincl v (Vword (xs.(xreg) r)).
Proof.
move: (@var_of_register_of_var x).
move => h [_ eqv _ _]; case: x h => -[] //= [] // x.
rewrite /register_of_var /=.
case: reg_of_string => [vx|] // /(_ _ erefl) <- {x} [<-] ok_v.
exact: eqv.
Qed.

Corollary xgetreg ii x r v s xs w :
  lom_eqv s xs →
  reg_of_var ii x = ok r →
  get_var s.(evm) x = ok v →
  to_word U64 v = ok w →
  xreg xs r = w.
Proof.
  move => eqm hx hv hw; move: (xgetreg_ex eqm hx hv) => /value_uincl_word -/(_ _ _ hw) [].
  by rewrite zero_extend_u. 
Qed.

(* -------------------------------------------------------------------- *)
Lemma xxgetreg_ex x r v s xs :
  lom_eqv s xs →
  xmm_register_of_var x = Some r →
  get_var (evm s) x = ok v →
  value_uincl v (Vword (xxreg xs r)).
Proof. by case => _ _ eqr _ /xmm_register_of_varI ?; subst x; auto. Qed.

(* -------------------------------------------------------------------- *)
Lemma xgetflag_ex ii m rf x f v :
  eqflags m rf →
  rflag_of_var ii x = ok f →
  get_var (evm m) x = ok v →
  value_uincl v (of_rbool (rf f)).
Proof.
move: (@var_of_flag_of_var x).
move => h eqm; case: x h => -[] //= x.
rewrite /flag_of_var /=.
case: rflag_of_string => [vx|] // /(_ _ erefl) <- {x} [<-] ok_v.
by move/(_ _ _ ok_v): eqm.
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

(* -------------------------------------------------------------------- *)
Lemma eval_assemble_cond ii gd m rf e c v:
  eqflags m rf →
  assemble_cond ii e = ok c →
  sem_pexpr gd m e = ok v →
  ∃ v', value_of_bool (eval_cond c rf) = ok v' ∧ value_uincl v v'.
Proof.
move=> eqv; case: e => //.
+ move => x /=; t_xrbindP => r ok_r ok_ct ok_v.
  have := xgetflag_ex eqv ok_r ok_v.
  by case: {ok_r ok_v} r ok_ct => // -[<-] {c} /= h; eexists; split; eauto; case: (rf _).
+ do 2! case=> //; move=> x /=; t_xrbindP => r.
  move => ok_r ok_ct vx ok_vx /sem_sop1I [/= vb ok_vb -> {v}].
  have := xgetflag eqv ok_r ok_vx ok_vb.
  by case: {ok_r ok_vx ok_vb} r ok_ct => // -[<-] {c} /= -> /=; eexists.
+ case=> //; first do 3! case=> //; move=> x.
  * case=> //; first do 2! case=> //; move=> y.
    - move=> /=; t_xrbindP => r1 ok_r1 r2 ok_r2.
      case: ifPn => // /andP[]; do 2! move/eqP=> ?; subst r1 r2.
      case=> <- resx vx ok_vx ok_resx resy vy ok_vy ok_resy ok_v.
      have /sem_sop1I [/=rxb ok_rxb resxE] := ok_resx.
      have /sem_sop1I [/=ryb ok_ryb resyE] := ok_resy.
      have := xgetflag eqv ok_r1 ok_vx ok_rxb => CFE.
      have := xgetflag eqv ok_r2 ok_vy ok_ryb => ZFE.
      rewrite /eval_cond; rewrite CFE ZFE /=; subst resx resy.
      by move: ok_v; rewrite /sem_sop2 /= => -[<-]; eauto.
    - case: y => // y; case=> // z; do 2! case=> //; case=> // t.
      move=> /=; t_xrbindP => rx ok_rx ry ok_ry rz ok_rz rt ok_rt.
      case: ifP => //; rewrite -!andbA => /and4P[].
      do 4! move/eqP=> ?; subst rx ry rz rt => -[<-].
      move=> vNx vx ok_vx ok_vNx res vby vy ok_vy ok_vby.
      move=> vz ok_vz vNt vt ok_vt ok_vNt.
      case: eqP => // hty.
      case: ifP => // _ [<-] {res} ok_v.
      have [/=vbx ok_vbx ?] := sem_sop1I ok_vNx; subst vNx.
      have [/=vbt ok_vbt ?] := sem_sop1I ok_vNt; subst vNt.
      have := xgetflag eqv ok_rx ok_vx ok_vbx => ZFE.
      have := xgetflag eqv ok_ry ok_vy ok_vby => SFE.
      have := xgetflag eqv ok_rt ok_vt ok_vbt => OFE.
      rewrite /= ZFE SFE OFE /=; move: ok_v.
      rewrite /sem_sop2 /=.
      t_xrbindP=> vres; case: (boolP vby) => hvby //=; last first.
      + by case=> <- <-; rewrite [false == _]eq_sym /= eqbF_neg; eexists.
      have := inj_rflag_of_var ok_rz ok_rt => eq_zt.
      have {eq_zt} ?: vt = vz; [have := ok_vz | subst vz].
      + by rewrite eq_zt ok_vt => -[].
      by rewrite ok_vbt => -[<-] <-; eauto.
  * case: x => // x; case => // [y /=|].
    - t_xrbindP=> rx ok_rx ry ok_ry; case: ifP => //.
      case/andP; do 2! move/eqP=> ?; subst rx ry.
      case=> <- vx ok_vx vy ok_vy.
      rewrite /sem_sop2; t_xrbindP => /= xb ok_bx yb ok_by <-.
      have -> /= := xgetflag eqv ok_rx ok_vx ok_bx.
      have ->/= := xgetflag eqv ok_ry ok_vy ok_by.
      eexists; split; reflexivity.
    - case=> // y; do 2! case=> //; case=> // z; case=> //= t.
      t_xrbindP=> rx ok_rx ry ok_ry rz ok_rz rt ok_rt.
      case: ifP=> //; rewrite -!andbA => /and4P[].
      do 4! move/eqP=> ?; subst rx ry rz rt => -[<-].
      move=> vx ok_vx res vby vy ok_vy ok_vby vNz vz ok_vz ok_vNz vt ok_vt.
      case: eqP => // hty; case: ifP => // _ [<-] {res}.
      rewrite /sem_sop2; t_xrbindP => /= vbx ok_vbx vbres ok_vbres <- {v}.
      have [/=vbz ok_vbz ?] := sem_sop1I ok_vNz; subst vNz.
      have := xgetflag eqv ok_rx ok_vx ok_vbx => ZFE.
      have := xgetflag eqv ok_ry ok_vy ok_vby => SFE.
      have := xgetflag eqv ok_rz ok_vz ok_vbz => OFE.
      rewrite /= ZFE SFE OFE /=; move: ok_vbres.
      case: (boolP vby) => hvby /= => [[<-]|].
      + by rewrite eq_sym eqb_id; eexists.
      have := inj_rflag_of_var ok_rz ok_rt => eq_zt.
      have {eq_zt} ?: vt = vz; [have := ok_vz | subst vt].
      + by rewrite eq_zt ok_vt => -[].
      by rewrite ok_vbz => -[<-]; rewrite eq_sym eqbF_neg negbK; eexists.
+ case=> // x [] // => [|[] // [] //] y.
  * case=> // -[] // -[] // z /=; t_xrbindP.
    move=> rx ok_rx ry ok_ry rz ok_rz.
    case: ifPn => //; rewrite -!andbA => /and3P[].
    do 3! move/eqP=> ?; subst rx ry rz.
    have eq_xy: v_var y = v_var z.
    - by apply/(inj_rflag_of_var ok_ry ok_rz).
    case=> <- vbx vx ok_vx ok_vbx vy ok_vy rvz vz ok_vz ok_rvz.
    case: eqP => // hty; case: ifP => // _ [<-] {v}.
    have /sem_sop1I[/=vbz ok_vbz ?] := ok_rvz; subst rvz.
    have := xgetflag eqv ok_rx ok_vx ok_vbx => SFE.
    have := xgetflag eqv ok_rz ok_vz ok_vbz => OFE.
    rewrite /= SFE OFE /=; have := inj_rflag_of_var ok_ry ok_rz.
    move=> eq_yz; have {eq_yz} ?: vy = vz; [have := ok_vy|subst vy].
    - by rewrite eq_yz ok_vz => -[].
    eexists; split; first by eauto.
    case: vz {ok_vy ok_rvz ok_vz hty} ok_vbz => //; last by case.
    move => b [->] {b}.
    by case: vbx {SFE} ok_vbx.
  * case=> // z /=; t_xrbindP => vx ok_x vy ok_y vz ok_z.
    case: ifPn => //; rewrite -!andbA => /and3P[].
    do 3! move/eqP=> ?; subst vx vy vz; case=> <-.
    move=> vbx vx ok_vx ok_vbx vNy vy ok_vy ok_vNy vz ok_vz.
    case: eqP => // hty; case: ifP => // _ [<-] {v}.
    have /sem_sop1I[/=vby ok_vby ?] := ok_vNy; subst vNy.
    have := xgetflag eqv ok_x ok_vx ok_vbx => SFE.
    have := xgetflag eqv ok_y ok_vy ok_vby => OFE.
    move: (inj_rflag_of_var ok_z ok_y) ok_vz.
    case: z {ok_z} => /= z _ -> {z}.
    rewrite ok_vy => -[] ?; subst vz.
    rewrite /= SFE {SFE} /= OFE {OFE} /=; eexists; split; first by eauto.
    case: vy {ok_vy hty} ok_vNy ok_vby => //; last by case.
    move => b [<-] [->] {b}.
    case: vbx {ok_vbx} => //.
    by case: vby.
Qed.

(* -------------------------------------------------------------------- *)
Definition sem_ofs m o : exec pointer :=
  match o with
  | Ofs_const z => ok z
  | Ofs_var x => get_var (evm m) x >>= to_pointer
  | Ofs_mul sc x =>
    Let w := get_var (evm m) x >>= to_pointer in
    ok (sc * w)%R
  | Ofs_add sc x z =>
    Let w := get_var (evm m) x >>= to_pointer in
    ok (sc * w + z)%R
  | Ofs_error => type_error
  end.
Import word.
Lemma addr_ofsP gd m e v w :
  sem_pexpr gd m e = ok v →
  to_pointer v = ok w →
  let ofs := addr_ofs e in
  (if ofs is Ofs_error then false else true) →
  sem_ofs m ofs = ok w.
Proof.
elim: e v w => //=.
- (* Cast Const *)
  case => // -[] // z ih v w ; t_xrbindP => ? ? [<-] [<-] <- [<-].
  by rewrite zero_extend_u.
- (* Pvar *)
  by move => x z w ->.
- (* Papp2 *)
  case => // -[] //.
  (* Add *)
  + move => [] // p ihp q ihq v w ; t_xrbindP => vp hvp vq hvq hv hw.
    case: (addr_ofs p) ihp => //; case: (addr_ofs q) ihq => //.
    * move => /= z /(_ _ _ hvq) hz z' /(_ _ _ hvp) hz' _ /=.
      move: hv => /=; rewrite /sem_sop2 /= ; t_xrbindP =>
        wp /hz' /(_ erefl) [<-] {wp} wq /hz /(_ erefl) [<-] {wq} ?; subst v.
      by case: hw => <-; rewrite zero_extend_u.
    * move => /= z /(_ _ _ hvq) hz z' /(_ _ _ hvp) hz' _ /=.
      move: hv => /=; rewrite /sem_sop2; t_xrbindP => wp /hz' /(_ erefl) [<-] {wp} wq /hz /(_ erefl).
      t_xrbindP => vz -> /= -> /= ?; subst v.
      case: hw => <-;f_equal;wring.
    * move => /= x z /(_ _ _ hvq) hz z' /(_ _ _ hvp) hz' _.
      move: hv hw => /=; rewrite /sem_sop2; t_xrbindP => wp /hz' /(_ erefl) [<-] {wp} wq /hz /(_ erefl).
      by t_xrbindP => ? ? -> /= -> <- /= <- [<-];f_equal; wring.
    * move => /= z /(_ _ _ hvq) hz z' /(_ _ _ hvp) hz' _ /=.
      move: hv hw => /=; rewrite /sem_sop2; t_xrbindP => wp /hz' /(_ erefl).
      by t_xrbindP => vz' -> /= -> wq /hz /(_ erefl) [<-] {wq} <- [<-] /=;f_equal;wring.
    move => /= z /(_ _ _ hvq) hz x z' /(_ _ _ hvp) hz' _ /=.
    move: hv hw => /=; rewrite /sem_sop2; t_xrbindP => wp /hz' /(_ erefl).
    by t_xrbindP => y vz' -> /= -> /= <- ? /hz /(_ erefl) [<-] <- [<-];rewrite zero_extend_u.
  (* Mul *)
  move => [] // p ihp q ihq v w ; t_xrbindP => vp hvp vq hvq hv hw.
  case: (addr_ofs p) ihp => //; case: (addr_ofs q) ihq => //.
  * move => /= z /(_ _ _ hvq) hz z' /(_ _ _ hvp) hz' _ /=.
    move: hv => /=; rewrite /sem_sop2; t_xrbindP => wp /hz' /(_ erefl) [<-] {wp} wq /hz /(_ erefl) [<-] {wq} ?; subst v.
    by case: hw => <-; f_equal;wring.
  * move => /= z /(_ _ _ hvq) hz z' /(_ _ _ hvp) hz' _ /=.
    move: hv => /=; rewrite /sem_sop2; t_xrbindP => wp /hz' /(_ erefl) [<-] {wp} wq /hz /(_ erefl).
    by t_xrbindP => vz -> /= -> /= ?; subst v; f_equal; case: hw => <-;rewrite zero_extend_u.
  move => /= z /(_ _ _ hvq) hz z' /(_ _ _ hvp) hz' _.
  move: hv hw => /=; rewrite /sem_sop2; t_xrbindP => wp /hz' /(_ erefl).
  by t_xrbindP => ? -> /= -> ? /hz /(_ erefl) [<-] <- /= [<-];f_equal;wring.
Qed.

(* -------------------------------------------------------------------- *)
Lemma xscale_ok ii z sc :
  scale_of_z' ii z = ok sc -> 
  z = word_of_scale sc.
Proof. 
  rewrite /scale_of_z' -[X in _ -> X = _]wrepr_unsigned.
  by case: sc (wunsigned z); do! case=> //. 
Qed.

(* -------------------------------------------------------------------- *)

