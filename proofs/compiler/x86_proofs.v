(* -------------------------------------------------------------------- *)
From mathcomp Require Import all_ssreflect.
(* ------- *) Require Import xseq utils expr linear compiler_util low_memory.
(* ------- *) Require Import sem linear linear_sem x86 x86_sem.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Unset SsrOldRewriteGoalsOrder.

Local Open Scope string_scope. 

Global Opaque String.append.

(* -------------------------------------------------------------------- *)
Lemma to_bool_ok v b : to_bool v = ok b -> v = Vbool b.
Proof. by case: v => //= [b' [->]|[]]. Qed.

Lemma to_word_ok v w : to_word v = ok w -> v = Vword w.
Proof. by case: v => //= [w' [->]|[]]. Qed.

Ltac t_XrbindP :=
  match goal with
  | [ |- Result.bind _ _ = Ok _ _ -> _ ] =>
      let y := fresh "y" in
      let h := fresh "h" in
      apply: rbindP=> y; t_XrbindP=> h;
      t_XrbindP; try move: h; try move: y
  | [ |- ok _ = ok _ -> _ ] =>
      case; t_XrbindP
  | [ |- ciok _ = ok _ -> _ ] =>
      case; t_XrbindP
  | [ |- to_word ?w = ok _ -> _ ] =>
      let h := fresh "h" in
      move/to_word_ok => h; subst w; t_XrbindP
  | [ |- to_bool ?w = ok _ -> _ ] =>
      let h := fresh "h" in
      move/to_bool_ok => h; subst w; t_XrbindP
  | [ |- _ -> _ ] =>
      let h := fresh "h" in move=> h; t_XrbindP; move: h
  | _ => idtac
  end.

Ltac findok := eexists; first by reflexivity.

(* -------------------------------------------------------------------- *)
Lemma eq_regmapP (rg1 rg2 : RegMap.map) : (rg1 =1 rg2) <-> (rg1 = rg2).
Proof. by apply: ffunP. Qed.

(* -------------------------------------------------------------------- *)
Lemma eq_rfmapP (rf1 rf2 : RflagMap.map) : (rf1 =1 rf2) <-> (rf1 = rf2).
Proof. by apply: ffunP. Qed.

(* -------------------------------------------------------------------- *)
Lemma to_estateK c s: to_estate (of_estate s c) = s.
Proof. by case: s. Qed.

(* -------------------------------------------------------------------- *)
Lemma get_var_type vm x v :
  get_var vm x = ok v -> type_of_val v = vtype x.
Proof.
by apply: on_vuP => [t ? <-|_ [<-]//]; apply: type_of_to_val.
Qed.

(* -------------------------------------------------------------------- *)
Definition to_rbool (v : value) :=
  match v with
  | Vbool   b    => ok (Def b)
  | Vundef sbool => ok Undef
  | _            => type_error
  end.

(* -------------------------------------------------------------------- *)
Definition of_rbool (v : RflagMap.rflagv) :=
  if v is Def b then Vbool b else Vundef sbool.

(* -------------------------------------------------------------------- *)
Lemma to_rboolK rfv : to_rbool (of_rbool rfv) = ok rfv.
Proof. by case: rfv. Qed.

(* -------------------------------------------------------------------- *)
Lemma uniq_regs_rflags_strings :
  uniq ([seq v.1 | v <- regs_strings  ] ++
        [seq v.1 | v <- rflags_strings] ).
Proof. by []. Qed.

(* -------------------------------------------------------------------- *)
Lemma mem_regs_strings_rflags (x : string) :
     x    \in [seq v.1 | v <-   regs_strings]
  -> x \notin [seq v.1 | v <- rflags_strings].
Proof. by apply/allP: x. Qed.

(* -------------------------------------------------------------------- *)
Lemma mem_rflags_strings_regs (x : string) :
     x    \in [seq v.1 | v <- rflags_strings]
  -> x \notin [seq v.1 | v <-   regs_strings].
Proof. by apply/allP: x. Qed.

(* -------------------------------------------------------------------- *)
Definition rflags_of_lvm (vm : vmap) (rf : rflagmap) :=
  forall x r, rflag_of_string x = Some r ->
    match get_var vm {| vtype := sbool; vname := x |} with
    | Ok v =>
      match to_rbool v with
      | Ok b => rf r = b
      | _    => False
      end
    | _ => False
    end.

(* -------------------------------------------------------------------- *)
Definition regs_of_lvm (vm : vmap) (rf : regmap) :=
  forall x r, reg_of_string x = Some r ->
    match get_var vm {| vtype := sword; vname := x |} with
    | Ok v =>
        match to_word v with
        | Ok    v => rf r = v
        | Error _ => False
        end
    | Error _ => False
    end. 

(* -------------------------------------------------------------------- *)
Lemma rflags_eq vm xf1 xf2 :
     rflags_of_lvm vm xf1
  -> rflags_of_lvm vm xf2
  -> xf1 = xf2.
Proof.
move=> eq1 eq2. apply/eq_rfmapP => rf.
move/(_ (string_of_rflag rf) rf (rflag_of_stringK _)): eq2.
move/(_ (string_of_rflag rf) rf (rflag_of_stringK _)): eq1.
by case: get_var => // v; case: to_rbool => // a -> ->.
Qed.

(* -------------------------------------------------------------------- *)
Lemma regs_eq vm xr1 xr2 :
     regs_of_lvm vm xr1
  -> regs_of_lvm vm xr2
  -> xr1 = xr2.
Proof.
move=> eq1 eq2; apply/eq_regmapP => rf.
move/(_ (string_of_register rf) rf (reg_of_stringK _)): eq2.
move/(_ (string_of_register rf) rf (reg_of_stringK _)): eq1.
by case: get_var => // v; case: to_word => // a -> ->.
Qed.

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
Lemma inj_reg_of_var ii x y v :
     reg_of_var ii x = ok v
  -> reg_of_var ii y = ok v
  -> x = y.
Proof.
case: x y => -[]// x [] []// y /=.
case Ex: (reg_of_string x) => [vx|] // -[?]; subst vx.
case Ey: (reg_of_string y) => [vy|] // -[?]; subst vy.
by f_equal; apply: (inj_reg_of_string Ex Ey).
Qed.

(* -------------------------------------------------------------------- *)
Lemma write_lvals_rcons gd xs vs x v s1 s2:
     write_lvals gd s1 (rcons xs x) (rcons vs v) = ok s2
  -> exists2 s,
       write_lvals gd s1 xs vs = ok s
     & write_lval gd x v s = ok s2.
Proof.
elim: xs vs s1 => [|xh xs ih] [|vh vs] s1 //=.
+ by t_xrbindP=> s ok_s <-; exists s1.
+ by case vs => [|_ _] /=; t_xrbindP.
+ by t_xrbindP=> s _; case: {ih} xs.
t_xrbindP=> s h1 /ih [s'] h2 h3; exists s' => //.
by rewrite h1 /=.
Qed.

(* -------------------------------------------------------------------- *)
Inductive xs86_equiv (c : lcmd) (s : lstate) (xs : x86_state) :=
| XS86Equiv of
    s.(lmem) = xs.(xmem)
  & assemble_c c = ok xs.(xc)
  & assemble_c s.(lc) = ok (drop xs.(xip) xs.(xc))
  & xs.(xip) <= size xs.(xc)
  & rflags_of_lvm s.(lvm) xs.(xrf)
  & regs_of_lvm s.(lvm) xs.(xreg).

(* -------------------------------------------------------------------- *)
Lemma xs86_equiv_cons li1 li c s xs :
     s.(lc) = li1 :: li
  -> xs86_equiv c s xs
  -> xs86_equiv c
       {| lmem := s.(lmem); lvm := s.(lvm); lc := li |}
       (st_write_ip xs.(xip).+1 xs).
Proof.
case: s=> /= lm lvm _ -> [/= -> eqc eqd]; split => //.
+ move: eqd; rewrite /assemble_c /=; t_xrbindP.
  move=> a _ sa -> eqd; congr ok; move/(congr1 behead): eqd.
  by move=> /= ->; rewrite -addn1 addnC -drop_add drop1.
+ rewrite /st_write_ip /= ltnNge; apply/negP => le.
  move: eqd; rewrite drop_oversize // /assemble_c /=.
  by case: assemble_i => //= a; case: mapM.
Qed.

(* -------------------------------------------------------------------- *)
Lemma xgetflag_r ii c x rf v b s xs :
     xs86_equiv c s xs
  -> rflag_of_var ii x = ok rf
  -> get_var s.(lvm) x = ok v
  -> to_rbool v = ok b
  -> xs.(xrf) rf = b.
Proof.
case=> _ _ _ _ eqv _; case: x => -[] //= x.
case E: rflag_of_string => [vx|] // -[<-] ok_v ok_b.
by move/(_ _ _ E): eqv; rewrite ok_v ok_b.
Qed.

(* -------------------------------------------------------------------- *)
Lemma xgetflag_ex ii c x rf v s xs :
     xs86_equiv c s xs
  -> rflag_of_var ii x = ok rf
  -> get_var s.(lvm) x = ok v
  -> exists2 b, to_rbool v = ok b & xs.(xrf) rf = b.
Proof.
case=> _ _ _ _ eqv _; case: x => -[] //= x.
case E: rflag_of_string => [vx|] // [<-] ok_v.
have /= := get_var_type ok_v; case: v ok_v => //=.
+ move=> b ok_v _; exists (Def b) => //.
  by move/(_ _ _ E): eqv; rewrite ok_v /=.
case=> //= ok_v _; exists Undef => //.
by move/(_ _ _ E): eqv; rewrite ok_v /=.
Qed.

(* -------------------------------------------------------------------- *)
Lemma xgetflag ii c x rf v b s xs :
     xs86_equiv c s xs
  -> rflag_of_var ii x = ok rf
  -> get_var s.(lvm) x = ok v
  -> to_bool v = ok b
  -> xs.(xrf) rf = Def b.
Proof.
move=> eqv ok_rf ok_v ok_b.
rewrite (xgetflag_r (b := Def b) eqv ok_rf ok_v) //.
by case: {ok_v} v ok_b => //= [? [<-]|] // [].
Qed.

(* -------------------------------------------------------------------- *)
Lemma xgetreg_ex ii c x r v s xs :
     xs86_equiv c s xs
  -> reg_of_var ii x = ok r
  -> get_var s.(lvm) x = ok v
  -> exists2 w, to_word v = ok w & xs.(xreg) r = w.
Proof.
case=> _ _ _ _ _ eqv; case: x => -[] //= x.
case E: reg_of_string => [vx|] // [<-] ok_v.
have /= := get_var_type ok_v; case: v ok_v => //=.
+ move=> w ok_v _; exists w => //.
  by move/(_ _ _ E): eqv; rewrite ok_v /=.
+ by case=> // ok_ud _; move/(_ _ _ E): eqv; rewrite ok_ud.
Qed.

(* -------------------------------------------------------------------- *)
Lemma xgetreg ii c x r v w s xs :
     xs86_equiv c s xs
  -> reg_of_var ii x = ok r
  -> get_var s.(lvm) x = ok v
  -> to_word v = ok w
  -> xs.(xreg) r = w.
Proof.
case=> _ _ _ _ _ eqv; case: x => -[] //= x.
case E: reg_of_string => [vx|] // -[<-] ok_v ok_w.
by move/(_ _ _ E): eqv; rewrite ok_v ok_w.
Qed.

(* -------------------------------------------------------------------- *)
Lemma ok_sem_op1_b f v b :
  sem_op1_b f v = ok b ->
    exists2 vb, to_bool v = ok vb & b = Vbool (f vb).
Proof.
rewrite /sem_op1_b /mk_sem_sop1; t_xrbindP => /= vb ->.
by move=> ok_b; exists vb.
Qed.

(* -------------------------------------------------------------------- *)
Lemma ok_sem_op2_b f v1 v2 b :
  sem_op2_b f v1 v2 = ok b ->
    exists2 vb,
        [/\ to_bool v1 = ok vb.1 & to_bool v2 = ok vb.2]
      & b = Vbool (f vb.1 vb.2).
Proof.
rewrite /sem_op2_b /mk_sem_sop2; t_xrbindP.
by move=> vb1 ok1 vb2 ok2 fE; exists (vb1, vb2).
Qed.

(* -------------------------------------------------------------------- *)
Lemma xeval_cond {ii e v c ct gd s xs} :
    xs86_equiv c s xs
 -> assemble_cond ii e = ok ct
 -> sem_pexpr gd (to_estate s) e = ok v
 -> eval_cond ct xs.(xrf) = to_bool v.
Proof.
move=> eqv; case: e => //.
+ move=> x /=; t_xrbindP => r ok_r ok_ct ok_v.
  have [vb h] := xgetflag_ex eqv ok_r ok_v.
  case: {ok_r} r ok_ct h => // -[<-];
    rewrite /eval_cond => ok_vb ->;
    by case: {ok_v} v ok_vb => //= [b [<-//]|[]//[<-]].
+ do 2! case=> //; move=> x /=; t_xrbindP => r.
  move=> ok_r ok_ct vx ok_vx ok_v.
  have /ok_sem_op1_b[vb ok_vb vE] := ok_v.
  have := xgetflag eqv ok_r ok_vx ok_vb => DE.
  by case: {ok_r} r ok_ct DE => // -[<-] /= -> //=; rewrite vE.
+ case=> //; first do 3! case=> //; move=> x.
  * case=> //; first do 2! case=> //; move=> y.
    - move=> /=; t_xrbindP => r1 ok_r1 r2 ok_r2.
      case: ifPn => // /andP[]; do 2! move/eqP=> ?; subst r1 r2.
      case=> <- resx vx ok_vx ok_resx resy vy ok_vy ok_resy ok_v.
      have /ok_sem_op1_b[rxb ok_rxb resxE] := ok_resx.
      have /ok_sem_op1_b[ryb ok_ryb resyE] := ok_resy.
      have := xgetflag eqv ok_r1 ok_vx ok_rxb => CFE.
      have := xgetflag eqv ok_r2 ok_vy ok_ryb => ZFE.
      rewrite /eval_cond; rewrite CFE ZFE /=; subst resx resy.
      by move: ok_v; rewrite /sem_op2_b /mk_sem_sop2 /= => -[<-].
    - case: y => // y; case=> // z; do 2! case=> //; case=> // t.
      move=> /=; t_xrbindP => rx ok_rx ry ok_ry rz ok_rz rt ok_rt.
      case: ifP => //; rewrite -!andbA => /and4P[].
      do 4! move/eqP=> ?; subst rx ry rz rt => -[<-].
      move=> vNx vx ok_vx ok_vNx res vby vy ok_vy ok_vby.
      move=> vz ok_vz vNt vt ok_vt ok_vNt vbz ok_vbz vbNz ok_vbNz.
      move=> /esym resE ok_v.
      have [vbx ok_vbx ?] := ok_sem_op1_b ok_vNx; subst vNx.
      have [vbt ok_vbt ?] := ok_sem_op1_b ok_vNt; subst vNt.
      have := xgetflag eqv ok_rx ok_vx ok_vbx => ZFE.
      have := xgetflag eqv ok_ry ok_vy ok_vby => SFE.
      have := xgetflag eqv ok_rt ok_vt ok_vbt => OFE.
      rewrite /= ZFE SFE OFE /=; move: ok_v.
      rewrite /sem_op2_b /mk_sem_sop2 /= resE.
      t_xrbindP=> vres; case: (boolP vby) => hvby //=; last first.
      + by case=> <- <-; rewrite [false == _]eq_sym /= eqbF_neg.
      have := inj_rflag_of_var ok_rz ok_rt => eq_zt.
      have {eq_zt} ?: vt = vz; [have := ok_vz | subst vz].
      + by rewrite eq_zt ok_vt => -[].
      by rewrite ok_vbt => -[<-] <-.
  * case: x => // x; case => // [y /=|].
    - t_xrbindP=> rx ok_rx ry ok_ry; case: ifP => //.
      case/andP; do 2! move/eqP=> ?; subst rx ry.
      case=> <- vx ok_vx vy ok_vy ok_v.
      have [[bx by_] /=] := ok_sem_op2_b ok_v => -[ok_bx ok_by] vE.
      have ->/= := xgetflag eqv ok_rx ok_vx ok_bx.
      have ->/= := xgetflag eqv ok_ry ok_vy ok_by.
      by rewrite vE.
    - case=> // y; do 2! case=> //; case=> // z; case=> //= t.
      t_xrbindP=> rx ok_rx ry ok_ry rz ok_rz rt ok_rt.
      case: ifP=> //; rewrite -!andbA => /and4P[].
      do 4! move/eqP=> ?; subst rx ry rz rt => -[<-].
      move=> vx ok_vx res vby vy ok_vy ok_vby vNz vz ok_vz ok_vNz.
      move=> vt ok_vt vbNz ok_vbNz vbt ok_vbt /esym resE ok_v.
      have [[vbx vbres]] := ok_sem_op2_b ok_v.
      rewrite /fst /snd => -[ok_vbx ok_vbres] ?; subst v.
      have [vbz ok_vbz ?] := ok_sem_op1_b ok_vNz; subst vNz.
      have := xgetflag eqv ok_rx ok_vx ok_vbx => ZFE.
      have := xgetflag eqv ok_ry ok_vy ok_vby => SFE.
      have := xgetflag eqv ok_rz ok_vz ok_vbz => OFE.
      rewrite /= ZFE SFE OFE /=; move: ok_vbres; rewrite resE.
      case: (boolP vby) => hvby /= => [[<-]|].
      + by rewrite eq_sym eqb_id.
      have := inj_rflag_of_var ok_rz ok_rt => eq_zt.
      have {eq_zt} ?: vt = vz; [have := ok_vz | subst vt].
      + by rewrite eq_zt ok_vt => -[].
      by rewrite ok_vbz => -[<-]; rewrite eq_sym eqbF_neg negbK.
+ case=> // x [] // => [|[] // [] //] y.
  * case=> // -[] // -[] // z /=; t_xrbindP.
    move=> rx ok_rx ry ok_ry rz ok_rz.
    case: ifPn => //; rewrite -!andbA => /and3P[].
    do 3! move/eqP=> ?; subst rx ry rz.
    have eq_xy: v_var y = v_var z.
    - by apply/(inj_rflag_of_var ok_ry ok_rz).
    case=> <- vbx vx ok_vx ok_vbx vy ok_vy.
    move=> rvz vz ok_vz ok_rvz vby ok_vby rbz ok_rbz ok_v.
    have /ok_sem_op1_b[vbz ok_vbz ?] := ok_rvz; subst rvz.
    have := xgetflag eqv ok_rx ok_vx ok_vbx => SFE.
    have := xgetflag eqv ok_rz ok_vz ok_vbz => OFE.
    rewrite /= SFE OFE /=; have := inj_rflag_of_var ok_ry ok_rz.
    move=> eq_yz; have {eq_yz} ?: vy = vz; [have := ok_vy|subst vy].
    - by rewrite eq_yz ok_vz => -[].
    rewrite -ok_v; case: (boolP vbx); rewrite eq_sym => _.
    - by rewrite ok_vbz eqb_id. - by rewrite eqbF_neg.
  * case=> // z /=; t_xrbindP => vx ok_x vy ok_y vz ok_z.
    case: ifPn => //; rewrite -!andbA => /and3P[].
    do 3! move/eqP=> ?; subst vx vy vz; case=> <-.
    move=> vbx vx ok_vx ok_vbx vNy vy ok_vy ok_vNy.
    move=> vz ok_vz vbNy ok_vbNy vbNz ok_vbNz ok_v.
    have /ok_sem_op1_b[vby ok_vby ?] := ok_vNy; subst vNy.
    have := xgetflag eqv ok_x ok_vx ok_vbx => SFE.
    have := xgetflag eqv ok_y ok_vy ok_vby => OFE.
    rewrite /= SFE OFE /= -ok_v; case: (boolP vbx) => _.
    - by rewrite eq_sym eqb_id.
    rewrite eq_sym eqbF_neg negbK; have := inj_rflag_of_var ok_y ok_z.
    move=> eq_yz; have {eq_yz} ?: vy = vz; [have := ok_vy|subst vy].
    - by rewrite eq_yz ok_vz => -[]. - by rewrite -ok_vby.
Qed.

(* -------------------------------------------------------------------- *)
Lemma xfind_label (c c' : lcmd) xc lbl :
     linear.find_label lbl c = Some c'
  -> assemble_c c = ok xc
  -> exists i,
       [/\ find_label lbl xc = ok i
         , i < size xc
         & assemble_c c' = ok (drop i.+1 xc)].
Proof.
elim: c c' xc => [|i c ih] c' xc //=; case: ifPn.
+ case: i => ii [] //= lbl'; rewrite /is_label /= => /eqP<-.
  case=> [<-] /=; rewrite /assemble_c /=; case: mapM => //=.
  move=> sa [<-]; exists 0; split=> //=; rewrite ?drop0 //.
  by rewrite /find_label /= eqxx ltnS.
move=> Nlbl eqc'; rewrite /assemble_c /=.
case E: assemble_i => [a|] //=; case E': mapM => [sa|] //=.
case=> <-; case/(ih _ sa): eqc' => // j [h1 h2 h3].
exists j.+1; split=> //; rewrite /find_label /=.
case: eqP => [|_]; last first.
  by move: h1; rewrite ltnS /find_label; case: ifP => // _ [->].
case: a E => //= pa E [paE]; move: Nlbl E; rewrite paE.
case: i => ii /=; rewrite /is_label /=; case=> //=.
+ by move=> lv _ p _; case: oprd_of_lval => //= ?; case: oprd_of_pexpr.
+ move=> lv op es _; rewrite /assemble_opn.
  case: kind_of_sopn => [ak|b||||] //.
  * case: lvals_as_alu_vars => // -[[v1 v2 v3 v4 v5] ls].
    t_xrbindP=> r1 _ r2 _ r3 _ r4 _ r5 _; case: ifP => // _.
    rewrite /assemble_fopn; case: ak => //.
    - by case: as_pair => // -[e1 e2]; case: ifP => // _; t_xrbindP.
    - move=> b; case: as_pair => // -[e1 e2]; case: as_singleton => //.
      move=> l; t_xrbindP => ev1 _ ev2 _ vl _; case: ifP => // _.
      by case: b.
    - move=> b; case: as_triple => // -[[e1 e2] [] // e3].
      case: as_singleton => // l; t_xrbindP => ev1 _ ev2 _ ev3 _ vl _.
      by do 2! case: ifP => // _; case: b.
    - move=> s. case:es => // e1 [//|e2 l'].
      case: as_singleton => // l; t_xrbindP=> ev1 _ ev2 _ vl _.
      case: ifP => // _. 
      case: s => [s | ].
      + by case:ifP => //;case:s.
      by case: as_singleton => //;case ev2 => // ??;t_xrbindP.
    - case: as_pair => // -[e1 e2]; case: as_pair => // -[l1 l2].
      by t_xrbindP => op1 _ op2 _ op3 _ op4 _; case: ifP.
    - case: as_pair => // -[e1 e2]; case: as_singleton => // l.
      by t_xrbindP => vl _ ve1 _; case: is_wconst => //; t_xrbindP; case: eqP.
    - case: as_singleton => // e; case: as_singleton => // l.
      by t_xrbindP=> v _ ve _; case: eqP => //.
    - case: es => //;case: as_singleton => // l.
      by t_xrbindP.
  * case: lvals_as_cnt_vars => // -[[v1 v2 v3 v4] ls].
    t_xrbindP => v _ bv1 _ bv2 _ bv3 _ bv4 _; case: ifP => // _.
    case: as_singleton => // ae; t_xrbindP=> vae _.
    by case: ifP => // _; case: b.
  * by case: as_singleton => // l; case: as_singleton => // e; t_xrbindP.
  * case: as_singleton => // l; case: as_triple => // -[[e1 e2] e3].
    by t_xrbindP=> vl _ v1 _ v2 _ v3 _; case: ifP.
+ by case: as_singleton => // ?; case: as_quadruple => // [[[[]]]]????; t_xrbindP.
+ by move=> lbl2 /eqP nq [[/esym]].
+ by move=> p l _; case: assemble_cond.
Qed.

(* -------------------------------------------------------------------- *)
Lemma lvals_as_alu_varsT xs x1 x2 x3 x4 x5 l :
     lvals_as_alu_vars xs = Some (ALUVars x1 x2 x3 x4 x5, l)
  -> xs = [:: Lvar x1, Lvar x2, Lvar x3, Lvar x4, Lvar x5 & l].
Proof.
move: xs; do 5! case=> [|[] ?] //; move=> /= l'.
by case=> *; subst.
Qed.

(* -------------------------------------------------------------------- *)
Lemma lvals_as_cnt_varsT xs x1 x2 x3 x4 l :
     lvals_as_cnt_vars xs = Some (CNTVars x1 x2 x3 x4, l)
  -> xs = [:: Lvar x1; Lvar x2; Lvar x3; Lvar x4; l].
Proof.
move: xs; do 4! case=> [|[] ?] //.
by case=> //= ? [] // [*]; subst.
Qed.

(* -------------------------------------------------------------------- *)
Lemma write_var_mem gd x v s1 s2 :
  write_lval gd (Lvar x) v s1 = ok s2 -> s1.(emem) = s2.(emem).
Proof.
by case: s1 s2=> [m1 v1] [m2 v2] /=; rewrite /write_var; t_xrbindP.
Qed.

(* -------------------------------------------------------------------- *)
Lemma write_vars_mem gd xs vs s1 s2 :
  write_lvals gd s1 (map Lvar xs) vs = ok s2 -> s1.(emem) = s2.(emem).
Proof.
elim: xs s1 vs => [|x xs ih] s1 [|v vs] //= => [[->]|] //.
by t_xrbindP=> s h /ih <-; apply (@write_var_mem gd x v).
Qed.

Lemma of_to_val t v w: of_val t v = ok w -> v = to_val w.
Proof.
case:t w => /=.
+ by apply: to_bool_ok.
+ by case: v => //= [ ??[->] | []].
+ case: v => //= [ | []//].
  + by move=> n t p w; case: CEDecStype.pos_dec => // ?; subst p => /= -[->].
  by move=> ???;case:ifP.
by apply: to_word_ok.
Qed.

(* -------------------------------------------------------------------- *)
(* TODO: move this *)
Definition is_sarr t := 
  match t with
  | sarr _ => true
  | _      => false
  end.

Lemma get_set_var x v vm1 vm2 :
  ~~(is_sarr (vtype x)) ->
  set_var vm1 x v = ok vm2 -> get_var vm2 x = ok v.
Proof.
rewrite /get_var=> His;apply: on_vuP=> [t /of_to_val -> <- | ].
+ by rewrite Fv.setP_eq.
case:eqP => // Hw /of_val_error -> [<-]; rewrite Fv.setP_eq /=. 
rewrite /undef_addr; case: vtype Hw His => //=.
Qed.

(* -------------------------------------------------------------------- *)
Lemma get_set_var_ne x y v vm1 vm2 : x <> y ->
  set_var vm1 x v = ok vm2 -> get_var vm2 y = get_var vm1 y.
Proof. 
  rewrite /get_var=> /eqP neq;apply: on_vuP => [t ? <- | ].
  + by rewrite Fv.setP_neq.    
  by move=> ?;case:eqP => // Hw [<-];rewrite Fv.setP_neq.
Qed.

(* -------------------------------------------------------------------- *)
Lemma get_write_var (x:var_i) v s1 s2 :
  ~~(is_sarr (vtype x)) ->
  write_var x v s1 = ok s2 -> get_var s2.(evm) x = ok v.
Proof.
rewrite /write_var => Htx; t_XrbindP => vm ok_vm <-.
by apply: get_set_var ok_vm.
Qed.

(* -------------------------------------------------------------------- *)
Lemma get_write_var_ne x y v s1 s2 : x.(v_var) <> y ->
  write_var x v s1 = ok s2 -> get_var s2.(evm) y = get_var s1.(evm) y.
Proof.
move=> ne_xy; rewrite /write_var; t_XrbindP => vm ok_vm <-.
by apply (get_set_var_ne ne_xy ok_vm).
Qed.

(* -------------------------------------------------------------------- *)
Lemma rflag_of_var_name ii x rf :
  rflag_of_var ii x = ok rf ->
  rflag_of_string x.(vname) = Some rf.
Proof.
case: x => //; case=> // x /=.
by case: rflag_of_string => // => rf' -[->].
Qed.

(* -------------------------------------------------------------------- *)
Definition iserror {E A : Type} (v : result E A) :=
  if v is Error _ then true else false.

(* -------------------------------------------------------------------- *)
Lemma rflag_of_var_regN ii x rf :
     rflag_of_var ii x = ok rf
  -> iserror (reg_of_var ii x).
Proof. by case: x => // -[]. Qed.

(* -------------------------------------------------------------------- *)
Lemma reg_of_var_rflagN ii x rf :
     reg_of_var ii x = ok rf
  -> iserror (rflag_of_var ii x).
Proof. by case: x => // -[]. Qed.

(* -------------------------------------------------------------------- *)
Lemma rflag_get_set rfm rf b :
  (RflagMap.set rfm rf b) rf = Def b.
Proof. by rewrite /RflagMap.set ffunE eqxx. Qed.

(* -------------------------------------------------------------------- *)
Lemma rflag_get_oset rfm rf b :
  (RflagMap.oset rfm rf b) rf = b.
Proof. by rewrite /RflagMap.oset ffunE eqxx. Qed.

(* -------------------------------------------------------------------- *)
Lemma rflag_get_set_ne rfm rf1 rf2 b : rf1 != rf2 ->
  (RflagMap.set rfm rf1 b) rf2 = rfm rf2.
Proof. by rewrite /RflagMap.set ffunE eq_sym => /negbTE ->. Qed.

(* -------------------------------------------------------------------- *)
Lemma rflag_get_oset_ne rfm rf1 rf2 b : rf1 != rf2 ->
  (RflagMap.oset rfm rf1 b) rf2 = rfm rf2.
Proof. by rewrite /RflagMap.oset ffunE eq_sym => /negbTE ->. Qed.

(* -------------------------------------------------------------------- *)
Lemma xwrite_var_orf x b ii rf s1 s2 rfmap :
     rflag_of_var ii (v_var x) = ok rf
  -> rflags_of_lvm s1.(evm) rfmap
  -> write_var x (of_rbool b) s1 = ok s2
  -> rflags_of_lvm s2.(evm) (RflagMap.oset rfmap rf b).
Proof.
move=> ok_rf ok_rm ok_s2 s rf' ok_rf'; set y := Var _ _.
case: (x.(v_var) =P y) => [eq_xy|]; first subst y.
+ rewrite -eq_xy (get_write_var _ ok_s2) /= ?eq_xy //.
  have := rflag_of_var_name ok_rf; rewrite eq_xy /=.
  by rewrite ok_rf' => -[->] /=; rewrite to_rboolK rflag_get_oset.
+ move=> ne_xy; rewrite (get_write_var_ne ne_xy ok_s2).
  move/(_ _ _ ok_rf'): ok_rm; rewrite -/y /=.
  case ok_vy: get_var => [vy|//]; case: to_rbool => // _ <-.
  rewrite rflag_get_oset_ne //; move/eqP: ne_xy; apply: contraNneq.
  move=> ?; subst rf'; apply/eqP; apply: (inj_rflag_of_var ok_rf).
  by rewrite /y /= ok_rf'.
Qed.

(* -------------------------------------------------------------------- *)
Lemma xwrite_var_rf x b ii rf s1 s2 rfmap :
     rflag_of_var ii (v_var x) = ok rf
  -> rflags_of_lvm s1.(evm) rfmap
  -> write_var x (Vbool b) s1 = ok s2
  -> rflags_of_lvm s2.(evm) (RflagMap.set rfmap rf b).
Proof. by apply: (xwrite_var_orf (b := Def b)). Qed.

(* -------------------------------------------------------------------- *)
Lemma xwrite_var_rfN x v ii s1 s2 rfmap :
     iserror (rflag_of_var ii (v_var x))
  -> rflags_of_lvm s1.(evm) rfmap
  -> write_var x v s1 = ok s2
  -> rflags_of_lvm s2.(evm) rfmap.
Proof.
move=> ko_x ok_rm ok_s2 s rf' ok_rf'; rewrite (get_write_var_ne _ ok_s2).
+ case: {ok_s2} x ko_x => -[[] // x vix] /=; case: (x =P s) => [->|].
  * by rewrite ok_rf'.
  * by move=> ne_xs _ [].
+ by apply: ok_rm.
Qed.

(* -------------------------------------------------------------------- *)
Lemma reg_of_var_name ii x reg :
  reg_of_var ii x = ok reg ->
  reg_of_string x.(vname) = Some reg.
Proof.
case: x => //; case=> // x /=.
by case: reg_of_string => // => rf' -[->].
Qed.

(* -------------------------------------------------------------------- *)
Lemma reg_get_set rgm rg w :
  (RegMap.set rgm rg w) rg = w.
Proof. by rewrite /RegMap.set ffunE eqxx. Qed.

(* -------------------------------------------------------------------- *)
Lemma reg_get_set_ne rgm rg1 rg2 w : rg1 != rg2 ->
  (RegMap.set rgm rg1 w) rg2 = rgm rg2.
Proof. by rewrite /RegMap.set ffunE eq_sym => /negbTE ->. Qed.

(* -------------------------------------------------------------------- *)
Lemma xwrite_var_reg ii x reg w s1 s2 rgmap :
     reg_of_var ii (v_var x) = ok reg
  -> regs_of_lvm s1.(evm) rgmap
  -> write_var x (Vword w) s1 = ok s2
  -> regs_of_lvm s2.(evm) (RegMap.set rgmap reg w).
Proof.
move=> ok_reg ok_rm ok_s2 s reg' ok_reg'; set y := Var _ _.
case: (x.(v_var) =P y) => [eq_xy|]; first subst y.
+ rewrite -eq_xy (get_write_var _ ok_s2) ?eq_xy //=.
  have := reg_of_var_name ok_reg; rewrite eq_xy /=.
  by rewrite ok_reg' => -[->]; rewrite reg_get_set.
+ move=> ne_xy; rewrite (get_write_var_ne ne_xy ok_s2).
  move/(_ _ _ ok_reg'): ok_rm; rewrite -/y /=.
  case ok_vy: get_var => [vy|//]; case: to_word => // _ <-.
  rewrite reg_get_set_ne //; move/eqP: ne_xy; apply: contraNneq.
  move=> ?; subst reg'; apply/eqP; apply: (inj_reg_of_var ok_reg).
  by rewrite /y /= ok_reg'.
Qed.

(* -------------------------------------------------------------------- *)
Lemma xwrite_var_regN x v ii s1 s2 rfmap :
     iserror (reg_of_var ii (v_var x))
  -> regs_of_lvm s1.(evm) rfmap
  -> write_var x v s1 = ok s2
  -> regs_of_lvm s2.(evm) rfmap.
Proof.
move=> ko_x ok_rm ok_s2 s rf' ok_rf'; rewrite (get_write_var_ne _ ok_s2).
+ case: {ok_s2} x ko_x => -[[] // x vix] /=; case: (x =P s) => [->|].
  * by rewrite ok_rf'.
  * by move=> ne_xs _ [].
+ by apply: ok_rm.
Qed.

(* -------------------------------------------------------------------- *)
Lemma xswrite_var_reg ii x reg w c cs s1 s2 xs :
     xs86_equiv c (of_estate s1 cs) xs
  -> reg_of_var ii (v_var x) = ok reg
  -> write_var x (Vword w) s1 = ok s2
  -> xs86_equiv c (of_estate s2 cs) (st_write_reg reg w xs).
Proof.
case=> /= xsE okc okd ipE rfE rgE ok_reg ok_s2; split=> //=.
+ move: ok_s2; rewrite /write_var; t_XrbindP.
  by move=> _ _ <- /=; rewrite -xsE.
+ apply: (xwrite_var_rfN (ii := ii) _ rfE ok_s2).
  by apply/reg_of_var_rflagN/ok_reg.
+ by apply: (xwrite_var_reg ok_reg rgE).
Qed.

(* -------------------------------------------------------------------- *)
Lemma xswrite_var_rflat ii x rf b c cs s1 s2 xs :
     xs86_equiv c (of_estate s1 cs) xs
  -> rflag_of_var ii (v_var x) = ok rf
  -> write_var x (Vbool b) s1 = ok s2
  -> xs86_equiv c (of_estate s2 cs) (st_set_rflags rf b xs).
Proof.
case=> /= xsE okc okd ipE rfE rgE ok_rf ok_s2; split=> //=.
+ move: ok_s2; rewrite /write_var; t_XrbindP.
  by move=> _ _ <- /=; rewrite -xsE.
+ by apply (xwrite_var_rf ok_rf rfE).
+ apply: (xwrite_var_regN (ii := ii) _ rgE ok_s2).
  by apply/rflag_of_var_regN/ok_rf.
Qed.

(* -------------------------------------------------------------------- *)
Variant RFI_t := RFI of var_i & rflag & RflagMap.rflagv.

Definition rfi2var  rfi := let: RFI v _  _ := rfi in v.
Definition rfi2lval rfi := let: RFI v _  _ := rfi in Lvar v.
Definition rfi2rf   rfi := let: RFI _ rf _ := rfi in rf.
Definition rfi2rfv  rfi := let: RFI _ _  v := rfi in v.
Definition rfi2val  rfi := of_rbool (rfi2rfv rfi).
Definition rfi2upd  rfi := (rfi2rf rfi, rfi2rfv rfi).

(* -------------------------------------------------------------------- *)
Definition pred_of_rfi ii (rfi : RFI_t) :=
  rflag_of_var ii (rfi2var rfi) = ok (rfi2rf rfi).

(* -------------------------------------------------------------------- *)
Definition pred_of_rfis ii (rfis : seq RFI_t) :=
  foldl and True (map (pred_of_rfi ii) rfis).

(* -------------------------------------------------------------------- *)
Definition is_rf_map ii xrs :=
   all (fun xr =>
          let: RFI v rfv _ := xr in
          if rflag_of_var ii (v_var v) is Ok rf then
            rfv == rf
          else false) xrs.

(* -------------------------------------------------------------------- *)
Lemma rfmap_update0 rfm : RflagMap.update rfm (fun _ => None) = rfm.
Proof. by apply/eq_rfmapP=> r; rewrite /RflagMap.update ffunE. Qed.

(* -------------------------------------------------------------------- *)
Lemma rfmap_update_of_sets upd (rfm : rflagmap) :
    foldl (fun rfm v => RflagMap.oset rfm v.1 v.2) rfm upd
  = RflagMap.update rfm (fun rf => assoc (rev upd) rf).
Proof.
set F := fun _ _ => _; elim: upd rfm => [|[r b] upd ih] rfm /=.
+ by rewrite rfmap_update0.
rewrite rev_cons -cats1 ih; apply/eq_rfmapP=> rf.
rewrite /RflagMap.update !ffunE /= assoc_cat /=.
by case: (assoc (rev upd) rf) => //; case: eqP.
Qed.

(* -------------------------------------------------------------------- *)
Lemma xwrite_vars_rf gd xrs ii s1 s2 xs1 :
     is_rf_map ii xrs
  -> rflags_of_lvm s1.(evm) xs1
  -> write_lvals gd s1 (map rfi2lval xrs) (map rfi2val xrs) = ok s2
  -> rflags_of_lvm s2.(evm) (RflagMap.update xs1 (fun rf =>
       assoc (rev [seq rfi2upd v | v <- xrs]) rf)).
Proof.
rewrite -rfmap_update_of_sets; elim/last_ind: xrs s2 xs1.
+ by move=> /= xs1 s2 _ ? -[<-].
move=> xrs [x r b] ih s2 xs1; rewrite /is_rf_map all_rcons.
rewrite  -/(is_rf_map _ _) => /andP[].
case Ex: rflag_of_var => [rf|//] /eqP-> ok_xrs ok_xs1 ok_s2.
move: ok_s2; rewrite 2!map_rcons => /write_lvals_rcons /=.
case=> s' /ih -/(_ _ ok_xrs ok_xs1) {ih}ih ok_s2.
by rewrite map_rcons -cats1 foldl_cat /=; apply: (xwrite_var_orf Ex ih).
Qed.

(* -------------------------------------------------------------------- *)
Lemma xwrite_vars_rf_regN gd xrs ii s1 s2 xs1 :
     regs_of_lvm s1.(evm) xs1
  -> is_rf_map ii xrs
  -> write_lvals gd s1 (map rfi2lval xrs) (map rfi2val xrs) = ok s2
  -> regs_of_lvm s2.(evm) xs1.
Proof.
elim: xrs s1 => [|[x r b] xrs ih] s1 rg1E /=; first by move=> _ [<-].
case ok_x: rflag_of_var => [rf|//] /andP[/eqP _ /ih {ih}ih].
t_XrbindP=> s' ok_s' ok_s2; have := rflag_of_var_regN ok_x.
by move=> /xwrite_var_regN /(_ rg1E ok_s') /ih; apply.
Qed.

(* -------------------------------------------------------------------- *)
Lemma eq_update_rf f1 f2 rfm :
  f1 =1 f2 -> RflagMap.update rfm f1 = RflagMap.update rfm f2.
Proof.
move=> eq_f; apply/eq_rfmapP => rf /=.
by rewrite /RflagMap.update !ffunE /= eq_f.
Qed.

(* -------------------------------------------------------------------- *)
Lemma xaddr_ofs_const gd s e v z :
     sem_pexpr gd s e = ok v
  -> addr_ofs e = Ofs_const z
  -> to_word v = ok (I64.repr z).
Proof.
elim: e v z => //; first by case=> // z' _ v z -[<-] -[<-].
case=> // -[]// p1 ih1 p2 ih2 v z; rewrite [X in X -> _]/=.
+ t_xrbindP=> v1 /ih1 {ih1}ih1 v2 /ih2 {ih2}ih2 ok_v /=.
  case E1: addr_ofs => [z1||||] //;
  case E2: addr_ofs => [z2||||] //.
  case=> <-; move: ok_v; rewrite /sem_op2_w /mk_sem_sop2.
  t_xrbindP=> w1 ok_w1 w2 ok_w2 ?; subst v; congr ok.
  move: ok_w1 ok_w2 => /=; rewrite !(ih1 z1, ih2 z2) //.
  by move=> [<-] [<-]; rewrite -iword_addP /iword_add repr_mod.
+ t_xrbindP=> v1 /ih1 {ih1}ih1 v2 /ih2 {ih2}ih2 ok_v /=.
  case E1: addr_ofs => [z1||||] //;
  case E2: addr_ofs => [z2||||] //.
  case=> <-; move: ok_v; rewrite /sem_op2_w /mk_sem_sop2.
  t_xrbindP=> w1 ok_w1 w2 ok_w2 ?; subst v; congr ok.
  move: ok_w1 ok_w2 => /=; rewrite !(ih1 z1, ih2 z2) //.
  by move=> [<-] [<-]; rewrite -iword_mulP /iword_mul repr_mod.
Qed.

(* -------------------------------------------------------------------- *)
Lemma xaddr_ofs_var c s xs gd ii e v r x :
     xs86_equiv c s xs
  -> sem_pexpr gd (to_estate s) e = ok v
  -> reg_of_var ii (v_var x) = ok r
  -> addr_ofs e = Ofs_var x
  -> to_word v = ok (xs.(xreg) r).
Proof.
move=> eqv; case: e => // [[]//||]; last first.
+ case=> // -[]// e1 e2 /=; t_xrbindP=> v1 _ v2 _ _ _.
  - by do! case: addr_ofs => //. - by do! case: addr_ofs => //.
move=> y /= ok_v ok_r -[?]; subst y.
by case: (xgetreg_ex eqv ok_r ok_v) => w -> ->.
Qed.

(* -------------------------------------------------------------------- *)
Lemma xscale_ok ii z sc :
   scale_of_z ii z = ok sc
-> I64.repr z = word_of_scale sc.
Proof. by case: sc z; do! case=> //. Qed.

(* -------------------------------------------------------------------- *)
Lemma xaddr_ofs_mul c s xs gd ii e v r sc x1 x2 :
     xs86_equiv c s xs
  -> sem_pexpr gd (to_estate s) e = ok v
  -> scale_of_z ii x1 = ok sc
  -> reg_of_var ii (v_var x2) = ok r
  -> addr_ofs e = Ofs_mul x1 x2
  -> to_word v = ok (I64.mul (word_of_scale sc) (xs.(xreg) r)).
Proof.
move=> eqv; case: e => // [[]//|] -[]// -[]// e1 e2 /=.
+ by t_xrbindP=> v1 _ v2 _ _ _ _; do! case: addr_ofs => //.
t_xrbindP=> v1 ok_v1 v2 ok_v2; rewrite /sem_op2_w.
rewrite /mk_sem_sop2; t_xrbindP=> /= w1 ok_w1 w2 ok_w2.
move=> ? ok_sc ok_r; subst v;
  case E1: addr_ofs => [z1|x|||] //;
  case E2: addr_ofs => [z2|y|||] //;
  case=> ? ?; subst x1 x2; congr ok.
+ have := xaddr_ofs_var eqv ok_v2 ok_r E2; rewrite ok_w2 => -[<-].
  have := xaddr_ofs_const ok_v1 E1; rewrite ok_w1 => -[->].
  by rewrite -(xscale_ok ok_sc).
+ have := xaddr_ofs_var eqv ok_v1 ok_r E1; rewrite ok_w1 => -[<-].
  have := xaddr_ofs_const ok_v2 E2; rewrite ok_w2 => -[->].
  by rewrite -(xscale_ok ok_sc) I64.mul_commut.
Qed.

(* -------------------------------------------------------------------- *)
Lemma xaddr_ofs_add c s xs gd ii e v r w sc x1 x2 x3 :
   xs86_equiv c s xs
-> sem_pexpr gd (to_estate s) e = ok v
-> scale_of_z ii x1 = ok sc
-> reg_of_var ii (v_var x2) = ok r
-> word_of_int x3 = ok w
-> addr_ofs e = Ofs_add x1 x2 x3
-> to_word v = ok (I64.add w (I64.mul (word_of_scale sc) (xs.(xreg) r))).
Proof.
move=> eqv; case: e => // [[]//|] -[]// -[]// e1 e2 /=; last first.
+ by t_xrbindP=> v1 _ v2 _ _ _ _; do! case: addr_ofs => //.
t_xrbindP=> v1 ok_v1 v2 ok_v2; rewrite /sem_op2_w.
rewrite /mk_sem_sop2; t_xrbindP=> /= w1 ok_w1 w2 ok_w2.
move=> ? ok_sc ok_r ok_w; subst v;
  case E1: addr_ofs => [z1|x|sc1 t1||] //;
  case E2: addr_ofs => [z2|y|sc2 t2||] //;
  case=> ? ? ?; subst x1 x2 x3.
+ case: ok_sc => <- /=; rewrite I64.mul_commut I64.mul_one.
  have := xaddr_ofs_var eqv ok_v2 ok_r E2; rewrite ok_w2.
  have := xaddr_ofs_const ok_v1 E1; rewrite ok_w1.
  by move=> [->] [->] /=; case: ok_w => <-.
+ have := xaddr_ofs_const ok_v1 E1; rewrite ok_w1 => -[->].
  have := xaddr_ofs_mul eqv ok_v2 ok_sc ok_r E2.
  by rewrite ok_w2 => -[<-]; case: ok_w => ->.
+ case: ok_sc=> <- /=; rewrite I64.mul_commut I64.mul_one.
  have := xaddr_ofs_var eqv ok_v1 ok_r E1; rewrite ok_w1.
  have := xaddr_ofs_const ok_v2 E2; rewrite ok_w2.
  by move=> [->] [->] /=; case: ok_w => <-; rewrite I64.add_commut.
+ have := xaddr_ofs_const ok_v2 E2; rewrite ok_w2 => -[->].
  have := xaddr_ofs_mul eqv ok_v1 ok_sc ok_r E1.
  by rewrite ok_w1 => -[<-]; case: ok_w => ->; rewrite I64.add_commut.
Qed.

(*  -------------------------------------------------------------------- *)
Lemma xread_ok gd ii v e op c s xs :
     xs86_equiv c s xs
  -> oprd_of_pexpr ii e = ok op
  -> sem_pexpr gd (to_estate s) e = ok v
  -> exists2 w, read_oprd gd op xs = ok w & v = Vword w.
Proof.
move=> eqv; case: e => //.
+ by case=> //= z [<-] [<-] /=; eexists.
+ move=> x; rewrite /oprd_of_pexpr /=; t_xrbindP.
  move=> r ok_r -[<-] ok_v /=; eexists; first by reflexivity.
  case: (xgetreg_ex eqv ok_r ok_v) => w ok_w ->.
  by case: {+}v ok_w => // [|[]//] w' -[->].
+ move=> g h; apply ok_inj in h; subst op; rewrite /= /get_global.
  case: (get_global_word _ _) => // v' h; apply ok_inj in h.
  by subst; eauto.
move=> x e /=; t_xrbindP => r1 ok_r1 w ok_w [<-].
move=> z o ok_o ok_z z' o' ok_o' ok_z' res ok_res <- {v} /=.
exists res => //; rewrite -ok_res; f_equal; first by case: eqv.
move: ok_w; rewrite /addr_of_pexpr.
case Ee: addr_ofs => [z''|y|y1 y2|v1 v2 v3|] //.
+ t_xrbindP=> w' -[?]; subst w' => -[<-]; rewrite /decode_addr /=.
  rewrite I64.mul_commut I64.mul_one I64.add_zero.
  rewrite (xgetreg eqv ok_r1 ok_o ok_z) I64.add_commut.
  suff ->: z' = I64.repr z'' by [].
  by rewrite (xaddr_ofs_const ok_o' Ee) in ok_z'; case: ok_z'.
+ t_xrbindP=> r ok_r -[<-]; rewrite /decode_addr /=.
  rewrite I64.mul_commut I64.mul_one I64.add_zero_l.
  rewrite (xgetreg eqv ok_r1 ok_o ok_z); f_equal.
  by rewrite (xaddr_ofs_var eqv ok_o' ok_r Ee) in ok_z'; case: ok_z'.
+ t_xrbindP=> r ok_r sc ok_sc -[<-]; rewrite /decode_addr /=.
  rewrite I64.add_zero_l (xgetreg eqv ok_r1 ok_o ok_z); f_equal.
  by rewrite (xaddr_ofs_mul eqv ok_o' ok_sc ok_r Ee) in ok_z'; case: ok_z'.
+ t_xrbindP=> // r2 ok_r2 w3 ok_w3 sc ok_sc -[<-].
  rewrite /decode_addr /= (xgetreg eqv ok_r1 ok_o ok_z).
  rewrite -I64.add_assoc [I64.add w3 _]I64.add_commut I64.add_assoc.
  rewrite (xaddr_ofs_add eqv ok_o' ok_sc ok_r2 ok_w3 Ee) in ok_z'.
  by case: ok_z' => <-.
Qed.

(*  -------------------------------------------------------------------- *)
Lemma xread_ireg_ok gd ii v e op c s xs :
     xs86_equiv c s xs
  -> ireg_of_pexpr ii e = ok op
  -> sem_pexpr gd (to_estate s) e = ok v
  -> exists2 w, read_ireg op xs = w & v = Vword w.
Proof.
move=> eqv; case: e => // [[] // z|] /=.
+ by case=> [<-] [<-]; eauto.
move=> x; t_xrbindP=> r ok_r [<-] ok_v.
by case: (xgetreg_ex eqv ok_r ok_v) => w /to_word_ok -> <-; eauto.
Qed.

(* -------------------------------------------------------------------- *)
Lemma xwrite_ok ii x (v : word) op c cs gd (s1 s2 : estate) xs1 :
     xs86_equiv c (of_estate s1 cs) xs1
  -> oprd_of_lval ii x = ok op
  -> write_lval gd x v s1 = ok s2
  -> exists2 xs2, write_oprd op v xs1 = ok xs2
                & xs86_equiv c (of_estate s2 cs) xs2.
Proof.
move=> eqv; case: x => // [x|x e] /=.
+ t_XrbindP=> r ok_r /esym opE ok_s2; subst op => /=.
  by findok; apply: (xswrite_var_reg eqv ok_r).
t_XrbindP=> r ok_r w ok_w /esym opE vx ok_vx ve ok_ve m ok_m.
move=> ?; subst s2 => /=; case: e ok_w ok_ve => // -[] //=.
move=> z -[?] -[?]; subst w ve op => /=; rewrite /decode_addr /=.
rewrite I64.mul_commut I64.mul_one I64.add_zero I64.add_commut.
rewrite /st_write_mem (xgetreg eqv ok_r ok_vx (erefl _)).
by case: {+}eqv => <- okc okd ipE rfE rgE; rewrite ok_m /=; findok.
Qed.

(* -------------------------------------------------------------------- *)
Lemma reg_oprd_of_lvalI ii x reg :
     oprd_of_lval ii x = ok (Reg_op reg)
  -> exists2 vx, x = Lvar vx & reg_of_var ii vx = ok reg.
Proof.
case: x => //= x; last by move=> e; t_xrbindP.
by t_xrbindP=> r' ok_r' -[?]; subst r'; exists x.
Qed.

(* -------------------------------------------------------------------- *)
Lemma imm_oprd_of_lvalI ii x z :
  oprd_of_lval ii x = ok (Imm_op z) -> false.
Proof. by case: x => //= [?|??]; t_xrbindP. Qed.

(* -------------------------------------------------------------------- *)
Lemma glo_oprd_of_lvalI ii x g :
  oprd_of_lval ii x = ok (Glo_op g) -> false.
Proof. by case: x => //= [?|??]; t_xrbindP. Qed.

(* -------------------------------------------------------------------- *)
Lemma reg_oprd_of_pexprI ii e reg :
     oprd_of_pexpr ii e = ok (Reg_op reg)
  -> exists2 vx, e = Pvar vx & reg_of_var ii vx = ok reg.
Proof.
case: e => //= x; last by move=> e; t_xrbindP.
+ by case: x.
+ by t_xrbindP=> r' ok_r' -[?]; subst r'; exists x.
Qed.

(* -------------------------------------------------------------------- *)
Lemma word_of_pexprP gd ii e w s : 
  word_of_pexpr ii e = ok w ->
  sem_pexpr gd s e = ok (Vword w).
Proof. by case: e => // -[] //= z [<-]. Qed.

(* -------------------------------------------------------------------- *)
Lemma oreg_of_pexprP gd ii lm vm e xr r w : 
  regs_of_lvm vm xr ->
  oreg_of_pexpr ii e = ok r ->
  sem_pexpr gd {| emem := lm; evm := vm |} e = ok (Vword w) ->
  (odflt I64.zero (omap xr r)) = w.
Proof.
case: e => //= [ []// z| x] Hvm.
+ by case: eqP => //= -> [<-] [<-].
apply: rbindP => r';case: x => -[[] xn] ? //=.
case Heq: reg_of_string => [r1|] // -[<-] [<-] /= Hget.
by have := Hvm _ _ Heq;rewrite Hget.   
Qed.

(* -------------------------------------------------------------------- *)
Lemma scale_of_zP ii wsc sc :
  scale_of_z ii (I64.unsigned wsc) = ok sc -> 
  (word_of_scale sc) = wsc.
Proof.
move=> h; apply/eqP; case: wsc h => z; rewrite /scale_of_z /=.
by case: z => //= -[||? [<-]]// [||? [<-]]// [||? [<-]]// [||? [<-]].
Qed.

(* -------------------------------------------------------------------- *)
Lemma write_lvalK gd ii lv e op s1 s2 v :
     oprd_of_pexpr ii e = ok op
  -> oprd_of_lval ii lv = ok op
  -> sem_pexpr gd s1 e = ok v
  -> write_lval gd lv v s1 = ok s2
  -> s1 = s2.
Proof.
case: s1 s2 => [m1 lv1] [m2 lv2]; case: e => //=; first case=> //.
+ by move=> z [<-] /imm_oprd_of_lvalI.
+ move=> x; t_xrbindP => r ok_r [<-] /reg_oprd_of_lvalI.
  case=> vx ?; subst lv => ok'_r ok_v /= /dup[h] /(@write_var_mem gd).
  move=> /= ->; f_equal; apply/vmap_eqP=> y; move: h.
  rewrite /write_var; t_xrbindP=> lv3 /= ok_lv2 _ ?; subst lv3.
  have eqx: v_var x = vx by apply: (inj_reg_of_var ok_r ok'_r).
  move: ok_lv2; rewrite -eqx; case: (v_var x =P y) => [<-|ne_xy].
  - rewrite ok_v. admit.
  - by move/(get_set_var_ne ne_xy) ->.
+ by move=> g [<-] /glo_oprd_of_lvalI.
+ move=> x p; t_XrbindP=> r ok_r a ok_a <- ok_lva w ok_w z ok_z.
  move=> wv ok_wv <- /=; move: ok_lva; case: lv => // y.
  - by rewrite /oprd_of_lval; t_xrbindP.
  move=> p' /=; t_XrbindP=> r' ok_r' w' ok_w' aE wy ok_wy.
  move=> wp' ok_wp' m3 ok_m2 ?; subst m3 => <-; f_equal.
Admitted.

(* -------------------------------------------------------------------- *)
Lemma addr_Ofs_constE gd e z s :
  addr_ofs e = Ofs_const z -> sem_pexpr gd s e = ok (Vword (I64.repr z)).
Proof.
elim: e z => //; [by case=> // z ih z' [->] | case=> //].
+ case=> // e1 ih1 e2 ih2 /= z;
    case E1: addr_ofs => // [z1||];
    case E2: addr_ofs => // [z2] [<-].
  rewrite !(ih1 z1, ih2 z2) //= /sem_op2_w /mk_sem_sop2 /=.
  by rewrite -iword_addP /iword_add repr_mod.
+ case=> // e1 ih1 e2 ih2 /= z;
    case E1: addr_ofs => // [z1|];
    case E2: addr_ofs => // [z2] [<-].
  rewrite !(ih1 z1, ih2 z2) //= /sem_op2_w /mk_sem_sop2 /=.
  by rewrite -iword_mulP /iword_mul repr_mod.
Qed.

(* -------------------------------------------------------------------- *)
Lemma addr_Ofs_varE gd e x s :
  addr_ofs e = Ofs_var x -> sem_pexpr gd s e = get_var s.(evm) x.
Proof.
case: e => // [[]//|x' [->//]|]; do 2! case=> //;
  by move=> e1 e2 /=; do! case: addr_ofs => //.
Qed.

(* -------------------------------------------------------------------- *)
Lemma addr_Ofs_mulE gd e x z s :
     addr_ofs e = Ofs_mul z x
  -> sem_pexpr gd s e =
       Let w := get_var s.(evm) x in
       Let w := to_word w in
       ok (Vword (I64.mul (I64.repr z) w)).
Proof.
case: e => // [[]//|]; do 2! case=> //.
+ by move=> e1 e2 /=; do 2! case: addr_ofs => //.
+ move=> e1 e2 /=; case E1: addr_ofs => // [z'|x'].
  * case E2: addr_ofs => // [x'] [<- <-] /=.
    by rewrite (addr_Ofs_constE gd s E1) (addr_Ofs_varE gd s E2).
  * case E2: addr_ofs => // [z'] [<- <-] /=.
    rewrite (addr_Ofs_constE gd s E2) (addr_Ofs_varE gd s E1).
    case: get_var => // w /=; rewrite /sem_op2_w /mk_sem_sop2 /=.
    by case: to_word => // w' /=; rewrite I64.mul_commut.
Qed.

(* -------------------------------------------------------------------- *)
Lemma addr_Ofs_addE gd e x z1 z2 s :
     addr_ofs e = Ofs_add z1 x z2
  -> sem_pexpr gd s e =
       Let w := get_var s.(evm) x in
       Let w := to_word w in
       ok (Vword (I64.add (I64.mul (I64.repr z1) w) (I64.repr z2))).
Proof.
case: e => // [[]//|]; do 2! case=> //.
+ move=> e1 e2 /=; case E1: addr_ofs => // [w|y|w y].
  * case E2: addr_ofs => // [y|w' y]; case=> <- <- <-.
    - rewrite (addr_Ofs_constE gd s E1) /=.
      rewrite (addr_Ofs_varE gd s E2) /=; case: get_var => //= w1.
      rewrite /sem_op2_w /mk_sem_sop2 /=; case: to_word => //= w2.
      by rewrite I64.mul_commut I64.mul_one I64.add_commut.
    - rewrite (addr_Ofs_constE gd s E1) (addr_Ofs_mulE gd s E2) /=.
      case: get_var => //= w1; rewrite /sem_op2_w /mk_sem_sop2 /=.
      by case: to_word => //= w2; rewrite I64.add_commut.
  * case E2: addr_ofs => // [z] [<- <- <-] /=.
    rewrite (addr_Ofs_constE gd s E2) (addr_Ofs_varE gd s E1) /=.
    case: get_var => //= w; rewrite /sem_op2_w /mk_sem_sop2 /=.
    by case: to_word => //= w'; rewrite I64.mul_commut I64.mul_one.
  * case E2: addr_ofs => // [w'] [<- <- <-].
    rewrite (addr_Ofs_mulE gd s E1) (addr_Ofs_constE gd s E2) /=.
    rewrite /sem_op2_w /mk_sem_sop2 /=; case: get_var => //= w2.
    by case: to_word.
+ by move=> e1 e2 /=; case E1: addr_ofs => //; case: addr_ofs.
Qed.

(* -------------------------------------------------------------------- *)
Lemma sem_addr_indep ii gd r e a s1 s2 :
     (forall x, iserror (rflag_of_var ii x) ->
        get_var s1.(evm) x = get_var s2.(evm) x)
  -> addr_of_pexpr ii r e = ok a 
  -> sem_pexpr gd s1 e = sem_pexpr gd s2 e.
Proof. move=> eqs; case: e => // [[]//|x|].
+ rewrite /addr_of_pexpr /=; t_xrbindP => r' ok_r' _; apply: eqs.
  by move/reg_of_var_rflagN: ok_r'.
+ do 2! case=> //; move=> e1 e2 /=; rewrite /addr_of_pexpr /=.
  case E1: addr_ofs => // [z1|x|z x].
  * case E2: addr_ofs => // [z2|x|z x]; first move=> _.
    - by rewrite (addr_Ofs_constE gd s1 E1);
         rewrite (addr_Ofs_constE gd s2 E1);
         rewrite (addr_Ofs_constE gd s1 E2);
         rewrite (addr_Ofs_constE gd s2 E2).
    - t_XrbindP=> r1 ok_r1 sc ok_sc _;
         rewrite (addr_Ofs_constE gd s1 E1);
         rewrite (addr_Ofs_constE gd s2 E1) /=.
      rewrite (addr_Ofs_varE gd s1 E2) (addr_Ofs_varE gd s2 E2).
      by rewrite eqs //; move/reg_of_var_rflagN: ok_r1.
    - t_XrbindP=> r1 ok_r1 sc ok_sc _;
         rewrite (addr_Ofs_constE gd s1 E1);
         rewrite (addr_Ofs_constE gd s2 E1) /=.
      rewrite (addr_Ofs_mulE gd s1 E2) (addr_Ofs_mulE gd s2 E2).
      by rewrite eqs //; move/reg_of_var_rflagN: ok_r1.
  * case E2: addr_ofs => // [z2]; t_XrbindP => r1 ok_r1 sc ok_sc _.
    rewrite (addr_Ofs_varE gd s1 E1) (addr_Ofs_varE gd s2 E1).
    rewrite eqs; first by move/reg_of_var_rflagN: ok_r1.
    by rewrite (addr_Ofs_constE gd s1 E2) (addr_Ofs_constE gd s2 E2).
+ case E2: addr_ofs => // [z2]; t_XrbindP=> r1 ok_r1 sc ok_sc _.
  rewrite (addr_Ofs_mulE gd s1 E1) (addr_Ofs_mulE gd s2 E1) /=.
  rewrite (addr_Ofs_constE gd s1 E2) (addr_Ofs_constE gd s2 E2).
  by rewrite eqs //; move/reg_of_var_rflagN: ok_r1.
+ case E1: addr_ofs => // [z1|x].
  * case E2: addr_ofs => // [z2|x]; first move=> _.
    - by rewrite (addr_Ofs_constE gd s1 E1);
         rewrite (addr_Ofs_constE gd s2 E1);
         rewrite (addr_Ofs_constE gd s1 E2);
         rewrite (addr_Ofs_constE gd s2 E2).
    - t_XrbindP=> r1 ok_r1 sc ok_sc _.
      rewrite (addr_Ofs_constE gd s1 E1) (addr_Ofs_constE gd s2 E1).
      rewrite (addr_Ofs_varE gd s1 E2) (addr_Ofs_varE gd s2 E2) eqs //.
      by move/reg_of_var_rflagN: ok_r1.   
  * case E2: addr_ofs => // [z2]; t_XrbindP => r1 ok_r1 sc ok_sc _.
    rewrite (addr_Ofs_constE gd s1 E2) (addr_Ofs_constE gd s2 E2).
    rewrite (addr_Ofs_varE gd s1 E1) (addr_Ofs_varE gd s2 E1) eqs //.
    by move/reg_of_var_rflagN: ok_r1.   
Qed.

(* -------------------------------------------------------------------- *)
Lemma write_rf_oprdN gd ii rf rfv (rfx : var_i) v e op s1 s2 :
     rflag_of_var ii rfx = ok rf
  -> oprd_of_pexpr ii e = ok op
  -> sem_pexpr gd s1 e = ok v
  -> write_lval gd (Lvar rfx) rfv s1 = ok s2
  -> sem_pexpr gd s2 e = ok v.
Proof. case: e => //= [[]//||].
+ move=> x ok_rf; t_XrbindP => r ok_r _ ok_v.
  rewrite /write_var; t_XrbindP=> vm2 ok_vm2 <- /=.
  rewrite (get_set_var_ne _ ok_vm2) // => /esym eq_x.
  by move/reg_of_var_rflagN: ok_r; rewrite eq_x ok_rf.
+ move=> x e ok_rf; t_XrbindP => r ok_r a ok_a _ w1 ok1 w2 ok2 w3 ok3.
  move=> ?; subst v; rewrite /write_var; t_xrbindP => vm2 ok_vm2.
  move=> <- /=; rewrite (get_set_var_ne _ ok_vm2) => [/esym eq_x|].
  - by move/reg_of_var_rflagN: ok_r; rewrite eq_x ok_rf.
(*
  by rewrite ok1 /=; rewrite (sem_addr_indep _ _ s1 ok_a) ok2 /= ok3.
*)
Admitted.

(* -------------------------------------------------------------------- *)
Lemma write_rfs_oprdN gd ii rfs rfvs (rfxs : seq var_i) v e op s1 s2 :
     [seq rflag_of_var ii rfx.(v_var) | rfx <- rfxs] = map (@ok _) rfs
  -> oprd_of_pexpr ii e = ok op
  -> sem_pexpr gd s1 e = ok v
  -> write_lvals gd s1 [seq Lvar x | x <- rfxs] rfvs = ok s2
  -> sem_pexpr gd s2 e = ok v.
Proof.
elim: rfxs rfs rfvs s1 => [|rfx rfsx ih] [|rf rfs] [|rfv rfvs] //= s1.
+ by move=> _ _ ? -[<-].
case=> ok_rf ok_all ok_op ok_v; t_xrbindP=> s' ok_s' ok_s2.
by apply: (ih _ _ s'); eauto; apply: write_rf_oprdN; eauto.
Qed.

(* -------------------------------------------------------------------- *)
Lemma xflagsok gd ii rfi c s1 s2 xs1 :
     xs86_equiv c s1 xs1
  -> s1.(lc) = s2.(lc)
  -> is_rf_map ii rfi
  -> pred_of_rfis ii rfi
  -> write_lvals gd (to_estate s1) (map rfi2lval rfi) (map rfi2val rfi)
       = ok (to_estate s2)
  -> xs86_equiv c s2 (st_update_rflags (fun rf =>
       assoc (rev [seq rfi2upd v | v <- rfi]) rf) xs1).
Proof.
move=> eqv eq_lc ok_rfi ok_rfis h; pose vs := map rfi2val rfi.
have eq_mem: (to_estate s1).(emem) = (to_estate s2).(emem).
+ apply: (write_vars_mem (xs := map rfi2var rfi) (vs := vs)).
  by rewrite -h -map_comp; congr write_lvals; apply/eq_map; case.
have E1: s1.(lvm) = (to_estate s1).(evm) by case: {+}s1.
have E2: s2.(lvm) = (to_estate s2).(evm) by case: {+}s2.
have := eqv => -[/= /esym m1E okc1 okd1 ip1E rf1E rg1E]; split => //=.
+ by rewrite m1E.
+ by rewrite -eq_lc okd1.
+ move: rf1E; rewrite {}E1 {}E2 => /(xwrite_vars_rf ok_rfi).
  by move/(_ gd _ h); set rfm1 := RflagMap.update _ _.
+ by move: rg1E; rewrite E1 E2 => /xwrite_vars_rf_regN /(_ ok_rfi h).
Qed.

(* -------------------------------------------------------------------- *)
Lemma xaluop c s1 s2 xs1 ii gd (rof rcf rsf rpf rzf : var_i) vof vcf vsf vpf vzf :
     xs86_equiv c s1 xs1
  -> s1.(lc) = s2.(lc)
  -> rflag_of_var ii rof = ok OF
  -> rflag_of_var ii rcf = ok CF
  -> rflag_of_var ii rsf = ok SF
  -> rflag_of_var ii rpf = ok PF
  -> rflag_of_var ii rzf = ok ZF
  -> write_lvals gd (to_estate s1)
       [:: Lvar  rof; Lvar  rcf; Lvar  rsf; Lvar  rpf; Lvar  rzf]
       [:: Vbool vof; Vbool vcf; Vbool vsf; Vbool vpf; Vbool vzf]
     = ok (to_estate s2)
  -> xs86_equiv c s2 (st_update_rflags (fun rf =>
              match rf with
              | CF => Some (Def vcf)
              | PF => Some (Def vpf)
              | ZF => Some (Def vzf)
              | SF => Some (Def vsf)
              | OF => Some (Def vof)
              | DF => None
              end) xs1).
Proof.
move=> eqv eq_lc h1 h2 h3 h4 h5 ok_s2; pose xrs := [::
  RFI rof OF (Def vof); RFI rcf CF (Def vcf);
  RFI rsf SF (Def vsf); RFI rpf PF (Def vpf); RFI rzf ZF (Def vzf)].
have ok_xrs: pred_of_rfis ii xrs by do! split.
have := xflagsok eqv eq_lc _ ok_xrs ok_s2.
set u1 := st_update_rflags _ _; set u2 := st_update_rflags _ _.
suff ->: u2 = u1 by apply; rewrite /is_rf_map /= !(h1, h2, h3, h4, h5).
congr X86State; apply/eq_rfmapP => rf.
by rewrite /RflagMap.update !ffunE; case: rf.
Qed.

(* -------------------------------------------------------------------- *)
Lemma xaluop_nocf c s1 s2 xs1 ii gd (rof rsf rpf rzf : var_i) vof vsf vpf vzf :
     xs86_equiv c s1 xs1
  -> s1.(lc) = s2.(lc)
  -> rflag_of_var ii rof = ok OF
  -> rflag_of_var ii rsf = ok SF
  -> rflag_of_var ii rpf = ok PF
  -> rflag_of_var ii rzf = ok ZF
  -> write_lvals gd (to_estate s1)
       [:: Lvar  rof; Lvar  rsf; Lvar  rpf; Lvar  rzf]
       [:: Vbool vof; Vbool vsf; Vbool vpf; Vbool vzf]
     = ok (to_estate s2)
  -> xs86_equiv c s2 (st_update_rflags (fun rf =>
              match rf with
              | CF => None
              | PF => Some (Def vpf)
              | ZF => Some (Def vzf)
              | SF => Some (Def vsf)
              | OF => Some (Def vof)
              | DF => None
              end) xs1).
Proof.
move=> eqv eq_lc h1 h2 h3 h4 ok_s2; pose xrs := [::
  RFI rof OF (Def vof); RFI rsf SF (Def vsf);
  RFI rpf PF (Def vpf); RFI rzf ZF (Def vzf)].
have ok_xrs: pred_of_rfis ii xrs by do! split.
have := xflagsok eqv eq_lc _ ok_xrs ok_s2.
set u1 := st_update_rflags _ _; set u2 := st_update_rflags _ _.
suff ->: u2 = u1 by apply; rewrite /is_rf_map /= !(h1, h2, h3, h4).
congr X86State; apply/eq_rfmapP => rf.
by rewrite /RflagMap.update !ffunE; case: rf.
Qed.

(* -------------------------------------------------------------------- *)
Lemma xmul c s1 s2 xs1 ii gd (rof rcf rsf rpf rzf : var_i) b :
     xs86_equiv c s1 xs1
  -> s1.(lc) = s2.(lc)
  -> rflag_of_var ii rof = ok OF
  -> rflag_of_var ii rcf = ok CF
  -> rflag_of_var ii rsf = ok SF
  -> rflag_of_var ii rpf = ok PF
  -> rflag_of_var ii rzf = ok ZF
  -> write_lvals gd (to_estate s1)
       [:: Lvar  rof; Lvar  rcf; Lvar  rsf; Lvar  rpf; Lvar rzf]
       [:: Vbool   b; Vbool   b; undef_b  ; undef_b  ; undef_b ]
     = ok (to_estate s2)
  -> xs86_equiv c s2 (st_update_rflags (fun rf =>
              match rf with
              | SF | ZF | PF => Some Undef
              | OF | CF => Some (Def b)
              | DF => None
              end) xs1).
Proof.
move=> eqv eq_lc h1 h2 h3 h4 h5 ok_s2; pose xrs := [::
  RFI rof OF (Def b); RFI rcf CF (Def b);
  RFI rsf SF Undef  ; RFI rpf PF Undef  ;
  RFI rzf ZF Undef  ].
have ok_xrs: pred_of_rfis ii xrs by do! split.
have := xflagsok eqv eq_lc _ ok_xrs ok_s2.
set u1 := st_update_rflags _ _; set u2 := st_update_rflags _ _.
suff ->: u2 = u1 by apply; rewrite /is_rf_map /= !(h1, h2, h3, h4, h5).
congr X86State; apply/eq_rfmapP => rf.
by rewrite /RflagMap.update !ffunE; case: rf.
Qed.

(* -------------------------------------------------------------------- *)
Lemma reg_oprd_of_lvalI ii x reg :
     oprd_of_lval ii x = ok (Reg_op reg)
  -> exists2 vx, x = Lvar vx & reg_of_var ii vx = ok reg.
Proof.
case: x => //= x; last by move=> e; t_xrbindP.
by t_xrbindP=> r' ok_r' -[?]; subst r'; exists x.
Qed.

(* -------------------------------------------------------------------- *)
Lemma reg_oprd_of_pexprI ii e reg :
     oprd_of_pexpr ii e = ok (Reg_op reg)
  -> exists2 vx, e = Pvar vx & reg_of_var ii vx = ok reg.
Proof.
case: e => //= x; last by move=> e; t_xrbindP.
+ by case: x.
+ by t_xrbindP=> r' ok_r' -[?]; subst r'; exists x.
Qed.

(* -------------------------------------------------------------------- *)
Lemma word_of_pexprP gd ii e w s : 
  word_of_pexpr ii e = ok w ->
  sem_pexpr gd s e = ok (Vword w).
Proof. by case: e => // -[] //= z [<-]. Qed.

Lemma oreg_of_pexprP gd ii lm vm e xr r w : 
  regs_of_lvm vm xr ->
  oreg_of_pexpr ii e = ok r ->
  sem_pexpr gd {| emem := lm; evm := vm |} e = ok (Vword w) ->
  (odflt I64.zero (omap xr r)) = w.
Proof.
  case: e => //= [ []// z| x] Hvm.
  + by case: eqP => //= -> [<-] [<-].
  apply: rbindP => r';case: x => -[[] xn] ? //=.
  case Heq: reg_of_string => [r1|] // -[<-] [<-] /= Hget.
  by have := Hvm _ _ Heq;rewrite Hget.   
Qed.

(* -------------------------------------------------------------------- *)
Lemma scale_of_zP ii wsc sc :
  scale_of_z ii (I64.unsigned wsc) = ok sc -> 
  (word_of_scale sc) = wsc.
Proof.
  move=> H;apply /eqP;case: wsc H => z;rewrite /scale_of_z /=.
  by case:z => //= -[||? [<-]]// [||? [<-]]// [||? [<-]]// [||? [<-]].
Qed.
  
(* -------------------------------------------------------------------- *)

Lemma assemble_i_ok (c : lcmd) gd (s1 s2 : lstate) (xs1 : x86_state) :
     xs86_equiv c s1 xs1
  -> lsem1 c gd s1 s2
  -> exists2 xs2, fetch_and_eval gd xs1 = ok xs2 & xs86_equiv c s2 xs2.
Proof.
move=> eqv1 h; case: h eqv1 => {s1 s2}.
+ case=> lm vm [|i li] //= s2 ii x tg e cs [-> <-] /= {cs}.
  rewrite /to_estate /=; t_xrbindP => v ok_v ok_s2.
  case: xs1 => xm xr xf xc ip -/dup[] [/= <-] ok_xc.
  rewrite /assemble_c /=; t_xrbindP => a op1 ok_op1 op2 ok_op2.
  case=> ok_a tla ok_tla drop_xc _ xfE xrE eqv1.
  rewrite /fetch_and_eval /=; have lt_ip: ip < size xc.
  * by rewrite leqNgt; apply/negP=> /drop_oversize; rewrite -drop_xc.
  move: drop_xc; rewrite (drop_nth a) // -{}ok_a => -[h tlaE].
  have {h} := congr1 some h; rewrite -(nth_map _ None) // => <- /=.
  rewrite /st_write_ip /eval_MOV /=; move/(xs86_equiv_cons _): eqv1 => /=.
  move/(_ _ _ (erefl _)) => /= /xread_ok /(_ ok_op2 ok_v) /=.
  case=> w -> ?; subst v => /=; apply: (xwrite_ok _ ok_op1 ok_s2).
  by split=> //=; rewrite /assemble_c ok_tla tlaE.
+ case=> lm vm [|_ _] //= s2 ii xs o es cs [-> ->] /=.
  rewrite /to_estate /=; t_xrbindP=> vs aout ok_aout ok_vs.
  move=> ok_wr; case: xs1 => xm xr xf xc ip -/dup[] [/= <-] ok_xc.
  rewrite /assemble_c /=; t_xrbindP => a ok_a sa ok_sa drop_xc _.
  move=> xfE xrE eqv1; rewrite /fetch_and_eval /=.
  have /xs86_equiv_cons := eqv1 => /(_ _ _ (erefl _)) /=.
  rewrite /st_write_ip /= => eqv' {eqv1}; have lt_ip: ip < size xc.
  * by rewrite leqNgt; apply/negP=> /drop_oversize; rewrite -drop_xc.
  move: drop_xc; rewrite (drop_nth a) // => -[aE saE].
  have := congr1 some aE; rewrite -(nth_map _ None) // => <- /=.
  rewrite /st_write_ip /=; move: ok_a; rewrite /assemble_opn.
  case Eo: kind_of_sopn => [ak|b||||] //.
  * case El: lvals_as_alu_vars => [[[rof rcf rsf rsp rzf]] l|//].
    t_xrbindP => of_ ok_of cf ok_cf sf ok_sf sp ok_sp zf ok_zf.
    case: ifP => //; rewrite -!andbA => /and5P[].
    do 5! move/eqP=> ?; subst of_ cf sf sp zf; case: ak Eo.
    - move=> Eo; rewrite /assemble_fopn; case Ee: as_pair => [[e1 e2]|//].
      case/boolP: (as_unit l) => // /as_unitP zl; subst l.
      t_xrbindP => op1 ok1 op2 ok2.
      case=> ?; subst a => /=; rewrite /eval_CMP.
      case: (as_pairT Ee) => ?; subst es => {Ee}; move: ok_aout.
      rewrite /sem_pexprs /=; t_xrbindP => ev1 ok_ev1 _ ev2 ok_ev2 <-.
      move=> ?; subst aout;
        have := eqv' => /xread_ok /(_ ok1 ok_ev1) => -[w1 -> ?];
        have := eqv' => /xread_ok /(_ ok2 ok_ev2) => -[w2 -> ?];
        subst ev1 ev2 => /=; eexists; first by reflexivity.
      case: o Eo ok_vs => //= _.
      case=> ?; subst vs; move/lvals_as_alu_varsT: El => ?; subst xs.
      apply: (xaluop eqv' _ ok_of ok_cf ok_sf ok_sp ok_zf) => //.
      by rewrite to_estateK.
    - move=> bop Eo /=; case Ees: as_pair => [[e1 e2]|//].
      case El1: as_singleton => [x|//]; t_xrbindP.
      move=> v1 ok1 v2 ok2 vx okx; case: eqP => //= ?; subst vx.
      move/lvals_as_alu_varsT: El => ?; subst xs.
      have := as_singletonT El1 => ?; subst l => {El1}.
      have := as_pairT Ees => ?; subst es => {Ees}.
      move: ok_aout; rewrite /sem_pexprs /=; t_xrbindP.
      move=> ve1 ok_ve1 _ ve2 ok_ve2 <- ?; subst aout.
      have := eqv' => /xread_ok /(_ ok1 ok_ve1) => -[w1 ok_w1] ?; subst ve1.
      have := eqv' => /xread_ok /(_ ok2 ok_ve2) => -[w2 ok_w2] ?; subst ve2.
      case: o Eo ok_vs => //= -[<-] ok_vs [?]; subst a; move: ok_vs; (
        case=> ?; subst vs => /=; match goal with
          | |- exists2 _, ?X _ _ _ = _ & _ => rewrite /X
        end; rewrite ok_w1 ok_w2 /=;
        move/(@write_lvals_rcons gd [:: _; _; _; _; _] [:: _; _; _; _; _]): ok_wr;
        case=> s' ok_s' ok_s2; move: ok_s'; rewrite -[s'](to_estateK cs) => ok_s';
        have := (xaluop eqv' _ ok_of ok_cf ok_sf ok_sp ok_zf ok_s') => //;
        move/(_ (erefl _)); set xs' := st_update_rflags _ _ => eqv_s';
        by case: (xwrite_ok eqv_s' okx ok_s2) => xs2 ok_xs2 eqv2; exists xs2 ).
    - move=> bop Eo /=; case Ee: as_triple => [[[e1 e2] [] // ecf]|] //.
      case El1: as_singleton => [x|] //; t_xrbindP => v1 ok1 v2 ok2 vcf okcf.
      move=> vx okx; case: eqP => //= ?; subst vcf.
      case: eqP => //= ?; subst v1 => -[?]; subst a => {aE}.
      move/lvals_as_alu_varsT: El => ?; subst xs.
      have := as_singletonT El1 => ?; subst l => {El1}.
      have := as_tripleT Ee => ?; subst es => {Ee}.
      move: ok_aout; rewrite /sem_pexprs /=; t_xrbindP.
      move=> ve1 ok_ve1 _ ve2 ok_ve2 _ vcf ok_vcf <- <- ?; subst aout.
      have := eqv' => /xread_ok /(_ ok1 ok_ve1) => -[w1 ok_w1] ?; subst ve1.
      have := eqv' => /xread_ok /(_ ok2 ok_ve2) => -[w2 ok_w2] ?; subst ve2.
      have [bcf]: exists cf, to_bool vcf = ok cf.
      * by case: o Eo ok_vs => //= _; t_xrbindP=> b ->; exists b.
      case: vcf ok_vcf ok_vs => //= [|[]//] b' ok_bcf ok_vs [?]; subst b'.
      have getcf := xgetflag_r eqv' okcf ok_bcf (erefl _).
      case: o Eo ok_vs => //= -[<-]; case=> ?; subst vs => /=; (
        match goal with
          | |- exists2 _, ?X _ _ _ = _ & _ => rewrite /X
        end; rewrite ok_w1 ok_w2 /=;
        move/(@write_lvals_rcons gd [:: _; _; _; _; _] [:: _; _; _; _; _]): ok_wr;
        case=> s' ok_s' ok_s2; move: ok_s'; rewrite -[s'](to_estateK cs) => ok_s';
        have := (xaluop eqv' _ ok_of ok_cf ok_sf ok_sp ok_zf ok_s');
        move/(_ (erefl _)); set xs' := st_update_rflags _ _ => eqv_s';
        case: (xwrite_ok eqv_s' okx ok_s2) => xs2 ok_xs2 eqv2; exists xs2 => //;
        by rewrite /st_get_rflag getcf /= ).
    - move=> sh Eo /=;case: es ok_aout => // [e1 [//|e2 es']] ok_aout.
      case El1: as_singleton => [lv|//]; t_XrbindP.
      move=> op1 ok1 op2 ok2 opl okl; case: eqP => //= ?; subst opl.
      have := as_singletonT El1 => ?; subst l => {El1}.
      move: ok_aout; rewrite /sem_pexprs /=; t_XrbindP.
      move=> v1 ok_v1 h0 v2 ok_v2 h3 ok_es' ??; subst h0 aout.
      case: (xread_ok eqv' ok1 ok_v1) => wv1 ok_wv1 ?; subst v1.
      case: (xread_ireg_ok eqv' ok2 ok_v2) => wv2 ok_wv2 ?; subst v2.
      set xs' := X86State _ _ _ _ _ in eqv' ok_wv1 ok_wv2 |- *.
      case: sh Eo ok_vs => [sh|].
      + case: eqP ok_es' => // ?; subst es' => -[?]; subst h3.
        case: sh => Eo ok_vs -[?]; subst a => {aE} /=.
        * case: o Eo ok_vs => //= _; t_XrbindP.
          rewrite /eval_SHL ok_wv1 ok_wv2 /x86_shl.
          case: ifPn => /= _ -[?]; subst vs.
          - admit.
          set bof := (X in fun rf => match rf with OF => Some X | _ => _ end).
          set bcf := (X in fun rf => match rf with CF => Some X | _ => _ end).
          set bsf := (X in fun rf => match rf with SF => Some X | _ => _ end).
          set bpf := (X in fun rf => match rf with PF => Some X | _ => _ end).
          set bzf := (X in fun rf => match rf with ZF => Some X | _ => _ end).
          set xs2 := st_update_rflags _ _.
          move/lvals_as_alu_varsT: El => ?; subst xs; move: ok_wr.
          move/(@write_lvals_rcons _ [:: _; _; _; _; _] [:: _; _; _; _; _]).
          case=> s' ok_s' ok_s2; have: xs86_equiv c (of_estate s' cs) xs2.
          - pose xrs := [::
              RFI rof OF bof; RFI rcf CF bcf; RFI rsf SF bsf;
              RFI rsp PF bpf; RFI rzf ZF bzf].
            have ok_xrs: pred_of_rfis ii xrs by do! split.
            have := xflagsok (gd := gd) eqv' _ _ ok_xrs.
            set xs2' := st_update_rflags _ _; suff ->: xs2' = xs2.
            * apply=> //; first by rewrite /= ?(ok_of, ok_cf, ok_sf, ok_sp, ok_zf).
              rewrite to_estateK -ok_s'; congr write_lvals => /=.
              by f_equal; rewrite /rfi2val /bof /=; case: ifP.
            rewrite /xs2 /xs2'; congr X86State; apply/eq_rfmapP => rf.
              by rewrite /RflagMap.update !ffunE; case: rf.
          by move=> eqv2; case: (xwrite_ok eqv2 okl ok_s2); eauto.
        * case: o Eo ok_vs => //= _; t_XrbindP.
          rewrite /eval_SHR ok_wv1 ok_wv2 /x86_shr.
          case: ifPn => /= _ -[?]; subst vs.
          - admit.
          set bof := (X in fun rf => match rf with OF => Some X | _ => _ end).
          set bcf := (X in fun rf => match rf with CF => Some X | _ => _ end).
          set bsf := (X in fun rf => match rf with SF => Some X | _ => _ end).
          set bpf := (X in fun rf => match rf with PF => Some X | _ => _ end).
          set bzf := (X in fun rf => match rf with ZF => Some X | _ => _ end).
          set xs2 := st_update_rflags _ _.
          move/lvals_as_alu_varsT: El => ?; subst xs; move: ok_wr.
          move/(@write_lvals_rcons _ [:: _; _; _; _; _] [:: _; _; _; _; _]).
          case=> s' ok_s' ok_s2; have: xs86_equiv c (of_estate s' cs) xs2.
          - pose xrs := [::
              RFI rof OF bof; RFI rcf CF bcf; RFI rsf SF bsf;
              RFI rsp PF bpf; RFI rzf ZF bzf].
            have ok_xrs: pred_of_rfis ii xrs by do! split.
            have := xflagsok (gd := gd) eqv' _ _ ok_xrs.
            set xs2' := st_update_rflags _ _; suff ->: xs2' = xs2.
            * apply=> //; first by rewrite /= ?(ok_of, ok_cf, ok_sf, ok_sp, ok_zf).
              rewrite to_estateK -ok_s'; congr write_lvals => /=.
              by f_equal; rewrite /rfi2val /bof /=; case: ifP.
            rewrite /xs2 /xs2'; congr X86State; apply/eq_rfmapP => rf.
              by rewrite /RflagMap.update !ffunE; case: rf.
          by move=> eqv2; case: (xwrite_ok eqv2 okl ok_s2); eauto.
        * case: o Eo ok_vs => //= _; t_XrbindP.
          rewrite /eval_SAR ok_wv1 ok_wv2 /x86_sar.
          case: ifPn => /= _ -[?]; subst vs.
          - admit.
          set bof := (X in fun rf => match rf with OF => Some X | _ => _ end).
          set bcf := (X in fun rf => match rf with CF => Some X | _ => _ end).
          set bsf := (X in fun rf => match rf with SF => Some X | _ => _ end).
          set bpf := (X in fun rf => match rf with PF => Some X | _ => _ end).
          set bzf := (X in fun rf => match rf with ZF => Some X | _ => _ end).
          set xs2 := st_update_rflags _ _.
          move/lvals_as_alu_varsT: El => ?; subst xs; move: ok_wr.
          move/(@write_lvals_rcons _ [:: _; _; _; _; _] [:: _; _; _; _; _]).
          case=> s' ok_s' ok_s2; have: xs86_equiv c (of_estate s' cs) xs2.
          - pose xrs := [::
              RFI rof OF bof; RFI rcf CF bcf; RFI rsf SF bsf;
              RFI rsp PF bpf; RFI rzf ZF bzf].
            have ok_xrs: pred_of_rfis ii xrs by do! split.
            have := xflagsok (gd := gd) eqv' _ _ ok_xrs.
            set xs2' := st_update_rflags _ _; suff ->: xs2' = xs2.
            * apply=> //; first by rewrite /= ?(ok_of, ok_cf, ok_sf, ok_sp, ok_zf).
              rewrite to_estateK -ok_s'; congr write_lvals => /=.
              by f_equal; rewrite /rfi2val /bof /=; case: ifP.
            rewrite /xs2 /xs2'; congr X86State; apply/eq_rfmapP => rf.
              by rewrite /RflagMap.update !ffunE; case: rf.
          by move=> eqv2; case: (xwrite_ok eqv2 okl ok_s2); eauto.
      + case Heq: as_singleton => //.
        have := as_singletonT Heq => ?; subst es' => {Heq}.     
        admit.
    - move=> Eo /=; case Ees: as_pair => [[e1 e2]|//].
      case El2: as_pair => [[x2 x1]|//]; t_xrbindP.
      move=> vx1 ok_vx1 vx2 ok_vx2 op1 ok_op1 op2 ok_op2.
      case: ifP => //; rewrite -!andbA => /and3P[].
      do 3! move/eqP=> ?; subst vx1 vx2 op1.
      case: (reg_oprd_of_lvalI ok_vx1) => y1 ? ok_y1; subst x1.
      case: (reg_oprd_of_lvalI ok_vx2) => y2 ? ok_y2; subst x2.
      case: (reg_oprd_of_pexprI ok_op1) => x ? ok_x; subst e1.
      case=> ?; subst a => /= {aE}; have := as_pairT Ees => ?.
      subst es => {Ees}; move: ok_aout; rewrite /sem_pexprs /=.
      t_xrbindP=> v1 ok1 _ v2 ok2 <- ?; subst aout.
      have := lvals_as_alu_varsT El => ?; subst xs => {El}.
      case: o Eo ok_vs => //= _; t_xrbindP => w1 ok_w1 w2 ok_w2.
      have := eqv' => /xread_ok /(_ ok_op2 ok2) => -[wv2 ok_wv2] ?.
      subst v2 => -[?]; subst vs; move: ok_w2 ok_wr => -[?]; subst wv2.
      have := as_pairT El2 => ?; subst l => {El2}.
      move/(@write_lvals_rcons gd [:: _; _; _; _; _; _] [:: _; _; _; _; _; _]).
      case=> s'2 /(@write_lvals_rcons gd [:: _; _; _; _; _] [:: _; _; _; _; _]).
      case=> s'1 ok_s'1 ok_s'2 ok_s2; rewrite /eval_MUL ok_wv2 /=.
      move: ok_s'1; rewrite -[s'1](to_estateK cs) => ok_s'1.
      have := (xmul eqv' _ ok_of ok_cf ok_sf ok_sp ok_zf ok_s'1).
      move/(_ (erefl _)); set xs' := st_update_rflags _ _ => eqv_s'1.
      have := xswrite_var_reg eqv_s'1 ok_y2 => h.
      move: ok_s'2; rewrite -{1}[s'2](to_estateK cs) => /h {h}h.
      have := xswrite_var_reg h ok_y1; rewrite to_estateK => {h}h.
      move: ok_s2; rewrite -{1}[s2](to_estateK cs) => /h {h}h.
      eexists; first by reflexivity.
      case: (xgetreg_ex eqv' ok_x ok1) => /= we1.
      by rewrite ok_w1 => -[?]; subst we1 => ->.
    - admit.
    - case: o ok_vs => //= ok_vs _;
        case Ees: as_singleton => [e|] //;
        case El1: as_singleton => [x|] //.
      t_XrbindP=> op1 ok_op1 op2 ok_op2; case: eqP => // op2E.
      subst op2 => -[?]; subst a => {aE}.
      have := as_singletonT Ees => ?; subst es => {Ees}.
      move: ok_aout; rewrite /sem_pexprs /=; t_XrbindP => ve ok_ve.
      move=> ?; subst aout; move: ok_vs; t_xrbindP => w.
      move/to_word_ok=> ?; subst ve => -[?]; subst vs.
      have := lvals_as_alu_varsT El => ?; subst xs => {El}.
      have := as_singletonT El1 => ?; subst l => {El1}; move: ok_wr.
      move/(@write_lvals_rcons gd [:: _; _; _; _; _] [:: _; _; _; _; _]).
      case=> s' ok_s' ok_s2; have := eqv' => /xread_ok /(_ ok_op2 ok_ve).
      case=> we ok_w -[?]; subst we; rewrite /eval_NEG ok_w /=.
      move: ok_s'; rewrite -{1}[s'](to_estateK cs) => ok_s'.
      have := (xaluop eqv' _ ok_of ok_cf ok_sf ok_sp ok_zf ok_s').
      move/(_ (erefl _)); set xs' := st_update_rflags _ _ => ok_xs'.
      have := xwrite_ok ok_xs' ok_op1 ok_s2 => -[xs'' ok_xs'' eqv''].
      exists xs'' => //; rewrite -ok_xs''; congr write_oprd.
      rewrite /xs' /st_update_rflags /=; f_equal => //.
      by apply/eq_rfmapP=> rf; rewrite /RflagMap.update !ffunE; case: rf.
    case: o ok_vs => //=;case: es ok_aout => //= -[<-] [?] _;subst vs.
    case El': as_singleton => [de|] //.
    have := as_singletonT El' => ?; subst l => {El'}.
    apply: rbindP => d Hd [?];subst a => //=.
    have := lvals_as_alu_varsT El => ?; subst xs => {El}; rewrite /eval_XOR.
    move/(@write_lvals_rcons gd [:: _; _; _; _; _] [:: _; _; _; _; _]): ok_wr.
    case=> [s' ok_s' ok_s2]; move: ok_s'; rewrite -{1}[s'](to_estateK cs) => ok_s'.
    have := (xaluop eqv' _ ok_of ok_cf ok_sf ok_sp ok_zf ok_s').
    move/(_ (erefl _)); set xs' := st_update_rflags _ _ => ok_xs'.
    have := xwrite_ok ok_xs' Hd ok_s2 => -[xs'' ok_xs'' eqv''].
    set xs := X86State _ _ _ _ _; have: exists w, read_oprd gd d xs = ok w.
    + move: ok_xs'' => /=; case: {+}d => //= [r _|a]; first by exists (xr r).
      have ->: (decode_addr xs a) = (decode_addr xs' a) by case: a.
      apply: rbindP => mem Hmem _; apply /Memory.readV.
      by apply /Memory.writeV; exists mem; eauto.
    by case=> w -> /=; rewrite I64.xor_idem; exists xs''; rewrite -?ok_xs''.
  + case El: lvals_as_cnt_vars => [[[xof xsf xpf xzf] ol]|//].
    t_xrbindP=> opl okl vof ok_of vsf ok_sf vpf ok_pf vzf ok_zf.
    case: ifP => //; rewrite -!andbA => /and4P[].
    do 4! move/eqP=> ?; subst vof vsf vpf vzf.
    case Ees: as_singleton => [e|//];  t_xrbindP=> opr okr.
    case: eqP=> // ?; subst opr.
    have := as_singletonT Ees => ?; subst es => {Ees}.
    have := lvals_as_cnt_varsT El => ?; subst xs => {El}.
    move: ok_aout; rewrite /sem_pexprs /=.
    t_xrbindP => ve ok_ve ?; subst aout.
    have := eqv' => /xread_ok /(_ okr ok_ve) => -[w ok_w] ?; subst ve.
    case=> ?; subst a => {aE}; case: b Eo ok_vs => /=; (
      case: o => //= _ -[?]; subst vs;
      match goal with
        | |- exists2 _, ?X _ _ = _ & _ => rewrite /X
      end; rewrite ok_w /=; move: ok_wr;
      move/(@write_lvals_rcons gd [:: _; _; _; _] [:: _; _; _; _]);
      case=> s' ok_s' ok_s2; move: ok_s'; rewrite -[s'](to_estateK cs) => ok_s';
      have := (xaluop_nocf eqv' _ ok_of ok_sf ok_pf ok_zf ok_s') => //;
      move/(_ (erefl _)); set xs' := st_update_rflags _ _ => eqv_s';
      case: (xwrite_ok eqv_s' okl ok_s2) => xs2 ok_xs2 eqv2; exists xs2 => //;
      by rewrite /st_get_rflag getcf /= ).
  + case Exs: (as_singleton xs) => [x|] //.
    case Ees: (as_singleton es) => [e|] //.
    t_xrbindP=> // op1 ok_op1 op2 ok_op2 [?]; subst a => /=.
    have := as_singletonT Ees => ?; subst es => {Ees}.
    move: ok_aout; rewrite /sem_pexprs /=; t_xrbindP.
    move=> v ok_v ?; subst aout; case: o Eo ok_vs => //= _.
    t_xrbindP=> wv ok_wv /= -[?]; subst vs.
    have := as_singletonT Exs => ?; subst xs => {Exs}.
    move: ok_wr => /=; t_xrbindP => s2' ok_s2 ?; subst s2'.
    case: v ok_v ok_wv => // [|[]//] w ok_w [?]; subst wv.
    rewrite /eval_MOV; move: eqv' => /xread_ok /(_ ok_op2 ok_w) /=.
    case=> w' -> -[?]; subst w' => /=; apply: (xwrite_ok _ ok_op1 ok_s2).
    by split=> //=; rewrite /assemble_c ok_sa saE.
  + case Exs: (as_singleton xs) => [x|] //.
    case Ees: (as_triple es) => [[[cb e1] e2]|] //=.
    t_xrbindP => vx ok_x v1 ok1 ct ok_ct v2 ok2.
    case: eqP=> // ?; subst v2 => -[?]; subst a.
    have := as_tripleT Ees => ?; subst es => {Ees}.
    have := as_singletonT Exs => ?; subst xs => {Exs}.
    move: ok_aout; rewrite /sem_pexprs /=; t_xrbindP.
    move=> vcb ok_cb _ vb1 ok_vb1 _ vb2 ok_vb2 <- <- ?.
    subst aout; case: o Eo ok_vs => //= _.
    t_xrbindP=> /= cond; case: vcb ok_cb => // [|[]//].
    move=> b ok_b [?]; subst cond => ok_vs.
    have /= := xeval_cond eqv' ok_ct ok_b.
    rewrite /eval_CMOVcc => -> /=; case: b ok_vs ok_b => /=.
    * t_xrbindP=> w ok_w ?; subst vs => ok_cb.
      move: ok_wr => /=; t_xrbindP=> s2' ok_s2 ?; subst s2'.
      rewrite /eval_MOV; move: eqv' => /xread_ok /(_ ok1 ok_vb1) /=.
      case=> w' -> ?; subst vb1; case: ok_w=> ?; subst w' => /=.
      apply: (xwrite_ok _ ok_x ok_s2).
      by split=> //=; rewrite /assemble_c ok_sa saE.
    * t_xrbindP=> w ok_w ?; subst vs => ok_cb.
      move: ok_wr => /=; t_xrbindP=> s2' ok_s2 ?; subst s2'.
      eexists; first by reflexivity. move=> {vb1 ok_vb1 e1 ok1}.
      admit.
  case Exs: (as_singleton xs) => [x|] //.
  case Ees: (as_quadruple es) => [[[[d b] sc] off]|] //=.
  have := as_quadrupleT Ees => ?; subst es => {Ees}.
  have := as_singletonT Exs => ?; subst xs => {Exs}.
  t_xrbindP => wd Hd rb Hb wsc Hwsc sc' Hsc' ro Hoff ds Hx [<-].
  case: o Eo ok_vs => //= _.
  move: ok_aout; rewrite /sem_pexprs /=; t_xrbindP.
  move=> vd sd ? vb sb ? vsc ssc ? voff soff <- <- <- <-.
  have := word_of_pexprP gd {| emem := lm; evm := vm |} Hd.
  have := word_of_pexprP gd {| emem := lm; evm := vm |} Hwsc.
  rewrite ssc sd => -[->] [->]/=; t_xrbindP => wb.
  move/to_word_ok=>  Hwb woff /to_word_ok Hwoff.
  rewrite /eval_LEA /x86_lea; case:ifP => //= Hscale [?]; subst vs vb voff.
  rewrite /decode_addr /= (oreg_of_pexprP xrE Hb sb) (oreg_of_pexprP xrE Hoff soff).
  rewrite I64.repr_unsigned in ok_wr; have ? := scale_of_zP Hsc'; subst wsc.
  move: ok_wr; apply: rbindP => s2' ok_wr [?]; subst s2'.
  apply: (xwrite_ok _ Hx ok_wr); split => //=.
  by rewrite /assemble_c ok_sa saE.
+ case=> lv vm [|_ _] //= ii lbl cs [-> ->].
  case: xs1 => xm xr xf xc ip -/dup[] [/= <-] ok_xc.
  rewrite /assemble_c /=; t_xrbindP => sa ok_sa drop_xc le_ip_c xfE xrE.
  move=> eqv1; rewrite /fetch_and_eval /=; have lt_ip: ip < size xc.
  * by rewrite leqNgt; apply/negP=> /drop_oversize; rewrite -drop_xc.
  move: drop_xc; rewrite (drop_nth (LABEL lbl)) // => -[h tlaE].
  have {h} := congr1 some h; rewrite -(nth_map _ None) // => <- /=.
  eexists; first by reflexivity. rewrite /st_write_ip /setc /=.
  by split=> //=; rewrite /assemble_c ok_sa tlaE.
+ case=> [lv vm] [|_ _] //= ii lbl cs csf [-> ->] /=.
  move=> ok_csf; case: xs1 => xm xr xf xc ip -/dup[] [/= <-] ok_xc.
  rewrite /assemble_c /setc /=; t_xrbindP => tla ok_tla drop_xc.
  move=> le_ip xfE xrE eqv1; rewrite /fetch_and_eval /=.
  have lt_ip: ip < size xc; first (rewrite leqNgt; apply/negP).
  * by move/drop_oversize; rewrite -drop_xc.
  move: drop_xc; rewrite (drop_nth (JMP lbl)) // => -[h tlaE].
  have {h} := congr1 some h; rewrite -(nth_map _ None) // => <- /=.
  rewrite /eval_JMP /st_write_ip /=.
  case: (xfind_label ok_csf ok_xc) => ip' [-> lt_ip' ok_tl] /=.
  by eexists; first by reflexivity.
+ move=> ii [lv vm] [|i li] //= e lbl cst csf [-> ->] {li} /=.
  rewrite /to_estate /=; t_xrbindP=> v ok_v vl_v ok_csf.
  case: xs1 => xm xr xf xc ip -/dup[] [/= <-] ok_xc.
  rewrite /assemble_c /setc /=; t_xrbindP=> a ct ok_ct [ok_a] /=.
  move=> tla ok_tla drop_xc le_ip xfE xrE eqv1; rewrite /fetch_and_eval /=.
  have lt_ip: ip < size xc; first (rewrite leqNgt; apply/negP).
  * by move/drop_oversize; rewrite -drop_xc.
  move: drop_xc; rewrite (drop_nth a) // -{}ok_a => -[h tlaE].
  have {h} := congr1 some h; rewrite -(nth_map _ None) // => <- /=.
  rewrite /st_write_ip /= /eval_Jcc /= /eval_JMP.
  rewrite (xeval_cond eqv1 ok_ct ok_v) vl_v /= /st_write_ip /=.
  case: (xfind_label ok_csf ok_xc) => ip' [-> lt_ip' ok_tl] /=.
  by eexists; first by reflexivity.
+ move=> ii [lv vm] [|i li] //= e lbl cs [-> ->] {li} /=.
  rewrite /to_estate /=; t_xrbindP => v ok_v ok_bv; rewrite /setc /=.
  case: xs1 => xm xr xf xc ip -/dup[] [/= <-] ok_xc.
  rewrite /assemble_c /setc /=; t_xrbindP=> a ct ok_ct [ok_a] /=.
  move=> tla ok_tla drop_xc le_ip xfE xrE eqv1; rewrite /fetch_and_eval /=.
  have lt_ip: ip < size xc; first (rewrite leqNgt; apply/negP).
  * by move/drop_oversize; rewrite -drop_xc. 
  move: drop_xc; rewrite (drop_nth a) // -{}ok_a => -[h tlaE].
  have {h} := congr1 some h; rewrite -(nth_map _ None) // => <- /=.
  rewrite /st_write_ip /= /eval_Jcc /= /eval_JMP.
  rewrite (xeval_cond eqv1 ok_ct ok_v) ok_bv /= /st_write_ip /=.
  eexists; first by reflexivity. split=> //=.
  by rewrite /assemble_c ok_tla tlaE.
Admitted.
