(* -------------------------------------------------------------------- *)
From mathcomp Require Import all_ssreflect.
(* ------- *) Require Import utils expr linear compiler_util low_memory.
(* ------- *) Require Import sem linear linear_sem x86 x86_sem.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Unset SsrOldRewriteGoalsOrder.

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
Definition rflags_of_lvm (vm : vmap) rf :=
  forall x r, rflag_of_string x = Some r ->
    match get_var vm {| vtype := sbool; vname := x |} with
    | Ok v =>
      match to_rbool v with
      | Ok b => RflagMap.get rf r = b
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
        | Ok    v => RegMap.get rf r = v
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
move=> eq1 eq2; apply/RflagMap.eq_rfmap => rf.
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
move=> eq1 eq2; apply/RegMap.eq_regmap => rf.
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
Lemma write_lvals_rcons xs vs x v s1 s2:
     write_lvals s1 (rcons xs x) (rcons vs v) = ok s2
  -> exists2 s,
       write_lvals s1 xs vs = ok s
     & write_lval x v s = ok s2.
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
  -> RflagMap.get xs.(xrf) rf = b.
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
  -> exists2 b, to_rbool v = ok b
                & RflagMap.get xs.(xrf) rf = b.
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
  -> RflagMap.get xs.(xrf) rf = Def b.
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
  -> exists2 w, to_word v = ok w
                & RegMap.get xs.(xreg) r = w.
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
  -> RegMap.get xs.(xreg) r = w.
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
Lemma xeval_cond {ii e v c ct s xs} :
    xs86_equiv c s xs
 -> assemble_cond ii e = ok ct
 -> sem_pexpr (to_estate s) e = ok v
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
  case: kind_of_sopn => [ak|b|||] //.
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
    - move=> s; case: as_pair => // -[e1 e2].
      case: as_singleton => // l; t_xrbindP=> ev1 _ ev2 _ vl _.
      by case: ifP => // _; case: s.
    - case: as_pair => // -[e1 e2]; case: as_pair => // -[l1 l2].
      by t_xrbindP.
    - case: as_pair => // -[e1 e2]; case: as_singleton => // l.
      by t_xrbindP => vl _ ve1 _; case: is_wconst => //; t_xrbindP.
    - by case: as_singleton => // e; case: as_singleton => // l; t_xrbindP.
  * case: lvals_as_cnt_vars => // -[[v1 v2 v3 v4] ls].
    t_xrbindP => v _ bv1 _ bv2 _ bv3 _ bv4 _; case: ifP => // _.
    case: as_singleton => // ae; t_xrbindP=> vae _.
    by case: ifP => // _; case: b.
  * by case: as_singleton => // l; case: as_singleton => // e; t_xrbindP.
  * case: as_singleton => // l; case: as_triple => // -[[e1 e2] e3].
    by t_xrbindP=> vl _ v1 _ v2 _ v3 _; case: ifP.
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
Lemma write_var_mem x v s1 s2 :
  write_lval (Lvar x) v s1 = ok s2 -> s1.(emem) = s2.(emem).
Proof.
by case: s1 s2=> [m1 v1] [m2 v2] /=; rewrite /write_var; t_xrbindP.
Qed.

(* -------------------------------------------------------------------- *)
Lemma write_vars_mem xs vs s1 s2 :
  write_lvals s1 (map Lvar xs) vs = ok s2 -> s1.(emem) = s2.(emem).
Proof.
elim: xs s1 vs => [|x xs ih] s1 [|v vs] //= => [[->]|] //.
by t_xrbindP=> s h /ih <-; apply (@write_var_mem x v).
Qed.

(* -------------------------------------------------------------------- *)
Lemma xwrite_var_rf x b ii rf s1 s2 xs1 :
     rflag_of_var ii (v_var x) = ok rf
  -> rflags_of_lvm s1.(lvm) xs1
  -> write_var x (Vbool b) (to_estate s1) = ok (to_estate s2)
  -> rflags_of_lvm s2.(lvm) (RflagMap.set xs1 rf b).
Proof. Admitted.

(* -------------------------------------------------------------------- *)
Variant RFI_t := RFI of var_i & rflag & bool.

Definition rfi2var  rfi := let: RFI v _  _ := rfi in Lvar v.
Definition rfi2rf   rfi := let: RFI _ rf _ := rfi in rf.
Definition rfi2bool rfi := let: RFI _ _  v := rfi in v.
Definition rfi2val  rfi := let: RFI _ _  v := rfi in Vbool v.

(* -------------------------------------------------------------------- *)
Definition is_rf_map ii xrs :=
   all (fun xr =>
          let: RFI v rfv _ := xr in
          if rflag_of_var ii (v_var v) is Ok rf then
            rfv == rf
          else false) xrs.

(* -------------------------------------------------------------------- *)
Lemma xwrite_vars_rf xrs ii s1 s2 xs1 :
     is_rf_map ii xrs
  -> uniq (map rfi2rf xrs)
  -> write_lvals (to_estate s1)
       (map rfi2var xrs) (map rfi2val xrs) = ok (to_estate s2)
  -> rflags_of_lvm s2.(lvm) (RflagMap.update xs1 (fun rf =>
       let j := seq.index rf (map rfi2rf xrs) in
       if j < size xrs then
         Some (Def (nth false (map rfi2bool xrs) j))
       else None)).
Proof. Admitted.

(* -------------------------------------------------------------------- *)
Lemma xwrite_vars_rf_regN xrs ii s1 s2 xs1 :
     is_rf_map ii xrs
  -> write_lvals (to_estate s1)
       (map rfi2var xrs) (map rfi2val xrs) = ok (to_estate s2)
  -> regs_of_lvm s2.(lvm) xs1.
Proof. Admitted.

(* -------------------------------------------------------------------- *)
Lemma eq_update_rf f1 f2 rfm :
  f1 =1 f2 -> RflagMap.update rfm f1 = RflagMap.update rfm f2.
Proof.
move=> eq_f; apply/RflagMap.eq_rfmap => rf /=.
by rewrite /RflagMap.update /RflagMap.get /= eq_f.
Qed.

(* -------------------------------------------------------------------- *)
Lemma xaddr_ofs_const s e v z :
     sem_pexpr s e = ok v
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

Lemma xaddr_ofs_var c s xs ii e v r x :
     xs86_equiv c s xs
  -> sem_pexpr (to_estate s) e = ok v
  -> reg_of_var ii (v_var x) = ok r
  -> addr_ofs e = Ofs_var x
  -> to_word v = ok (RegMap.get xs.(xreg) r).
Proof.
move=> eqv; case: e => // [[]//||]; last first.
+ case=> // -[]// e1 e2 /=; t_xrbindP=> v1 _ v2 _ _ _.
  - by do! case: addr_ofs => //. - by do! case: addr_ofs => //.
move=> y /= ok_v ok_r -[?]; subst y.
by case: (xgetreg_ex eqv ok_r ok_v) => w -> ->.
Qed.

Lemma xaddr_ofs_mul c s xs ii e v r sc x1 x2 :
     xs86_equiv c s xs
  -> sem_pexpr (to_estate s) e = ok v
  -> scale_of_z ii x1 = ok sc
  -> reg_of_var ii (v_var x2) = ok r
  -> addr_ofs e = Ofs_mul x1 x2
  -> to_word v = ok (I64.mul (word_of_scale sc) (RegMap.get xs.(xreg) r)).
Proof.
move=> eqv; case: e => // [[]//|] -[]// -[]// e1 e2 /=.
+ by t_xrbindP=> v1 _ v2 _ _ _ _; do! case: addr_ofs => //.
t_xrbindP=> v1 ok_v1 v2 ok_v2; rewrite /sem_op2_w.
rewrite /mk_sem_sop2; t_xrbindP=> /= w1 ok_w1 w2 ok_w2.
move=> ? ok_sc ok_r; subst v;
  case E1: addr_ofs => [z1|x|||] //;
  case E2: addr_ofs => [z2|y|||] //;
  case=> ? ?; subst x1 x2; congr ok.
+ have := xaddr_ofs_var eqv ok_v2 ok_r E2; rewrite ok_w2.
  case=> <-. admit.
+ have := xaddr_ofs_var eqv ok_v1 ok_r E1; rewrite ok_w1.
  case=> <-. admit.
Admitted.

Lemma xaddr_ofs_add c s xs ii e v r w sc x1 x2 x3 :
   xs86_equiv c s xs
-> sem_pexpr (to_estate s) e = ok v
-> scale_of_z ii x1 = ok sc
-> reg_of_var ii (v_var x2) = ok r
-> word_of_int x3 = ok w
-> addr_ofs e = Ofs_add x1 x2 x3
-> to_word v = ok (
     I64.add w (I64.mul
      (word_of_scale sc) (RegMap.get xs.(xreg) r))).
Proof.
move=> eqv; case: e => // [[]//|] -[]// -[]// e1 e2 /=; last first.
+ by t_xrbindP=> v1 _ v2 _ _ _ _; do! case: addr_ofs => //.
t_xrbindP=> v1 ok_v1 v2 ok_v2; rewrite /sem_op2_w.
rewrite /mk_sem_sop2; t_xrbindP=> /= w1 ok_w1 w2 ok_w2.
move=> ? ok_v ok_sc ok_w; subst v;
  case E1: addr_ofs => [z1|x|sc1 t1||] //;
  case E2: addr_ofs => [z2|y|sc2 t2||] //;
  case=> ? ? ?; subst x1 x2 x3.
+ case: ok_v=> <- /=; rewrite I64.mul_commut I64.mul_one.
  have := xaddr_ofs_var eqv ok_v2 ok_sc E2; rewrite ok_w2.
  have := xaddr_ofs_const ok_v1 E1; rewrite ok_w1.
  by move=> [->] [->] /=; case: ok_w => <-.
+ admit.
+ case: ok_v=> <- /=; rewrite I64.mul_commut I64.mul_one.
  have := xaddr_ofs_var eqv ok_v1 ok_sc E1; rewrite ok_w1.
  have := xaddr_ofs_const ok_v2 E2; rewrite ok_w2.
  by move=> [->] [->] /=; case: ok_w => <-; rewrite I64.add_commut.
+ admit.
Admitted.

Lemma xread_ok ii v e op c s xs :
     xs86_equiv c s xs
  -> oprd_of_pexpr ii e = ok op
  -> sem_pexpr (to_estate s) e = ok v
  -> exists2 w, read_oprd op xs = ok w & v = Vword w.
Proof.
move=> eqv; case: e => //.
+ by case=> //= z [<-] [<-] /=; eexists.
+ move=> x; rewrite /oprd_of_pexpr /=; t_xrbindP.
  move=> r ok_r -[<-] ok_v /=; eexists; first by reflexivity.
  case: (xgetreg_ex eqv ok_r ok_v) => w ok_w ->.
  by case: {+}v ok_w => // [|[]//] w' -[->].
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

(* -------------------------------------------------------------------- *)
Lemma xwrite_ok ii x (v : word) op c cs (s1 s2 : estate) xs1 :
     xs86_equiv c (of_estate s1 cs) xs1
  -> oprd_of_lval ii x = ok op
  -> write_lval x v s1 = ok s2
  -> exists2 xs2, write_oprd op v xs1 = ok xs2
                & xs86_equiv c (of_estate s2 cs) xs2.
Proof.
move=> eqv; case: x => // [x|x e].
+ case: x => [[]] []//= x vix; case Ex: reg_of_string => [r|] //=.
  case=> <- ok_s2 /=; eexists; first by reflexivity.
  move: ok_s2; rewrite /write_var; t_xrbindP => vm /= ok_vm <-.
  case: {+}eqv => /= m1E okc1 okd1 ip1E rf1E rg1E.
  split=> //=. admit. admit.
+ admit.
Admitted.

(* -------------------------------------------------------------------- *)
Lemma xaluop c s1 s2 xs1 ii (rof rcf rsf rpf rzf : var_i) vof vcf vsf vpf vzf :
     xs86_equiv c s1 xs1
  -> s1.(lc) = s2.(lc)
  -> rflag_of_var ii rof = ok OF
  -> rflag_of_var ii rcf = ok CF
  -> rflag_of_var ii rsf = ok SF
  -> rflag_of_var ii rpf = ok PF
  -> rflag_of_var ii rzf = ok ZF
  -> write_lvals (to_estate s1)
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
move=> eqv1 eq_lc ok_of ok_cf ok_sf ok_pf ok_zf h.
have eq_mem: (to_estate s1).(emem) = (to_estate s2).(emem).
+ by apply: (write_vars_mem (xs := [:: rof; rcf; rsf; rpf; rzf]) h).
case: xs1 eqv1 => [m1 rg1 rf1 xc1 ip1] eqv1.
rewrite /st_update_rflags /=; subst=> /=.
pose xrs := [:: RFI rof OF vof; RFI rcf CF vcf;
                RFI rsf SF vsf; RFI rpf PF vpf; RFI rzf ZF vzf].
have rfi: is_rf_map ii xrs.
* by rewrite /xrs /= !(ok_of, ok_cf, ok_sf, ok_pf, ok_zf).
have := eqv1 => -[/= /esym m1E okc1 okd1 ip1E rf1E rg1E]; split => //=.
+ by rewrite m1E.
+ by rewrite -eq_lc okd1.
+ have := xwrite_vars_rf rf1 rfi (erefl _) h.
  set rfm1 := RflagMap.update _ _;
  set rfm2 := RflagMap.update _ _.
  suff ->: rfm1 = rfm2 by done.
  by apply: eq_update_rf; case.
+ by apply: (xwrite_vars_rf_regN _ rfi h).
Qed.

(* -------------------------------------------------------------------- *)
Lemma xaluop_nocf c s1 s2 xs1 ii (rof rsf rpf rzf : var_i) vof vsf vpf vzf :
     xs86_equiv c s1 xs1
  -> s1.(lc) = s2.(lc)
  -> rflag_of_var ii rof = ok OF
  -> rflag_of_var ii rsf = ok SF
  -> rflag_of_var ii rpf = ok PF
  -> rflag_of_var ii rzf = ok ZF
  -> write_lvals (to_estate s1)
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
move=> eqv1 eq_lc ok_of ok_sf ok_pf ok_zf h.
have eq_mem: (to_estate s1).(emem) = (to_estate s2).(emem).
+ by apply: (write_vars_mem (xs := [:: rof; rsf; rpf; rzf]) h).
case: xs1 eqv1 => [m1 rg1 rf1 xc1 ip1] eqv1.
rewrite /st_update_rflags /=; subst=> /=.
pose xrs := [:: RFI rof OF vof; RFI rsf SF vsf; RFI rpf PF vpf; RFI rzf ZF vzf].
have rfi: is_rf_map ii xrs.
* by rewrite /xrs /= !(ok_of, ok_sf, ok_pf, ok_zf).
have := eqv1 => -[/= /esym m1E okc1 okd1 ip1E rf1E rg1E]; split => //=.
+ by rewrite m1E.
+ by rewrite -eq_lc okd1.
+ have := xwrite_vars_rf rf1 rfi (erefl _) h.
  set rfm1 := RflagMap.update _ _;
  set rfm2 := RflagMap.update _ _.
  suff ->: rfm1 = rfm2 by done.
  by apply: eq_update_rf; case.
+ by apply: (xwrite_vars_rf_regN _ rfi h).
Qed.

(* -------------------------------------------------------------------- *)
Lemma assemble_i_ok (c : lcmd) (s1 s2 : lstate) (xs1 : x86_state) :
     xs86_equiv c s1 xs1
  -> lsem1 c s1 s2
  -> exists2 xs2, fetch_and_eval xs1 = ok xs2 & xs86_equiv c s2 xs2.
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
  case Eo: kind_of_sopn => [ak|b|||] //.
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
        move/(@write_lvals_rcons [:: _; _; _; _; _] [:: _; _; _; _; _]): ok_wr;
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
        move/(@write_lvals_rcons [:: _; _; _; _; _] [:: _; _; _; _; _]): ok_wr;
        case=> s' ok_s' ok_s2; move: ok_s'; rewrite -[s'](to_estateK cs) => ok_s';
        have := (xaluop eqv' _ ok_of ok_cf ok_sf ok_sp ok_zf ok_s') => //;
        move/(_ (erefl _)); set xs' := st_update_rflags _ _ => eqv_s';
        case: (xwrite_ok eqv_s' okx ok_s2) => xs2 ok_xs2 eqv2; exists xs2 => //;
        by rewrite /st_get_rflag getcf /= ).
    - admit.
    - move=> Eo /=; case Ees: as_pair => [[e1 e2]|//].
      case El2: as_pair => [[x1 x2]|//]; t_xrbindP => ve2 ok_ve2.
      move=> ?; subst a => /= {aE}; have := as_pairT Ees => ?.
      subst es => {Ees}; move: ok_aout; rewrite /sem_pexprs /=.
      t_xrbindP=> v1 ok1 _ v2 ok2 <- ?; subst aout.
      have := lvals_as_alu_varsT El => ?; subst xs => {El}.
      case: o Eo ok_vs => //= _; t_xrbindP => w1 ok_w1 w2 ok_w2.
      have := eqv' => /xread_ok /(_ ok_ve2 ok2) => -[wv2 ok_wv2] ?.
      subst v2 => -[?]; subst vs. admit.
    - admit.
    - admit.
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
      move/(@write_lvals_rcons [:: _; _; _; _] [:: _; _; _; _]);
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
