(* -------------------------------------------------------------------- *)
From mathcomp Require Import all_ssreflect.
(* ------- *) Require Import utils expr linear compiler_util low_memory.
(* ------- *) Require Import sem linear linear_sem x86 x86_sem.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Unset SsrOldRewriteGoalsOrder.

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
Lemma xread_ok ii v e op c s xs :
   xs86_equiv c s xs
-> oprd_of_pexpr ii e = ok op
-> sem_pexpr (to_estate s) e = ok v
-> read_oprd op xs = to_word v.
Proof.
move=> eqv; case: e => //.
+ case=> //= z; t_xrbindP => w; rewrite /word_of_int.
  by case: ifP => // _ [<-] [<-] <-.
+ move=> x /=; t_xrbindP => r; case: x => -[vt x vi].
  case: vt => //=; case E: reg_of_string => [r'|] //.
  case=> <- [<-] /=; case: eqv => _ _ _ _ _ eqv ok_v.
  move/(_ _ _ E): eqv; rewrite ok_v; case E': (to_word v) => [w|//].
  by move=> <-.
move=> x e /=; t_xrbindP => r1 ok_r1 w ok_w [<-].
move=> z o ok_o ok_z z' o' ok_o' ok_z' res ok_res <- {v} /=.
rewrite -ok_res; case: eqv => -> _ _ _ _ eqv; f_equal.
rewrite /decode_addr /= I64.mul_zero I64.add_zero.
rewrite I64.add_commut; f_equal.
+ case: x ok_r1 ok_o ok_z => -[] [] // x vi /=.
  case E: reg_of_string => [r'|] // [<-] ok_o ok_z.
  by move/(_ _ _ E): eqv; rewrite ok_o ok_z.
case: e ok_w ok_o' => // -[] //= zw; rewrite /word_of_int.
by case: ifPn => // _ [<-] [o'E]; move: ok_z'; rewrite -o'E => -[].
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
+ move=> lv op es _. admit.
+ by move=> lbl2 /eqP nq [[/esym]].
+ by move=> p l _; case: assemble_cond.
Admitted.

(* -------------------------------------------------------------------- *)
Lemma assemble_i_ok (c : lcmd) (s1 s2 : lstate) (xs1 xs2 : x86_state) :
     xs86_equiv c s1 xs1
  -> xs86_equiv c s2 xs2
  -> lsem1 c s1 s2
  -> fetch_and_eval xs1 = ok xs2.
Proof.
move=> eqv1 eqv2 h; case: h eqv1 eqv2 => {s1 s2}.
+ case=> lm vm [|i li] //= s2 ii x tg e cs [-> <-] /= {cs}.
  rewrite /to_estate /=; t_xrbindP => v ok_v ok_s2.
  case: xs1 => xm xr xf xc ip -/dup[] [/= <-] ok_xc.
  rewrite /assemble_c /=; t_xrbindP => a op1 ok_op1 op2 ok_op2.
  case=> ok_a tla ok_tla drop_xc _ xfE xrE eqv1 eqv2.
  rewrite /fetch_and_eval /=; have lt_ip: ip < size xc.
  * by rewrite leqNgt; apply/negP=> /drop_oversize; rewrite -drop_xc.
  move: drop_xc; rewrite (drop_nth a) // -{}ok_a => -[h tlaE].
  have {h} := congr1 some h; rewrite -(nth_map _ None) // => <- /=.
  rewrite /st_write_ip /eval_MOV /=; move/(xs86_equiv_cons _): eqv1 => /=.
  move/(_ _ _ (erefl _)) => /= /xread_ok /(_ ok_op2 ok_v) /=.
  rewrite /st_write_ip /= => ->. admit.
+ admit.
+ case=> lv vm [|_ _] //= ii lbl cs [-> ->].
  case: xs1 => xm xr xf xc ip -/dup[] [/= <-] ok_xc.
  rewrite /assemble_c /=; t_xrbindP => sa ok_sa drop_xc le_ip_c xfE xrE.
  move=> eqv1 eqv2; rewrite /fetch_and_eval /=; have lt_ip: ip < size xc.
  * by rewrite leqNgt; apply/negP=> /drop_oversize; rewrite -drop_xc.
  move: drop_xc; rewrite (drop_nth (LABEL lbl)) // => -[h tlaE].
  have {h} := congr1 some h; rewrite -(nth_map _ None) // => <- /=.
  congr ok; rewrite /st_write_ip /=; move: eqv2; rewrite /setc /=.
  case=> /= ->; rewrite ok_xc /assemble_c ok_sa => -[eq_xc] ok_sa2.
  move=> le_ip2_c /(rflags_eq xfE) -> /(regs_eq xrE) ->.
  move: ok_sa2; rewrite tlaE => -[].
  rewrite eq_xc; move/inj_drop=> ->//; first by rewrite -eq_xc.
  by case: {+}xs2.
+ case=> [lv vm] [|_ _] //= ii lbl cs csf [-> ->] /=.
  move=> ok_csf; case: xs1 => xm xr xf xc ip -/dup[] [/= <-] ok_xc.
  rewrite /assemble_c /setc /=; t_xrbindP => tla ok_tla drop_xc.
  move=> le_ip xfE xrE eqv1 eqv2; rewrite /fetch_and_eval /=.
  have lt_ip: ip < size xc; first (rewrite leqNgt; apply/negP).
  * by move/drop_oversize; rewrite -drop_xc.
  move: drop_xc; rewrite (drop_nth (JMP lbl)) // => -[h tlaE].
  have {h} := congr1 some h; rewrite -(nth_map _ None) // => <- /=.
  rewrite /eval_JMP /st_write_ip /=.
  case: (xfind_label ok_csf ok_xc) => ip' [-> lt_ip' ok_tl] /=; congr ok.
  case: xs2 eqv2 => xm2 xr2 xf2 xc2 ip2 [/= ->].
  rewrite ok_xc => -[<-] ok_drop le_ip2.
  move=> /(rflags_eq xfE) -> /(regs_eq xrE) ->; f_equal.
  by move: ok_drop; rewrite ok_tl => -[] => /inj_drop -> //; apply/ltnW. 
+ move=> ii [lv vm] [|i li] //= e lbl cst csf [-> ->] {li} /=.
  rewrite /to_estate /=; t_xrbindP=> v ok_v vl_v ok_csf.
  case: xs1 => xm xr xf xc ip -/dup[] [/= <-] ok_xc.
  rewrite /assemble_c /setc /=; t_xrbindP=> a ct ok_ct [ok_a] /=.
  move=> tla ok_tla drop_xc le_ip xfE xrE eqv1 eqv2; rewrite /fetch_and_eval /=.
  have lt_ip: ip < size xc; first (rewrite leqNgt; apply/negP).
  * by move/drop_oversize; rewrite -drop_xc.
  move: drop_xc; rewrite (drop_nth a) // -{}ok_a => -[h tlaE].
  have {h} := congr1 some h; rewrite -(nth_map _ None) // => <- /=.
  rewrite /st_write_ip /= /eval_Jcc /= /eval_JMP.
  rewrite (xeval_cond eqv1 ok_ct ok_v) vl_v /= /st_write_ip /=.
  case: (xfind_label ok_csf ok_xc) => ip' [-> lt_ip' ok_tl] /=; congr ok.
  case: xs2 eqv2 => xm2 xr2 xf2 xc2 ip2 [/= ->].
  rewrite ok_xc => -[<-] ok_drop le_ip2.
  move=> /(rflags_eq xfE) -> /(regs_eq xrE) ->; f_equal.
  by move: ok_drop; rewrite ok_tl => -[] => /inj_drop -> //; apply/ltnW. 
+ move=> ii [lv vm] [|i li] //= e lbl cs [-> ->] {li} /=.
  rewrite /to_estate /=; t_xrbindP => v ok_v ok_bv; rewrite /setc /=.
  case: xs1 => xm xr xf xc ip -/dup[] [/= <-] ok_xc.
  rewrite /assemble_c /setc /=; t_xrbindP=> a ct ok_ct [ok_a] /=.
  move=> tla ok_tla drop_xc le_ip xfE xrE eqv1 eqv2; rewrite /fetch_and_eval /=.
  have lt_ip: ip < size xc; first (rewrite leqNgt; apply/negP).
  * by move/drop_oversize; rewrite -drop_xc. 
  move: drop_xc; rewrite (drop_nth a) // -{}ok_a => -[h tlaE].
  have {h} := congr1 some h; rewrite -(nth_map _ None) // => <- /=.
  rewrite /st_write_ip /= /eval_Jcc /= /eval_JMP.
  rewrite (xeval_cond eqv1 ok_ct ok_v) ok_bv /= /st_write_ip /=.
  case: eqv2 => /= ->; rewrite ok_xc /assemble_c ok_tla.
  case=> [eq_xc] [tlaE2] le_ip2.
  move=> /(rflags_eq xfE) -> /(regs_eq xrE) ->; congr ok.
  move: tlaE2; rewrite tlaE eq_xc => /inj_drop -> //.
  + by rewrite -eq_xc. + by case: {+}xs2.
Admitted.
