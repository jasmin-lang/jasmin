From mathcomp Require Import ssreflect ssrfun ssrbool ssralg eqtype word_ssrZ.
Require Import psem safety_shared.
Import Utf8.

Section LEMMAS.
Context
  {asm_op syscall_state : Type}
  {ep : EstateParams syscall_state}
  {spp : SemPexprParams}.

#[local] Existing Instance nosubword.
#[local] Existing Instance withassert.

Lemma to_val_defined t (x : sem_t t) v : to_val x = v -> is_defined v.
Proof. by move=>/to_valI; case: v. Qed.

Lemma sem_pexpr_defined {wc: WithCatch} s gd e v : sem_pexpr true gd s e = ok v -> is_defined v.
Proof.
  case: e => /=; t_xrbindP; try by move=> *; subst.
  + by move=> > /get_gvar_compat /= [].
  + by move=> >; apply: on_arr_gvarP => ????; t_xrbindP => *; subst.
  + by move=> >; apply: on_arr_gvarP => ????; t_xrbindP => *; subst.
  + move=> > _; rewrite /sem_sop1; case: wc => -[] /=; first last.
    + by t_xrbindP => ????; apply to_val_defined.
    case: of_val=> ? /=; first case: sem_sop1_typed => ? /=.
    + by move=> [] /to_val_defined.
    1-2: by case: ifP => //= _ [] <-; apply /is_defined_default_val.
  + move=> > _ > _ >; rewrite /sem_sop2; case: wc => -[] /=; first last.
    + by t_xrbindP => ??????; apply to_val_defined.
    case: of_val=> ? /=; case: of_val=> ? /=; first case: sem_sop2_typed => ? /=.
    + by move=> [] /to_val_defined.
    1-4: by case: ifP => //= _ [] <-; apply /is_defined_default_val.
  + move=> > _; rewrite /sem_opN; case: wc => -[] /=; first last.
    + by t_xrbindP => ??; apply to_val_defined.
    case: app_sopn=> ? /=; first by move=> [] /to_val_defined.
    by case: ifP => //= _ [] <-; apply /is_defined_default_val.
  + by move=> > _ _ > _ /truncate_val_defined ? > _ /truncate_val_defined ? <-; case: ifP.
  + move=> > _ _ > _ _ vid > _ /truncate_val_defined.
    elim: ziota vid => //=.
    + by move=> ?? [<-].
    move=> ?? hrec vid _; t_xrbindP => > _ > _ hop2; apply hrec.
    move: hop2; rewrite /sem_sop2; case: wc hrec => -[] /= hrec; first last.
    + by t_xrbindP => ??????; apply to_val_defined.
    + case: of_val => ? /=; case: of_val => ? /=; first case: sem_sop2_typed => ? /=.
      + by move=> [] /to_val_defined.
      1-4: by case: ifP => //= _ [] <-; apply /is_defined_default_val.
  all: by move=> >; apply: on_arr_varP; t_xrbindP => *; subst.
Qed.

Lemma sem_pexprs_defined s gd es vs : sem_pexprs true gd s es = ok vs -> all is_defined vs.
Proof.
  elim : es vs => /= [ | e es hrec] vs; t_xrbindP.
  + by move=> <-.
  by move=> ? /sem_pexpr_defined he ? /hrec hes <- /=; rewrite he hes.
Qed.

Lemma isdef_errtype v t e:
  is_defined v ->
  of_val t v = Error e ->
  e = ErrType.
Proof.
  case: t; case: v => //=; rewrite /type_error;
  try by move=> > ? > ? [].
  by rewrite /WArray.cast=> > _; case: ifP => // _ [].
  by move=> > _ /truncate_word_errP[].
Qed.

Lemma etrueE {wc:WithCatch} gd s : sem_cond gd etrue s = ok true.
Proof. done. Qed.

Opaque of_val.
Lemma enotE {wc:WithCatch} gd s e b:
  sem_cond gd (enot e) s = ok b <-> sem_cond gd e s = ok (~~b).
Proof.
  rewrite /sem_cond /= /sem_sop1 /=; split; t_xrbindP.
  + rewrite /with_catch; case: wc => -[] >.
    + move=> he; rewrite he /=.
      have hdef := isdef_errtype (sem_pexpr_defined he).
      case heq : of_val => /=.
      + by move=> [<-] /to_boolI[<-]; rewrite Bool.negb_involutive.
      by have -> := hdef cbool _ heq.
    t_xrbindP => -> ? /to_boolI -> <- /to_boolI[<-] /=.
    by rewrite Bool.negb_involutive.
  move=> z -> /= /to_boolI ?; subst z.
  rewrite /with_catch; case: wc => -[].
  + case heq : of_val => //=.
    + by move: heq => /to_boolI[<-]; rewrite Bool.negb_involutive.
  by rewrite of_val_to_val /= Bool.negb_involutive.
Qed.

Lemma eandE {wc:WithCatch} gd s e1 e2 :
  sem_cond gd (eand e1 e2) s = ok true <->
    sem_cond gd e1 s = ok true /\ sem_cond gd e2 s = ok true.
Proof.
  rewrite /eand /sem_cond /= /sem_sop2 /=; split.
  + t_xrbindP => z z1 he1 z2 he2; rewrite he1 he2 /=.
    case: wc he1 he2 => -[] /= /sem_pexpr_defined he1 /sem_pexpr_defined he2.
    + move=> + /to_boolI ?; subst z.
      case h2: of_val=> [?|e] /=; case h1: of_val => [?|e']/=.
      + by move: h1 h2 => /= /to_boolI -> /to_boolI -> [] /andP[-> ->].
        1,3: by case: ifP => //; have:=isdef_errtype (t:=sbool) he1 h1; move=> ->.
      by case: ifP => //; have:=isdef_errtype (t:=sbool) he2 h2; move=> ->.
  + by t_xrbindP=> b1 /to_boolI -> b2 /to_boolI -> <-; case: b1 b2 => -[].
  move=> []; t_xrbindP => z -> /to_boolI ?; subst z.
  move=> z -> /to_boolI ?; subst z => /=.
  by case: with_catch.
Qed.
Transparent of_val.

Lemma eandsE_nil {wc: WithCatch} gd s : sem_cond gd (eands [::]) s = ok true.
Proof. done. Qed.

Lemma eandsE_1 {wc: WithCatch} gd s e : sem_cond gd (eands [::e]) s = sem_cond gd e s.
Proof. done. Qed.

Lemma eandsE_cons {wc: WithCatch} gd s e es :
  sem_cond gd (eands (e::es)) s = ok true <-> sem_cond gd e s = ok true /\ sem_cond gd (eands es) s = ok true.
Proof.
  rewrite /=; case: es => /=.
  + rewrite etrueE; tauto.
  by move=> ??; rewrite eandE.
Qed.

Lemma read_etrue : read_e etrue = Sv.empty.
Proof. done. Qed.

Lemma read_eands es : Sv.Equal (read_e (eands es)) (read_es es).
Proof.
  elim: es => //= e l hrec; rewrite read_es_cons -hrec => {hrec}.
  case: l.
  + rewrite /= read_etrue; SvD.fsetdec.
  move=> a l; move: (a::l) => {a} {}l.
  by rewrite read_e_Papp2.
Qed.

Lemma use_mem_eands es :
  use_mem (eands es) = has (fun e => use_mem e) es.
Proof.
  elim: es => //=.
  move=> a [ /= | a' l] hl.
  + by rewrite orbF.
  by move: (a'::l) hl => {a'} {}l <-.
Qed.

Opaque eands.

Lemma eandsE_cat {wc:WithCatch} gd s es1 es2 :
   sem_cond gd (eands (es1 ++ es2)) s = ok true <->
   sem_cond gd (eands es1) s = ok true /\ sem_cond gd (eands es2) s = ok true.
Proof.
  elim: es1 => //=.
  + by rewrite etrueE; tauto.
  move=> e es1 hrec; rewrite !eandsE_cons hrec; tauto.
Qed.

Lemma wmin_signed_neg ws : (wmin_signed ws < 0)%Z.
Proof. rewrite /wmin_signed; have := half_modulus_pos ws; Lia.lia. Qed.

Lemma wmax_signed_pos ws : (0 < wmax_signed ws)%Z.
Proof. by case: ws. Qed.

Lemma in_wint_range_zasr sg sz (w1 : word sz) (w2 : u8) :
  in_wint_range sg sz (zasr (int_of_word sg w1) (int_of_word Unsigned w2)) = ok tt.
Proof.
  rewrite /in_wint_range /zasr /zlsl /assert; case: ifPn => // /negP.
  have [h1 h2] := wunsigned_range w2.
  rewrite /int_of_word /=; elim; case: ZleP => ?.
  + have -> /= : wunsigned w2 = 0%Z by Lia.lia.
    rewrite Z.mul_1_r; case: (sg) => /=;
    [have [??] := wsigned_range w1 | have [??] := wunsigned_range w1];
    apply/andP; split; apply /ZleP => //.
    rewrite /wmax_unsigned; Lia.lia.
  have ? : (0 < 2 ^ wunsigned w2)%Z by Lia.nia.
  rewrite Z.opp_involutive; case: (sg) => /=.
  + have ? := wmin_signed_neg sz; have ? := wmax_signed_pos sz.
    have [??] := wsigned_range w1.
    apply/andP;split;apply/ZleP.
    + by apply Z.div_le_lower_bound => //; Lia.nia.
    by apply Z.div_le_upper_bound => //; Lia.nia.
  have ? : (1 <= wmax_unsigned sz)%Z.
  + by case sz.
  have [??] := wunsigned_range w1.
  have ? : (0 < 2 ^ wunsigned w1)%Z by Lia.nia.
  apply/andP;split;apply/ZleP.
  + apply Z.div_le_lower_bound => //; Lia.nia.
  apply Z.div_le_upper_bound => //; rewrite /wmax_unsigned; Lia.nia.
Qed.

Lemma wsigned_opp sz (w:word sz) : wsigned w ≠ wmin_signed sz → (- wsigned w)%Z = wsigned (- w).
Proof.
  rewrite !wsigned_alt.
  rewrite !wunsigned_add_if wunsigned_opp_if.
  have h1 := half_modulus_pos sz.
  have h2 := wbase_twice_half sz.
  have -> : wunsigned (wrepr sz (half_modulus sz)) = half_modulus sz.
  + by apply wunsigned_repr_small; Lia.lia.
  case: eqP => [-> | ? ].
  + rewrite Z.add_0_l; have -> : (half_modulus sz <? wbase sz)%Z.
    + by apply /ZltP; Lia.lia.
    by move=> _; ring.
  rewrite /wmin_signed; case: ZltP => ?; case: ZltP => ?; Lia.lia.
Qed.

Section SC.

Context (gd : glob_decls) (s : estate).

Lemma eleiP {wc: WithCatch} e1 e2 i1 i2 :
  sem_pexpr true gd s e1 = ok (Vint i1) →
  sem_pexpr true gd s e2 = ok (Vint i2) →
  sem_cond gd (elei e1 e2) s = ok (i1 <=? i2)%Z.
Proof. by rewrite /sem_cond /= => -> ->; case: wc => -[]. Qed.

Lemma eltiP e1 e2 i1 i2 :
  sem_pexpr true gd s e1 = ok (Vint i1) →
  sem_pexpr true gd s e2 = ok (Vint i2) →
  sem_cond gd (elti e1 e2) s = ok (i1 <? i2)%Z.
Proof. by rewrite /sem_cond /= => -> ->. Qed.

Lemma eeqiP {wc:WithCatch} e1 e2 i1 i2 :
  sem_pexpr true gd s e1 = ok (Vint i1) →
  sem_pexpr true gd s e2 = ok (Vint i2) →
  sem_cond gd (eeqi e1 e2) s = ok (i1 == i2).
Proof. by rewrite /sem_cond /= => -> ->; case: wc => -[]. Qed.

Lemma eneqiP {wc: WithCatch} e1 e2 i1 i2 :
  sem_pexpr true gd s e1 = ok (Vint i1) →
  sem_pexpr true gd s e2 = ok (Vint i2) →
  sem_cond gd (eneqi e1 e2) s = ok (i1 != i2).
Proof. by rewrite /sem_cond /= => -> ->; case: wc => -[]. Qed.

Lemma sc_sint_rangeP {wc:WithCatch} e i sz :
  sem_pexpr true gd s e = ok (Vint i) →
  sem_cond gd (sc_sint_range sz e) s = ok true →
  in_sint_range sz i.
Proof.
  rewrite /sc_sint_range /sc_in_range eandE => he.
  rewrite (eleiP (i1 := wmin_signed sz) _ he) => //.
  by rewrite (eleiP (i2 := wmax_signed sz) he) /in_sint_range => // -[[->] [->]].
Qed.

Lemma sc_uint_rangeP {wc:WithCatch} e i sz :
  sem_pexpr true gd s e = ok (Vint i) →
  sem_cond gd (sc_uint_range sz e) s = ok true →
  in_uint_range sz i.
Proof.
  rewrite /sc_uint_range /sc_in_range eandE => he.
  rewrite (eleiP (i1 := 0%Z) _ he) => //.
  by rewrite (eleiP (i2 := wmax_unsigned sz) he) /in_uint_range => // -[[->] [->]].
Qed.

Lemma sc_wi_rangeP {wc:WithCatch} e i sg sz :
  sem_pexpr true gd s e = ok (Vint i) →
  sem_cond gd (sc_wi_range sg sz e) s = ok true →
  in_wint_range sg sz i = ok tt.
Proof.
  rewrite /sc_wi_range /in_wint_range.
  case: sg => /= he hc.
  + by rewrite (sc_sint_rangeP he hc).
  by rewrite (sc_uint_rangeP he hc).
Qed.

Lemma int_of_word_wrepr sg sz z :
  in_wint_range sg sz z = ok tt ->
  int_of_word sg (wrepr sz z) = z.
Proof.
  case: sg => /assertP /andP[] /ZleP ? /ZleP; rewrite /wmax_unsigned => ?.
  + exact: wsigned_repr.
  apply wunsigned_repr_small; Lia.lia.
Qed.

Lemma wint_of_int_of_word sg sz (w : word sz) :
  wint_of_int sg sz (int_of_word sg w) = ok w.
Proof.
  rewrite /wint_of_int /int_of_word /in_wint_range /signed.
  case: sg.
  + rewrite wrepr_signed /in_sint_range.
    by have [/ZleP -> /ZleP ->]:= wsigned_range w.
  rewrite wrepr_unsigned /in_uint_range.
  have [/ZleP -> h]:= wunsigned_range w.
  have /ZleP -> //: (wunsigned w <= wmax_unsigned sz)%Z.
  by rewrite /wmax_unsigned; Lia.lia.
Qed.

Lemma sc_int_of_word_wrepr {wc:WithCatch} e i sg sz:
  sem_pexpr true gd s e = ok (Vint i) →
  sem_cond gd (sc_wi_range sg sz e) s = ok true →
  int_of_word sg (wrepr sz i) = i.
Proof.
  move=> he hsc; apply int_of_word_wrepr.
  apply: sc_wi_rangeP he hsc.
Qed.

Lemma sc_wi_range_of_int {wc:WithCatch} e i sg sz :
  sem_pexpr true gd s e = ok (Vint i) →
  sem_cond gd (sc_wi_range sg sz e) s = ok true →
  wint_of_int sg sz i = ok (wrepr sz i).
Proof. by move=> he hsc; rewrite -{1}(sc_int_of_word_wrepr he hsc) wint_of_int_of_word. Qed.

Lemma sc_allE body start len (xi:var_i) sti leni:
  vtype xi = aint ->
  sem_pexpr true gd s start = ok (Vint sti) ->
  sem_pexpr true gd s len = ok (Vint leni) ->
  sem_cond gd (eands (sc_all body xi start len)) s = ok true ->
  List.Forall (fun (j : Z) =>
    (Let s := write_var true xi j s in
     sem_cond gd (eands body) s) = ok true) (ziota sti leni).
Proof.
  move=> hxi hst hlen; rewrite /sc_all.
  case: body.
  + move=> _; elim: ziota => // j js hrec; constructor => //.
    by rewrite (write_var_eq_type (x:=xi) (v:=Vint j)) //= hxi.
  move=> a l; move: (a :: l) => body {a l}.
  rewrite eandsE_1 /sem_cond /= hst hlen /=; t_xrbindP.
  move=> z + /to_boolI ?; subst z.
  elim: ziota => //= j js hrec; t_xrbindP.
  move=> v s1 hw v2 hv2 hand hfold.
  move: hand; rewrite /sem_sop2 /=; t_xrbindP => b hb ?; subst v.
  case: b hfold hb; last first.
  + move=> hfold _; have //: False.
    elim: (js) hfold => //= j' js' hrec'; rewrite {2}/sem_sop2 /= /mk_sem_sop2; t_xrbindP => /=.
    by move=> > _ > _ > _ <-.
  move=> hfold /to_boolI ?; subst v2; constructor => //.
  + by rewrite hw /= hv2.
  by apply hrec.
Qed.

Lemma int_of_word0 sg sz : int_of_word (sz:=sz) sg 0 = 0%Z.
Proof. by case: sg => /=; rewrite ?wsigned0 ?wunsigned0. Qed.

Lemma sem_sc_divmod {wc: WithCatch} sz sg (w1 w2 : word sz) e1 e2 :
  sem_pexpr true gd s e1 = ok (Vint (int_of_word sg w1)) →
  sem_pexpr true gd s e2 = ok (Vint (int_of_word sg w2)) →
  sem_cond gd (eands (sc_divmod sg sz e1 e2)) s = ok true →
  ((w2 == 0%R) || [&& sg == Signed, wsigned w1 == wmin_signed sz & w2 == (-1)%R]) = false.
Proof.
  move=> h1 h2; rewrite /sc_divmod eandsE_cons.
  rewrite (eneqiP (i2:=0%Z) h2) // => -[[/eqP h0] hsc].
  apply/negbTE/negP => /orP [ /eqP ?| /and3P [/eqP ? /eqP hw1 /eqP ?]].
  + by subst w2; apply/h0/int_of_word0.
  subst w2 sg; move: hsc => /=; rewrite eandsE_1 enotE.
  have -> // : sem_cond gd (eand (eeqi e1 (emin_signed sz)) (eeqi e2 (-1)%Z)) s = ok true.
  by rewrite eandE (eeqiP (i2:= wmin_signed sz) h1) // (eeqiP (i2:= -1) h2) // -hw1 eqxx /= wsignedN1 eqxx.
Qed.

Lemma sem_pexpr_tovI e v t :
  sem_pexpr true gd s e = ok v ->
  type_of_val v = t ->
  match t with
  | cbool => ∃ b : bool, v = b
  | cint => ∃ i : Z, v = i
  | carr len => ∃ a : WArray.array len, v = Varr a
  | cword ws => ∃ w : word ws, v = Vword w
  end.
Proof.
  move=> /sem_pexpr_defined hd /type_of_valI h.
  by case: t h hd => // [||ws] [->| ].
Qed.

Lemma check_scP {wc: WithCatch} sc s1 s2 okmem W:
  okmem || ~~has use_mem sc ->
  disjoint (read_es sc) W ->
  evm s1 =[\W] evm s2 ->
  (okmem → emem s1 = emem s2) ->
  sem_cond gd (eands sc) s1 = sem_cond gd (eands sc) s2.
Proof.
  rewrite -read_eands -use_mem_eands /sem_cond.
  move: (eands _) => e hokm /Sv.is_empty_spec hdisj hvm hmem.
  suff : [elaborate sem_pexpr true gd s1 e = sem_pexpr true gd s2 e].
  + by move=> ->.
  have ? : evm s1 =[read_e e] evm s2.
  + by move=> x hx; apply hvm; SvD.fsetdec.
  case: okmem hokm hmem => /=.
  + by move=> _ /(_ erefl) hmem; apply: (eq_on_sem_pexpr true gd hmem).
  by move=> huse _; apply use_memP_eq_on.
Qed.

End SC.

(* FIXME: move this in relationnal, and generalize to wequiv, safe_assert should be move in expr *)
Section SafeAssert.
Context {sip : SemInstrParams asm_op syscall_state}.
#[local] Existing Instance progUnit.
#[local] Existing Instance indirect_c.

Context {E E0: Type -> Type} {wE : with_Error E E0} {rE : EventRels E0}.
Variable (p1 p2:uprog) (ev:extra_val_t).

Notation gd := (p_globs p1).

Lemma safe_assertP {wc1 wc2: WithCatch} R spec ii scs :
  wequiv_rec (wc1:=wc1) (wc2:=wc2) p1 p2 ev ev spec R (safe_assert ii scs) [::]
    (λ s1 s2 : estate, R s1 s2 ∧ sem_cond (wc:=wc1) gd (eands scs) s1 = ok true).
Proof.
  apply wkequiv_eq_pred => s1 s2 hR.
  apply wequiv_weaken with
    (eq_init s1 s2) (λ s1' s2' : estate, eq_init s1 s2 s1' s2' ∧ sem_cond (wc:=wc1) gd (eands scs) s1 = ok true) => //.
  + by move=> _ _ [[-> ->] ?].
  elim : scs => [| sc scs hrec].
  + by apply wequiv_nil => ?? [-> ->]; rewrite eandsE_nil.
  rewrite /= -(cats0 [::]) -cat1s.
  apply wequiv_cat with (λ s1' s2' : estate, eq_init s1 s2 s1' s2' ∧ sem_cond (wc:=wc1) gd sc s1 = ok true).
  + apply wequiv_assert_left =>  _ _ _ [-> ->] /=; rewrite /sem_cond.
    + by move=> ->.
  apply wkequiv_eq_pred => _ _ [[-> ->] hsc].
  apply wequiv_weaken with (eq_init s1 s2)
      (λ s1' s2' : estate, (s1' = s1 ∧ s2' = s2) ∧ sem_cond (wc:=wc1) gd (eands scs) s1 = ok true) => //.
  by move => ?? [[-> ->]]; rewrite eandsE_cons.
Qed.

Lemma syscall_u_toutP o fs fs' :
  fexec_syscall o fs = ok fs' ->
  fmem fs = fmem fs' /\ List.map type_of_val fs'.(fvals) = map eval_atype (scs_tout (syscall_sig_u o)).
Proof.
  rewrite /fexec_syscall; t_xrbindP => -[[scs m_] vs_] + [<-] /=.
  case: o => ws len /=.
  rewrite /exec_getrandom_u.
  case: (fvals fs) => // v [] //; t_xrbindP.
  by move=> ?? _ ? _ <- /= _ <- <-.
Qed.

End SafeAssert.

End LEMMAS.
