(* * Semantic lemmas shared by the users of [safety_common.v]:
   the [wint_int] pass and the safety pass.

   Everything here is parametric in the [WithCatch] instance: the safety
   conditions are meant to be evaluated under the defensive semantics
   ([withcatch]), while the programs they instrument run under the standard
   one. *)

From mathcomp Require Import ssreflect ssrfun ssrbool ssralg eqtype word_ssrZ.
Require Import op_semi psem safety_common.
Import Utf8.

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

Lemma use_mem_eands es : use_mem (eands es) = has use_mem es.
Proof.
  elim: es => //=.
  move=> a [ /= | a' l] hl.
  + by rewrite orbF.
  by move: (a'::l) hl => {a'} {}l <-.
Qed.

Lemma read_aands as_ : Sv.Equal (read_eassert (aands as_)) (read_easserts as_).
Proof.
  elim: as_ => //= a l hrec; rewrite read_easserts_cons -hrec => {hrec}.
  case: l.
  + by rewrite /= /read_easserts /=; clear; SvD.fsetdec.
  move=> b l; move: (b::l) => {b} {}l.
  by rewrite read_eassert_Pand.
Qed.

Lemma use_mem_aands as_ : use_mem_eassert (aands as_) = has use_mem_eassert as_.
Proof.
  elim: as_ => //=.
  move=> a [ /= | a' l] hl.
  + by rewrite orbF.
  by move: (a'::l) hl => {a'} {}l <-.
Qed.

Section LEMMAS.

Context
  {asm_op syscall_state : Type}
  {ep : EstateParams syscall_state}
  {spp : SemPexprParams}.

#[local] Existing Instance nosubword.
#[local] Existing Instance withassert.

Lemma to_val_defined t (x : sem_t t) v : to_val x = v -> is_defined v.
Proof. by move=> /to_valI; case: v. Qed.

(* Under [withcatch] a failing operator returns [default_val], which is defined;
   under [nocatch] the value comes from a successful [to_val]. *)
Lemma sem_pexpr_defined {wc : WithCatch} s gd e v :
  sem_pexpr true gd s e = ok v -> is_defined v.
Proof.
  case: e => /=; t_xrbindP; try by move=> *; subst.
  + by move=> > /get_gvar_compat /= [].
  + by move=> >; apply: on_arr_gvarP => ????; t_xrbindP => *; subst.
  + by move=> >; apply: on_arr_gvarP => ????; t_xrbindP => *; subst.
  + move=> > _; rewrite /sem_sop1; case: wc => -[] /=; first last.
    + by t_xrbindP => ????; apply to_val_defined.
    case: of_val => ? /=; first case: sem_sop1_typed => ? /=.
    + by move=> [] /to_val_defined.
    1-2: by case: ifP => //= _ [] <-; apply /is_defined_default_val.
  + move=> > _ > _ >; rewrite /sem_sop2; case: wc => -[] /=; first last.
    + by t_xrbindP => ??????; apply to_val_defined.
    case: of_val => ? /=; case: of_val => ? /=; first case: sem_sop2_typed => ? /=.
    + by move=> [] /to_val_defined.
    1-4: by case: ifP => //= _ [] <-; apply /is_defined_default_val.
  + move=> > _; rewrite /sem_opN; case: wc => -[] /=; first last.
    + by t_xrbindP => ??; apply to_val_defined.
    case: app_sopn => ? /=; first by move=> [] /to_val_defined.
    by case: ifP => //= _ [] <-; apply /is_defined_default_val.
  by move=> > _ _ > _ /truncate_val_defined ? > _ /truncate_val_defined ? <-; case: ifP.
Qed.

Lemma sem_pexprs_defined {wc : WithCatch} s gd es vs :
  sem_pexprs true gd s es = ok vs -> all is_defined vs.
Proof.
  elim: es vs => /= [ | e es hrec] vs; t_xrbindP.
  + by move=> <-.
  by move=> ? /sem_pexpr_defined he ? /hrec hes <- /=; rewrite he hes.
Qed.

(* A defined value can only fail to be coerced for a typing reason. *)
Lemma isdef_errtype v t e :
  is_defined v ->
  of_val t v = Error e ->
  e = ErrType.
Proof.
  case: t; case: v => //=; rewrite /type_error;
  try by move=> > ? > ? [].
  + by rewrite /WArray.cast => > _; case: ifP => // _ [].
  by move=> > _ /truncate_word_errP [].
Qed.

(* ------------------------------------------------------------------------- *)
(* Under [withcatch] the only remaining failure is a typing error             *)

(* This is what justifies the points that are deliberately *not* caught:
   [get_global], [on_arr_var], the [to_*] coercions and the [truncate_val] of
   [Pif] can only fail for a typing reason, never for a safety one. *)

Lemma get_gvar_errty gd vm x er :
  get_gvar (wc:=withcatch) true gd vm x = Error er -> er = ErrType.
Proof.
  rewrite /get_gvar; case: ifP => _.
  + by apply catch_core_errty.
  rewrite /get_global; case: get_global_value => [ga|]; last by move=> [<-].
  by case: eqP => // _ [<-].
Qed.

Lemma on_arr_gvar_errty A gd vm x (f : forall n, WArray.array n -> exec A) er :
  (forall n t, f n t = Error er -> er = ErrType) ->
  on_arr_var (get_gvar (wc:=withcatch) true gd vm x) f = Error er -> er = ErrType.
Proof.
  rewrite /on_arr_var => hf.
  case heq: get_gvar => [v|e2] /=; last by move=> [<-]; apply: get_gvar_errty heq.
  case: v heq => //=.
  + by move=> ? _ [<-].
  + by move=> ? _ [<-].
  + by move=> ?? _; apply hf.
  + by move=> ?? _ [<-].
  by move=> ?? _ [<-].
Qed.

Lemma sem_to_errty gd s e v t er :
  sem_pexpr (wc:=withcatch) true gd s e = ok v -> of_val t v = Error er -> er = ErrType.
Proof. by move=> /sem_pexpr_defined h; apply: isdef_errtype h. Qed.

Lemma sem_pexpr_errty_pair gd s :
  (forall e er, sem_pexpr (wc:=withcatch) true gd s e = Error er -> er = ErrType) /\
  (forall es er, sem_pexprs (wc:=withcatch) true gd s es = Error er -> er = ErrType).
Proof.
  apply: pexprs_ind_pair; split => //=.
  - move=> pe hpe pes hpes er.
    case heq: (sem_pexpr true gd s pe) => [y|e1] /=; last by move=> [<-]; apply: hpe heq.
    case heq2: (sem_pexprs true gd s pes) => [ys|e2] /=; last by move=> [<-]; apply: hpes heq2.
    by [].
  - by move=> x er; apply get_gvar_errty.
  - move=> al aa sz x e he er.
    apply: on_arr_gvar_errty => n t.
    case heq: (sem_pexpr true gd s e) => [v|e1] /=; last by move=> [<-]; apply: he heq.
    case hi: (to_int v) => [i|e2] /=; last by move=> [<-]; apply: (sem_to_errty (t:=cint) heq hi).
    case hw: catch_core => [w|e3] /=; last by move=> [<-]; apply: catch_core_errty hw.
    by [].
  - move=> aa sz len x e he er.
    apply: on_arr_gvar_errty => n t.
    case heq: (sem_pexpr true gd s e) => [v|e1] /=; last by move=> [<-]; apply: he heq.
    case hi: (to_int v) => [i|e2] /=; last by move=> [<-]; apply: (sem_to_errty (t:=cint) heq hi).
    case hw: catch_core => [w|e3] /=; last by move=> [<-]; apply: catch_core_errty hw.
    by [].
  - move=> al sz e he er.
    case heq: (sem_pexpr true gd s e) => [v|e1] /=; last by move=> [<-]; apply: he heq.
    case hp: (to_pointer v) => [p|e2] /=;
      last by move=> [<-]; apply: (sem_to_errty (t:=cword Uptr) heq hp).
    case hr: catch_core => [w|e3] /=; last by move=> [<-]; apply: catch_core_errty hr.
    by [].
  - move=> op e he er.
    case heq: (sem_pexpr true gd s e) => [v|e1] /=; last by move=> [<-]; apply: he heq.
    by apply catch_core_errty.
  - move=> op e1 h1 e2 h2 er.
    case q1: (sem_pexpr true gd s e1) => [v1|er1] /=; last by move=> [<-]; apply: h1 q1.
    case q2: (sem_pexpr true gd s e2) => [v2|er2] /=; last by move=> [<-]; apply: h2 q2.
    by apply catch_core_errty.
  - move=> op es hes er.
    case q: (mapM (sem_pexpr true gd s) es) => [vs|er1] /=; last by move=> [<-]; apply: hes q.
    by apply catch_core_errty.
  move=> ty e he e1 h1 e2 h2 er.
  case q: (sem_pexpr true gd s e) => [v|er0] /=; last by move=> [<-]; apply: he q.
  case qb: (to_bool v) => [b|er1] /=; last by move=> [<-]; apply: (sem_to_errty (t:=cbool) q qb).
  case q1: (sem_pexpr true gd s e1) => [w1|er2] /=; last by move=> [<-]; apply: h1 q1.
  rewrite /truncate_val.
  case t1: (of_val (eval_atype ty) w1) => [u1|er3] /=;
    last by move=> [<-]; apply: (sem_to_errty q1 t1).
  case q2: (sem_pexpr true gd s e2) => [w2|er4] /=; last by move=> [<-]; apply: h2 q2.
  case t2: (of_val (eval_atype ty) w2) => [u2|er5] /=;
    last by move=> [<-]; apply: (sem_to_errty q2 t2).
  by [].
Qed.

Definition sem_pexpr_errty gd s := proj1 (sem_pexpr_errty_pair gd s).
Definition sem_pexprs_errty gd s := proj2 (sem_pexpr_errty_pair gd s).

(* ------------------------------------------------------------------------- *)
(* The boolean connectives of the condition language                          *)

Lemma etrueE {wc : WithCatch} gd s : sem_cond gd etrue s = ok true.
Proof. done. Qed.

Opaque of_val.

Lemma enotE {wc : WithCatch} gd s e b :
  sem_cond gd (enot e) s = ok b <-> sem_cond gd e s = ok (~~b).
Proof.
  rewrite /sem_cond /= /sem_sop1 /=; split; t_xrbindP.
  + rewrite /with_catch; case: wc => -[] >.
    + move=> he; rewrite he /=.
      have hdef := isdef_errtype (sem_pexpr_defined he).
      case heq : of_val => /=.
      + by move=> [<-] /to_boolI [<-]; rewrite Bool.negb_involutive.
      by have -> := hdef cbool _ heq.
    t_xrbindP => -> ? /to_boolI -> <- /to_boolI [<-] /=.
    by rewrite Bool.negb_involutive.
  move=> z -> /= /to_boolI ?; subst z.
  rewrite /with_catch; case: wc => -[].
  + case heq : of_val => //=.
    by move: heq => /to_boolI [<-]; rewrite Bool.negb_involutive.
  by rewrite of_val_to_val /= Bool.negb_involutive.
Qed.

Lemma eandE {wc : WithCatch} gd s e1 e2 :
  sem_cond gd (eand e1 e2) s = ok true <->
    sem_cond gd e1 s = ok true /\ sem_cond gd e2 s = ok true.
Proof.
  rewrite /eand /sem_cond /= /sem_sop2 /=; split.
  + t_xrbindP => z z1 he1 z2 he2; rewrite he1 he2 /=.
    case: wc he1 he2 => -[] /= /sem_pexpr_defined he1 /sem_pexpr_defined he2.
    + move=> + /to_boolI ?; subst z.
      case h2: of_val => [?|e] /=; case h1: of_val => [?|e'] /=.
      + by move: h1 h2 => /= /to_boolI -> /to_boolI -> [] /andP [-> ->].
      1,3: by case: ifP => //; have := isdef_errtype (t:=cbool) he1 h1; move=> ->.
      by case: ifP => //; have := isdef_errtype (t:=cbool) he2 h2; move=> ->.
    by t_xrbindP => b1 /to_boolI -> b2 /to_boolI -> <-; case: b1 b2 => -[].
  move=> []; t_xrbindP => z -> /to_boolI ?; subst z.
  move=> z -> /to_boolI ?; subst z => /=.
  by case: with_catch.
Qed.

Transparent of_val.

Lemma eandsE_nil {wc : WithCatch} gd s : sem_cond gd (eands [::]) s = ok true.
Proof. done. Qed.

Lemma eandsE_1 {wc : WithCatch} gd s e :
  sem_cond gd (eands [::e]) s = sem_cond gd e s.
Proof. done. Qed.

Lemma eandsE_cons {wc : WithCatch} gd s e es :
  sem_cond gd (eands (e::es)) s = ok true <->
  sem_cond gd e s = ok true /\ sem_cond gd (eands es) s = ok true.
Proof.
  rewrite /=; case: es => /=.
  + rewrite etrueE; tauto.
  by move=> ??; rewrite eandE.
Qed.

Opaque eands.

Lemma eandsE_cat {wc : WithCatch} gd s es1 es2 :
  sem_cond gd (eands (es1 ++ es2)) s = ok true <->
  sem_cond gd (eands es1) s = ok true /\ sem_cond gd (eands es2) s = ok true.
Proof.
  elim: es1 => //=.
  + by rewrite etrueE; tauto.
  move=> e es1 hrec; rewrite !eandsE_cons hrec; tauto.
Qed.


(* ------------------------------------------------------------------------- *)
(* Same, one level up: conditions as [eassert]                                *)
(* [safety_cond] is [seq eassert], so the safety pass reasons through [aands] *)
(* and [sem_eassert] rather than [eands] and [sem_cond].                      *)

Lemma aandsE_nil {wc : WithCatch} gd s : sem_eassert gd s (aands [::]) = ok true.
Proof. done. Qed.

Lemma aandsE_1 {wc : WithCatch} gd s a :
  sem_eassert gd s (aands [::a]) = sem_eassert gd s a.
Proof. done. Qed.

Lemma aandE {wc : WithCatch} gd s a1 a2 :
  sem_eassert gd s (Pand a1 a2) = ok true <->
  sem_eassert gd s a1 = ok true /\ sem_eassert gd s a2 = ok true.
Proof.
  split.
  + rewrite /=; t_xrbindP => b1 h1 b2 h2 /andP [] hb1 hb2; split.
    + by rewrite h1 hb1.
    by rewrite h2 hb2.
  by move=> [] h1 h2; rewrite /= h1 h2.
Qed.

Lemma aandsE_cons {wc : WithCatch} gd s a as_ :
  sem_eassert gd s (aands (a::as_)) = ok true <->
  sem_eassert gd s a = ok true /\ sem_eassert gd s (aands as_) = ok true.
Proof.
  case: as_ => /=.
  + by split => [h | []].
  by move=> ??; rewrite aandE.
Qed.

(* The operator conditions are built as [seq pexpr] and injected into
   [safety_cond] with [map Pexpr]; this is the bridge between the two layers. *)
Lemma aands_map_PexprE {wc : WithCatch} gd s l :
  sem_eassert gd s (aands [seq Pexpr e | e <- l]) = ok true <->
  sem_cond gd (eands l) s = ok true.
Proof.
  elim: l => [ | e l hrec]; first by split.
  rewrite /= aandsE_cons eandsE_cons; split.
  + by move=> [] h1 h2; split => //; apply/hrec.
  by move=> [] h1 h2; split => //; apply/hrec.
Qed.

Lemma aandsE_cat {wc : WithCatch} gd s as1 as2 :
  sem_eassert gd s (aands (as1 ++ as2)) = ok true <->
  sem_eassert gd s (aands as1) = ok true /\ sem_eassert gd s (aands as2) = ok true.
Proof.
  elim: as1 => /=.
  + by split => [h | []].
  by move=> a as1 hrec; rewrite !aandsE_cons hrec; tauto.
Qed.

(* ------------------------------------------------------------------------- *)
(* The generated conditions, evaluated                                        *)

Section SC.

Context {wc : WithCatch} (gd : glob_decls) (s : estate).

Lemma eleiP e1 e2 i1 i2 :
  sem_pexpr true gd s e1 = ok (Vint i1) ->
  sem_pexpr true gd s e2 = ok (Vint i2) ->
  sem_cond gd (elei e1 e2) s = ok (i1 <=? i2)%Z.
Proof. by rewrite /sem_cond /= => -> ->; case: wc => -[]. Qed.

Lemma eltiP e1 e2 i1 i2 :
  sem_pexpr true gd s e1 = ok (Vint i1) ->
  sem_pexpr true gd s e2 = ok (Vint i2) ->
  sem_cond gd (elti e1 e2) s = ok (i1 <? i2)%Z.
Proof. by rewrite /sem_cond /= => -> ->; case: wc => -[]. Qed.

Lemma eeqiP e1 e2 i1 i2 :
  sem_pexpr true gd s e1 = ok (Vint i1) ->
  sem_pexpr true gd s e2 = ok (Vint i2) ->
  sem_cond gd (eeqi e1 e2) s = ok (i1 == i2).
Proof. by rewrite /sem_cond /= => -> ->; case: wc => -[]. Qed.

Lemma eneqiP e1 e2 i1 i2 :
  sem_pexpr true gd s e1 = ok (Vint i1) ->
  sem_pexpr true gd s e2 = ok (Vint i2) ->
  sem_cond gd (eneqi e1 e2) s = ok (i1 != i2).
Proof. by rewrite /sem_cond /= => -> ->; case: wc => -[]. Qed.

Lemma sc_sint_rangeP e i sz :
  sem_pexpr true gd s e = ok (Vint i) ->
  sem_cond gd (sc_sint_range sz e) s = ok true ->
  in_sint_range sz i.
Proof.
  rewrite /sc_sint_range /sc_in_range eandE => he.
  rewrite (eleiP (i1 := wmin_signed sz) _ he) => //.
  by rewrite (eleiP (i2 := wmax_signed sz) he) /in_sint_range => // -[[->] [->]].
Qed.

Lemma sc_uint_rangeP e i sz :
  sem_pexpr true gd s e = ok (Vint i) ->
  sem_cond gd (sc_uint_range sz e) s = ok true ->
  in_uint_range sz i.
Proof.
  rewrite /sc_uint_range /sc_in_range eandE => he.
  rewrite (eleiP (i1 := 0%Z) _ he) => //.
  by rewrite (eleiP (i2 := wmax_unsigned sz) he) /in_uint_range => // -[[->] [->]].
Qed.

Lemma sc_wi_rangeP e i sg sz :
  sem_pexpr true gd s e = ok (Vint i) ->
  sem_cond gd (sc_wi_range sg sz e) s = ok true ->
  in_wint_range sg sz i = ok tt.
Proof.
  rewrite /sc_wi_range /in_wint_range.
  case: sg => /= he hc.
  + by rewrite (sc_sint_rangeP he hc).
  by rewrite (sc_uint_rangeP he hc).
Qed.

Lemma sc_int_of_word_wrepr e i sg sz :
  sem_pexpr true gd s e = ok (Vint i) ->
  sem_cond gd (sc_wi_range sg sz e) s = ok true ->
  int_of_word sg (wrepr sz i) = i.
Proof. by move=> he hsc; apply int_of_word_wrepr; apply: sc_wi_rangeP he hsc. Qed.

Lemma sc_wi_range_of_int e i sg sz :
  sem_pexpr true gd s e = ok (Vint i) ->
  sem_cond gd (sc_wi_range sg sz e) s = ok true ->
  wint_of_int sg sz i = ok (wrepr sz i).
Proof.
  by move=> he hsc; rewrite -{1}(sc_int_of_word_wrepr he hsc) wint_of_int_of_word.
Qed.

Lemma sem_sc_divmod sz sg (w1 w2 : word sz) e1 e2 :
  sem_pexpr true gd s e1 = ok (Vint (int_of_word sg w1)) ->
  sem_pexpr true gd s e2 = ok (Vint (int_of_word sg w2)) ->
  sem_cond gd (eands (sc_divmod sg sz e1 e2)) s = ok true ->
  ((w2 == 0%R) || [&& sg == Signed, wsigned w1 == wmin_signed sz & w2 == (-1)%R]) = false.
Proof.
  move=> h1 h2; rewrite /sc_divmod eandsE_cons.
  rewrite (eneqiP (i2:=0%Z) h2) // => -[[/eqP h0] hsc].
  apply/negbTE/negP => /orP [/eqP ? | /and3P [/eqP ? /eqP hw1 /eqP ?]].
  + by subst w2; apply/h0/int_of_word0.
  subst w2 sg; move: hsc => /=; rewrite eandsE_1 enotE.
  have -> // : sem_cond gd (eand (eeqi e1 (emin_signed sz)) (eeqi e2 (-1)%Z)) s = ok true.
  by rewrite eandE (eeqiP (i2:= wmin_signed sz) h1) // (eeqiP (i2:= -1) h2) //
     -hw1 eqxx /= wsignedN1 eqxx.
Qed.

Lemma sem_pexpr_tovI e v t :
  sem_pexpr true gd s e = ok v ->
  type_of_val v = t ->
  match t with
  | cbool => exists b : bool, v = b
  | cint => exists i : Z, v = i
  | carr len => exists a : WArray.array len, v = Varr a
  | cword ws => exists w : word ws, v = Vword w
  end.
Proof.
  move=> /sem_pexpr_defined hd /type_of_valI h.
  by case: t h hd => // [||ws] [-> | ].
Qed.

End SC.

(* The conditions attached to the left values of an assignment are asserted
   *before* the assignment.  [check_xs] checks syntactically that this is
   legitimate; these two lemmas are what it buys. *)

Lemma check_scP {wc : WithCatch} gd (sc : seq pexpr) s1 s2 okmem W :
  okmem || ~~ has use_mem sc ->
  disjoint (read_es sc) W ->
  evm s1 =[\W] evm s2 ->
  (okmem -> emem s1 = emem s2) ->
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

Lemma check_scaP {wc : WithCatch} gd (sc : safety_cond) s1 s2 okmem W :
  okmem || ~~ has use_mem_eassert sc ->
  disjoint (read_easserts sc) W ->
  evm s1 =[\W] evm s2 ->
  (okmem -> emem s1 = emem s2) ->
  sem_eassert gd s1 (aands sc) = sem_eassert gd s2 (aands sc).
Proof.
  rewrite -read_aands -use_mem_aands.
  move: (aands _) => a hokm /Sv.is_empty_spec hdisj hvm hmem.
  have ? : evm s1 =[read_eassert a] evm s2.
  + by move=> x hx; apply hvm; SvD.fsetdec.
  case: okmem hokm hmem => /=.
  + by move=> _ /(_ erefl) hmem; apply: eq_on_sem_eassert.
  by move=> huse _; apply: use_mem_eassertP_eq_on.
Qed.


(* ------------------------------------------------------------------------- *)
(* Running the generated assertions                                           *)

Section SAFE_ASSERT.

Context {sip : SemInstrParams asm_op syscall_state}.
#[local] Existing Instance progUnit.
#[local] Existing Instance indirect_c.

Context {E E0 : Type -> Type} {wE : with_Error E E0} {rE : EventRels E0}.
Variable (p1 p2 : uprog) (ev : extra_val_t).

Notation gd := (p_globs p1).

(* [safe_assert ii scs] leaves the state untouched and establishes that every
   condition of [scs] holds, while the right-hand side does nothing.  This is
   the first place where the two [WithCatch] instances really differ: the
   conditions are evaluated on the left, under [wc1]. *)
Lemma safe_assertP {wc1 wc2 : WithCatch} R spec ii scs :
  wequiv_rec (wc1:=wc1) (wc2:=wc2) p1 p2 ev ev spec R (safe_assert ii scs) [::]
    (fun s1 s2 => R s1 s2 /\ sem_eassert (wc:=wc1) gd s1 (aands scs) = ok true).
Proof.
  apply wkequiv_eq_pred => s1 s2 hR.
  apply wequiv_weaken with (eq_init s1 s2)
    (fun t1 t2 => eq_init s1 s2 t1 t2 /\ sem_eassert (wc:=wc1) gd s1 (aands scs) = ok true).
  - by move=> ?? [].
  - by move=> t1 t2 [[-> ->] h]; split.
  elim: scs => [| sc scs hrec].
  - by apply wequiv_nil => ?? [-> ->]; split.
  rewrite /= -(cats0 [::]) -cat1s.
  rewrite -/(aands (sc :: scs)).
  apply wequiv_cat with
    (fun t1 t2 => eq_init s1 s2 t1 t2 /\ sem_eassert (wc:=wc1) gd s1 sc = ok true).
  - by apply wequiv_assert_left => _ ?? [-> ->] h; split.
  apply wkequiv_eq_pred => t1 t2 [[-> ->] hsc].
  apply wequiv_weaken with (eq_init s1 s2)
    (fun u1 u2 => (u1 = s1 /\ u2 = s2) /\ sem_eassert (wc:=wc1) gd s1 (aands scs) = ok true).
  - by move=> ?? [].
  - move=> u1 u2 [[-> ->] h]; split; first by [].
    by apply/aandsE_cons; split; [exact hsc | exact h].
  exact hrec.
Qed.


(* The unit syscall semantics does not touch the memory and returns values of
   the declared output types. *)
Lemma syscall_u_toutP o fs fs2 :
  fexec_syscall o fs = ok fs2 ->
  fmem fs = fmem fs2 /\
  List.map type_of_val fs2.(fvals) = map eval_atype (scs_tout (syscall_sig_u o)).
Proof.
  rewrite /fexec_syscall.
  t_xrbindP => -[[scs m_] vs_] + [<-] /=.
  case: o => ws len /=; rewrite /exec_getrandom_u.
  t_xrbindP => a ha t ht heq.
  by move=> <- /= _ <- <-.
Qed.

End SAFE_ASSERT.

End LEMMAS.
