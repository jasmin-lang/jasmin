(* * Correctness of the safety pass.

   The instrumented program, run under the defensive semantics ([withcatch],
   which is the one EasyCrypt implements) and with assertions enabled, refines
   the original program run under the standard semantics. *)

From mathcomp Require Import ssreflect ssrfun ssrbool ssralg eqtype word_ssrZ.
Require Import psem psem_facts compiler_util safety safety_common_proof.
Import Utf8.

Local Open Scope Z_scope.
Local Open Scope seq_scope.

Section SAFETY_PROOF.

#[local] Existing Instance progUnit.

Context
  {asm_op syscall_state : Type}
  {ep : EstateParams syscall_state}
  {spp : SemPexprParams}
  {sip : SemInstrParams asm_op syscall_state}.

#[local] Existing Instance sCP_unit.
#[local] Existing Instance nosubword.
#[local] Existing Instance indirect_c.
#[local] Existing Instance withassert.

Context {E E0 : Type -> Type} {wE : with_Error E E0} {rE : EventRels E0}.

Variable (p : uprog) (ev : extra_val_t).

Notation gd := (p_globs p).
Notation sem_pexpr_wc := (sem_pexpr (wc:=withcatch)).
Notation sem_pexprs_wc := (sem_pexprs (wc:=withcatch)).
Notation sem_eassert_wc := (sem_eassert (wc:=withcatch)).

(* ------------------------------------------------------------------------- *)
(* An array variable is always defined, so it carries no condition.           *)

Lemma var_init_arr s (x : var_i) ws len :
  vtype x = aarr ws len -> sem_eassert_wc gd s (aands (sc_var x)) = ok true.
Proof. by move=> h; rewrite /sc_var h. Qed.

Lemma gvar_init_arr s x ws len :
  vtype (gv x) = aarr ws len -> sem_eassert_wc gd s (aands (sc_gvar x)) = ok true.
Proof. by move=> h; rewrite /sc_gvar /sc_var h; case: ifP. Qed.

(* ------------------------------------------------------------------------- *)
(* Alignment and bounds                                                       *)

Lemma sc_is_aligned_ifP s (i : sem_t cint) al aa sz e :
  sem_pexpr_wc true gd s e = ok (to_val i) ->
  sem_eassert_wc gd s (aands (sc_is_aligned_if al aa sz e)) = ok true ->
  is_aligned_if (Pointer := WArray.PointerZ) al (i * mk_scale aa sz) sz.
Proof.
  rewrite /sc_is_aligned_if /is_aligned_if => hi.
  case: al => //=.
  case: aa => /=; last by move=> _; apply WArray.is_align_scale.
  rewrite /eis_aligned /eeqi /emodi /ewsize /= hi /= /sem_sop2 /=.
  move=> [] /Z.eqb_eq h.
  rewrite is_alignE WArray.p_to_zE Z.mul_1_r; apply/eqP; exact h.
Qed.

Lemma eval_atype_carr ty n :
  eval_atype ty = carr n -> exists ws len, ty = aarr ws len /\ n = arr_size ws len.
Proof. by case: ty => // ws len [<-]; exists ws, len. Qed.

Lemma sc_in_boundP s ty n (i ilen : sem_t cint) aa sz (e elen : pexpr) :
  eval_atype ty = carr n ->
  sem_pexpr_wc true gd s e = ok (to_val i) ->
  sem_pexpr_wc true gd s elen = ok (to_val ilen) ->
  sem_eassert_wc gd s (aands (sc_in_bound ty aa sz e elen)) = ok true ->
  (0 <= i * mk_scale aa sz /\ i * mk_scale aa sz + ilen <= n)%Z.
Proof.
  rewrite /sc_in_bound /= /emk_scale /emuli.
  move=> /eval_atype_carr [ws [len [-> ?]]] he helen; subst n.
  case: aa; rewrite /= helen he /arr_size.
  all: by move=> /= -[] /andP [] /ZleP h1 /ZleP h2; Lia.lia.
Qed.

Lemma sc_in_boundP_all s ty n (t : sem_t (carr n)) (i : sem_t cint) aa sz e :
  eval_atype ty = carr n ->
  sem_pexpr_wc true gd s e = ok (to_val i) ->
  sem_eassert_wc gd s (aands (sc_in_bound ty aa sz e (Pconst (wsize_size sz)))) = ok true ->
  all (fun j => WArray.in_bound t (i * mk_scale aa sz + j)) (ziota 0 (wsize_size sz)).
Proof.
  move=> /[dup] hty /eval_atype_carr [ws [len [? ?]]] he hscs; subst ty n.
  have helen : sem_pexpr_wc true gd s (Pconst (wsize_size sz)) =
                 ok (to_val (t:=cint) (wsize_size sz)) by done.
  have [h1 h2] := sc_in_boundP hty he helen hscs.
  apply /allP => j; rewrite in_ziota !zify => hj.
  rewrite /WArray.in_bound; Lia.lia.
Qed.

Lemma sc_in_sub_boundP s ty n (t : sem_t (carr n)) a e1 e2 (ve1 ve2 : Z) :
  eval_atype ty = carr n ->
  sem_pexpr_wc true gd s e1 = ok (Vint ve1) ->
  sem_pexpr_wc true gd s e2 = ok (Vint ve2) ->
  0 <= a < ve2 ->
  sem_eassert_wc gd s (aands (sc_in_bound' ty e1 e2)) = ok true ->
  WArray.in_bound t (ve1 + a).
Proof.
  move=> /[dup] hty /eval_atype_carr [ws [len [? ?]]] he1 he2 hb; subst ty n.
  have {}hb : ve1 <= ve1 + a < ve1 + ve2 by Lia.lia.
  rewrite /= he1 he2 /=.
  move=> [] /andP [] /Z.leb_le hlo /Z.leb_le hhi.
  rewrite /WArray.in_bound /arr_size !zify.
  rewrite /arr_size in hhi; Lia.lia.
Qed.


(* ------------------------------------------------------------------------- *)
(* The catch is transparent on array variables: they are always defined       *)

Lemma arr_isdef s x len :
  eval_atype (vtype (gv x)) = carr len -> is_defined (evm s).[gv x].
Proof.
  move=> hty; have := Vm.getP (evm s) (gv x).
  by rewrite hty => /compat_valEl [? ->].
Qed.

Lemma arr_catch_get_gvar {n} s x (t : WArray.array n) :
  eval_atype (vtype (gv x)) = carr n ->
  get_gvar (wc:=withcatch) true gd (evm s) x = ok (Varr t) ->
  get_gvar (wc:=nocatch) true gd (evm s) x = ok (Varr t).
Proof. by rewrite /get_gvar /get_var => /(arr_isdef s) ->. Qed.

Lemma get_gvar_catch s x v :
  get_gvar (wc:=nocatch) true gd (evm s) x = ok v ->
  get_gvar (wc:=withcatch) true gd (evm s) x = ok v.
Proof. by rewrite /get_gvar /with_catch /nocatch /withcatch; case: ifP => // _ ->. Qed.

(* ------------------------------------------------------------------------- *)
(* Initialisation of the array cells that an access reads                     *)

Section GLOBALS.

(* Discharged by [sc_prog], which checks [check_glob] on every global. *)
Hypothesis get_global_arr_init :
  forall x len (t : WArray.array len),
  get_global gd x = ok (Varr t) -> all (WArray.is_init t) (ziota 0 len).

Opaque wsize_size.

Lemma sc_arr_initP s ty n (t : WArray.array n) (i : sem_t cint) x aa sz e :
  eval_atype ty = carr n ->
  sem_pexpr_wc true gd s e = ok (to_val i) ->
  get_gvar (wc:=nocatch) true gd (evm s) x = ok (Varr t) ->
  sem_eassert_wc gd s (aands (sc_arr_init ty x aa sz e)) = ok true ->
  all (fun j => WArray.in_bound t (i * mk_scale aa sz + j)) (ziota 0 (wsize_size sz)) ->
  all (fun j => WArray.is_init t (i * mk_scale aa sz + j)) (ziota 0 (wsize_size sz)).
Proof using get_global_arr_init.
  move=> /eval_atype_carr [ws [len [? ?]]]; subst ty n.
  rewrite /sc_arr_init /emk_scale /emuli /= => hi hget.
  move: (get_gvar_catch hget) => hgc.
  case: ifP => /= hloc; last first.
  + move: hget; rewrite /get_gvar hloc => /get_global_arr_init /allP hinit _ /allP hbound.
    apply/allP => j hj; apply/hinit; move: (hbound j hj).
    rewrite in_ziota /WArray.in_bound !zify => *; Lia.lia.
  rewrite hgc /=.
  case: aa; rewrite /= hi /= /sem_opN_safety /=.
  all: rewrite arr_sizeE wsize8 Z.mul_1_l WArray.castK /=.
  all: move=> [] /allP h _; apply/allP => j; rewrite in_ziota !zify => hj;
    apply/h; rewrite in_ziota !zify; Lia.nia.
Qed.


Lemma is_wi1P o :
  match is_wi1 o with
  | Some (s, oi) => o = Owi1 s oi
  | None =>
     let t := etype_of_op1 (len:=Z) o in
     sign_of_etype t.1 = None /\ sign_of_etype t.2 = None
  end.
Proof. by case: o => // -[]. Qed.

(* ------------------------------------------------------------------------- *)
(* Main lemma on expressions: if the generated conditions hold, the defensive
   semantics agrees with the standard one.                                    *)

Let Pe e :=
  forall s v,
  sem_eassert_wc gd s (aands (sc_pexpr e)) = ok true ->
  sem_pexpr_wc true gd s e = ok v ->
  sem_pexpr (wc:=nocatch) true gd s e = ok v.

Let Qe es :=
  forall s vs,
  sem_eassert_wc gd s (aands (List.flat_map sc_pexpr es)) = ok true ->
  sem_pexprs_wc true gd s es = ok vs ->
  sem_pexprs (wc:=nocatch) true gd s es = ok vs.

Lemma sc_pexprP_aux : (forall e, Pe e) /\ (forall es, Qe es).
Proof using Pe Qe asm_op ep get_global_arr_init p sip spp syscall_state.
apply: pexprs_ind_pair; subst Pe Qe; split => //=; t_xrbindP => //.
+ by move=> e he es hes s vs /aandsE_cat [/he{}he] /hes{}hes v {}/he -> vs2 /hes -> <- /=.
+ move=> x s v.
  rewrite /sc_gvar /get_gvar /=.
  case: (is_lvar x) => //.
  rewrite /sc_var /get_var /with_catch /nocatch /withcatch /=.
  case harr: is_aarr.
  + move: harr => /is_aarrP [ws [len htx]].
    have /(_ x (arr_size ws len)) -> // := arr_isdef s.
    by rewrite htx.
  by move=> /= [] hdef; rewrite hdef /=.
+ move=> al aa sz x e he s v /aandsE_cat [/he{}he].
  rewrite /sc_arr_get => /aandsE_cat [+ /aandsE_cat []].
  move=> hal hbound hinit; apply on_arr_gvarP => n r htx.
  have xdef := arr_isdef s htx.
  move=> /(arr_catch_get_gvar htx) hgvr /=.
  t_xrbindP => zi z hewc /to_intI ? w wcatch <-; subst z.
  have {}he := he _ hewc; rewrite he hgvr /=.
  move: wcatch; rewrite /WArray.get /read /=.
  have -> /= := sc_is_aligned_ifP hewc hal.
  move: hbound => /(sc_in_boundP_all r htx hewc) hbound.
  have {}hinit := sc_arr_initP htx hewc hgvr hinit hbound.
  have : exists l, mapM (fun k : Z => WArray.get8 r (add (zi * mk_scale aa sz) k)) (ziota 0 (wsize_size sz)) = ok l; last first.
  + by move=> [l -> /=] [->].
  elim: (ziota 0 (wsize_size sz)) hbound hinit => //=; eauto.
  move=> j js hrec /andP [h1 h2] /andP [h3 h4].
  rewrite {2}/WArray.get8 WArray.addE h1 /= h3 /=.
  by have [l -> /=] := hrec h2 h4; eauto.
+ move=> aa sz len x e he s v /aandsE_cat [/he {}he].
  move=> hbound; apply on_arr_gvarP => n r htx.
  have xdef := arr_isdef s htx.
  move=> /(arr_catch_get_gvar htx) hgvr /=.
  t_xrbindP => zi z hewc /to_intI ? w wcatch <-; subst z.
  have {}he := he _ hewc; rewrite he hgvr /=.
  move: wcatch.
  have helen : sem_pexpr (wc:=withcatch) true gd s (Pconst (arr_size sz len)) =
                 ok (to_val (t:=cint) (arr_size sz len)) by done.
  move: hbound => /(sc_in_boundP htx hewc helen) [] /ZleP h1 /ZleP h2.
  by rewrite /WArray.get_sub h1 h2 /= => [] [->].
+ move=> al sz e he s v /aandsE_cat [/he{}he].
  move=> /aandsE_cat [hal hmem] w wv hewc.
  have {}he := he _ hewc; rewrite /read he => /= topow w2.
  move: hmem => /=; rewrite hewc /=; rewrite topow /=.
  move=> [] /allP hread.
  have hali : is_aligned_if al w sz.
  + move: hal; rewrite /sc_is_aligned_if_m; case: al => //=.
    rewrite /eis_aligned /eeqi /emodi /ewsize /eint_of_word /= hewc /= /sem_sop1 /= topow /= /sem_sop2 /=.
    by move=> [] /Z.eqb_eq h; rewrite is_alignE p_to_zE; apply/eqP.
  rewrite hali /=.
  have : exists l, mapM (fun k : Z => get (emem s) (add w k)) (ziota 0 (wsize_size sz)) = ok l; last first.
  + by move=> [l -> /=] [->] <-.
  move: hread; elim: (ziota 0 (wsize_size sz)) => [|k ks hrec] hread /=; first by eauto.
  have hk : is_ok (read (emem s) Unaligned (w + wrepr Uptr k)%w U8).
  + by apply: hread; rewrite in_cons eqxx.
  case/is_okP: hk => w8 hw8.
  rewrite (get_read8 _ Unaligned) addE hw8 /=.
  have [l ->] : exists l, mapM (fun k0 : Z => get (emem s) (add w k0)) ks = ok l.
  + by apply: hrec => x hx; apply: hread; rewrite in_cons hx orbT.
  by exists (w8 :: l).
+ move=> op e he s v /aandsE_cat [/he{}he].
  move=> /aands_map_PexprE hop v1 hewc; have {}he := he _ hewc.
  rewrite he /= /sem_sop1.
  have {}hdef := sem_pexpr_defined hewc.
  case hval: of_val => [a|e0] /=; last first.
  + by have -> := isdef_errtype hdef hval.
  move: hop; rewrite /sc_op1 /sc_wiop1.
  case: is_wi1 (is_wi1P op); last first.
  + case: op a hval => //=; first by case.
    by move=> sg +++ []; case.
  case => sg wop ?; subst op.
  case: wop a hval => //=.
  + move=> ws z /to_intI ?; subst v1.
    by move=> /(sc_wi_range_of_int hewc) ->.
  move=> ws w /to_wordI [ws2 [w2] [? htr]]; subst v1 => /=.
  rewrite /signed /safety_common.sc_op1 /=.
  case: sg; rewrite /sem_cond /=.
  1-2: rewrite hewc /= /sem_sop1 /= htr /= /sem_sop2 /=.
  + move=> [] /negbTE /Z.eqb_neq hne.
    rewrite /wint_of_int /in_wint_range /in_sint_range /= (wsigned_opp hne) /=.
    by have [/ZleP -> /ZleP ->] := wsigned_range (-w).
  by move=> [] /Z.eqb_eq ->.
+ move=> op e1 he1 e2 he2 s v /aandsE_cat [/he1{}he1].
  move=> /aandsE_cat [/he2{}he2] /aands_map_PexprE hop v2 he1wc v3 he2wc.
  have {}he1 := he1 _ he1wc.
  have {}he2 := he2 _ he2wc.
  rewrite he1 he2 /sem_sop2 /=.
  have {}hdef1 := sem_pexpr_defined he1wc.
  have {}hdef2 := sem_pexpr_defined he2wc.
  case hval2: of_val => [a2|er2];
  case hval1: of_val => [a1|er1] //=; last first.
  1,3: by have -> := isdef_errtype hdef1 hval1.
  + by have -> := isdef_errtype hdef2 hval2.
  move: hop; case: op a1 hval1 a2 hval2 => //=; try by case.
  1-2: move=> sg; case => // ws w1p /to_wordI [ws1 [w1 [? tr1]]] w2p /to_wordI [ws2 [w2 [? tr2]]] hsc; subst v2 v3.
  1-2: have hd1 : sem_pexpr (wc:=withcatch) true gd s (eint_of_word sg ws e1) = ok (Vint (int_of_word sg w1p)).
  1: by rewrite /eint_of_word /= he1wc /= /sem_sop1 /= tr1.
  2: by rewrite /eint_of_word /= he1wc /= /sem_sop1 /= tr1.
  1-2: have hd2 : sem_pexpr (wc:=withcatch) true gd s (eint_of_word sg ws e2) = ok (Vint (int_of_word sg w2p)).
  1: by rewrite /eint_of_word /= he2wc /= /sem_sop1 /= tr2.
  2: by rewrite /eint_of_word /= he2wc /= /sem_sop1 /= tr2.
  1-2: by rewrite /mk_sem_divmod (sem_sc_divmod hd1 hd2 hsc) /=.
  move=> sg ws; case => //= w1p /to_wordI [ws1 [w1 [? tr1]]] w2p /to_wordI [ws2 [w2 [? tr2]]] hsc; subst v2 v3.
  1-3: move: hsc; rewrite /mk_sem_wiop2 /sc_op2 /= /sc_wiop2 /sc_wi_range_op2 => hsc.
  1-3: rewrite (sc_wi_range_of_int _ hsc) //=.
  1-3: by rewrite he1wc he2wc /= /sem_sop1 /= tr1 /= tr2 /= /sem_sop2 /=.
  1-2: have hw1 : sem_pexpr (wc:=withcatch) true gd s (toint sg ws e1) = ok (Vint (int_of_word sg w1p)).
  1: by rewrite /toint /= he1wc /= /sem_sop1 /= tr1.
  2: by rewrite /toint /= he1wc /= /sem_sop1 /= tr1.
  1-2: have hw2 : sem_pexpr (wc:=withcatch) true gd s (toint sg ws e2) = ok (Vint (int_of_word sg w2p)).
  1: by rewrite /toint /= he2wc /= /sem_sop1 /= tr2.
  2: by rewrite /toint /= he2wc /= /sem_sop1 /= tr2.
  1-2: by rewrite /mk_sem_divmod (sem_sc_divmod hw1 hw2 hsc) /=.
  2: by rewrite /mk_sem_wishift /wint_of_int in_wint_range_zasr.
  have hr : in_wint_range sg ws (zlsl (int_of_word sg w1p) (int_of_word Unsigned w2p)) = ok tt.
  + apply: (sc_wi_rangeP (wc:=withcatch) (gd:=gd) (s:=s)
             (e := elsli (toint sg ws e1) (toint Unsigned U8 e2))); last exact hsc.
    by rewrite /elsli /toint /= he1wc he2wc /= /sem_sop1 /= tr1 /= tr2 /= /sem_sop2 /=.
  by rewrite /mk_sem_wishift /wint_of_int hr /=.
+ move=> op es he s v.
  move=> /he{}he v2 {}/he.
  rewrite /sem_pexprs /sem_opN => he; rewrite he /=.
  have := [elaborate sem_opN_typed_ok op].
  move: (type_of_opN op) (sem_opN_typed op) => [tin tout] /=.
  elim: tin v2 es he => [| tin tins hrec] [|vp vsp] es he semop //=.
  + by case/is_okP => semtout ->.
  move: es he => [| e es] //= + hok.
  t_xrbindP => z /sem_pexpr_defined vpdef zs hes ? ?; subst z zs.
  case hval: (of_val _ vp) => [semtin|] //=;
    last by rewrite (isdef_errtype vpdef hval).
  exact: hrec _ _ hes _ (hok semtin).
move=> ty e he e1 he1 e2 he2 s v /aandsE_cat [/he{}he].
move=> /aandsE_cat [/he1{}he1] /he2{}he2.
by move=> v2 v3 {}/he -> /= -> v5 v6 {}/he1 -> /= -> v7 v8 {}/he2 -> /= -> <-.
Qed.

Lemma sc_pexprP : forall e, Pe e.
Proof using Pe Qe asm_op ep get_global_arr_init p sip spp syscall_state.
  by have [] := sc_pexprP_aux.
Qed.

Lemma sc_pexprsP : forall es, Qe es.
Proof using Pe Qe asm_op ep get_global_arr_init p sip spp syscall_state.
  by have [] := sc_pexprP_aux.
Qed.


(* ------------------------------------------------------------------------- *)
(* Main lemma on left values                                                  *)

Lemma DB_to_val ty (vv : sem_t ty) wdb : DB wdb (to_val vv).
Proof. by case: ty vv; rewrite /DB /= orbT. Qed.

Lemma compat_val_to_val ty (vv : sem_t ty) : compat_val ty (to_val vv).
Proof. by case: ty vv => *; rewrite /compat_val /= eq_refl. Qed.

Lemma all_get_read8 mem al wlo sz :
  all (fun i : Z => is_ok (read mem al (wlo + wrepr Uptr i)%R U8)) (ziota 0 sz)
  = all (fun i : Z => is_ok (get mem (wlo + wrepr Uptr i)%R)) (ziota 0 sz).
Proof. by elim: ziota => [| k ks hrec] //=; rewrite -get_read8 hrec. Qed.

Lemma set_allgetok ks mem mem2 q w wlo :
  all (fun i => is_ok (get mem (wlo + wrepr Uptr i)%R)) ks ->
  set mem q w = ok mem2 ->
  all (fun i => is_ok (get mem2 (wlo + wrepr Uptr i)%R)) ks.
Proof.
  move=> + hset; elim: ks => [// | k ks hind].
  move=> /andP [h1 h2] /=.
  rewrite hind //= (setP _ hset).
  by case: eqP => //; rewrite h1.
Qed.

(* [memory_model] exposes [get_valid8] and [valid8P] but not their composition. *)
Lemma getok_setok (m : mem) r q w :
  get m q = ok r -> exists m2, set m q w = ok m2.
Proof. move=> hg; apply/valid8P; exact: get_valid8 hg. Qed.

Lemma sc_lvalP l v s s2 :
  sem_eassert_wc gd s (aands (sc_lval l)) = ok true ->
  write_lval (wc:=withcatch) true gd l v s = ok s2 ->
  write_lval (wc:=nocatch) true gd l v s = ok s2.
Proof using Pe Qe asm_op ep get_global_arr_init p sip spp syscall_state.
  case: l => [vi tynone | x | al sz x e | al aa sz x e | aa sz pos x e ] //=.
  + t_xrbindP => /aandsE_cat [] /sc_pexprP he /aandsE_cat [hal hmem] wpt vpt hewc.
    have {}he := he _ hewc.
    rewrite he => /to_wordI [sz2 [w2 [? htr2]]]; subst vpt.
    move=> w /to_wordI [sz3 [w3 [? htr3]]] me + ?; subst v s2.
    rewrite /= htr2 htr3 /= /write.
    have hali : is_aligned_if al wpt sz.
    + move: hal; rewrite /sc_is_aligned_if_m; case: al => //=.
      rewrite /eis_aligned /eeqi /emodi /ewsize /eint_of_word /= hewc /= /sem_sop1 /=
              htr2 /= /sem_sop2 /=.
      by move=> [] /Z.eqb_eq h; rewrite is_alignE p_to_zE; apply/eqP.
    rewrite hali /=.
    suff : [elaborate exists l,
      foldM (fun (k : Z) (m : mem) => set m (add wpt k) (LE.wread8 w k))
            (emem s) (ziota 0 (wsize_size sz)) = ok l].
    + by move=> [l -> /=] [->].
    move: hmem => /=; rewrite hewc /= htr2 /= => -[].
    rewrite all_get_read8.
    elim: ziota (emem s) => [| k ks hrec m2] /=; first by eauto.
    move=> /andP [] /is_okP [gv okg] okgs.
    have [fmem hset] := getok_setok (LE.wread8 w k) okg.
    have {}okgs := set_allgetok okgs hset.
    have {}hrec := hrec fmem okgs.
    by rewrite hset /=.
  + rewrite /sc_arr_set => /aandsE_cat [] /sc_pexprP he /aandsE_cat [hal hbound].
    rewrite /on_arr_var; t_xrbindP => v1 getx; rewrite getx /=.
    case: v1 getx => //= len r; t_xrbindP => /get_varI htx z v2 hewc.
    have {}he := he _ hewc.
    rewrite he => /= /to_intI ?; subst v2 => w -> r2 + <- /=.
    rewrite /WArray.set /write /=.
    have -> /= := sc_is_aligned_ifP hewc hal.
    move: hbound => /(sc_in_boundP_all r htx hewc) hbound.
    have : exists l, foldM (fun (k : Z) (m : WArray.array len) =>
             WArray.set8 m (add (z * mk_scale aa sz) k) (LE.wread8 w k))
             r (ziota 0 (wsize_size sz)) = ok l; last first.
    + by move=> [rf ->] /= [->].
    elim: (ziota 0 (wsize_size sz)) r hbound => //=; eauto.
    move=> j js hrec r /andP [h1 h2].
    rewrite {2}/WArray.set8 WArray.addE h1 /=.
    have [l -> /=] := hrec {| WArray.arr_data :=
      Mz.set (WArray.arr_data r) (z * mk_scale aa sz + j) (LE.wread8 w j) |} h2.
    by eauto.
  move=> /aandsE_cat [] /sc_pexprP he hbound.
  rewrite /on_arr_var; t_xrbindP => v1 getx; rewrite getx /=.
  case: v1 getx => //= len r; t_xrbindP => /get_varI htx z v2 hewc.
  have {}he := he _ hewc.
  rewrite he => /= /to_intI ?; subst v2 => w -> r2 + <- /=.
  rewrite /WArray.set_sub /=.
  have [//|] := sc_in_boundP htx hewc _ hbound (aa:=aa) (ilen:=arr_size sz pos).
  move=> /ZleP -> /ZleP -> /=.
  rewrite /write_var /set_var /= htx eq_refl => -[<-] /=.
  by eauto.
Qed.


Lemma sc_lvalsP ls vs s0 s s2 okmem :
  sem_eassert_wc gd s0 (aands (sc_lvals ls okmem)) = ok true ->
  evm s0 = evm s ->
  (okmem -> emem s0 = emem s) ->
  write_lvals (wc:=withcatch) true gd s ls vs = ok s2 ->
  write_lvals (wc:=nocatch) true gd s ls vs = ok s2.
Proof using E E0 Pe Qe asm_op ep get_global_arr_init p rE sip spp syscall_state wE.
  move=> hscs hvm.
  have {}hvm : evm s0 =[\Sv.empty] evm s by rewrite hvm.
  move: hscs hvm; rewrite /sc_lvals => /aandsE_cons [].
  rewrite /= => -[].
  elim: ls vs s Sv.empty okmem => [|l ls hrec] [|v vs] s W okmem //=.
  rewrite Bool.andb_assoc => /= /andP [] /andP [] hmemok hdisj hcheck.
  t_xrbindP => /aandsE_cat [] hsc hscs hvm hokm sf hw hws.
  rewrite (check_scaP _ hmemok hdisj hvm hokm) in hsc.
  have -> /= := sc_lvalP hsc hw.
  apply: (hrec _ _ _ _ hcheck) hws => //.
  + rewrite vrv_recE.
    apply (eq_exT (vm2 := evm s)).
    + by apply: eq_exI hvm; SvD.fsetdec.
    by apply: eq_exI (vrvP hw); SvD.fsetdec.
  by move=> /andP [/hokm -> hlv]; exact: lv_write_memP hlv (sc_lvalP hsc hw).
Qed.


(* [eassert] counterpart of [sc_pexprP]: needed because in [main] the assertion
   language is a separate type, so [sc_pexprP] alone does not cover [Cassert]
   nor the contracts. *)
Lemma sc_eassertP a s b :
  sem_eassert_wc gd s (aands (sc_eassert a)) = ok true ->
  sem_eassert (wc:=withcatch) gd s a = ok b ->
  sem_eassert (wc:=nocatch) gd s a = ok b.
Proof using Pe Qe asm_op ep get_global_arr_init p sip spp syscall_state.
  elim: a b => /=.
  + by move=> e b /sc_pexprP he; t_xrbindP => vv /he -> /=.
  + move=> o es b hsc; have hes := sc_pexprsP (es:=es) (s:=s).
    case heq: (mapM (sem_pexpr (wc:=withcatch) true gd s) es) => [vs|er] //=.
    have hn := hes vs hsc heq.
    by move: hn; rewrite /sem_pexprs => ->.
  + by [].
  + move=> e1 e2 b /aandsE_cat [] /sc_pexprP h1 /sc_pexprP h2.
    t_xrbindP => lo v1 hv1 hlo szz v2 hv2 hsz.
    by move=> <-; rewrite (h1 _ hv1) /= hlo /= (h2 _ hv2) /= hsz /=.
  move=> a1 h1 a2 h2 b /aandsE_cat [] hs1 hs2.
  by t_xrbindP => b1 hb1 b2 hb2 <-; rewrite (h1 _ hs1 hb1) (h2 _ hs2 hb2).
Qed.


(* ------------------------------------------------------------------------- *)
(* Contracts                                                                  *)

Let psc := map_prog sc_fun p.

Lemma sem_pre_sc fn fs :
  sem_pre (wc:=withcatch) psc fn fs = ok tt ->
  sem_pre (wc:=nocatch) p fn fs = ok tt.
Proof using Pe Qe asm_op ep get_global_arr_init p psc sip spp syscall_state.
  rewrite /sem_pre /psc get_map_prog /=.
  case: get_fundef => [fd | //] /=.
  case: fd => /= fi [] // ci ftin fp fb ftout fr fe /=.
  t_xrbindP => vst -> /= s2 -> /= us + _.
  elim: (f_pre ci) us => [|a l] //=.
  t_xrbindP => hrec us hsca us2 /hrec{}hrec ?; subst us.
  move: hsca; rewrite /sc_a_and /sem_assert /= -cats1.
  t_xrbindP; case => // /aandsE_cat [] hsce /=.
  move=> hewc _ _.
  rewrite (sc_eassertP hsce hewc) /=.
  by move: hrec; case: (mapM _ l) => //= ys _.
Qed.

Lemma sem_post_sc fn vs fs :
  sem_post (wc:=withcatch) psc fn vs fs = ok tt ->
  sem_post (wc:=nocatch) p fn vs fs = ok tt.
Proof using Pe Qe asm_op ep get_global_arr_init p psc sip spp syscall_state.
  rewrite /sem_post /psc get_map_prog /=.
  case: get_fundef => [fd | //] /=.
  case: fd => /= fi [] // ci ftin fp fb ftout fr fe /=.
  t_xrbindP => vst -> /= s1 -> /= s2 -> /= s3 + _.
  elim: (f_post ci) s3 => [|a l] //=.
  t_xrbindP => hrec us hsca us2 /hrec{}hrec ?; subst us.
  move: hsca; rewrite /sc_a_and /sem_assert /= -cats1.
  t_xrbindP; case => // /aandsE_cat [] hsce /=.
  move=> hewc _ _.
  rewrite (sc_eassertP hsce hewc) /=.
  by move: hrec; case: (mapM _ l) => //= ys _.
Qed.


(* ------------------------------------------------------------------------- *)
(* The [i_safe] conditions of the instruction operators                       *)

Lemma nth_sem_pexprs gd0 s es pos e vs :
  List.nth_error es pos = Some e ->
  sem_pexprs (wc:=withcatch) true gd0 s es = ok vs ->
  sem_pexpr (wc:=withcatch) true gd0 s e = ok (nth undef_b vs pos).
Proof.
  elim: pos es vs => [ | n hrec] [ | e0 es] //=; t_xrbindP.
  + by move=> ? [->] ve -> ? _ <-.
  by move=> ? hnth v0 he0 vs hes <- /=; apply: hrec hes.
Qed.

Lemma nth_sem_pexprs_nth gd0 s es pos vs :
  ssrnat.leq (S pos) (size es) ->
  sem_pexprs (wc:=withcatch) true gd0 s es = ok vs ->
  sem_pexpr (wc:=withcatch) true gd0 s (nth (Pbool false) es pos) = ok (nth undef_b vs pos).
Proof.
  elim: pos es vs => [ | n hrec] [ | e0 es] vs //=.
  + by t_xrbindP => _ ve -> l hl <-.
  by t_xrbindP => hn v0 he0 l hl <- /=; apply: (hrec _ _ hn hl).
Qed.

(* On the source language the coercion of [sc_to_e] is exactly [Papp1], so the
   special case for [Oint_of_word] is transparent. *)
Lemma sc_to_e_op1 o c e :
  sc_op1_to_e eint_of_word o c e = Papp1 o e.
Proof. by case: o => //= sg ws; case: c. Qed.

(* [sc_to_e] computes, under the defensive semantics, the interpretation of the
   condition on the values of the arguments: the operators of the white list
   [sc_expr] only fail for a typing reason, which is not caught. *)
Lemma sem_pexpr_sc_to_e gd0 s es vs c v :
  sem_pexprs (wc:=withcatch) true gd0 s es = ok vs ->
  sc_expr c -> ssrnat.leq (sc_max_var c) (size es) ->
  sem_pexpr (wc:=withcatch) true gd0 s (sc_to_e eint_of_word es c) = ok v ->
  interp_safe_cond vs c = ok v /\ is_defined v.
Proof.
  move=> hes; elim/safe_cond_ind_s: c v => //=.
  + by move=> b v _ _ [<-].
  + by move=> z v _ _ [<-].
  + move=> k v _ hk.
    have hsem := nth_sem_pexprs_nth hk hes.
    rewrite hsem => -[<-].
    by split => //; apply: sem_pexpr_defined hsem.
  + move=> o c ih v /andP [hto htot] hk.
    rewrite sc_to_e_op1 /=.
    t_xrbindP => v1 /(ih _ htot hk) [hv1 hd1].
    rewrite /sem_sop1 /=.
    case hof: (of_val (eval_atype (type_of_op1 o).1) v1) => [x | er] /=; last first.
    + by rewrite (isdef_errtype hd1 hof) /=.
    rewrite (sem_sop1_typed_totalE hto) /= => -[<-].
    rewrite hv1 /= hof /=.
    by split => //; apply: (to_val_defined (erefl _)).
  move=> o c1 ih1 c2 ih2 v /and3P [hto ht1 ht2].
  rewrite ssrnat.geq_max => /andP [hk1 hk2].
  t_xrbindP => v1 /(ih1 _ ht1 hk1) [hv1 hd1] v2 /(ih2 _ ht2 hk2) [hv2 hd2].
  rewrite /sem_sop2 /=.
  case hof1: (of_val (eval_atype (type_of_op2 o).1.1) v1) => [x1 | er] /=; last first.
  + by rewrite (isdef_errtype hd1 hof1) /=.
  case hof2: (of_val (eval_atype (type_of_op2 o).1.2) v2) => [x2 | er] /=; last first.
  + by rewrite (isdef_errtype hd2 hof2) /=.
  rewrite (sem_sop2_typed_totalE hto) /= => -[<-].
  rewrite hv1 /= hv2 /= hof1 /= hof2 /=.
  by split => //; apply: (to_val_defined (erefl _)).
Qed.

Lemma sem_pexprs_sc_to_e gd0 s es vs cs l :
  sem_pexprs (wc:=withcatch) true gd0 s es = ok vs ->
  all sc_expr cs -> all (fun c => ssrnat.leq (sc_max_var c) (size es)) cs ->
  mapM (sem_pexpr (wc:=withcatch) true gd0 s) (map (sc_to_e eint_of_word es) cs) = ok l ->
  mapM (interp_safe_cond vs) cs = ok l.
Proof.
  move=> hes; elim: cs l => [ | c cs ih] l /=; first by move=> _ _ [<-].
  move=> /andP [h1 h2] /andP [k1 k2].
  t_xrbindP => v /(sem_pexpr_sc_to_e hes h1 k1) [hv _] l' /(ih _ h2 k2) hl' <-.
  by rewrite hv /= hl'.
Qed.

(* The assertion generated for a safety condition implies the condition. *)
Lemma sem_cond_interp_safe gd0 s es vs sc :
  sem_pexprs (wc:=withcatch) true gd0 s es = ok vs ->
  sem_eassert (wc:=withcatch) gd0 s (safe_cond_to_e es sc) = ok true ->
  safe_cond_b vs sc.
Proof.
  move=> hes; rewrite /safe_cond_to_e /sc_to_eassert.
  have hPexpr : forall c,
      sem_eassert (wc:=withcatch) gd0 s
        (Pexpr (if sc_expr c && ssrnat.leq (sc_max_var c) (size es)
                then sc_to_e eint_of_word es c else Pbool false)) = ok true ->
      safe_cond_b vs c.
  + move=> c; case: ifP => [/andP [hexp hk] | _]; last by move=> [].
    rewrite /=; t_xrbindP => v hv /to_boolI ?; subst v.
    by have [hi _] := sem_pexpr_sc_to_e hes hexp hk hv; rewrite /safe_cond_b hi.
  case: sc => [b | z | k | o c | o c1 c2 | o cs];
    [ exact: (hPexpr (IBool b)) | exact: (hPexpr (IConst z))
    | exact: (hPexpr (IVar k)) | exact: (hPexpr (IOp1 o c))
    | exact: (hPexpr (IOp2 o c1 c2)) | ].
  case: ifP => [/andP [hexp hk] | _]; last by move=> [].
  have hall : all (fun c => ssrnat.leq (sc_max_var c) (size es)) cs
    by rewrite -(sc_max_var_appN_le o).
  rewrite /=; t_xrbindP => l hl hop.
  move: hop; rewrite /sem_opN_safety => hop.
  by rewrite /safe_cond_b /= (sem_pexprs_sc_to_e hes hexp hall hl) /= hop.
Qed.

Lemma sem_cond_interp_safes gd0 s es vs sc :
  sem_pexprs (wc:=withcatch) true gd0 s es = ok vs ->
  sem_eassert (wc:=withcatch) gd0 s (aands [seq safe_cond_to_e es i | i <- sc]) = ok true ->
  all (safe_cond_b vs) sc.
Proof.
  move=> hes; elim: sc => [ | sc scs hrec] //=.
  move=> /aandsE_cons [hsc hscs]; rewrite (hrec hscs) andbT.
  by apply: sem_cond_interp_safe hsc.
Qed.

Lemma type_of_val_to_val v ty v2 :
  type_of_val v = ty ->
  is_defined v ->
  of_val ty v = ok v2 ->
  to_val v2 = v.
Proof.
  move=> hty; case: (ty) v2 (type_of_valI hty) => /=.
  1,2: by move=> ? [|[?]] -> // _ [->].
  + by move=> ?? [t ->] _ /to_arrI [->].
  by move=> ?? [|[?]] -> // _ /=; rewrite truncate_word_u => -[->].
Qed.

Lemma sem_pexpr_type_of gd0 s e v :
  sem_pexpr (wc:=nocatch) true gd0 s e = ok v ->
  type_of_val v = eval_atype (type_of_expr e).
Proof.
  case: e => /=.
  1-3: by move=> > [<-].
  + by move=> x /type_of_get_gvar /eqP.
  1-2: by move=> >; apply on_arr_gvarP; t_xrbindP => > _ _ > _ _ > _ <-.
  + by move=> >; t_xrbindP => > _ _ > _ <-.
  + by move=> >; t_xrbindP => > _ /sem_sop1I [?] [?] [_ _ ->]; apply type_of_to_val.
  + by move=> >; t_xrbindP => > _ > _ /sem_sop2I [?] [?] [?] [_ _ _ ->]; apply type_of_to_val.
  + by rewrite /sem_opN => >; t_xrbindP => > _ > _ <-; apply type_of_to_val.
  t_xrbindP => > _ _ > _ ht1 > _ ht2 <-; case: ifP => ?.
  + by apply: truncate_val_has_type ht1.
  by apply: truncate_val_has_type ht2.
Qed.

(* ------------------------------------------------------------------------- *)
(* Correctness of the pass                                                    *)

Lemma estate_eq s1 s2 : st_rel (fun _ : unit => eq) tt s1 s2 -> s1 = s2.
Proof. by case: s1 s2 => ??? [] ??? [] /= <- <- <-. Qed.

Lemma safety_callP_aux fn :
  wiequiv_f (wc1:=withcatch) (wc2:=nocatch) psc p ev ev
    (rpreF (eS:=eq_spec)) fn fn (rpostF (eS:=eq_spec)).
Proof using E E0 Pe Qe asm_op ep ev get_global_arr_init p psc rE sip spp
  syscall_state wE.
  apply wequiv_fun_ind_wa => {}fn _ fs _ [<- <-] fd hgetsc.
  have : exists fd2, get_fundef (p_funcs p) fn = Some fd2 /\ fd = sc_fun fd2.
  + move: hgetsc; rewrite /psc get_map_prog /=.
    by case heq: get_fundef => [fd2|] //= [?]; subst fd; eauto.
  move=> [fd2] [hget ?]; rewrite hget; subst fd; exists fd2 => // hpre; split.
  + by apply sem_pre_sc.
  move=> s1 hinit; exists s1 => //.
  + move: hinit hpre; rewrite /initialize_funcall /sem_pre /sc_fun /= hgetsc /=.
    by clear hget hgetsc; case: fd2 => //=.
  exists (st_rel (fun _ : unit => eq) tt), (st_rel (fun _ : unit => eq) tt); split => //.
  + rewrite /sc_fun /=; clear hget hinit hgetsc.
    case: fd2 => //= finf fcont ftin ftparam fbody ftout fres _.

    set Pi := (fun i =>
                 wequiv_rec (wc1 := withcatch) (wc2 := nocatch)
                   psc p ev ev eq_spec (st_rel (fun _ : unit => eq) tt)
                   (sc_instr i) [::i] (st_rel (fun _ : unit => eq) tt)).

    set Pc := (fun c =>
                 wequiv_rec (wc1 := withcatch) (wc2 := nocatch)
                   psc p ev ev eq_spec (st_rel (fun _ : unit => eq) tt)
                   (List.flat_map sc_instr c) c (st_rel (fun _ : unit => eq) tt)).

    set Pi_r := (fun ir => forall ii,
                 wequiv_rec (wc1 := withcatch) (wc2 := nocatch)
                   psc p ev ev eq_spec
                   (fun si s => st_rel (fun _ : unit => eq) tt si s /\
                      sem_eassert_wc gd si (aands (sc_instr_ir ii ir).1) = ok true)
                   ([:: MkI ii (sc_instr_ir ii ir).2]) ([:: MkI ii ir])
                   (st_rel (fun _ : unit => eq) tt)).

    rewrite -{2}(cats0 fbody).
    apply wequiv_cat with (st_rel (fun _ : unit => eq) tt); last first.
    + rewrite /safe_assert.
      have -> :
        [seq MkI dummy_instr_info (Cassert (safety_lbl, e)) | e <- List.flat_map sc_var fres] =
        [seq MkI dummy_instr_info (Cassert a)
           | a <- [seq (safety_lbl, e) | e <- List.flat_map sc_var fres]].
      + by rewrite -map_comp.
      by apply wequiv_asserts_left.
    apply (cmd_rect (Pr := Pi_r) (Pi:=Pi) (Pc:=Pc)) => //;
      subst Pi_r Pi Pc => {fn fs hpre s1 finf fcont ftin ftparam fbody ftout}.

    + move=> ir ii hi /=; rewrite -(cat0s [:: MkI _ _]) -cats1.
      apply wequiv_cat with (fun si s => st_rel (fun _ : unit => eq) tt si s /\
        sem_eassert_wc (p_globs psc) si (aands (sc_instr_ir ii ir).1) = ok true).
      + by apply safe_assertP.
      by apply hi.

    + by apply wequiv_nil.

    + move=> i c hi hc; rewrite /= -cat1s.
      by apply wequiv_cat with (st_rel (fun _ : unit => eq) tt).

    + move=> x tg ty e ii; apply wequiv_assgn_core.
      move=> si s si0 [/estate_eq ->] /aandsE_cat [hscx1 hsce1].
      rewrite /sem_assgn; t_xrbindP=> vei hvei vei2 htri hwi.
      have {}hvei := sc_pexprP hsce1 hvei.
      have {}hwi := sc_lvalP hscx1 hwi.
      by rewrite hvei /= htri /= hwi; eexists.

    + move=> xs tg o es ii; apply wkequiv_eq_pred; move=> s t [/estate_eq <-].
      move=> /aandsE_cons[] hwt /aandsE_cat[] hscx /aandsE_cat[] hsco hsce.
      apply wequiv_opn with (fun vs1 vs2 => [/\ vs1 = vs2,
                                  sem_pexprs_wc true gd s es = ok vs1 &
                                  sem_pexprs (wc:=nocatch) true gd s es = ok vs2]) eq.
      + by move=> s1 s2 sf [] ??; subst s1 s2 => he; have -> := sc_pexprsP hsce he; exists sf.
      + move=> s1 s2 [] ??; subst s1 s2 => vs _ vf [] <- hewc he.
        rewrite /exec_sopn /sopn_sem /=; case h: i_valid => //=.
        have := i_semi_safe h.
        have := sem_cond_interp_safes hewc hsco.
        have := sem_pexprs_defined he.
        have : List.Forall2 (fun ty vv => type_of_val vv = eval_atype ty)
                            (tin (get_instr_desc o)) vs.
        + move: hwt he => [] {hewc hsco hsce}.
          elim: (tin _) es vs => [ | ty tys ih] [ | e es] //=.
          + by move=> vs2 _ [<-]; constructor.
          move=> vs2 /andP [hty htys].
          t_xrbindP => v hv vs3 hes <-; constructor.
          + rewrite -(convertible_eval_atype hty).
            by apply: sem_pexpr_type_of hv.
          by apply: ih htys hes.
        rewrite -{3}(cat0s vs) /sopn_sem_ /safe_cond_ty.
        move=> {hewc he}.
        elim: (tin (get_instr_desc o)) (semi (get_instr_desc o)) {1 2}[::] vs.
        + move=> semi vs1 [] //=; rewrite cats0 => _ _ hall /(_ hall) [vr] -> /= [<-].
          by exists (list_ltuple vr).
        move=> ty tys ih semi vs1 [] //= v vs /List.Forall2_cons_iff [hty htys] /andP [hv hvs].
        rewrite -cat_rcons => hall_safe hinterp.
        case hof: of_val => [v2 /= | er]; last by rewrite (isdef_errtype hv hof).
        apply: ih => //.
        by rewrite (type_of_val_to_val hty hv hof).
      move=> vs _ <- s1 s2 sf [] ??; subst s1 s2 => hws.
      by rewrite (sc_lvalsP hscx erefl (fun _ => erefl) hws); exists sf.

    + move => xs o es ii; apply wkequivP' => si0 s0.
      apply wequiv_syscall with
        eq (fun fs1 fs2 => [/\ fs1 = fs2, emem si0 = fmem fs1
                            & map type_of_val fs1.(fvals) =
                              map eval_atype (scs_tout (syscall_sig_u o))]).
      + apply wrequiv_weaken with
          (fun t s => t = s /\
             sem_eassert_wc gd t (aands (List.flat_map sc_pexpr es)) = ok true) eq => //.
        + by move=> ??[ [-> ->] []] /estate_eq -> /aandsE_cat [_].
        move=> s1 s2 vs [? hwc] h; subst s2.
        by rewrite (sc_pexprsP hwc h); exists vs.
      + move=> s1 s2 [][] ?? [] /estate_eq ?; subst si0 s0 s2.
        move=> hcond vs vs2 fs2 ?; subst vs2 => hex.
        by have /= [-> <-] := syscall_u_toutP hex; exists fs2.
      move=> fs1 _ [] <- efmem htyof si s sf [][] ?? [] /estate_eq ?.
      rewrite /upd_estate; subst si0 s0 si => + hws.
      move=> /aandsE_cat[] hscx hsce.
      by rewrite (sc_lvalsP (s := with_scs (with_mem s (fmem fs1)) (fscs fs1))
                    hscx erefl (fun _ => efmem) hws); exists sf.

    + move=> a ii; apply wequiv_assert => /= _; split => //.
      move=> si s [hst hsce]; have ? := estate_eq hst; subst si.
      by move=> hewc; rewrite (sc_eassertP hsce hewc).

    + move=> e c1 c2 hc1 hc2 ii; apply wequiv_if.
      + move=> si s b [hst hsce]; have ? := estate_eq hst; subst si.
        rewrite /sem_cond; t_xrbindP => v he /to_boolI ?; subst v.
        by have -> := sc_pexprP hsce he; eexists.
      move=> b; apply wequiv_weaken with (st_rel (fun _ : unit => eq) tt)
        (st_rel (fun _ : unit => eq) tt) => //; first by move=> ??[].
      by case: b.

    + move=> x dir lo hi c hc ii.
      apply wequiv_for_eq with (st_rel (fun _ : unit => eq) tt) => //.
      + by move=> > [].
      + move=> s1 s2 vs [hst] /aandsE_cat[hsclo hschi].
        have ? := estate_eq hst; subst s2.
        move=> /=; t_xrbindP => vlo hlo z0 vhi hhi ? ?; subst z0 vs.
        have -> := sc_pexprP hsclo hlo.
        have -> := sc_pexprP hschi hhi.
        by eexists.
      move=> i si s si2 hst hw; have ? := estate_eq hst; subst s.
      by exists si2.

    + move=> al c e ii2 c2 hc hc2 ii.
      apply wequiv_weaken with (st_rel (fun _ : unit => eq) tt)
        (fun si s => st_rel (fun _ : unit => eq) tt si s /\
           sem_eassert_wc (p_globs psc) si (aands (sc_pexpr e)) = ok true).
      1-2: by move=> > [].
      apply wequiv_while.
      + move=> s s2 b [hst]; have ? := estate_eq hst; subst s2; move=> /sc_pexprP he.
        by rewrite /sem_cond; t_xrbindP=> v /he -> /to_boolI ?; subst v; exists b.
      + rewrite -{2}(cats0 c); apply wequiv_cat with (st_rel (fun _ : unit => eq) tt) => //.
        by apply safe_assertP.
      by apply wequiv_weaken with (st_rel (fun _ : unit => eq) tt)
                                  (st_rel (fun _ : unit => eq) tt) => // > [].

    + move=> xs f es ii.
      apply wequiv_call_wa with (rpreF (eS:=eq_spec)) (rpostF (eS:=eq_spec)) eq.
      + move=> s s2 vs [hst]; have ? := estate_eq hst; subst s2.
        move=> /aandsE_cat[] hscx hsce hewc.
        by have -> := sc_pexprsP hsce hewc; eauto.
      + move=> s s2 vs vs2 [hst] + ?; subst vs2; have ? := estate_eq hst; subst s2.
        by move=> _; apply sem_pre_sc.
      + by move=> s s2 vs vs2 [hst _] ?; subst vs2; have ? := estate_eq hst; subst s2.
      + move=> fs1 fs2 fr1 fr2 [_ ?]; subst fs2 => /= ?; subst fr2.
        by apply sem_post_sc.
      + by move=> ???; exact/wequiv_fun_rec.
      move=> fs1 fs2 fr1 fr2 [_ ?]; subst fs2 => hfr; rewrite /= in hfr; subst fr2.
      move=> s s2 sf [hst]; have ? := estate_eq hst; subst s2.
      move=> /aandsE_cat[] hscx hsce; rewrite /upd_estate => hw; exists sf => //.
      have falseP : forall q : Prop, false -> q by [].
      by rewrite (sc_lvalsP (s := with_scs (with_mem s (fmem fr1)) (fscs fr1))
                    hscx erefl (falseP _) hw).

    + move=> s s2 fs2 hst; have ? := estate_eq hst; subst s2.
      case: fd2 hgetsc hget hinit => //=.
      move=> > _ _ _; rewrite /finalize_funcall /=.
      by t_xrbindP => vs -> /= vs2 -> /= <-; eauto.
    by move=> fr1 fr2 hfr; rewrite /= in hfr; subst fr2; apply sem_post_sc.
Qed.

End GLOBALS.

Lemma safety_callP psc2 :
  sc_prog p = ok psc2 ->
  forall fn,
  wiequiv_f (wc1:=withcatch) (wc2:=nocatch) psc2 p ev ev
    (rpreF (eS:=eq_spec)) fn fn (rpostF (eS:=eq_spec)).
Proof.
  rewrite /sc_prog; t_xrbindP => hall <- fn.
  apply safety_callP_aux.
  move=> x len t /get_globalI [gv] [hget hgv hty].
  Opaque ziota.
  elim: gd hget hall => // -[y yd] gd ih /=.
  case: eqP => // heq; last by move=> + /andP [_ ].
  move=> [->] /andP [] {ih}.
  by case: gv hgv => //= len2 t2 /Varr_inj [?] ?; subst len2 t2.
Qed.
Transparent ziota.

End SAFETY_PROOF.
