(* * Correctness of the safety pass.

   The instrumented program, run in the total mode (the semantics EasyCrypt
   implements) and with assertions enabled, refines the original program run in
   the partial mode. *)

From mathcomp Require Import ssreflect ssrfun ssrbool ssralg eqtype word_ssrZ.
Require Import psem psem_facts op_semi compiler_util safety safety_common_proof.
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
Notation sem_pexpr_t := (sem_pexpr (sm := total)).
Notation sem_pexprs_t := (sem_pexprs (sm := total)).
Notation sem_eassert_t := (sem_eassert (sm := total)).

(* ------------------------------------------------------------------------- *)
(* Array types                                                                *)

Lemma eval_atype_carr ty n :
  eval_atype ty = carr n -> exists ws len, ty = aarr ws len /\ n = arr_size ws len.
Proof. by case: ty => // ws len [<-]; exists ws, len. Qed.

(* ------------------------------------------------------------------------- *)
(* Array variables are always defined, so both modes read them alike          *)

Lemma arr_isdef s x len :
  eval_atype (vtype (gv x)) = carr len -> is_defined (evm s).[gv x].
Proof.
  move=> hty; have := Vm.getP (evm s) (gv x).
  by rewrite hty => /compat_valEl [? ->].
Qed.

Lemma arr_get_gvar_partial {n} s x (t : WArray.array n) :
  eval_atype (vtype (gv x)) = carr n ->
  get_gvar (sm := total) true gd (evm s) x = ok (Varr t) ->
  get_gvar (sm := partial) true gd (evm s) x = ok (Varr t).
Proof.
  rewrite /get_gvar; case: ifP => // _ hty.
  have hdef := arr_isdef s hty.
  by rewrite /get_var /= (Vm.get_totalE hdef) hdef.
Qed.

(* A success of the partial mode is a success of the total mode. *)
Lemma get_gvar_partialE s x v :
  get_gvar (sm := partial) true gd (evm s) x = ok v ->
  get_gvar (sm := total) true gd (evm s) x = ok v.
Proof.
  rewrite /get_gvar; case: ifP => // _; rewrite /get_var /=.
  by case heq: is_defined => //= -[<-]; rewrite (Vm.get_totalE heq) heq.
Qed.

(* ------------------------------------------------------------------------- *)
(* Global arrays: [sc_prog] checks that they are fully initialised            *)

Section GLOBALS.

(* Discharged by [sc_prog], which checks [check_glob] on every global. *)
Hypothesis get_global_arr_init :
  forall x len (t : WArray.array len),
  get_global gd x = ok (Varr t) -> all (WArray.is_init t) (ziota 0 len).

Opaque wsize_size.

(* ------------------------------------------------------------------------- *)
(* The [i_safe] conditions of the instruction operators                       *)

Lemma nth_sem_pexprs_nth gd0 s es pos vs :
  ssrnat.leq (S pos) (size es) ->
  sem_pexprs_t true gd0 s es = ok vs ->
  sem_pexpr_t true gd0 s (nth (Pbool false) es pos) = ok (nth undef_b vs pos).
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

(* [sc_to_e] computes, in the total mode, the interpretation of the condition
   on the values of the arguments: [Papp1] and [Papp2] there are literally the
   [IOp1] and [IOp2] cases of [sem_safety_cond]. *)
Lemma sem_pexpr_sc_to_e gd0 s es vs c v :
  sem_pexprs_t true gd0 s es = ok vs ->
  safety_cond_expr c -> safety_cond_vars_below (size es) c ->
  sem_pexpr_t true gd0 s (sc_to_e eint_of_word es c) = ok v ->
  sem_safety_cond vs c = ok v /\ is_defined v.
Proof.
  move=> hes; elim/safety_cond_ind_seq: c v => //=.
  + by move=> b v _ _ [<-].
  + by move=> z v _ _ [<-].
  + move=> k v _ hk.
    have hsem := nth_sem_pexprs_nth hk hes.
    rewrite hsem => -[<-].
    by split => //; apply: sem_pexpr_defined hsem.
  + move=> o c ih v /andP [_ htot] hk.
    rewrite sc_to_e_op1 /=.
    t_xrbindP => v1 /(ih _ htot hk) [hv1 hd1].
    rewrite /sem_sop1; t_xrbindP => x hof r hr <-.
    move: hr; rewrite sem_sop1_typed_total => -[<-].
    rewrite hv1 /= hof /=.
    by split => //; apply: (to_val_defined (erefl _)).
  move=> o c1 ih1 c2 ih2 v /and3P [_ ht1 ht2] /andP [hk1 hk2].
  t_xrbindP => v1 /(ih1 _ ht1 hk1) [hv1 hd1] v2 /(ih2 _ ht2 hk2) [hv2 hd2].
  rewrite /sem_sop2; t_xrbindP => x1 hof1 x2 hof2 r hr <-.
  move: hr; rewrite sem_sop2_typed_total => -[<-].
  rewrite hv1 /= hv2 /= hof1 /= hof2 /=.
  by split => //; apply: (to_val_defined (erefl _)).
Qed.

Lemma sem_pexprs_sc_to_e gd0 s es vs cs l :
  sem_pexprs_t true gd0 s es = ok vs ->
  all safety_cond_expr cs -> all (safety_cond_vars_below (size es)) cs ->
  mapM (sem_pexpr_t true gd0 s) (map (sc_to_e eint_of_word es) cs) = ok l ->
  mapM (sem_safety_cond vs) cs = ok l.
Proof.
  move=> hes; elim: cs l => [ | c cs ih] l /=; first by move=> _ _ [<-].
  move=> /andP [h1 h2] /andP [k1 k2].
  t_xrbindP => v /(sem_pexpr_sc_to_e hes h1 k1) [hv _] l' /(ih _ h2 k2) hl' <-.
  by rewrite hv /= hl'.
Qed.

(* The assertion generated for a safety condition implies the condition. *)
Lemma sem_cond_interp_safe gd0 s es vs sc :
  sem_pexprs_t true gd0 s es = ok vs ->
  sem_eassert_t gd0 s (safety_cond_to_e es sc) = ok true ->
  safety_cond_holds vs sc.
Proof.
  move=> hes; rewrite /safety_cond_to_e /sc_to_eassert.
  have hPexpr : forall c,
      sem_eassert_t gd0 s
        (Pexpr (if safety_cond_expr c && safety_cond_vars_below (size es) c
                then sc_to_e eint_of_word es c else Pbool false)) = ok true ->
      safety_cond_holds vs c.
  + move=> c; case: ifP => [/andP [hexp hk] | _]; last by move=> [].
    rewrite /=; t_xrbindP => v hv /to_boolI ?; subst v.
    by have [hi _] := sem_pexpr_sc_to_e hes hexp hk hv; rewrite /safety_cond_holds hi.
  case: sc => [b | z | k | o c | o c1 c2 | o cs];
    [ exact: (hPexpr (IBool b)) | exact: (hPexpr (IConst z))
    | exact: (hPexpr (IVar k)) | exact: (hPexpr (IOp1 o c))
    | exact: (hPexpr (IOp2 o c1 c2)) | ].
  case: ifP => [/andP [hexp hall] | _]; last by move=> [].
  rewrite /=; t_xrbindP => l hl hop.
  move: hop; rewrite /sem_opN_safety => hop.
  by rewrite /safety_cond_holds /= (sem_pexprs_sc_to_e hes hexp hall hl) /= hop.
Qed.

Lemma sem_cond_interp_safes gd0 s es vs sc :
  sem_pexprs_t true gd0 s es = ok vs ->
  sem_eassert_t gd0 s (aands [seq safety_cond_to_e es i | i <- sc]) = ok true ->
  all (safety_cond_holds vs) sc.
Proof.
  move=> hes; elim: sc => [ | sc scs hrec] //=.
  move=> /aandsE_cons [hsc hscs]; rewrite (hrec hscs) andbT.
  by apply: sem_cond_interp_safe hsc.
Qed.

(* ------------------------------------------------------------------------- *)
(* Array and memory accesses: the assertions generated for an access imply the
   conditions of the semantics, hence the partial access succeeds and returns
   what the total access returns.                                            *)

Lemma check_safe_seqP vs scs :
  all (safety_cond_holds vs) (unzip1 scs) -> check_safe_seq vs scs = ok tt.
Proof.
  elim: scs => [|[c er] scs ih] //=; rewrite /check_safe_seq /=.
  by move=> /andP [-> /ih].
Qed.

Lemma sc_accessP gd0 s es vs scs :
  sem_pexprs_t true gd0 s es = ok vs ->
  sem_eassert_t gd0 s (aands (sc_access es scs)) = ok true ->
  check_safe_seq vs scs = ok tt.
Proof.
  by move=> hes hsc; apply/check_safe_seqP/(sem_cond_interp_safes hes hsc).
Qed.

(* The initialisation condition is not emitted for a global array: [check_glob]
   gives it, on the whole array. *)
Lemma sc_arr_getP s x al aa sz e n (r : WArray.array n) (i : Z) :
  eval_atype (vtype (gv x)) = carr n ->
  get_gvar (sm := partial) true gd (evm s) x = ok (Varr r) ->
  sem_pexpr_t true gd s e = ok (Vint i) ->
  sem_eassert_t gd s (aands (sc_arr_get x al aa sz e)) = ok true ->
  WArray.get (sm := partial) al aa sz r i = WArray.get (sm := total) al aa sz r i.
Proof using asm_op ep get_global_arr_init p sip spp syscall_state.
  move=> /[dup] hty /eval_atype_carr [ws [len [htyx ?]]]; subst n.
  move=> hgv he.
  have hes : sem_pexprs_t true gd s [:: Pvar x; e] = ok [:: Varr r; Vint i].
  + by rewrite /sem_pexprs /= (get_gvar_partialE hgv) /= he /=.
  rewrite /sc_arr_get htyx => hsc.
  suff h :
    all (safety_cond_holds [:: Varr r; Vint i]) (unzip1 (sc_get (arr_size ws len) al aa sz)).
  + have hok : is_ok (WArray.get (sm := total) al aa sz r i).
    + by apply: read_total_ok.
    case hg: (WArray.get (sm := total) al aa sz r i) hok => [w | er] //= _.
    by apply/getE; split; [apply: check_safe_seqP h | exact hg].
  move: hsc; case: ifP => hlv hsc.
  + by apply: (sem_cond_interp_safes hes hsc).
  have {}hsc := sem_cond_interp_safes hes hsc.
  move: hsc; rewrite /sc_get_noinit /sc_get /unzip1 /= => /andP [hal /andP [hb _]].
  rewrite hal hb /= andbT.
  have h0 : nth undef_b [:: Varr r; Vint i] 0 = Varr r by [].
  have h1 : nth undef_b [:: Varr r; Vint i] 1 = Vint i by [].
  rewrite (safety_cond_holds_arr_init aa sz (wsize_size sz) h0 h1).
  move: hb.
  rewrite (safety_cond_holds_arr_in_bound (arr_size ws len) aa sz (wsize_size sz) h1).
  move=> /andP [/ZleP hlo /ZleP hhi].
  move: hgv; rewrite /get_gvar hlv => /get_global_arr_init /allP hinit.
  apply/allP => j; rewrite in_ziota !zify => hj.
  by apply/hinit; rewrite in_ziota !zify; Lia.lia.
Qed.

Lemma sc_arr_get_subP s x aa sz len e n (r : WArray.array n) (i : Z) :
  eval_atype (vtype (gv x)) = carr n ->
  get_gvar (sm := partial) true gd (evm s) x = ok (Varr r) ->
  sem_pexpr_t true gd s e = ok (Vint i) ->
  sem_eassert_t gd s (aands (sc_arr_get_sub x aa sz len e)) = ok true ->
  WArray.get_sub (sm := partial) aa sz len r i
  = WArray.get_sub (sm := total) aa sz len r i.
Proof.
  move=> /[dup] hty /eval_atype_carr [ws [lenx [htyx ?]]]; subst n.
  move=> hgv he.
  have hes : sem_pexprs_t true gd s [:: Pvar x; e] = ok [:: Varr r; Vint i].
  + by rewrite /sem_pexprs /= (get_gvar_partialE hgv) /= he /=.
  rewrite /sc_arr_get_sub htyx => /(sc_accessP hes) hchk.
  have hok : is_ok (WArray.get_sub (sm := total) aa sz len r i).
  + by rewrite /WArray.get_sub or_is_total_total.
  case hg: (WArray.get_sub (sm := total) aa sz len r i) hok => [b | er] //= _.
  by apply/get_subE; split; [exact hchk | exact hg].
Qed.

(* The conditions of a write mention only the index, so they do not depend on
   the value written, which is the third argument of [sc_set]. *)
Lemma sc_arr_setP s (x : var_i) al aa sz e n (r : WArray.array n) (i : Z) (w : word sz) :
  eval_atype (vtype x) = carr n ->
  get_var (sm := partial) true (evm s) x = ok (Varr r) ->
  sem_pexpr_t true gd s e = ok (Vint i) ->
  sem_eassert_t gd s (aands (sc_arr_set x al aa sz e)) = ok true ->
  WArray.set (sm := partial) r al aa i w = WArray.set (sm := total) r al aa i w.
Proof.
  move=> /[dup] hty /eval_atype_carr [ws [len [htyx ?]]]; subst n.
  move=> hgv he.
  have hes : sem_pexprs_t true gd s [:: Plvar x; e] = ok [:: Varr r; Vint i].
  + by rewrite /sem_pexprs /= (get_gvar_partialE (x := mk_lvar x) hgv) /= he /=.
  rewrite /sc_arr_set htyx => /(sc_accessP hes) hchk.
  have h1 : nth undef_b [:: Varr r; Vint i] 1 = Vint i by [].
  have h1' : nth undef_b [:: Varr r; Vint i; Vword w] 1 = Vint i by [].
  have {}hchk :
    check_safe_seq [:: Varr r; Vint i; Vword w] (sc_set (arr_size ws len) al aa sz) = ok tt.
  + move: hchk; rewrite /check_safe_seq /sc_set /=
      (safety_cond_holds_arr_aligned al aa sz h1)
      (safety_cond_holds_arr_in_bound (arr_size ws len) aa sz (wsize_size sz) h1)
      (safety_cond_holds_arr_aligned al aa sz h1')
      (safety_cond_holds_arr_in_bound (arr_size ws len) aa sz (wsize_size sz) h1').
    by case: is_aligned_if => //; case: (_ && _).
  have hok : is_ok (WArray.set (sm := total) r al aa i w).
  + by apply: write_total_ok.
  case hg: (WArray.set (sm := total) r al aa i w) hok => [a | er] //= _.
  by apply/setE; split; [exact hchk | exact hg].
Qed.

(* The counterpart of [sc_arr_setP] for a sub-array write. *)
Lemma sc_arr_set_subP s (x : var_i) aa sz len e n (r : WArray.array n) (i : Z)
    (b : WArray.array (arr_size sz len)) :
  eval_atype (vtype x) = carr n ->
  get_var (sm := partial) true (evm s) x = ok (Varr r) ->
  sem_pexpr_t true gd s e = ok (Vint i) ->
  sem_eassert_t gd s (aands (sc_arr_set_sub x aa sz len e)) = ok true ->
  WArray.set_sub (sm := partial) aa r i b = WArray.set_sub (sm := total) aa r i b.
Proof.
  move=> /[dup] hty /eval_atype_carr [ws [lenx [htyx ?]]]; subst n.
  move=> hgv he.
  have hes : sem_pexprs_t true gd s [:: Plvar x; e] = ok [:: Varr r; Vint i].
  + by rewrite /sem_pexprs /= (get_gvar_partialE (x := mk_lvar x) hgv) /= he /=.
  rewrite /sc_arr_set_sub htyx => /(sc_accessP hes) hchk.
  have h1 : nth undef_b [:: Varr r; Vint i] 1 = Vint i by [].
  have h1' : nth undef_b [:: Varr r; Vint i; Varr b] 1 = Vint i by [].
  have {}hchk :
    check_safe_seq [:: Varr r; Vint i; Varr b] (sc_set_sub (arr_size ws lenx) aa sz len) = ok tt.
  + move: hchk; rewrite /check_safe_seq /sc_set_sub /=
      (safety_cond_holds_arr_in_bound (arr_size ws lenx) aa sz (arr_size sz len) h1)
      (safety_cond_holds_arr_in_bound (arr_size ws lenx) aa sz (arr_size sz len) h1').
    by case: (_ && _).
  have hok : is_ok (WArray.set_sub (sm := total) aa r i b).
  + by rewrite /WArray.set_sub or_is_total_total.
  case hg: (WArray.set_sub (sm := total) aa r i b) hok => [a | er] //= _.
  by apply/set_subE; split; [exact hchk | exact hg].
Qed.

(* The pointer of a memory access is read as a word of size [Uptr], which is
   what [to_pointer] does: the condition does not see the coercion. *)
Lemma safety_cond_holds_to_pointer al sz (v : value) (pt : pointer) :
  to_pointer v = ok pt ->
  safety_cond_holds [:: v] (sc_mem_aligned al sz 0) = is_aligned_if al pt sz.
Proof.
  move=> h; rewrite /sc_mem_aligned; case: al => //=.
  rewrite /safety_cond_holds /sc_eqi /sc_modi /sc_toint /= h /=.
  by rewrite is_alignE memory_model.p_to_zE Z_eqbE.
Qed.

(* [Pis_mem_init e sz] says that every byte of the access can be read, which is
   what [validr] asks on top of the alignment condition. *)
Lemma all_get_read8 mem wlo sz :
  all (fun i : Z => validr mem Unaligned (wlo + wrepr Uptr i)%R U8) (ziota 0 sz)
  = all (fun i : Z => is_ok (get mem (wlo + wrepr Uptr i)%R)) (ziota 0 sz).
Proof.
  by elim: ziota => [| k ks hrec] //=; rewrite -is_ok_read_partial -get_read8 hrec.
Qed.

Lemma sc_memP s al sz e v (pt : pointer) :
  sem_pexpr_t true gd s e = ok v ->
  to_pointer v = ok pt ->
  sem_eassert_t gd s (aands (sc_mem al sz e)) = ok true ->
  validr (emem s) al pt sz.
Proof.
  move=> he htop /aandsE_cons [h1 h2].
  have hes : sem_pexprs_t true gd s [:: e] = ok [:: v].
  + by rewrite /sem_pexprs /= he.
  have hal := sem_cond_interp_safe hes h1.
  rewrite (safety_cond_holds_to_pointer al sz htop) in hal.
  move: h2 => /=; rewrite he /= htop /= => -[] hall.
  rewrite /validr hal /=.
  move: hall; rewrite all_get_read8 => /allP hg.
  by apply/allP => k hk; rewrite addE; apply: hg hk.
Qed.

Lemma sc_mem_readP s al sz e v (pt : pointer) :
  sem_pexpr_t true gd s e = ok v ->
  to_pointer v = ok pt ->
  sem_eassert_t gd s (aands (sc_mem al sz e)) = ok true ->
  read (sm := partial) (emem s) al pt sz = read (sm := total) (emem s) al pt sz.
Proof.
  move=> he htop hsc; have hv := sc_memP he htop hsc.
  have hok : is_ok (read (sm := total) (emem s) al pt sz).
  + by apply: read_total_ok.
  case hr: (read (sm := total) (emem s) al pt sz) hok => [w | er] //= _.
  by apply/read_partialE; split; [exact hv | exact hr].
Qed.

Lemma sc_mem_writeP s al sz e v (pt : pointer) (w : word sz) :
  sem_pexpr_t true gd s e = ok v ->
  to_pointer v = ok pt ->
  sem_eassert_t gd s (aands (sc_mem al sz e)) = ok true ->
  write (sm := partial) (emem s) al pt w = write (sm := total) (emem s) al pt w.
Proof.
  move=> he htop hsc; have hv := validr_validw (sc_memP he htop hsc).
  have hok : is_ok (write (sm := total) (emem s) al pt w).
  + by apply: write_total_ok.
  case hr: (write (sm := total) (emem s) al pt w) hok => [m | er] //= _.
  by apply/write_partialE; split; [exact hv | exact hr].
Qed.

(* ------------------------------------------------------------------------- *)
(* Main lemma on expressions: under the generated assertions, what the total
   mode computes the partial mode computes too.                              *)

Let Pe e :=
  forall s v,
  sem_eassert_t gd s (aands (sc_pexpr e)) = ok true ->
  sem_pexpr_t true gd s e = ok v ->
  sem_pexpr (sm := partial) true gd s e = ok v.

Let Qe es :=
  forall s vs,
  sem_eassert_t gd s (aands (List.flat_map sc_pexpr es)) = ok true ->
  sem_pexprs_t true gd s es = ok vs ->
  sem_pexprs (sm := partial) true gd s es = ok vs.

Lemma sc_pexprP_aux : (forall e, Pe e) /\ (forall es, Qe es).
Proof using Pe Qe asm_op ep get_global_arr_init p sip spp syscall_state.
  apply: pexprs_ind_pair; subst Pe Qe; split => //=; t_xrbindP => //.
  + by move=> e he es hes s vs /aandsE_cat [/he{}he] /hes{}hes v {}/he -> vs2 /hes -> <- /=.
  + move=> x s v.
    rewrite /sc_gvar /get_gvar /=.
    case: (is_lvar x) => //.
    rewrite /sc_var /get_var /=; case harr: is_aarr.
    + move: harr => /is_aarrP [ws [len htx]] _.
      have hdef : is_defined (evm s).[gv x].
      + by apply: (arr_isdef s (len := arr_size ws len)); rewrite htx.
      by rewrite (Vm.get_totalE hdef) hdef /= => -[<-].
    rewrite /= Vm.is_var_initE => -[] hdef.
    by rewrite (Vm.get_totalE hdef) hdef.
  + move=> al aa sz x e he s v /aandsE_cat [/he{}he hsc].
    apply on_arr_gvarP => n r htx.
    move=> /(arr_get_gvar_partial htx) hgvr /=.
    t_xrbindP => zi z hewc /to_intI ? w hw <-; subst z.
    have {}he := he _ hewc; rewrite hgvr /= he /=.
    by rewrite (sc_arr_getP htx hgvr hewc hsc) hw.
  + move=> aa sz len x e he s v /aandsE_cat [/he {}he hsc].
    apply on_arr_gvarP => n r htx.
    move=> /(arr_get_gvar_partial htx) hgvr /=.
    t_xrbindP => zi z hewc /to_intI ? <-; subst z.
    have {}he := he _ hewc; rewrite hgvr /= he /=.
    by rewrite (sc_arr_get_subP htx hgvr hewc hsc) /=.
  + move=> al sz e he s v /aandsE_cat [/he{}he hsc] pt vpt hewc htop w hread <-.
    have {}he := he _ hewc; rewrite he /= htop /=.
    by rewrite (sc_mem_readP hewc htop hsc) hread.
  + move=> op e he s v /aandsE_cat [/he{}he] hop v1 hewc.
    have {}he := he _ hewc; rewrite he /= /sem_sop1.
    case hval: of_val => [a|e0] //=.
    have hes : sem_pexprs_t true gd s [:: e] = ok [:: v1] by rewrite /= hewc.
    by rewrite (sem_sop1_typed_safeE hval (sem_cond_interp_safes hes hop)).
  + move=> op e1 he1 e2 he2 s v /aandsE_cat [/he1{}he1].
    move=> /aandsE_cat [/he2{}he2] hop v2 he1wc v3 he2wc.
    have {}he1 := he1 _ he1wc; have {}he2 := he2 _ he2wc.
    rewrite he1 he2 /sem_sop2 /=.
    case hval1: (of_val (eval_atype (type_of_op2 op).1.1) v2) => [a1|er1] //=.
    case hval2: (of_val (eval_atype (type_of_op2 op).1.2) v3) => [a2|er2] //=.
    have hes : sem_pexprs_t true gd s [:: e1; e2] = ok [:: v2; v3].
    + by rewrite /= he1wc /= he2wc.
    by rewrite (sem_sop2_typed_safeE hval1 hval2 (sem_cond_interp_safes hes hop)).
  (* [PappN] carries no condition, and its two modes are the same function *)
  + by move=> op es he s v /he{}he v2 {}/he; rewrite /sem_pexprs => hn; rewrite hn /=.
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

Lemma sc_lvalP l v s s2 :
  sem_eassert_t gd s (aands (sc_lval l)) = ok true ->
  write_lval (sm := total) true gd l v s = ok s2 ->
  write_lval (sm := partial) true gd l v s = ok s2.
Proof using Pe Qe asm_op ep get_global_arr_init p sip spp syscall_state.
  case: l => [vi tynone | x | al sz x e | al aa sz x e | aa sz pos x e ] //=.
  + t_xrbindP => /aandsE_cat [] /sc_pexprP he hsc wpt vpt hewc htop w htow m hwr ?.
    subst s2.
    have {}he := he _ hewc; rewrite he /= htop /= htow /=.
    by rewrite (sc_mem_writeP w hewc htop hsc) hwr.
  + move=> /aandsE_cat [] /sc_pexprP he hsc.
    apply: on_arr_varP => n r htx getx.
    have getxp : get_var (sm := partial) true (evm s) x = ok (Varr r).
    + exact: (arr_get_gvar_partial (x := mk_lvar x) htx getx).
    t_xrbindP => i z hewc /to_intI ? w htow t hset hwv; subst z.
    have {}he := he _ hewc.
    rewrite /on_arr_var getxp /= he /= htow /= (sc_arr_setP w htx getxp hewc hsc) hset /=.
    exact: hwv.
  move=> /aandsE_cat [] /sc_pexprP he hsc.
  apply: on_arr_varP => n r htx getx.
  have getxp : get_var (sm := partial) true (evm s) x = ok (Varr r).
  + exact: (arr_get_gvar_partial (x := mk_lvar x) htx getx).
  t_xrbindP => i z hewc /to_intI ? b htoarr hwv; subst z.
  have {}he := he _ hewc.
  rewrite /on_arr_var getxp /= he /= htoarr /= (sc_arr_set_subP b htx getxp hewc hsc) /=.
  exact: hwv.
Qed.

Lemma sc_lvalsP ls vs s0 s s2 okmem :
  sem_eassert_t gd s0 (aands (sc_lvals ls okmem)) = ok true ->
  evm s0 = evm s ->
  (okmem -> emem s0 = emem s) ->
  write_lvals (sm := total) true gd s ls vs = ok s2 ->
  write_lvals (sm := partial) true gd s ls vs = ok s2.
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

(* [eassert] counterpart of [sc_pexprP]: the assertion language is a separate
   type, so [sc_pexprP] alone covers neither [Cassert] nor the contracts. *)
Lemma sc_eassertP a s b :
  sem_eassert_t gd s (aands (sc_eassert a)) = ok true ->
  sem_eassert_t gd s a = ok b ->
  sem_eassert (sm := partial) gd s a = ok b.
Proof using Pe Qe asm_op ep get_global_arr_init p sip spp syscall_state.
  elim: a b => /=.
  + by move=> e b /sc_pexprP he; t_xrbindP => vv /he -> /=.
  + move=> o es b hsc; have hes := sc_pexprsP (es:=es) (s:=s).
    case heq: (mapM (sem_pexpr_t true gd s) es) => [vs|er] //=.
    have hn := hes vs hsc heq.
    by move: hn; rewrite /sem_pexprs => ->.
  (* [Pis_var_init] observes the raw state, which the mode does not change *)
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
  sem_pre (sm := total) psc fn fs = ok tt ->
  sem_pre (sm := partial) p fn fs = ok tt.
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
  sem_post (sm := total) psc fn vs fs = ok tt ->
  sem_post (sm := partial) p fn vs fs = ok tt.
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

(* On a defined value of exactly the right type, [truncate_val] is the
   identity: this is what makes the arguments of an instruction their own
   truncation. *)
Lemma truncate_val_type_of v ty :
  type_of_val v = ty -> is_defined v -> truncate_val ty v = ok v.
Proof.
  move=> <-; case: v => //= [len a|ws w] _.
  + by rewrite /truncate_val /= WArray.castK.
  by rewrite /truncate_val /= truncate_word_u.
Qed.

Lemma sem_pexpr_type_of gd0 s e v :
  sem_pexpr (sm := partial) true gd0 s e = ok v ->
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
  wiequiv_f (sm1 := total) (sm2 := partial) psc p ev ev
    (rpreF (eS:=eq_spec)) fn fn (rpostF (eS:=eq_spec)).
Proof using E E0 Pe Qe asm_op ep ev get_global_arr_init p psc rE sip spp syscall_state wE.
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
                 wequiv_rec (sm1 := total) (sm2 := partial)
                   psc p ev ev eq_spec (st_rel (fun _ : unit => eq) tt)
                   (sc_instr i) [::i] (st_rel (fun _ : unit => eq) tt)).

    set Pc := (fun c =>
                 wequiv_rec (sm1 := total) (sm2 := partial)
                   psc p ev ev eq_spec (st_rel (fun _ : unit => eq) tt)
                   (List.flat_map sc_instr c) c (st_rel (fun _ : unit => eq) tt)).

    set Pi_r := (fun ir => forall ii,
                 wequiv_rec (sm1 := total) (sm2 := partial)
                   psc p ev ev eq_spec
                   (fun si s => st_rel (fun _ : unit => eq) tt si s /\
                      sem_eassert_t gd si (aands (sc_instr_ir ii ir).1) = ok true)
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
        sem_eassert_t (p_globs psc) si (aands (sc_instr_ir ii ir).1) = ok true).
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
                                  sem_pexprs_t true gd s es = ok vs1 &
                                  sem_pexprs (sm := partial) true gd s es = ok vs2]) eq.
      + by move=> s1 s2 sf [] ??; subst s1 s2 => he; have -> := sc_pexprsP hsce he; exists sf.
      + move=> s1 s2 [] ??; subst s1 s2 => vs _ vf [] <- hewc he.
        (* the arguments are well typed and defined, so they are their own
           truncation *)
        have hty : List.Forall2 (fun ty vv => type_of_val vv = eval_atype ty)
                            (tin (get_instr_desc o)) vs.
        + move: hwt he => [] {hewc hsco hsce}.
          elim: (tin _) es vs => [ | ty tys ih] [ | e es] //=.
          + by move=> vs2 _ [<-]; constructor.
          move=> vs2 /andP [hty htys].
          t_xrbindP => v hv vs3 hes <-; constructor.
          + rewrite -(convertible_eval_atype hty).
            by apply: sem_pexpr_type_of hv.
          by apply: ih htys hes.
        have htr : mapM2 ErrType truncate_val
                     [seq eval_atype i | i <- tin (get_instr_desc o)] vs = ok vs.
        + move: hty (sem_pexprs_defined hewc) => {}hty hdef.
          elim: hty hdef => //= ty v tys ws h1 _ ih /andP [hd hds].
          by rewrite (truncate_val_type_of h1 hd) /= (ih hds).
        (* the asserted conditions are [i_safe], so the two modes of the
           descriptor agree on these arguments *)
        have hall := sem_cond_interp_safes hewc hsco.
        rewrite /exec_sopn /sopn_sem /sopn_sem_ /semi /mk_semi.
        case: (i_valid (get_instr_desc o)) => //=.
        rewrite !mk_semi_aux_app_sopnE htr /=.
        rewrite !(check_safe_ok (i_err (get_instr_desc o)) hall) /=.
        by move=> ->; exists vf.
      move=> vs _ <- s1 s2 sf [] ??; subst s1 s2 => hws.
      by rewrite (sc_lvalsP hscx erefl (fun _ => erefl) hws); exists sf.

    + move => xs o es ii; apply wkequivP' => si0 s0.
      apply wequiv_syscall with
        eq (fun fs1 fs2 => [/\ fs1 = fs2, emem si0 = fmem fs1
                            & map type_of_val fs1.(fvals) =
                              map eval_atype (scs_tout (syscall_sig_u o))]).
      + apply wrequiv_weaken with
          (fun t s => t = s /\
             sem_eassert_t gd t (aands (List.flat_map sc_pexpr es)) = ok true) eq => //.
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
           sem_eassert_t (p_globs psc) si (aands (sc_pexpr e)) = ok true).
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
  wiequiv_f (sm1 := total) (sm2 := partial) psc2 p ev ev
    (rpreF (eS := eq_spec)) fn fn (rpostF (eS := eq_spec)).
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
