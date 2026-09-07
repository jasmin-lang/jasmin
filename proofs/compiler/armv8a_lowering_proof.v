From mathcomp Require Import ssreflect ssrfun ssrbool eqtype order ssralg.
Import
  Order.POrderTheory
  Order.TotalTheory.
From mathcomp Require Import word_ssrZ.

From Coq Require Import Lia.

Require Import
  compiler_util
  expr
  lowering
  lowering_lemmas
  psem
  utils.
Require Import
  arch_extra
  sem_params_of_arch_extra.
Require Import
  armv8a_decl
  armv8a_extra
  armv8a_instr_decl
  armv8a_lowering.

Set SsrOldRewriteGoalsOrder.  (* change Set to Unset when porting the file, then remove the line when requiring MathComp >= 2.6 *)

(* On AArch64, register operations exist at both the X (64-bit) and
   W (32-bit) widths. *)
Lemma chk_ws_regP {A ws a} {oa : option A} :
  (let%opt _ := chk_ws_reg ws in oa) = Some a
  -> ((ws == U64) || (ws == U32)) /\ oa = Some a.
Proof. by move=> /oassertP []. Qed.

(* TODO_ARM: Improve. Move? *)
Lemma nzcv_of_aluop_CF_sub ws (x y : word ws) :
  (wunsigned (x - y) != (wunsigned x + wunsigned (wnot y) + 1)%Z)
  = (wunsigned (x - y) == (wunsigned x - wunsigned y)%Z).
Proof.
  rewrite wunsigned_sub_if.

  case: ZleP => _;
    rewrite wunsigned_wnot;
    generalize (wunsigned x) (wunsigned y);
    clear;
    move=> x y.

  all: have h := @wbase_n0 ws.

  - rewrite eqxx. apply/eqP. lia.

  have -> : (wbase ws + x - y == x - y)%Z = false.
  - apply/eqP. lia.

  apply/eqP.
  lia.
Qed.

Section PROOF.

Context
  {wsw : WithSubWord}
  {dc : DirectCall}
  {atoI : arch_toIdent}
  {syscall_state : Type}
  {sc_sem : syscall_sem syscall_state}
  {pT : progT}
  {sCP : semCallParams}
  (p : prog)
  (ev : extra_val_t)
  (warning : instr_info -> warning_msg -> instr_info)
  (fv : fresh_vars)
  (fv_correct : fvars_correct (all_fresh_vars fv) (fvars fv) (p_funcs p)).

Notation fvars := (fvars fv).
Notation lower_pexpr := (lower_pexpr fv).
Notation lower_cmd :=
  (lower_cmd
     (fun _ => lower_i)
     warning
     fv).
Notation lower_prog :=
  (lower_prog
     (fun _ => lower_i)
     warning
     fv).
Notation lower_i := (lower_i fv).
Notation disj_fvars := (disj_fvars fvars).
Notation disj_fvars_get_fundef := (disj_fvars_get_fundef fv_correct).

Notation p' := (lower_prog p).

(* -------------------------------------------------------------------- *)

Definition eq_fv (s0 s1 : estate) : Prop :=
  st_eq_ex fvars s0 s1.

Ltac t_fvars_neq :=
  move: fv_correct;
  move=> /andP [] _;
  rewrite /all_fresh_vars /=;
  t_elim_uniq;
  by (move=> [?]; auto).

Ltac t_get_var :=
  repeat (rewrite get_var_neq; last t_fvars_neq);
  rewrite get_var_eq /=.

Lemma fvars_NF : Sv.In (fvNF fv) fvars.
Proof. by repeat (exact: SvD.F.add_1 || apply: SvD.F.add_2). Qed.

Lemma fvars_ZF : Sv.In (fvZF fv) fvars.
Proof. by repeat (exact: SvD.F.add_1 || apply: SvD.F.add_2). Qed.

Lemma fvars_CF : Sv.In (fvCF fv) fvars.
Proof. by repeat (exact: SvD.F.add_1 || apply: SvD.F.add_2). Qed.

Lemma fvars_VF : Sv.In (fvVF fv) fvars.
Proof. by repeat (exact: SvD.F.add_1 || apply: SvD.F.add_2). Qed.


(* -------------------------------------------------------------------- *)
(* Lowering of conditions. *)

Definition condition_mnemonics := [:: CMP; TST ].

Definition estate_of_CMP {ws : wsize} s (w0 w1 : word ws) : estate :=
  let w1not := wnot w1 in
  let res := (w0 + w1not + 1)%R in
  let res_unsigned := (wunsigned w0 + wunsigned w1not + 1)%Z in
  let res_signed := (wsigned w0 + wsigned w1not + 1)%Z in
  let vm' :=
    (evm s)
      .[fvNF fv <- NF_of_word res]
      .[fvZF fv <- ZF_of_word res]
      .[fvCF fv <- wunsigned res != res_unsigned]
      .[fvVF fv <- wsigned res != res_signed]
  in
  with_vm s vm'.

(* Contrary to AArch32, TST also (re)sets VF (to false). *)
Definition estate_of_TST {ws : wsize} s (w0 w1 : word ws) : estate :=
  let res := wand w0 w1 in
  let vm' :=
    (evm s)
      .[fvNF fv <- NF_of_word res]
      .[fvZF fv <- ZF_of_word res]
      .[fvCF fv <- false]
      .[fvVF fv <- false]
  in
  with_vm s vm'.

(* Precondition: [mn] is a condition mnemonic. *)
Definition estate_of_condition_mn
  (mn : armv8a_mnemonic) {ws : wsize} : estate -> word ws -> word ws -> estate :=
  match mn with
  | CMP => estate_of_CMP
  | TST => estate_of_TST
  | _ => fun s _ _ => s (* Never happens. *)
  end.

Lemma estate_of_condition_mn_eq_fv mn ws s (w0 w1 : word ws) :
  mn \in condition_mnemonics
  -> eq_fv s (estate_of_condition_mn mn s w0 w1).
Proof.
  case: mn => // _.
  all: split => // x hx.
  all: rewrite /=.
  all: rewrite !Vm.setP_neq; first reflexivity.

  all: apply/eqP.
  all: move=> ?; subst x.
  all: apply: hx.

  all: by move: fvars_NF fvars_ZF fvars_CF fvars_VF.
Qed.

Lemma sem_condition_mn ii vi tag mn s es ws ws0 ws1
    (w0 : word ws0) (w1 : word ws1) :
  mn \in condition_mnemonics
  -> ((ws == U64) || (ws == U32))
  -> (ws <= ws0)%CMP
  -> (ws <= ws1)%CMP
  -> sem_pexprs true (p_globs p) s es = ok [:: Vword w0; Vword w1 ]
  -> let w0' := zero_extend ws w0 in
     let w1' := zero_extend ws w1 in
     let aop := Oarmv8a (ARMv8A_op mn (opts_at ws)) in
     let i := Copn (lflags_of_mn fv vi mn) tag aop es in
     esem p' ev [:: MkI ii i ] s = ok (estate_of_condition_mn mn s w0' w1').
Proof.
  move=> hmn hws hws0 hws1 hsemes /=.
  rewrite /sem_sopn /=.
  rewrite hsemes {hsemes} /=.

  case/orP: hws => /eqP ?; subst ws.
  all: case: mn hmn => // _.
  all: rewrite /exec_sopn /=.
  all: by rewrite !truncate_word_le.
Qed.

Lemma lower_TST_match e0 e1 es :
  lower_TST e0 e1 = Some es
  -> exists ws e00 e01 ws',
      e0 = Papp2 (Oland ws) e00 e01
      /\ e1 = Papp1 (Oword_of_int ws') (Pconst 0).
Proof.
  case: e0 => // -[] // ws e00 e01.
  case: e1 => // -[] // ws' [] // [] //.
  move=> [?]; subst es.
  eexists; eexists; eexists; eexists;
    split;
    reflexivity.
Qed.

Lemma pair_eq_dec A B
  (A_dec : forall a1 a2 : A, { a1 = a2 } + { a1 <> a2 })
  (B_dec : forall b1 b2 : B, { b1 = b2 } + { b1 <> b2 }) :
  forall ab1 ab2 : A * B, { ab1 = ab2 } + {ab1 <> ab2 }.
Proof. by decide equality. Qed.

Lemma lower_condition_Papp2P vi s op e0 e1 mn ws e es v0 v1 v :
  lower_condition_Papp2 fv vi op e0 e1 = Some (mn, ws, e, es)
  -> sem_pexpr true (p_globs p) s e0 = ok v0
  -> sem_pexpr true (p_globs p) s e1 = ok v1
  -> sem_sop2 op v0 v1 = ok v
  -> exists (ws0 ws1 : wsize) (w0 : word ws0) (w1 : word ws1),
      let w0' := zero_extend ws w0 in
      let w1' := zero_extend ws w1 in
      [/\ mn \in condition_mnemonics
        , ((ws == U64) || (ws == U32))
        , (ws <= ws0)%CMP
        , (ws <= ws1)%CMP
        , sem_pexprs true (p_globs p) s es = ok [:: Vword w0; Vword w1 ]
        & sem_pexpr true (p_globs p) (estate_of_condition_mn mn s w0' w1') e = ok v
      ].
Proof using atoI fv fv_correct p pT sc_sem syscall_state wsw.
  move=> h hseme0 hseme1 hsemop.
  move: h; rewrite /lower_condition_Papp2.
  apply: obindP => -[cf ws'] hcf /chk_ws_regP [hws h].

  (* whatever [op] is, it takes two words as arguments and returns a bool *)
  have: exists ws0 ws1 (w0 : word ws0) (w1 : word ws1) b,
    [/\ (ws' <= ws0)%CMP,
        (ws' <= ws1)%CMP,
        v0 = Vword w0,
        v1 = Vword w1,
        forall eq : type_of_op2 op = (aword ws', aword ws', abool),
          ecast t (let t := t in _) eq (sem_sop2_typed op) (zero_extend ws' w0) (zero_extend ws' w1) = ok b &
        v = Vbool b].
  + have hty: type_of_op2 op = (aword ws', aword ws', abool).
    + by case: (op) hcf => // -[] //= > [_ ->].
    move: hsemop; rewrite /sem_sop2.
    move: (sem_sop2_typed op); rewrite -> hty.
    t_xrbindP=> /= sem _ /to_wordI' [ws0 [w0 [hcmp0 -> ->]]]
      _ /to_wordI' [ws1 [w1 [hcmp1 -> ->]]] b ok_b <-.
    exists ws0, ws1, w0, w1, b; split=> //.
    move=> eq.
    have eq_dec := pair_eq_dec (pair_eq_dec atype_eqb_OK_sumbool atype_eqb_OK_sumbool) atype_eqb_OK_sumbool.
    by rewrite (Eqdep_dec.UIP_dec eq_dec eq erefl).
  move=> /= [ws0 [ws1 [w0 [w1 [b [hcmp0 hcmp1 ?? {}hsemop ->]]]]]]; subst v0 v1.

  (* default case: CMP *)
  have suff hdefault: Some (CMP, ws', pexpr_of_cf cf vi (fresh_flags fv), [:: e0; e1]) = Some (mn, ws, e, es).
  + move=> [<- <- <- <-].
    exists ws0, ws1, w0, w1; split=> //.
    + by rewrite /= hseme0 hseme1 /=.
    rewrite /= /get_gvar /=; repeat t_get_var => //.
    case: op hcf hsemop {h} => //= -[] // => [||[]|[]|[]|[]] _ [<- ->] /(_ erefl);
      rewrite /mk_sem_sop2 /sem_opN /= /sem_combine_flags /cf_xsem /NF_of_word /ZF_of_word /=
        1?wsub_wnot1
        1?nzcv_of_aluop_CF_sub
        1?wsigned_wsub_wnot1
        ?GRing.Theory.subr_eq0
        //
      => -[<-].

   (* Case [w0 == w1]. *)
   - done.

   (* Case [w0 != w1]. *)
   - done.

   (* Case [w0 <s w1]. *)
   - by rewrite wltsE.

   (* Case [w0 <u w1]. *)
   - by rewrite wleuE ltzE ltNge.

   (* Case [w0 <=s w1]. *)
   - by rewrite wlesE'.

   (* Case [w0 <=u w1]. *)
   - by rewrite wleuE'.

   (* Case [w0 >s w1]. *)
   - by rewrite wlesE' ltzE ltNge.

   (* Case [w0 >u w1]. *)
   - by rewrite wleuE' ltzE ltNge.

   (* Case [w0 >=s w1]. *)
   - by rewrite wltsE lezE leNgt.

   (* Case [w0 >=u w1]. *)
   by rewrite -word.wltuE lezE leNgt.

  case: op hcf hsemop h => // -[] //= _ [? ->] /(_ erefl) hsemop; subst cf.
  case hlower: lower_TST => [es'|//].
  (* special case: TST, [w00 & w01 == 0] *)
  move=> [<- <- <- <-].
  have [ws0' [e00 [e01 [ws1' [??]]]]] := lower_TST_match hlower; subst e0 e1.
  move: hlower => /= [<-].
  move: hseme0 hseme1; rewrite /= /sem_sop2 /sem_sop1 /=.
  apply: rbindP => v00 hseme00.
  apply: rbindP => v01 hseme01.
  apply: rbindP => _ /to_wordI' [ws00 [w00 [hcmp00 ? ->]]]; subst v00.
  apply: rbindP => _ /to_wordI' [ws01 [w01 [hcmp01 ? ->]]]; subst v01.
  move=> /ok_inj /Vword_inj [??] /ok_inj /Vword_inj [??]; subst ws0' ws1' w0 w1.
  move: hsemop; rewrite /mk_sem_sop2 /= wrepr0 zero_extend0 => -[<-].
  exists ws00, ws01, w00, w01; split=> //.
  + by apply (cmp_le_trans hcmp0 hcmp00).
  + by apply (cmp_le_trans hcmp0 hcmp01).
  + by rewrite hseme00 hseme01 /=.
  rewrite /get_gvar /=; repeat t_get_var => //.
  by rewrite /ZF_of_word /= -wand_zero_extend // !zero_extend_idem //.
Qed.

Lemma sem_lower_condition_pexpr vi tag s0 s0' ii e v lvs aop es c :
  lower_condition_pexpr fv vi e = Some (lvs, aop, es, c)
  -> eq_fv s0 s0'
  -> disj_fvars (read_e e)
  -> sem_pexpr true (p_globs p) s0 e = ok v
  -> exists s1',
       [/\ esem p' ev [:: MkI ii (Copn lvs tag aop es) ] s0' = ok s1'
         , eq_fv s0 s1'
         & sem_pexpr true (p_globs p) s1' c = ok v
       ].
Proof using atoI ev fv fv_correct p pT sCP sc_sem syscall_state warning wsw.
  apply: obindP => -[[op e0] e1] /is_Papp2P ?; subst.
  apply: obindP => -[[[mn ws] e] es'] h [????]; subst.

  move=> hs00 /disj_fvars_read_e_Papp2 [hfv0 hfv1] /=.
  t_xrbindP=> v0 hsem0 v1 hsem1 hsemop.

  have hsem0' := eeq_exc_sem_pexpr hfv0 hs00 hsem0.
  have hsem1' := eeq_exc_sem_pexpr hfv1 hs00 hsem1.
  clear hfv0 hsem0 hsem1 hfv1.

  have [ws0 [ws1 [w0 [w1 [hmn hws hws0 hws1 hsemes hseme]]]]] :=
    lower_condition_Papp2P h hsem0' hsem1' hsemop.
  clear h hsemop hsem0' hsem1'.

  have /= hsem' := sem_condition_mn ii vi tag hmn hws hws0 hws1 hsemes.
  clear hws0 hws1 hsemes.

  eexists;
    split;
    first exact: hsem';
    last exact: hseme.
  apply: (eeq_excT hs00).
  exact: (estate_of_condition_mn_eq_fv s0' _ _ hmn).
Qed.

Lemma sem_lower_condition vi s0 s0' ii e v pre e' :
  lower_condition fv vi e = (pre, e')
  -> eq_fv s0 s0'
  -> disj_fvars (read_e e)
  -> sem_pexpr true (p_globs p) s0 e = ok v
  -> exists s1',
       [/\ esem p' ev (map (MkI ii) pre) s0' = ok s1'
         , eq_fv s0 s1'
         & sem_pexpr true (p_globs p) s1' e' = ok v
       ].
Proof using atoI ev fv fv_correct p pT sCP sc_sem syscall_state warning wsw.
  move=> h hs00 hfv hseme.

  move: h.
  rewrite /lower_condition.
  case h: lower_condition_pexpr => [[[[lvs op] es] c]|] [? ?];
    subst e' pre.

  - exact: sem_lower_condition_pexpr h hs00 hfv hseme.
  clear h.

  exists s0'.
  split => //.

  exact: (eeq_exc_sem_pexpr hfv hs00 hseme).
Qed.


(* -------------------------------------------------------------------- *)
(* Lowering of assignments. *)

(* Note that the interpretation of the expression is [zero_extend ws w]
   due to the implicit castings in [sem]. *)
Lemma get_arg_shiftP s e ws v e' sh n :
  get_arg_shift ws [:: e ] = Some (e', sh, n)
  -> disj_fvars (read_e e)
  -> sem_pexpr true (p_globs p) s e = ok v
  -> exists ws1 (wbase : word ws1) (wsham : word U8),
       [/\ (ws <= ws1)%CMP
         , sem_pexpr true (p_globs p) s e' = ok (Vword wbase)
         , sem_pexpr true (p_globs p) s n = ok (Vword wsham)
         , to_word ws v
           = ok (shift_op sh (zero_extend ws wbase) (wunsigned wsham))
         & (disj_fvars (read_e e') /\ disj_fvars (read_e n))
       ].
Proof.
  move=> h hfve hseme.

  case: e hseme hfve h => // op.
  move=> [] //= gx.
  move=> [] //.
  move=> [[]|||||||] //.
  move=> [] // z.

  rewrite /=.
  t_xrbindP=> vbase hget hsemop.
  move=> hfve.

  apply: obindP => sh' hsh /oassertP [hchk [???]];
    subst e' sh' n.

  (* whatever [op] is, the type is the same: (aword ws, aword8, aword ws) *)
  have hty: type_of_op2 op = (aword ws, aword U8, aword ws).
  + move: hsh; rewrite /shift_of_sop2; apply: obindP => -[] _ /= hsh'.
    by case: (op) hsh' => //=;
      (try by move=> -[] //= ws'; case: (ws' =P ws) => // ->);
      move=> ws'; case: (ws' =P ws) => // ->.

  have: exists ws1 (wbase : word ws1) w,
    [/\ (ws <= ws1)%CMP,
        vbase = Vword wbase,
        forall eq : type_of_op2 op = (aword ws, aword U8, aword ws),
          ecast t (let t := t in _) eq (sem_sop2_typed op) (zero_extend ws wbase) (wrepr U8 z) = ok w &
        v = Vword w].
  + move: hsemop; rewrite /sem_sop2.
    move: (sem_sop2_typed op); rewrite -> hty.
    rewrite /= truncate_word_u.
    t_xrbindP=> sem _ /to_wordI' [ws1 [wbase [hcmp -> ->]]] _ <- w ok_w <-.
    exists ws1, wbase, w; split=> //.
    move=> eq.
    have eq_dec := pair_eq_dec (pair_eq_dec atype_eqb_OK_sumbool atype_eqb_OK_sumbool) atype_eqb_OK_sumbool.
    by rewrite (Eqdep_dec.UIP_dec eq_dec eq erefl).
  move=> /= [ws1 [wbase [w [hcmp ? {}hsemop ->]]]]; subst vbase.
  exists ws1, wbase, (wrepr U8 z); split=> //=.
  rewrite truncate_word_u.

  move: hsh; rewrite /shift_of_sop2; apply: obindP => -[] _ /= hsh.
  by case: op hty hsh hsemop {hfve} => //=;
    (try by move=> -[] //= ws' _; case: (ws' =P ws) => // -> -[<-] /(_ erefl));
    move=> ws' _; case: (ws' =P ws) => // -> -[<-] /(_ erefl).
Qed.

Lemma disj_fvars_read_es2 e0 e1 :
  disj_fvars (read_e e0)
  -> disj_fvars (read_e e1)
  -> disj_fvars (read_es [:: e0; e1 ]).
Proof.
  move=> h0 h1.
  apply: (disjoint_equal_r (read_eE _ _)).
  exact: (union_disjoint h1 h0).
Qed.

Lemma disj_fvars_read_es2_app2 e op x y :
  disj_fvars (read_e e)
  -> disj_fvars (read_e (Papp2 op x y))
  -> disj_fvars (read_es [:: x; y; e ]).
Proof.
  rewrite /disj_fvars {2}/read_e/= read_eE -/read_e => h0 /disjoint_union [] h1 h2.
  rewrite /read_es /= 2!read_eE.
  by repeat apply: union_disjoint.
Qed.

Lemma disj_fvars_read_es3 e0 e1 e2 :
  disj_fvars (read_e e0)
  -> disj_fvars (read_e e1)
  -> disj_fvars (read_e e2)
  -> disj_fvars (read_es [:: e0; e1; e2 ]).
Proof.
  move=> h0 h1 h2.
  apply: (disjoint_equal_r (read_eE _ _)).
  apply: (union_disjoint h2).
  apply: (disjoint_equal_r (read_eE _ _)).
  exact: (union_disjoint h1 h0).
Qed.

(* Invariant of [lower_pexpr_aux]: on AArch64 there are no conditionally
   executed operations, so contrary to AArch32 nothing about the
   instruction options needs to be tracked. *)
#[ local ]
Definition inv_lower_pexpr_aux
  (ws : wsize) (op : sopn) (es : seq pexpr) : Prop :=
  [/\ disj_fvars (read_es es)
    & sopn_tout op = [:: aword ws ]
  ].

(* We prove the following for each case of [lower_pexpr_aux]. *)
#[ local ]
Definition ok_lower_pexpr_aux
  (s : estate) (ws ws' : wsize) (op : sopn) (es : seq pexpr) (w : word ws') :
  Prop :=
  (exists2 vs,
     sem_pexprs true (p_globs p) s es = ok vs
     & exec_sopn op vs = ok [:: Vword (zero_extend ws w) ])
  /\ inv_lower_pexpr_aux ws op es.

#[ local ]
Definition Plower_pexpr_aux (e : pexpr) : Prop :=
  forall s ws ws' aop es (w : word ws'),
    lower_pexpr_aux ws e = Some (aop, es)
    -> (ws <= ws')%CMP
    -> disj_fvars (read_e e)
    -> sem_pexpr true (p_globs p) s e = ok (Vword w)
    -> ok_lower_pexpr_aux s ws aop es w.

Lemma lower_PvarP gx :
  Plower_pexpr_aux (Pvar gx).
Proof.
  move=> s ws ws' aop es w.
  move=> h hws hfvx /= hget.
  move: h.
  rewrite /lower_pexpr_aux /lower_Pvar /ok_lower_pexpr_aux.
  move=> /chk_ws_regP [hws' [? ?]]; subst aop es.
  case/orP: hws' => /eqP ?; subst ws.

  all: case: is_var_in_memory.

  all: split; last done.
  all: clear hfvx.

  all: rewrite /= hget {hget} /=.
  all: eexists; first reflexivity.
  all: rewrite /exec_sopn /=.
  all: rewrite truncate_word_le // {hws} /=.
  all: by rewrite ?zero_extend_u.
Qed.

Lemma lower_loadP e :
  match e with Pload _ _ _ | Pget _ _ _ _ _ => Plower_pexpr_aux e
  | _ => True end.
Proof.
  case: e => // [ al aa wsg x| al wsg] e s ws' ws'' aop es w.
  all: rewrite /lower_pexpr_aux /lower_load.
  all: move=> /chk_ws_regP [hwsx [??]] hws hfve; subst aop es.
  all: have hwsx' : (ws' == U32) || (ws' == U64) by rewrite orbC.
  all: rewrite /sem_pexpr -/(sem_pexpr _ _ s e).

  - apply: on_arr_gvarP => n t hty ok_t.
    apply: rbindP => idx.
    apply: rbindP => ? ok_idx /to_intI ?; subst.
    apply: rbindP => r ok_r /ok_inj /Vword_inj[] ??; subst => /=.
    split.
    + rewrite /= ok_t /= ok_idx /= ok_r /=.
      eexists; first reflexivity.
      rewrite /exec_sopn /sopn_sem /sopn_sem_ /= hwsx' /=.
      rewrite /semi_to_atype !computational_eq_refl /=.
      by rewrite truncate_word_le // /= zero_extend_u.
    done.

  t_xrbindP=> woff' voff hseme hoff wres hread ? hw;
    subst ws''.
  move: hoff => /to_wordI [ws1 [woff [? /truncate_wordP [hws1 ?]]]];
    subst woff' voff.
  move: hw => [?]; subst wres.

  split; last done.
  clear hfve.

  rewrite /sem_pexprs /=.
  rewrite hseme {hseme} /=.
  rewrite truncate_word_le // {hws1} /=.
  rewrite hread {hread} /=.

  eexists; first reflexivity.

  rewrite /exec_sopn /sopn_sem /sopn_sem_ /= hwsx' /=.
  rewrite /semi_to_atype !computational_eq_refl /=.
  rewrite truncate_word_le // {hws} /=.
  by rewrite zero_extend_u.
Qed.

Lemma lower_Papp1P op e:
  Plower_pexpr_aux (Papp1 op e).
Proof.
  move=> s ws ws' op' es w.
  move=> h hws hfve.

  rewrite /sem_pexpr -/(sem_pexpr _ _ s e).
  t_xrbindP=> v hseme hw.

  move: h.
  rewrite /lower_pexpr_aux /lower_Papp1.
  move=> /chk_ws_regP [hwsx h].
  have hwsx' : (ws == U32) || (ws == U64) by rewrite orbC.
  move: h.
  case: op hw hfve => [ ws'' || ws0 ws'' | ws0 ws'' || ws0 | [] // ws0 |] // hw hfve.

  (* Case: [Oword_of_int]. *)
  - move: hw => /sem_sop1I /= [w' [?] [hw' [?] hw]].
    move: hw => /Vword_inj [?]; subst ws'; subst.
    move=> /= ?; subst w.
    rewrite hws /= /mov_imm_op.
    {
      case: isSome => -[??]; subst op' es.
      all: split; last by split.
      all: eexists; first by rewrite /= hseme /= /sem_sop1 /= hw'.
      all: rewrite /exec_sopn /sopn_sem /sopn_sem_ /= ?hwsx' /=.
      all: rewrite /semi_to_atype ?computational_eq_refl /=.
      all: by rewrite truncate_word_u zero_extend_wrepr.
    }

  (* Case: [Osignext]. *)
  - move: hw => /sem_sop1I /= [w' [?] [hw' [?] hw]].
    move: hw => /Vword_inj [?]; subst ws'.
    move=> /= ?; subst.
    move=> /oassertP [/eqP ? h]; subst ws0.
    move: h => /oassertP [hlt h]; move: h.
    case: (is_load e);
      (apply: obindP => mn hmn [??]; subst op' es;
       case/orP: hwsx' => /eqP ?; subst ws;
       move: hmn; case: ws'' hlt hfve w' hw' => //= hlt hfve w' hw' [?]; subst mn;
       (split; last by split);
       clear hfve;
       rewrite /= hseme {hseme} /=;
       (eexists; first reflexivity);
       rewrite /exec_sopn /sopn_sem /sopn_sem_ /= hw' {hw'} /=;
       by rewrite /armv8a_extend_semi ?zero_extend_u).

  (* Case: [Ozeroext]. *)
  - move: hw => /sem_sop1I /= [w' [?] [hw' [?] hw]].
    move: hw => /Vword_inj [?]; subst ws'.
    move=> /= ?; subst.
    move=> /oassertP [/eqP ? h]; subst ws0.
    move: h => /oassertP [hlt h]; move: h.
    case: (is_load e);
      (apply: obindP => mn hmn [??]; subst op' es;
       case/orP: hwsx' => /eqP ?; subst ws;
       move: hmn; case: ws'' hlt hfve w' hw' => //= hlt hfve w' hw' [?]; subst mn;
       (split; last by split);
       clear hfve;
       rewrite /= hseme {hseme} /=;
       (eexists; first reflexivity);
       rewrite /exec_sopn /sopn_sem /sopn_sem_ /= hw' {hw'} /=;
       by rewrite /armv8a_extend_semi ?zero_extend_u).

  (* Case: [Olnot]. *)
  - move: hw => /sem_sop1I /= [w' [?] [hw' [?] hw]].
    move: hw => /Vword_inj [?]; subst ws'.
    move=> /= ?; subst.
    move=> /oassertP [/eqP ? h]; subst ws0; move: h.

    rewrite /arg_shift.
    case hshift: get_arg_shift => [[[e' sh] sham]|] /=;
      first case hallowed: (shift_allowed _ sh).

    (* Recognized, allowed shift: fused. *)
    + have [ws1 [wbase [wsham [hws1 hbase hsham hv [hfvbase hfvsham]]]]] :=
        get_arg_shiftP hshift hfve hseme.
      case/to_wordI': hv => wsv [] w'' []  hwsv ? hv; subst v.
      case/truncate_wordP: hw' => hws0 ?; subst w'.
      clear hshift hseme hfve.
      move=> [? ?]; subst op' es.
      have hfves := disj_fvars_read_es2 hfvbase hfvsham.
      clear hfvbase hfvsham.
      split; last by split.
      clear hfves.
      rewrite /=.
      rewrite hbase hsham {hbase hsham} /=.
      eexists; first reflexivity.
      rewrite /exec_sopn /sopn_sem /sopn_sem_ /= ?hwsx' /=.
      rewrite /semi_to_atype ?computational_eq_refl /=.
      rewrite !truncate_word_le // {hws1} /=.
      rewrite hallowed /=.
      by rewrite !zero_extend_u hv.

    (* Shift kind not allowed for this mnemonic: not fused. *)
    + move=> [? ?]; subst op' es;
      (split; last by split);
      rewrite /= hseme /=;
      (eexists; first reflexivity);
      rewrite /exec_sopn /sopn_sem /sopn_sem_ /= ?hwsx' /=;
      rewrite /semi_to_atype ?computational_eq_refl /=;
      by rewrite hw' /= zero_extend_u.

    (* No recognized shift: not fused. *)
    move=> [? ?]; subst op' es;
      (split; last by split);
      rewrite /= hseme /=;
      (eexists; first reflexivity);
      rewrite /exec_sopn /sopn_sem /sopn_sem_ /= ?hwsx' /=;
      rewrite /semi_to_atype ?computational_eq_refl /=;
      by rewrite hw' /= zero_extend_u.

  (* Case: [Oneg]. *)
  move: hw => /sem_sop1I /= [w' [?] [hw' [?] hw]].
  move: hw => /Vword_inj [?]; subst ws'.
  move=> /= ?; subst.
  move=> /oassertP [/eqP ? h]; subst ws0; move: h.

  rewrite /arg_shift.
  case hshift: get_arg_shift => [[[e' sh] sham]|] /=;
    first case hallowed: (shift_allowed _ sh).

  (* Recognized, allowed shift: fused. *)
  + have [ws1 [wbase [wsham [hws1 hbase hsham hv [hfvbase hfvsham]]]]] :=
      get_arg_shiftP hshift hfve hseme.
    case/to_wordI': hv => wsv [] w'' []  hwsv ? hv; subst v.
    case/truncate_wordP: hw' => hws0 ?; subst w'.
    clear hshift hseme hfve.
    move=> [? ?]; subst op' es.
    have hfves := disj_fvars_read_es2 hfvbase hfvsham.
    clear hfvbase hfvsham.
    split; last by split.
    clear hfves.
    rewrite /=.
    rewrite hbase hsham {hbase hsham} /=.
    eexists; first reflexivity.
    rewrite /exec_sopn /sopn_sem /sopn_sem_ /= ?hwsx' /=.
    rewrite /semi_to_atype ?computational_eq_refl /=.
    rewrite !truncate_word_le // {hws1} /=.
    rewrite hallowed /=.
    rewrite /armv8a_NEG_semi.
    by rewrite !zero_extend_u hv add_wordE wnot1_wopp.

  (* Shift kind not allowed for this mnemonic: not fused. *)
  + move=> [? ?]; subst op' es;
    (split; last by split);
    rewrite /= hseme /=;
    (eexists; first reflexivity);
    rewrite /exec_sopn /sopn_sem /sopn_sem_ /= ?hwsx' /=;
    rewrite /semi_to_atype ?computational_eq_refl /=;
    rewrite hw' /= zero_extend_u /armv8a_NEG_semi;
    by rewrite add_wordE wnot1_wopp.

  (* No recognized shift: not fused. *)
  move=> [? ?]; subst op' es;
    (split; last by split);
    rewrite /= hseme /=;
    (eexists; first reflexivity);
    rewrite /exec_sopn /sopn_sem /sopn_sem_ /= ?hwsx' /=;
    rewrite /semi_to_atype ?computational_eq_refl /=;
    rewrite hw' /= zero_extend_u /armv8a_NEG_semi;
    by rewrite add_wordE wnot1_wopp.
Qed.

Lemma mk_sem_divmodP si ws op (w0 w1 : word ws) w :
  mk_sem_divmod si op w0 w1 = ok w
  -> [/\ (w1 <> 0%R)
       , si <> Signed \/ (wsigned w0 <> wmin_signed ws) \/ (w1 <> (-1)%R)
       & w = op w0 w1
     ].
Proof.
  rewrite /mk_sem_divmod.
  case: ifPn => //; rewrite negb_or => /andP [] /eqP ? h [<-]; split => //.
  move: h; rewrite !negb_and => /or3P [] /eqP; auto.
Qed.

Section IS_MUL.

Variant is_mul_spec (ws : wsize) (e: pexpr) : option (pexpr * pexpr) -> Type :=
  | IsMulSome ws' x y :
      (ws <= ws')%CMP
      -> e = Papp2 (Omul (Op_w ws')) x y
      -> is_mul_spec (Some (x, y))
  | IsMulNone : is_mul_spec None.

#[local] Hint Constructors is_mul_spec : core.

Lemma is_mulP ws e : is_mul_spec ws e (is_mul ws e).
Proof.
  rewrite /is_mul.
  case: e; try (move=> *; exact: IsMulNone).
  move=> op e1 e2.
  case: op; try (move=> *; exact: IsMulNone).
  move=> c; case: c; try (move=> *; exact: IsMulNone).
  move=> ws'.
  case hle: (ws <= ws')%CMP; last exact: IsMulNone.
  exact: (IsMulSome hle erefl).
Qed.

End IS_MUL.

(* The main consequence of the lemmas in this section is lemma [lower_base_op].
   It was moved far from it, because we also use [with_shift_binop]
   in the proof of [lower_Papp2P]. *)
Section WITH_SHIFT_OP.

#[ local ]
Ltac intro_opn_args :=
  rewrite /sem_tuple /=;
  repeat
    match goal with
    | [ |- forall (_ : _ * _), _ ] => move=> []
    | [ |- forall (_ : option bool), _ ] => move=> ?
    | [ |- forall (_ : word _), _ ] => move=> ?
    end.

#[local]
Ltac intro_args_wrapper :=
  intro_opn_args;
  rewrite !truncate_word_le // => -> _ /ok_inj <-.

#[local]
Ltac destruct_args_wrapper vs :=
  move: vs;
  destruct_opn_args;
  repeat (move=> ? ->).

(* Rewrite result of execution. If we are under conditional execution, find
   the condition and case on it, the case when the instruction is not
   executiod is trivial.
   We can't match on [sopn_sem] because of the dependent types. *)
#[local]
Ltac rewrite_exec :=
  let h := fresh "h" in
  move=> /= h ?;
  subst;
  move: h;
  (move=> /ok_inj; (move=> <- || move=> [] *; subst));
  rewrite /= !zero_extend_u.

Lemma with_shift_unop mn s eb ea ts (b: word ts) (a: u8) x vs sh opts r :
  mn \in [:: MVN; NEG ] ->
  shift_allowed mn sh ->
  (opts_size opts ≤ ts)%CMP ->
  has_shift opts = None ->
  sem_pexpr true (p_globs p) s eb = ok (Vword b) ->
  sem_pexpr true (p_globs p) s ea = ok (Vword a) ->
  to_word (opts_size opts) x
    = ok (shift_op sh (zero_extend (opts_size opts) b) (wunsigned a)) ->
  exec_sopn (Oasm (BaseOp (None, ARMv8A_op mn opts))) [:: x & vs] = ok r ->
  exec_sopn (Oasm (BaseOp (None, ARMv8A_op mn (with_shift opts sh) ))) [:: Vword b, Vword a & vs] = ok r.
Proof.
  rewrite !inE.
  case: opts => sho sz /= mn_unop hallow hts -> ok_b ok_a hx.
  move: hallow.
  case/orP: mn_unop => /eqP -> {mn}.
  all: move=> /= hallow.
  all: rewrite /exec_sopn /sopn_sem /sopn_sem_ /=.
  all: t_xrbindP => ha hvalid hsemi z0 z1 hz1 hmatch heq.
  all: subst ha.
  all: move: hz1; rewrite hx => -[?]; subst z1.
  all: move: hmatch; case: vs => //= hmatch.
  all: move: hmatch;
    rewrite /semi_to_atype !computational_eq_refl /= => -[?]; subst z0.
  all: rewrite hvalid hallow /=.
  all: rewrite (truncate_word_le _ hts) truncate_word_u /= /mk_semi1_shifted /=.
  all: by rewrite -heq.
Qed.

Lemma with_shift_binop mn s eb ea ts (b: word ts) (a: u8) x y vs sh opts r :
  mn \in [:: ADD; ADDS; SUB; SUBS; AND; EOR; ORR; CMP; TST] ->
  shift_allowed mn sh ->
  (opts_size opts ≤ ts)%CMP ->
  has_shift opts = None ->
  sem_pexpr true (p_globs p) s eb = ok (Vword b) ->
  sem_pexpr true (p_globs p) s ea = ok (Vword a) ->
  to_word (opts_size opts) y
    = ok (shift_op sh (zero_extend (opts_size opts) b) (wunsigned a)) ->
  exec_sopn (Oasm (BaseOp (None, ARMv8A_op mn opts))) [:: x, y & vs] = ok r ->
  exec_sopn (Oasm (BaseOp (None, ARMv8A_op mn (with_shift opts sh) ))) [:: x, Vword b, Vword a & vs] = ok r.
Proof.
  rewrite !inE.
  case: opts => sho sz /= mn_binop hallow hts -> ok_b ok_a hy.
  move: hallow.
  repeat case/orP: mn_binop => [ /eqP -> { mn } | mn_binop ]; last move/eqP: mn_binop => -> { mn }.
  all: move=> /= hallow.
  all: rewrite /exec_sopn /sopn_sem /sopn_sem_ /=.
  all: t_xrbindP => ha hvalid hsemi z0 z1 hzx z2 hzy hmatch heq.
  all: subst ha.
  all: move: hzy; rewrite hy => -[?]; subst z2.
  all: move: hmatch; case: vs => //=.
  all: rewrite /semi_to_atype !computational_eq_refl /= => -[?]; subst z0.
  all: rewrite hvalid hallow /=.
  all: rewrite hzx (truncate_word_le _ hts) truncate_word_u /= /mk_semi2_2_shifted /=.
  all: by rewrite heq.
Qed.

End WITH_SHIFT_OP.

(* changing the shift component preserves the output type *)
Lemma sopn_tout_with_shift mn opts sk :
  id_tout (mn_desc (with_shift opts sk) mn) = id_tout (mn_desc opts mn).
Proof.
  case: opts => sho sz.
  by case: sho => [sk'|]; case: mn => //=.
Qed.

(* The rotate-left-to-rotate-right amount conversion: rotating right by
   [wsize - c] (computed on u8, where the subtraction may wrap) is rotating
   left by [c], modulo the operand size. Wrapping is harmless because the
   u8 base (256) is a multiple of both operand sizes (32 and 64). *)
Lemma u8_sub_amount_mod (wb : Z) (x1 : word U8) :
  (0 <= wb < wbase U8)%Z ->
  (wbase U8 mod wb = 0)%Z ->
  (wunsigned (wrepr U8 wb - x1)%R mod wb)%Z = ((wb - wunsigned x1) mod wb)%Z.
Proof.
  move=> hwb hdvd.
  rewrite wunsigned_sub_if wunsigned_repr_small //.
  case: ifP => _; first by [].
  by rewrite -Z.add_sub_assoc Zplus_mod hdvd Z.add_0_l Zmod_mod.
Qed.

Lemma rol_ror_shift_amount ws (x1 : word U8) :
  (ws == U64) || (ws == U32)
  -> (wunsigned (wrepr U8 (wsize_bits ws) - x1)%w mod wsize_bits ws)%Z
     = ((wsize_bits ws - wunsigned x1) mod wsize_bits ws)%Z.
Proof. by case/orP => /eqP ->; rewrite sub_wordE u8_sub_amount_mod. Qed.

(* TODO: factorize with x86/riscv *)
Lemma to_word_m sz sz' a w :
  to_word sz a = ok w ->
  (sz' <= sz)%CMP ->
  to_word sz' a = ok (zero_extend sz' w).
Proof.
  clear.
  case/to_wordI' => n [] m [] sz_le_n ->{a} ->{w} /= sz'_le_sz.
  by rewrite truncate_word_le ?zero_extend_idem // (cmp_le_trans sz'_le_sz sz_le_n).
Qed.

(* Masking a u8 word with [wsize_bits - 1] is reduction modulo the operand
   size, for the two register widths. *)
Lemma wand_mask_mod ws (x : word U8) :
  (ws == U64) || (ws == U32)
  -> wunsigned (wand x (wrepr U8 (wsize_bits ws - 1)))
     = (wunsigned x mod wsize_bits ws)%Z.
Proof.
  by case/orP => /eqP ->; [ exact: (wand_modulo x 6) | exact: (wand_modulo x 5) ].
Qed.

(* An accepted shift amount evaluates, modulo the operand size, to the same
   value as the original expression; and reading it needs no new variables. *)
Lemma check_shift_exprP ws e e' s v w :
  check_shift_expr ws e = Some e'
  -> (ws == U64) || (ws == U32)
  -> sem_pexpr true (p_globs p) s e = ok v
  -> to_word U8 v = ok w
  -> [/\ Sv.Subset (read_e e') (read_e e)
       & exists v' (w' : word U8),
           [/\ sem_pexpr true (p_globs p) s e' = ok v'
             , to_word U8 v' = ok w'
             & wunsigned w = (wunsigned w' mod wsize_bits ws)%Z ] ].
Proof.
  rewrite /check_shift_expr => h hws; move: h.
  case en: is_wconst => [ n | ].
  - case: eqP => [n_in_range|//] [<-] ok_v ok_w.
    split; first by [].
    exists v, w; split=> //.
    assert (hn := is_wconstP true (p_globs p) s en).
    move: hn; rewrite ok_v /= ok_w => -[?]; subst n.
    by rewrite {1}n_in_range (wand_mask_mod _ hws).
  case: {en} e => // -[] // sz' a b.
  case en: is_wconst => [ n | ]; last by [].
  case: eqP => [?|//]; subst n.
  move=> [<-] /=.
  rewrite /sem_sop2 /=.
  t_xrbindP=> va ok_a vb ok_b wa ok_wa wb ok_wb <-{v} ok_w.
  split.
  - clear; rewrite {2}/read_e /= !read_eE; SvD.fsetdec.
  assert (hb := is_wconstP true (p_globs p) s en).
  move: hb; rewrite ok_b /= => hb.
  exists va, (zero_extend U8 wa); split=> //.
  - exact: (to_word_m ok_wa (wsize_le_U8 _)).
  move: ok_w => /truncate_wordP [_ ->].
  rewrite -wand_zero_extend; last exact: wsize_le_U8.
  have hwb : zero_extend U8 wb = wrepr U8 (wsize_bits ws - 1).
  - have h' := to_word_m ok_wb (wsize_le_U8 _).
    move: h'; rewrite hb => h'.
    exact: (esym (ok_inj h')).
  rewrite hwb.
  by rewrite (wand_mask_mod _ hws).
Qed.

Lemma large_arith_immP ws mn es imm :
  large_arith_imm ws mn es = Some imm
  -> [/\ ws = U64
       , mn \in [:: ADD; SUB ]
       & exists2 e, es = [:: e ]
         & exists2 c : word U64,
             is_wconst U64 e = Some c
             & imm = (if mn == ADD then wunsigned c else - wunsigned c)%Z ].
Proof.
  rewrite /large_arith_imm.
  move=> /oassertP [/eqP hws h]; move: h.
  apply: obindP => e he.
  apply: obindP => c hc.
  case: ifP => // _.
  case: mn => // -[<-];
    (split=> //; exists e; first by case: es he => // ? [|//] [->]);
    by exists c.
Qed.

Lemma lower_Papp2P op e0 e1 :
  Plower_pexpr_aux (Papp2 op e0 e1).
Proof.
  move=> s ws ws' op' es w.
  move=> h hws hfve hseme.

  move: hseme.
  rewrite /sem_pexpr -!/(sem_pexpr _ _ s _).
  t_xrbindP=> v0 hseme0 v1 hseme1 hsemop.

  move: hfve => /disj_fvars_read_e_Papp2 [hfve0 hfve1].

  move: h.
  rewrite /= /lower_Papp2.

  apply: obindP => -[[mn' e0'] e1'] /chk_ws_regP [hwsx hop].

  (* the default case: there is no arg shift *)
  have hdflt:
    let dflt_op := Oasm (BaseOp (None, ARMv8A_op mn' (opts_at ws))) in
    ok_lower_pexpr_aux s ws dflt_op (e0' :: e1') w.
  {
    case: op hop hsemop => //;
      rewrite /lower_Papp2_op /=.

    all:
      match goal with
      | [ |- forall _ : op_kind, _ -> _ ] => move=> [|ws''] //
      | [ |- forall (_ : cmp_kind), _ -> _ ] => move=> [|[] ws''] //
      | [ |- forall (_ : signedness) (_ : op_kind), _ -> _ ] => move=> [] [|ws''] //
      | [ |- forall _ : wsize, _ -> _ ] => move=> ws'' //
      end.

    (* Resolve the mnemonic: peel the [oassert (ws'' == ws)] (forcing
       [ws'' = ws]), split the [is_mul] / [is_wconst] / [if] choices. *)
    all: repeat first
      [ move=> /oassertP [/eqP ?]; subst ws''
      | match goal with
        | [ |- context[ is_mul ] ] =>
            case: is_mulP => [wsm ? ? hlem ?|]; subst
        end
      | match goal with
        | [ |- context[ is_wconst ] ] => case hconst: is_wconst => [c|//]
        end
      ].
    all: repeat (match goal with |- context[ if _ then _ else _ ] => case: ifP => hif end).
    all: try (match goal with
              | [ |- context[ check_shift_expr ] ] =>
                  apply: obindP => amt hchk
              end).

    all: move=> [???] hsemop; subst mn' e0' e1'.
    all: first
      [ (* Plain binary ops: ADD, SUB, MUL, AND, ORR, EOR. *)
        lazymatch goal with
        | [ |- context[ARMv8A_op ADD _] ] => idtac
        | [ |- context[ARMv8A_op SUB _] ] => idtac
        | [ |- context[ARMv8A_op MUL _] ] => idtac
        | [ |- context[ARMv8A_op AND _] ] => idtac
        | [ |- context[ARMv8A_op ORR _] ] => idtac
        | [ |- context[ARMv8A_op EOR _] ] => idtac
        end;
        move: hsemop => /sem_sop2I /= [w0' [w1' [w2 [hw0 hw1 hop hw]]]];
        move: hw0 => /to_wordI [ws0 [w0 [? /truncate_wordP [hws0 ?]]]]; subst v0 w0';
        move: hw1 => /to_wordI [ws1 [w1 [? /truncate_wordP [hws1 ?]]]]; subst v1 w1';
        move: hop => [?]; subst w2;
        move: hw => /Vword_inj [?]; subst ws'; move=> /= ?; subst w;
        (split;
          last (split; [ exact: (disj_fvars_read_es2 hfve0 hfve1) | by [] ]));
        (exists [:: Vword w0; Vword w1];
          first by rewrite /sem_pexprs /= hseme0 hseme1 /=);
        move: (hwsx); rewrite orbC => hval;
        rewrite /exec_sopn /sopn_sem /sopn_sem_ /= hval /=;
        rewrite !(truncate_word_le _ (cmp_le_trans hws _)) //;
        rewrite /semi_to_atype !computational_eq_refl /=;
        rewrite /armv8a_ADD_semi /armv8a_SUB_semi /armv8a_MUL_semi /armv8a_bitwise_semi /=;
        rewrite ?add_wordE ?sub_wordE;
        rewrite ?(wadd_zero_extend _ _ hws) ?(wsub_zero_extend _ _ hws)
                ?(wmul_zero_extend _ _ hws)
                -?(wand_zero_extend _ _ hws)
                -?(wor_zero_extend _ _ hws) -?(wxor_zero_extend _ _ hws);
        rewrite ?(wopp_zero_extend _ hws) ?(zero_extend_idem _ hws);
        by rewrite ?(zero_extend_idem _ hws)
      | (* Division: SDIV, UDIV (operate at [ws''= ws]). *)
        lazymatch goal with
        | [ |- context[ARMv8A_op SDIV _] ] => idtac
        | [ |- context[ARMv8A_op UDIV _] ] => idtac
        end;
        move: hsemop => /sem_sop2I /= [w0' [w1' [w2 [hw0 hw1 hop hw]]]];
        move: hw0 => /to_wordI [ws0 [w0 [? /truncate_wordP [hws0 ?]]]]; subst v0 w0';
        move: hw1 => /to_wordI [ws1 [w1 [? /truncate_wordP [hws1 ?]]]]; subst v1 w1';
        move: hop => /mk_sem_divmodP [hdiv0 hdiv1 ?]; subst w2;
        move: hw => /Vword_inj [?]; subst ws'; move=> /= ?; subst w;
        (split;
          last (split; [ exact: (disj_fvars_read_es2 hfve0 hfve1) | by [] ]));
        (exists [:: Vword w0; Vword w1];
          first by rewrite /sem_pexprs /= hseme0 hseme1 /=);
        move: (hwsx); rewrite orbC => hval;
        rewrite /exec_sopn /sopn_sem /sopn_sem_ /= hval /=;
        rewrite !(truncate_word_le _ (cmp_le_trans hws _)) //;
        rewrite /semi_to_atype !computational_eq_refl /=;
        rewrite /armv8a_SDIV_semi /armv8a_UDIV_semi;
        by rewrite zero_extend_u
      | (* TODO(armv8a): remaining hdflt classes.
           - MADD / MSUB (from [is_mul] rewriting of Oadd / Osub): 3-operand
             arithmetic, need to evaluate the [is_mul] subexpressions and use
             commutativity of [+]/[-] with the [w*w] product.
           - MOV (degenerate shift-by-zero from Olsr/Olsl/Oasr/Oror with
             [is_zero e1], and Orol with the rotation constant 0): identity.
           - LSR / LSL / ASR / ROR (non-zero variable shift) and the
             Orol-with-nonzero-constant ROR: BLOCKED by a semantic mismatch.
             [armv8a_shift_semi] reduces the shift amount by [_ mod wsize_bits],
             whereas Jasmin's source [wshr]/[wsar]/[wshl]/[wror] clamp it via
             [Z.min (wsize_bits ws) _]. For a u8 shift amount >= wsize_bits the
             two disagree (source yields 0, armv8a yields a nonzero rotate/shift
             of [amount mod wsize_bits]). [arm_shift_semi] uses the raw amount,
             so arm has no such gap. This must be reconciled in the instruction
             model (clamp instead of mod, or guard the shift amount in the
             lowering) is now provable for constant in-range amounts. *)
        lazymatch goal with
        | [ |- context[ARMv8A_op LSR _] ] => idtac
        | [ |- context[ARMv8A_op LSL _] ] => idtac
        | [ |- context[ARMv8A_op ASR _] ] => idtac
        end;
        move: hsemop => /sem_sop2I /= [x0 [x1 [w2 [hx0 hx1 hop hw]]]];
        move: hop => [?]; subst w2;
        move: hw => /Vword_inj [?]; subst ws'; move=> /= ?; subst w;
        have [hsub [v1' [w1' [hsem1' hw1' heq]]]] :=
          check_shift_exprP hchk hwsx hseme1 hx1;
        (split;
          last (split;
            [ apply: (disj_fvars_read_es2 hfve0);
              exact: (disjoint_w hsub hfve1)
            | by [] ]));
        (exists [:: v0; v1'];
          first by rewrite /sem_pexprs /= hseme0 hsem1' /=);
        move: (hwsx); rewrite orbC => hval;
        rewrite /exec_sopn /sopn_sem /sopn_sem_ /= hval /= hx0 hw1' /=;
        rewrite /semi_to_atype !computational_eq_refl /=;
        rewrite /armv8a_shift_semi -heq;
        by rewrite /sem_shr /sem_shl /sem_sar /sem_shift zero_extend_u
      | (* MOV: a shift or rotate by zero, i.e. the identity. *)
        lazymatch goal with
        | [ |- context[ARMv8A_op MOV _] ] => idtac
        end;
        move: hsemop => /sem_sop2I /= [x0 [x1 [w2 [hx0 hx1 hop hw]]]];
        move: hop => [?]; subst w2;
        move: hw => /Vword_inj [?]; subst ws'; move=> /= ?; subst w;
        (* Pin the shift amount [x1] to zero. *)
        first
          [ assert (hwc := is_wconstP true (p_globs p) s hconst);
            move/eqP: hif => ?; subst c;
            move: hwc; rewrite hseme1 /= hx1 => -[?]; subst x1
          | move/is_zeroP: hif => ?; subst e1;
            move: hseme1; rewrite /= /sem_sop1 /= => -[?]; subst v1;
            move: hx1; rewrite /= truncate_word_u => -[?]; subst x1
          ];
        (split; last (split; [ exact: hfve0 | by [] ]));
        (exists [:: v0 ]; first by rewrite /sem_pexprs /= hseme0 /=);
        move: (hwsx); rewrite orbC => hval;
        rewrite /exec_sopn /sopn_sem /sopn_sem_ /= hval /= hx0 /=;
        rewrite /semi_to_atype !computational_eq_refl /=;
        rewrite /armv8a_MOV_semi
          /sem_shr /sem_shl /sem_sar /sem_ror /sem_rol /sem_shift
          ?wrepr0 wunsigned0 ?wshr0 ?wshl0 ?wsar0 ?wror0 ?wrol0;
        by rewrite zero_extend_u
      | (* ROR from [Oror] (variable rotate): rotation is periodic, so the
           [mod] in [armv8a_shift_semi] is harmless. *)
        lazymatch goal with
        | [ _ : sem_sop2 (Oror _) _ _ = ok _ |- context[ARMv8A_op ROR _] ] =>
            idtac
        end;
        move: hsemop => /sem_sop2I /= [x0 [x1 [w2 [hx0 hx1 hop hw]]]];
        move: hop => [?]; subst w2;
        move: hw => /Vword_inj [?]; subst ws'; move=> /= ?; subst w;
        (split;
          last (split;
            [ exact: (disj_fvars_read_es2 hfve0 hfve1) | by [] ]));
        (exists [:: v0; v1 ];
          first by rewrite /sem_pexprs /= hseme0 hseme1 /=);
        move: (hwsx); rewrite orbC => hval;
        rewrite /exec_sopn /sopn_sem /sopn_sem_ /= hval /= hx0 hx1 /=;
        rewrite /semi_to_atype !computational_eq_refl /=;
        rewrite /armv8a_shift_semi /sem_ror /sem_shift zero_extend_u;
        do 3 f_equal; apply: wror_m;
        by rewrite Zmod_mod
      | (* ROR from [Orol]: a rotate left by [c] is a rotate right by
           [wsize - c]. *)
        lazymatch goal with
        | [ _ : sem_sop2 (Orol _) _ _ = ok _ |- context[ARMv8A_op ROR _] ] =>
            idtac
        end;
        move: hsemop => /sem_sop2I /= [x0 [x1 [w2 [hx0 hx1 hop hw]]]];
        move: hop => [?]; subst w2;
        move: hw => /Vword_inj [?]; subst ws'; move=> /= ?; subst w;
        assert (hwc := is_wconstP true (p_globs p) s hconst);
        move: hwc; rewrite hseme1 /= hx1 => -[?]; subst c;
        (split; last (split; [ exact: hfve0 | by [] ]));
        (eexists; first by rewrite /sem_pexprs /= hseme0 /=);
        move: (hwsx); rewrite orbC => hval;
        rewrite /exec_sopn /sopn_sem /sopn_sem_ /= hval /= hx0 /=;
        rewrite truncate_word_u /=;
        rewrite /semi_to_atype !computational_eq_refl /=;
        rewrite /armv8a_shift_semi wrepr_unsigned /sem_rol /sem_shift
          zero_extend_u -wror_opp;
        do 3 f_equal; apply: wror_m;
        rewrite Zmod_mod;
        by apply: rol_ror_shift_amount
      | (* MADD/MSUB: fused multiply-add/subtract from [is_mul]. *)
        lazymatch goal with
        | [ |- context[ARMv8A_op MADD _] ] => idtac
        | [ |- context[ARMv8A_op MSUB _] ] => idtac
        end;
        (* Evaluate the [is_mul] product subexpression. *)
        let t0 := type of hseme0 in
        lazymatch t0 with
        | sem_pexpr _ _ _ (Papp2 (Omul _) _ _) = _ =>
            move: hseme0 => /=;
            t_xrbindP=> vx hsemx vy hsemy;
            rewrite /sem_sop2 /=;
            t_xrbindP=> wx hwx wy hwy ?; subst v0
        | _ =>
            move: hseme1 => /=;
            t_xrbindP=> vx hsemx vy hsemy;
            rewrite /sem_sop2 /=;
            t_xrbindP=> wx hwx wy hwy ?; subst v1
        end;
        move: hsemop => /sem_sop2I /= [x0 [x1 [w2 [hx0 hx1 hop hw]]]];
        move: hop => [?]; subst w2;
        move: hw => /Vword_inj [?]; subst ws'; move=> /= ?; subst w;
        (* The product is at width [wsm >= ws] (from [is_mul]), the outer
           operation at [ws'' >= ws]: only the low [ws] bits are kept, so
           the widths need not coincide and the zero extensions distribute
           over the operations. *)
        (first
          [ move: hx0; rewrite /= => /truncate_wordP [hle ?]; subst x0;
            rename hx1 into haddend
          | move: hx1; rewrite /= => /truncate_wordP [hle ?]; subst x1;
            rename hx0 into haddend ]);
        (split;
          last (split;
            [ first
                [ exact: (disj_fvars_read_es2_app2 hfve1 hfve0)
                | exact: (disj_fvars_read_es2_app2 hfve0 hfve1) ]
            | by [] ]));
        (eexists;
          first by rewrite /sem_pexprs /= hsemx hsemy ?hseme0 ?hseme1 /=);
        move: (hwsx); rewrite orbC => hval;
        rewrite /exec_sopn /sopn_sem /sopn_sem_ /= hval /=
          (to_word_m hwx hlem) (to_word_m hwy hlem) (to_word_m haddend hws) /=;
        rewrite /semi_to_atype !computational_eq_refl /=;
        rewrite /armv8a_MADD_semi /armv8a_MSUB_semi
          ?add_wordE ?sub_wordE ?mul_wordE
          ?(wadd_zero_extend _ _ hws) ?(wsub_zero_extend _ _ hws)
          ?(wopp_zero_extend _ hws) ?(zero_extend_idem _ hws)
          ?(wmul_zero_extend _ _ hlem) ?zero_extend_u;
        first [ by [] | by rewrite GRing.addrC ] ].
  }

  case hlarge: (large_arith_imm ws mn' e1') => [imm|]; last first.

  (* No large immediate: the [arg_shift] path. *)
  - rewrite /arg_shift /=.
    case hhas_shift: (mn' \in has_shift_mnemonics); last by move=> [<- <-].
    case hget_arg_shift: get_arg_shift => [[[b' sh] n]|]; last by move=> [<- <-].
    case hallowed: (shift_allowed mn' sh); last by move=> [<- <-].
    (* special case: there is some arg shift *)
    move=> [<- <-].
    (* we want to use with_shift_binop, so we have to prove this *)
    have hshift_binop:
      mn' \in [:: ADD; ADDS; SUB; SUBS; AND; EOR; ORR; CMP; TST].
    {
      case: op hop hhas_shift hsemop => //;
        rewrite /lower_Papp2_op /=.
      all:
        match goal with
        | [ |- forall _ : op_kind, _ -> _ ] => move=> [|ws''] //
        | [ |- forall (_ : cmp_kind), _ -> _ ] => move=> [|[] ws''] //
        | [ |- forall (_ : signedness) (_ : op_kind), _ -> _ ] => move=> [] [|ws''] //
        | [ |- forall _ : wsize, _ -> _ ] => move=> ws'' //
        end.
      all: repeat first
        [ move=> /oassertP [/eqP ?]; subst ws''
        | match goal with
          | [ |- context[ is_mul ] ] => case: is_mulP => [? ? ? ? ?|]; subst
          end
        | match goal with
          | [ |- context[ is_wconst ] ] => case hc': is_wconst => [c'|//]
          end
        ].
      all: repeat (match goal with |- context[ if _ then _ else _ ] => case: ifP => _ end).
      all: try (match goal with
                | [ |- context[ check_shift_expr ] ] =>
                    apply: obindP => ? ?
                end).
      all: by move=> [<- _ _].
    }
    move: hdflt => [[vs ok_vs hsopn] [hfv htout]].
    have: exists e1'', e1' = [:: e1'' ].
    + move: hget_arg_shift; rewrite /get_arg_shift.
      case: (e1') => // -[] // ? [] // ? [] // [] // [] // [] // ? [] //.
      move=> _.
      by eexists; reflexivity.
    move=> [e1'' ?]; subst e1'.
    have hfve1'': disj_fvars (read_e e1'').
    + by apply: disjoint_w hfv; clear; rewrite !read_es_cons /=; SvD.fsetdec.
    move: ok_vs => /=.
    t_xrbindP => v0' ok_v0' _ v1'' ok_v1'' <- ?; subst vs.
    have [ws1 [wbase [wsham [hcmp1 hbase hsham hw1'' [hfvbase hfvsham]]]]] :=
      get_arg_shiftP hget_arg_shift hfve1'' ok_v1''.
    split.
    + rewrite /= ok_v0' hbase hsham /=.
      eexists; first by reflexivity.
      by apply (with_shift_binop (opts := opts_at ws) hshift_binop hallowed hcmp1 erefl hbase hsham hw1'' hsopn).
    split.
    + apply disj_fvars_read_es3 => //.
      by apply: disjoint_w hfv; clear; rewrite !read_es_cons /=; SvD.fsetdec.
    by move: htout; rewrite /sopn_tout /= (sopn_tout_with_shift mn' (opts_at ws) sh).

  (* Large 64-bit immediate: through [Oarmv8a_add_large_imm]. *)
  move=> [<- <-] {hdflt}.
  case: op hop hsemop => //;
    rewrite /lower_Papp2_op /=.
  all:
    match goal with
    | [ |- forall _ : op_kind, _ -> _ ] => move=> [|ws''] //
    | [ |- forall (_ : cmp_kind), _ -> _ ] => move=> [|[] ws''] //
    | [ |- forall (_ : signedness) (_ : op_kind), _ -> _ ] => move=> [] [|ws''] //
    | [ |- forall _ : wsize, _ -> _ ] => move=> ws'' //
    end.
  all: repeat first
    [ move=> /oassertP [/eqP ?]; subst ws''
    | match goal with
      | [ |- context[ is_mul ] ] => case: is_mulP => [? ? ? ? ?|]; subst
      end
    | match goal with
      | [ |- context[ is_wconst ] ] => case hconst: is_wconst => [c'|//]
      end
    ].
  all: repeat (match goal with |- context[ if _ then _ else _ ] => case: ifP => hif end).
  all: try (match goal with
            | [ |- context[ check_shift_expr ] ] =>
                apply: obindP => amt hchk
            end).
  all: move=> [???] hsemop; subst mn' e0' e1'.
  all: have [? hmns [e he1' [c hc himm]]] := large_arith_immP hlarge.
  all: try (exfalso; exact: (Bool.diff_false_true hmns)).
  all: subst ws.
  all: move: he1' => [?]; subst e.
  all: move: himm; rewrite /= => ?; subst imm.
  all: move: hsemop => /sem_sop2I /= [x0 [x1 [w2 [hx0 hx1 hop2 hw]]]].
  all: move: hop2 => [?]; subst w2.
  all: move: hw => /Vword_inj [?]; subst ws'; move=> /= ?; subst w.
  all: move: hx0 => /to_wordI [ws0 [w0 [? /truncate_wordP [hws0 ?]]]]; subst v0 x0.
  all: move: hx1 => /to_wordI [ws1 [w1 [? /truncate_wordP [hws1 ?]]]]; subst v1 x1.
  all: assert (hwc := is_wconstP true (p_globs p) s hc).
  all: move: hwc;
    rewrite hseme1 /= (truncate_word_le _ (cmp_le_trans hws hws1)) => -[?];
    subst c.
  all: split; last (split; [ exact: hfve0 | by [] ]).
  all: eexists;
    first by rewrite /sem_pexprs /= hseme0 /= /sem_sop1 /=.
  all: rewrite /exec_sopn /sopn_sem /sopn_sem_ /=.
  all: rewrite (truncate_word_le _ (cmp_le_trans hws hws0)) truncate_word_u /=.
  all: rewrite wrepr_unsigned ?wrepr_opp wrepr_unsigned.
  all: rewrite ?add_wordE ?sub_wordE.
  all: rewrite ?(wadd_zero_extend _ _ hws) ?(wsub_zero_extend _ _ hws)
               ?(zero_extend_idem _ hws).
  all: by rewrite ?(wopp_zero_extend _ hws) ?(zero_extend_idem _ hws).
Qed.

Lemma lower_pexpr_auxP e :
  Plower_pexpr_aux e.
Proof.
  move=> s ws ws' aop es w.
  case: e => [||| gx | al aa ws0 x e || al ws0 x e | op e | op e0 e1 ||] //.

  - exact: lower_PvarP.
  - exact: (lower_loadP (Pget _ _ _ _ _)).
  - exact: (lower_loadP (Pload _ _ _)).
  - exact: lower_Papp1P.
  exact: lower_Papp2P.
Qed.

Lemma sem_i_lower_pexpr_aux s0 s1 s0' ws ws' ii e op es (w : word ws') lv tag :
  lower_pexpr_aux ws e = Some (op, es)
  -> eq_fv s0 s0'
  -> (ws <= ws')%CMP
  -> disj_fvars (read_e e)
  -> disj_fvars (vars_lval lv)
  -> sem_pexpr true (p_globs p) s0 e = ok (Vword w)
  -> write_lval true (p_globs p) lv (Vword (zero_extend ws w)) s0 = ok s1
  -> exists2 s1',
       esem_i p' ev (MkI ii (Copn [:: lv ] tag op es)) s0' = ok s1'
       & eq_fv s1 s1'.
Proof.
  move=> h hs00 hws hfve hfvlv hseme hwrite.

  have hseme' := eeq_exc_sem_pexpr hfve hs00 hseme.
  clear hseme.

  have [[vs hsemes hexec] _] := lower_pexpr_auxP h hws hfve hseme'.
  clear h hws hfve hseme'.

  have [s1' hwrite' hs11] := eeq_exc_write_lval hfvlv hs00 hwrite.
  clear hfvlv hs00 hwrite.

  exists s1'; last exact: hs11.
  clear hs11.
  rewrite /= /sem_sopn /=.
  rewrite hsemes {hsemes} /=.
  rewrite hexec {hexec} /=.
  by rewrite hwrite' {hwrite'} /=.
Qed.

Lemma no_preP o pre aop es :
  no_pre o = Some (pre, aop, es)
  -> pre = [::] /\ o = Some (aop, es).
Proof. case: o => //. by move=> [? ?] [<- <- <-]. Qed.

Lemma sem_lower_pexpr
  s0 s1 s0' ii vi ws ws' e pre op es (w : word ws') lv tag :
  lower_pexpr vi ws e = Some (pre, op, es)
  -> eq_fv s0 s0'
  -> (ws <= ws')%CMP
  -> disj_fvars (read_e e)
  -> disj_fvars (vars_lval lv)
  -> sem_pexpr true (p_globs p) s0 e = ok (Vword w)
  -> write_lval true (p_globs p) lv (Vword (zero_extend ws w)) s0 = ok s1
  -> exists2 s1',
       let cmd := map (MkI ii) (pre ++ [:: Copn [:: lv ] tag op es ]) in
       esem p' ev cmd s0' = ok s1' & eq_fv s1 s1'.
Proof using atoI ev fv fv_correct p pT sCP sc_sem syscall_state warning wsw.
  move=> h hs00 hws hfve hfvlv hseme hwrite.

  move: s0 ws' pre op es w h hs00 hws hfve hfvlv hseme hwrite.
  case: e =>
    [||| gx | al aa ws0 x e || al ws0 e | op e | op e0 e1 || ty c e0 e1] //
    s0 ws' pre aop es w h hs00 hws hfve hfvlv hseme hwrite.

  1-5: move: h => /no_preP [? h]; subst pre.
  1-5: have [s1' hsem' hs11] :=
    sem_i_lower_pexpr_aux ii tag h hs00 hws hfve hfvlv hseme hwrite.
  1-5: clear s0 ws w h hs00 hws hfve hfvlv hseme hwrite.
  1-5: exists s1'; last exact: hs11.
  1-5: by move: hsem'; rewrite /= => ->.

  (* [Pif]: lowered to CSEL (A64 has no conditional execution). *)
  clear hws.
  move: h.
  case: ty hfve hfvlv hseme => // ws0 hfve hfvlv hseme.

  rewrite /lower_pexpr.
  move=> /oassertP [] /eqP ?; subst ws0.
  rewrite /lower_Pif.
  move=> /oassertP [] hwsx h.
  move: h => /oassertP [] hcselargs h.
  move: h.
  case hc: lower_condition => [pre' c'] [? ? ?]; subst pre aop es.
  rename pre' into pre.

  move: hseme.
  rewrite /=.
  rewrite /truncate_val /=.
  t_xrbindP=> b vb hsemc hb v0' v0 hseme0 w0' hw0 ? v1' v1 hseme1 w1' hw1 ? hw;
    subst v0' v1'.
  move: hb => /to_boolI ?; subst vb.
  move: hw0 => /to_wordI [ws0 [w0 [? /truncate_wordP [hws0 ?]]]]; subst v0 w0'.
  move: hw1 => /to_wordI [ws1 [w1 [? /truncate_wordP [hws1 ?]]]]; subst v1 w1'.

  move: hfve => /disj_fvars_read_e_Pif [hfvc hfve0 hfve1].

  have [s1' [hsem01' hs10 hsemc']] := sem_lower_condition ii hc hs00 hfvc hsemc.
  clear hc hs00 hfvc hsemc.

  have [s2' hwrite12' hs21] :
    exists2 s2',
      write_lval true (p_globs p) lv
        (Vword (if b then zero_extend ws w0 else zero_extend ws w1)) s1'
        = ok s2'
      & eq_fv s1 s2'.
  {
    case: b hw hsemc' => hw _.
    all: move: hw => /Vword_inj [?]; subst ws'.
    all: move=> /= ?; subst w.
    all: rewrite zero_extend_u in hwrite.
    all: have [s2' hwrite12' hs21] := eeq_exc_write_lval hfvlv hs10 hwrite.
    all: exists s2'; last exact: hs21.
    all: exact: hwrite12'.
  }

  exists s2'; last exact: hs21.
Opaque esem esem_i.
  rewrite map_cat esem_cat hsem01' /= esem1.
Transparent esem esem_i.
  clear hsem01'.
  rewrite /= /sem_sopn /=.
  rewrite (eeq_exc_sem_pexpr hfve0 hs10 hseme0) /=
          (eeq_exc_sem_pexpr hfve1 hs10 hseme1) /=
          hsemc' /=.
  rewrite /exec_sopn /sopn_sem /sopn_sem_ /=.
  move: (hwsx); rewrite orbC => hval; rewrite hval /=.
  rewrite (truncate_word_le _ hws0) (truncate_word_le _ hws1) /=.
  rewrite /semi_to_atype !computational_eq_refl /=.
  rewrite /armv8a_CSEL_semi.
  by rewrite hwrite12'.
Qed.

Lemma sem_i_lower_store s0 s1 s0' ws ws' ii e aop es (w : word ws') lv tag :
  lower_store ws e = Some (aop, es)
  -> eq_fv s0 s0'
  -> (ws <= ws')%CMP
  -> disj_fvars (read_e e)
  -> sem_pexpr true (p_globs p) s0 e = ok (Vword w)
  -> write_lval true (p_globs p) lv (Vword (zero_extend ws w)) s0' = ok s1
  -> esem_i p' ev (MkI ii (Copn [:: lv ] tag (Oarmv8a aop) es)) s0' = ok s1.
Proof.
  move=> h hs00 hws hfv hseme hwrite.

  move: h.
  rewrite /lower_store.
  case hmn: store_mn_of_wsize => [mn|] //.

  (* On armv8a only a register can be stored: [e] is a [Pvar]. *)
  case: e hseme hfv => [||| gx |||||||] // hseme hfv [? ?]; subst aop es.
  rewrite /= /sem_sopn /=.
  have /= -> := eeq_exc_sem_pexpr hfv hs00 hseme.
  rewrite /exec_sopn /sopn_sem /sopn_sem_ /=.
  case: ws hws hwrite hmn => // hws hwrite [?]; subst mn.
  all: rewrite /= (truncate_word_le _ hws) /=.
  all: rewrite /semi_to_atype ?computational_eq_refl /=.
  all: rewrite /armv8a_extend_semi ?zero_extend_u /=.
  all: by rewrite hwrite.
Qed.

Lemma lower_cassgn_wordP ii s0 lv tag ws e v v' s0' s1' pre lvs op es :
  lower_cassgn_word fv lv ws e = Some (pre, (lvs, op, es))
  -> sem_pexpr true (p_globs p) s0 e = ok v
  -> truncate_val (cword ws) v = ok v'
  -> write_lval true (p_globs p) lv v' s0' = ok s1'
  -> eq_fv s0 s0'
  -> disj_fvars (read_e e)
  -> disj_fvars (vars_lval lv)
  -> esem_i p' ev (MkI ii (Cassgn lv tag (aword ws) e)) s0' = ok s1'
  -> exists2 s2',
       esem p' ev (map (MkI ii) (pre ++ [:: Copn lvs tag op es ])) s0' = ok s2'
       & eq_fv s1' s2'.
Proof using atoI ev fv fv_correct p pT sCP sc_sem syscall_state warning wsw.
  rewrite /lower_cassgn_word.
  move=> h hseme htrunc hwrite01' hs00 hfve hfvlv hsem01'.

  move: h.
  move: htrunc.
  rewrite /truncate_val.
  t_xrbindP=> w' hw' ?; subst v'.
  move: hw' => /to_wordI [ws' [w [? /truncate_wordP [hws ?]]]]; subst v w'.

  case: is_lval_in_memory.
  - case h: lower_store => [[op' es']|] // [? ? ? ?]; subst pre lvs op es.
    exists s1'; last exact: eeq_excR.
    rewrite esem1.
    exact: (sem_i_lower_store ii tag h hs00 hws hfve hseme hwrite01').

  case h: lower_pexpr => [[[pre' op'] es']|] // [? ? ? ?];
    subst pre lvs op es.

  have [s2 hwrite02 hs12] :=
    eeq_exc_write_lval hfvlv (eeq_excS hs00) hwrite01'.
  clear hwrite01'.

  have /= [s3' hsem03' hs23] :=
    sem_lower_pexpr ii tag h hs00 hws hfve hfvlv hseme hwrite02.
  exists s3'; last exact: (eeq_excT hs12 hs23).
  exact: hsem03'.
Qed.

Lemma lower_cassgn_boolP ii s0 lv tag e v v' s0' s1' irs :
  lower_cassgn_bool fv lv tag e = Some irs
  -> sem_pexpr true (p_globs p) s0 e = ok v
  -> truncate_val cbool v = ok v'
  -> write_lval true (p_globs p) lv v' s0' = ok s1'
  -> eq_fv s0 s0'
  -> disj_fvars (read_e e)
  -> disj_fvars (vars_lval lv)
  -> esem_i p' ev (MkI ii (Cassgn lv tag abool e)) s0' = ok s1'
  -> exists2 s2',
       esem p' ev (map (MkI ii) irs) s0' = ok s2'
       & eq_fv s1' s2'.
Proof using atoI ev fv fv_correct p pT sCP sc_sem syscall_state warning wsw.
  rewrite /lower_cassgn_bool => h ok_v ok_v' ok_s1' hs00 hfve hfvlv hsem01'.
  case h: lower_condition_pexpr h => [ [] [] [] lvs op es c | // ] /Some_inj <-{irs}.
  have [ si [] hsem0i hs0i {} ok_v ] := sem_lower_condition_pexpr tag ii h hs00 hfve ok_v.
  have hsi0' : eq_fv s0' si := eeq_excS (eeq_excT (eeq_excS hs0i) hs00).
  have [ sj ok_sj hsj1' ] := eeq_exc_write_lval hfvlv hsi0' ok_s1'.
  eexists.
  - rewrite -cat1s map_cat esem_cat hsem0i /= /sem_assgn.
    rewrite ok_v /= ok_v' /= ok_sj /=; reflexivity.
  done.
Qed.

(* -------------------------------------------------------------------- *)
(* Lowering of ARM-specific instructions. *)

(* TODO_ARM: This lemma is similar to the one in x86_lowering, but not quite:
   in x86 [res] is [wunsigned (wrepr (wunsigned w + wunsigned w' + Z.b2z b))].
*)
Lemma wunsigned_carry ws w w' b :
  let: res := wunsigned (w + w' + wrepr ws (Z.b2z b))%R in
  let: res' := (wunsigned w + wunsigned w' + Z.b2z b)%Z in
  (wbase ws <=? res')%Z = (res != res')%Z.
Proof.
  case: b => /=; first last.
  - rewrite Z.add_0_r wrepr0 GRing.addr0. exact: add_overflow.

  rewrite wunsigned_add_if.
  rewrite wrepr1 wunsigned1.
  case: ZltP.
  - rewrite wunsigned_add_if.
    case: ZltP.
    + move=> _.
      move=> /Z.lt_nge /ZleP /negPf ->.
      by symmetry; apply/negPn.

    move=> h _.
    have -> : (wbase ws <=? wunsigned w + wunsigned w' + 1)%Z.
    + apply/ZleP. lia.
    symmetry; apply/eqP.
    have := wbase_pos ws.
    lia.

  rewrite wunsigned_add_if.
  case: ZltP.
  - move=> /Z.le_succ_l h0 /Z.le_ngt h1.
    rewrite -(Z.le_antisymm _ _ h0 h1).
    rewrite Z.leb_refl.
    symmetry; apply/eqP.
    have := wunsigned_range w.
    lia.

  move=> /Z.le_ngt h0 /Z.le_ngt h1.
  have -> : (wbase ws <=? wunsigned w + wunsigned w' + 1)%Z.
  - apply/ZleP. lia.
  symmetry; apply/eqP.
  have := wunsigned_range w.
  lia.
Qed.

Lemma write_Lnone wdb gd x v s s' :
  isLnone x ->
  write_lval wdb gd x v s = ok s' ->
  s = s'.
Proof.
  case: x => // ii ty _ /=.
  by rewrite /write_none /=; t_xrbindP.
Qed.

Lemma lower_add_carryP s0 s1 ii lvs tag es lvs' op' es' :
  esem_i p' ev (MkI ii (Copn lvs tag (sopn_addcarry U64) es)) s0 = ok s1
  -> lower_add_carry lvs es = Some (lvs', op', es')
  -> esem_i p' ev (MkI ii (Copn lvs' tag op' es')) s0 = ok s1.
Proof.
  case: lvs => [] // lv0 [] // lv1 [] //.
  case: es => [] // e0 [] // e1 [] // e2 [] //.
  move=> + h.
  rewrite /= /sem_sopn /=.
  t_xrbindP=> res _ v0 hseme0 _ v1 hseme1 _ v2 hseme2 <- <- <- + hwrite.
  rewrite /exec_sopn /=.
  t_xrbindP=> /= res' w0 hw0 w1 hw1 b hb hsopn ?; subst res.
  move: hw0 => /to_wordI [ws [w [? hw0]]]; subst v0.
  move: hw0 => /truncate_wordP [hws ?]; subst w0.
  move: hw1 => /to_wordI [ws' [w' [? hw1]]]; subst v1.
  move: hw1 => /truncate_wordP [hws' ?]; subst w1.
  move: hb => /to_boolI ?; subst v2.
  move: hsopn => [?]; subst res'.
  move: hwrite => /=.
  t_xrbindP=> s00 hwrite00 s01 hwrite1 ?; subst s01.

  rewrite /sem_sopn /=.

  move: hwrite1.
  rewrite !wrepr_add !wrepr_unsigned.
  move=> hwrite1.

  move: h.
  case: e2 hseme2 => [| [] || gx |||||||] //= hseme2 [???];
    subst lvs' op' es'.
  all: rewrite /= hseme0 hseme1 /= {hseme0 hseme1}.

  2: rewrite hseme2 /= {hseme2}.

  all: case no_carry: (isLnone _) => /=.

  all: rewrite /exec_sopn /=.
  all: rewrite !truncate_word_le // {hws hws'} /=.
  all: move: hwrite00 hwrite1.
  all: rewrite wunsigned_carry.

  1, 2: move: hseme2 => [?]; subst b.
  1, 2: rewrite /= Z.add_0_r wrepr0 GRing.addr0.

  2, 4: by move=> -> /= ->.

  1, 2: by move => /(write_Lnone no_carry) <- ->.
Qed.

Lemma lower_base_op s0 s1 ii lvs tag aop es lvs' op' es' :
  disj_fvars (read_es es)
  -> esem_i p' ev (MkI ii (Copn lvs tag (Oasm (BaseOp (None, aop))) es)) s0 = ok s1
  -> lower_base_op lvs aop es = Some (lvs', op', es')
  -> esem_i p' ev (MkI ii (Copn lvs' tag op' es')) s0 = ok s1.
Proof.
  move: aop => [mn opts].
  move=> hfve hsemi.
  rewrite /lower_base_op.
  assert (default : forall lvs' op' es', Some (lvs, Oasm (BaseOp (None, ARMv8A_op mn opts)), es) = Some (lvs', op', es') ->
                    esem_i p' ev (MkI ii (Copn lvs' tag op' es')) s0 = ok s1).
  - move: hsemi; clear => hsemi lvs' op' es' /Some_inj[? ? ?]; subst lvs' op' es'.
    exact: hsemi.
  case: ifP.
  - case: (_ \in _) => // _.
    exact: default.
  move/eqP => no_shift.
  case: ifP => mn_unop.
  - case: es hsemi hfve default => // x es hsemi hfve default.
    case x_has_shift: get_arg_shift => [ [ [] ebase sh esham ] | ] ; last exact: default.
    case hallowed: (shift_allowed mn sh); last exact: default.
    case/Some_inj => <-{lvs'} <-{op'} <-{es'} /=.
    have {} hfve : disj_fvars (read_e x).
    + move: hfve; clear.
      by rewrite /disj_fvars read_es_cons => /disjoint_union[].
    move: hsemi.
    rewrite /= /sem_sopn /=; t_xrbindP => r _ w hx ws hes <- hr hwrite.
    have [ ts [] t [] wsham [] hts ht hwsham hw [] hfb hfa ] := get_arg_shiftP x_has_shift hfve hx.
    rewrite ht hwsham hes /=.
    have -> /= := with_shift_unop mn_unop hallowed hts no_shift ht hwsham hw hr.
    exact: hwrite.
  case: ifP => mn_binop; last by [].
  case: es hsemi hfve default => // x [] // y es hsemi hfve default.
  case y_has_shift: get_arg_shift => [ [ [] ebase sh esham ] | ] ; last exact: default.
  case hallowed: (shift_allowed mn sh); last exact: default.
  case/Some_inj => <-{lvs'} <-{op'} <-{es'} /=.
  have {} hfve : disj_fvars (read_e y).
  + move: hfve; clear.
    by rewrite /disj_fvars !read_es_cons => /disjoint_union[] _ /disjoint_union[].
  move: hsemi.
  rewrite /= /sem_sopn /=; t_xrbindP => r _ w -> _ z hy ws hes <- <- hr hwrite.
  have [ ts [] t [] wsham [] hts ht hwsham hw [] hfb hfa ] := get_arg_shiftP y_has_shift hfve hy.
  rewrite ht hwsham hes /=.
  have -> /= := with_shift_binop mn_binop hallowed hts no_shift ht hwsham hw hr.
  exact: hwrite.
Qed.

Lemma lower_copnP s0 s1 ii lvs tag op es lvs' op' es' :
  disj_fvars (read_es es)
  -> esem_i p' ev (MkI ii (Copn lvs tag op es)) s0 = ok s1
  -> lower_copn lvs op es = Some (lvs', op', es')
  -> exists2 vm1,
     esem_i p' ev (MkI ii (Copn lvs' tag op' es')) s0 = ok (with_vm s1 vm1) &
     vm1 =1 evm s1.
Proof.
  case: op => // [pop | [[[|] aop]|//]] //; last first.
  - (* Base op. *)
    move=> hd hs hl; exists (evm s1) => //.
    rewrite with_vm_same; exact: lower_base_op hd hs hl.
  (* Pseudo operators: [Oaddcarry U64] and [Oswap]. *)
  case: pop => //.
  - (* Oaddcarry U64. *)
    move=> w hd hsemi hlow.
    move: hlow; case: w hsemi => // hsemi hlow.
    exists (evm s1) => //.
    rewrite with_vm_same; exact: (lower_add_carryP hsemi hlow).
  (* Oswap. *)
  move=> ty hd hsem hlow.
  move: hlow; rewrite /= /lower_swap.
  case: ty hsem => // [len ty | ws] hsem.
  - move=> [<- <- <-].
    by exists (evm s1) => //; rewrite with_vm_same.
  case: ifP => // hcmp [<- <- <-].
  by exists (evm s1) => //; rewrite with_vm_same.
Qed.

(* -------------------------------------------------------------------- *)

Section IT.
Context {E E0: Type -> Type} {wE : with_Error E E0} {rE0 : EventRels E0}.

#[ local ]
Definition Pi_ (i : instr) :=
  disj_fvars (vars_I i) ->
  wequiv_rec p p' ev ev eq_spec eq_fv [::i] (lower_i i) eq_fv.

#[ local ]
Definition Pi_r_ (i : instr_r) := forall ii, Pi_ (MkI ii i).

#[ local ]
Definition Pc_ (c : cmd) :=
  disj_fvars (vars_c c) ->
  wequiv_rec p p' ev ev eq_spec eq_fv c (lower_cmd c) eq_fv.

Lemma checker_st_eq_exP_ : Checker_eq p p' checker_st_eq_ex.
Proof. apply checker_st_eq_exP => //. Qed.
#[local] Hint Resolve checker_st_eq_exP_ : core.

Lemma it_lower_callP fn :
  wiequiv_f p p' ev ev (rpreF (eS:= eq_spec)) fn fn (rpostF (eS:=eq_spec)).
Proof using E E0 atoI dc ev fv fv_correct p pT rE0 sCP sc_sem syscall_state wE warning wsw.
  apply wequiv_fun_ind => {}fn _ fs _ [<- <-] fd hget.
  have [_ hfvres hfvc] := disj_fvars_get_fundef hget.
  rewrite get_map_prog hget /= /lower_fd.
  eexists; first reflexivity.
  move=> s.
  move=> /(eq_initialize (fd':= with_body fd (lower_cmd (f_body fd)))) -/(_ p' erefl erefl erefl erefl) hinit.
  exists s => //; exists eq_fv, eq_fv; split => //=; last by apply st_eq_ex_finalize.
  move: (f_body fd) hfvc. clear fn fs fd hget hfvres hinit s.
  set sip := sip_of_asm_e.
  apply (cmd_rect (Pr := Pi_r_) (Pi:=Pi_) (Pc:=Pc_)) => //; rewrite /Pi_r_ /Pi_ /Pc_.
  + by move=> _; apply (wequiv_nil (sip:=sip)).
  + move=> i c hi hc /disj_fvars_vars_c_cons [/hi{}hi /hc{}hc].
    rewrite -cat1s.
    by apply (wequiv_cat (sip:=sip)) with eq_fv.
  (* Assgn *)
  + move=> x tg ty e ii /disj_fvars_vars_I_Cassgn [hfvlv hfve].
    apply (wequiv_assgn_esem (sip:=sip)).
    move=> s0 s0' s1 hs00; rewrite /sem_assgn; t_xrbindP => v hseme v' htrunc hwrite.
    have [s1' hwrite' hs11] := eeq_exc_write_lval hfvlv hs00 hwrite.
    clear hwrite.
    assert (hassgn : esem_i p' ev (MkI ii (Cassgn x tg ty e)) s0' = ok s1').
    - by rewrite /= /sem_assgn (eeq_exc_sem_pexpr hfve hs00 hseme) /= htrunc /=.
    assert (default: exists2 s1'0 : estate, esem p' ev [:: MkI ii (Cassgn x tg ty e)] s0' = ok s1'0 & eq_fv s1 s1'0).
    - exists s1'; last exact: hs11.
      by rewrite esem1.
    rewrite /lower_i.
    case: ty htrunc hassgn default => // [ | ws ] htrunc hassgn default.
    - case h: lower_cassgn_bool => [ irs | ]; last by [].
      have [ sj hsemj hs1j ] := lower_cassgn_boolP h hseme htrunc hwrite' hs00 hfve hfvlv hassgn.
      exists sj => //.
      by apply: eeq_excT hs1j.
    case h: lower_cassgn_word => [[pre [[lvs op] es]]|]; last by [].
    have [s2' hsem02' hs12'] :=
      lower_cassgn_wordP h hseme htrunc hwrite' hs00 hfve hfvlv hassgn.
    by exists s2'; last exact: (eeq_excT hs11 hs12').
  (* Copn *)
  + move=> lvs tag op es ii /disj_fvars_vars_I_Copn [hfvlvs hfve].
    apply (wequiv_opn_esem (sip:=sip)) => s0 s0' s1 hs00.
    rewrite /sem_sopn; t_xrbindP=> vs xs hsemes hexec hwrite.
    have [s1' hwrite' hs11] := eeq_exc_write_lvals hfvlvs hs00 hwrite.
    clear hfvlvs hwrite.
    assert (hcopn : esem_i p' ev (MkI ii (Copn lvs tag op es)) s0' = ok s1').
    - rewrite /= /sem_sopn /=.
      rewrite (eeq_exc_sem_pexprs hfve hs00 hsemes) {hfve hs00 hsemes} /=.
      rewrite hexec /=.
      exact: hwrite'.
Opaque esem.
    clear hs00 hsemes hwrite' => /=.
    case h: lower_copn => [[[lvs' op'] es']|]; last first.
    + exists s1'; last exact: hs11.
      by rewrite esem1.
    have [vm hsem1 heq]:= lower_copnP hfve hcopn h.
    exists (with_vm s1' vm); first by rewrite esem1.
    case: hs11=> ?? hvm; split => //=.
    by move=> z hz; rewrite heq; apply hvm.
  (* Syscall *)
  + move=> xs o es ii.
    rewrite /disj_fvars vars_I_syscall => /disjoint_union [hdisjx hdisje].
    apply (wequiv_syscall_rel_eq (sip:=sip)) with
       checker_st_eq_ex fvars => //.
  (* Assert *)
  + by move=> ? ii _; apply wequiv_noassert with (ev1:=ev) (ii:=ii).
  (* If *)
  + move=> e c1 c2 hc1 hc2 ii /disj_fvars_vars_I_Cif [hfve /hc1{}hc1 /hc2{}hc2] /=.
    case heq: lower_condition => [pre e'].
    rewrite map_cat /=.
    apply (wequiv_if_esem (sip:=sip)) with eq_fv.
    + by move=> s t v heqfv; apply (sem_lower_condition ii heq).
    by move=> [].
  (* For *)
  + move=> x dir lo hi c hc ii /= /disj_fvars_vars_I_Cfor [hfvc hfvlo hfvhi].
    apply (wequiv_for_rel_eq (sip:=sip)) with checker_st_eq_ex fvars fvars => //.
    + by split => //; apply disj_fvars_read_es2.
    split => //.
    + rewrite /vars_lvals /read_rvs /vrvs /=; apply /disjointP.
      by move=> z hz; move/disjointP: hfvc => /(_ z); SvD.fsetdec.
    by apply/hc/disjointP => z hz; move/disjointP: hfvc => /(_ z); SvD.fsetdec.
  (* While *)
  + move=> al c e ii' c' hc hc' ii /disj_fvars_vars_I_Cwhile [/hc{}hc hfve /hc'{}hc'] /=.
    case heq: lower_condition => [pre e'].
    apply (wequiv_while_esem (sip:=sip)) with eq_fv => //.
    by move=> s t v heqfv; apply (sem_lower_condition ii' heq).
  (* Call *)
  move=> xs fn es ii /disj_fvars_vars_I_Ccall [hdisjx hdisje] /=.
  apply (wequiv_call_rel_eq (sip:=sip)) with checker_st_eq_ex fvars => //.
  by move=> ???; apply: (wequiv_fun_rec (spec := eq_spec)).
Qed.
End IT.

End PROOF.
