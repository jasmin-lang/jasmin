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
  arm_decl
  arm_extra
  arm_instr_decl
  arm_instr_decl_lemmas
  arm_lowering.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma chk_ws_regP {A ws a} {oa : option A} :
  (let%opt _ := chk_ws_reg ws in oa) = Some a
  -> ws = reg_size /\ oa = Some a.
Proof. by move=> /oassertP [] /eqP. Qed.

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
  (options : lowering_options)
  (warning : instr_info -> warning_msg -> instr_info)
  (fv : fresh_vars)
  (fv_correct : fvars_correct (all_fresh_vars fv) (fvars fv) (p_funcs p)).

Notation fvars := (fvars fv).
Notation lower_pexpr := (lower_pexpr fv).
Notation lower_cmd :=
  (lower_cmd
     (fun _ _ => lower_i)
     options
     warning
     fv).
Notation lower_prog :=
  (lower_prog
     (fun _ _ => lower_i)
     options
     warning
     fv).
Notation lower_i := (lower_i fv).
Notation disj_fvars := (disj_fvars fvars).
Notation disj_fvars_get_fundef := (disj_fvars_get_fundef fv_correct).

Notation p' := (lower_prog p).

(* -------------------------------------------------------------------- *)

Definition eq_fv (s0 s1 : estate) : Prop :=
  estate_eq_except fvars s0 s1.

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

Definition estate_of_CMP s (w0 w1 : wreg) : estate :=
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

Definition estate_of_TST s (w0 w1 : wreg) : estate :=
  let res := wand w0 w1 in
  let vm' :=
    (evm s)
      .[fvNF fv <- NF_of_word res]
      .[fvZF fv <- ZF_of_word res]
      .[fvCF fv <- false]
  in
  with_vm s vm'.

(* Precondition: [mn] is a condition mnemonic. *)
Definition estate_of_condition_mn
  (mn : arm_mnemonic) : estate -> wreg -> wreg -> estate :=
  match mn with
  | CMP => estate_of_CMP
  | TST => estate_of_TST
  | _ => fun s _ _ => s (* Never happens. *)
  end.

Lemma estate_of_condition_mn_eq_fv mn s w0 w1 :
  mn \in condition_mnemonics
  -> eq_fv (estate_of_condition_mn mn s w0 w1) s.
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

Lemma sem_condition_mn ii vi tag mn s es ws0 ws1 (w0 : word ws0) (w1 : word ws1) :
  mn \in condition_mnemonics
  -> (reg_size <= ws0)%CMP
  -> (reg_size <= ws1)%CMP
  -> sem_pexprs true (p_globs p) s es = ok [:: Vword w0; Vword w1 ]
  -> let w0' := zero_extend reg_size w0 in
     let w1' := zero_extend reg_size w1 in
     let aop := Oarm (ARM_op mn default_opts) in
     let i := Copn (lflags_of_mn fv vi mn) tag aop es in
     sem p' ev s [:: MkI ii i ] (estate_of_condition_mn mn s w0' w1').
Proof.
  move=> hmn hws0 hws1 hsemes /=.
  apply: sem_seq_ir. apply: Eopn.
  rewrite /sem_sopn /=.
  rewrite hsemes {hsemes} /=.

  case: mn hmn => // _.
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

Lemma lower_condition_Papp2P vi s op e0 e1 mn e es v0 v1 v :
  lower_condition_Papp2 fv vi op e0 e1 = Some (mn, e, es)
  -> sem_pexpr true (p_globs p) s e0 = ok v0
  -> sem_pexpr true (p_globs p) s e1 = ok v1
  -> sem_sop2 op v0 v1 = ok v
  -> exists (ws0 ws1 : wsize) (w0 : word ws0) (w1 : word ws1),
      let w0' := zero_extend reg_size w0 in
      let w1' := zero_extend reg_size w1 in
      [/\ mn \in condition_mnemonics
        , (reg_size <= ws0)%CMP
        , (reg_size <= ws1)%CMP
        , sem_pexprs true (p_globs p) s es = ok [:: Vword w0; Vword w1 ]
        & sem_pexpr true (p_globs p) (estate_of_condition_mn mn s w0' w1') e = ok v
      ].
Proof.
  move=> h hseme0 hseme1 hsemop.

  (* TODO_ARM: Can this common part be abstracted? *)
  case: op h hsemop => //.
  all:
    match goal with
    | [ |- forall (_ : op_kind), _ -> _ ] => move=> [|[]] //=
    | [ |- forall (_ : cmp_kind), _ -> _ ] => move=> [|[] []] //=
    end.

  - rewrite /lower_condition_Papp2.
    case hTST: lower_TST => [es'|] //.

  all: move=> [? ? ?] hsemop; subst mn e es.

  all: move: hsemop => /sem_sop2I /= [w0 [w1 [b [hw0 hw1 hop]]]].
  all: move: hw0 => /to_wordI [ws0 [w0' [? /truncate_wordP [hws0 ?]]]];
         subst v0 w0.
  all: move: hw1 => /to_wordI [ws1 [w1' [? /truncate_wordP [hws1 ?]]]];
         subst v1 w1.
  all: move: hop => [?] ?; subst b v.

  (* Case [w00 & w01 == 0]. *)
  - have [? [e00 [e01 [? [? ?]]]]] := lower_TST_match hTST; subst e0 e1.
    move: hTST.

    move: hseme0 => /=.
    t_xrbindP=> v00 hseme00 v01 hseme01 hw0'.
    move: hw0' => /sem_sop2I /= [w00 [w01 [w0 [hw00 hw01 hw0 hw0']]]].
    move: hw00 => /to_wordI [ws00 [w00' [? /truncate_wordP [hws00 ?]]]];
      subst v00 w00.
    move: hw01 => /to_wordI [ws01 [w01' [? /truncate_wordP [hws01 ?]]]];
      subst v01 w01.
    move: hw0 => [?]; subst w0.
    move: hw0' => /Vword_inj [?]; subst ws0.
    move=> /= ?; subst w0'.

    move: hseme1 => /sem_sop1I /= [w1 [?] hw1']; subst w1.
    move: hw1' => /Vword_inj [?]; subst ws1.
    move=> /= ?; subst w1'.

    move=> [?]; subst es'.
    rewrite /=.

    rewrite hseme00 hseme01 {hseme00 hseme01} /=.
    eexists; eexists; eexists; eexists;
      split;
      first done;
      first exact: (cmp_le_trans hws0 hws00);
      first exact: (cmp_le_trans hws0 hws01);
      first reflexivity.
    clear hws00 hws01.

    rewrite /pexpr_of_cf /= /get_gvar /=.
    repeat t_get_var => //.

    rewrite wrepr0 zero_extend0.
    rewrite -(wand_zero_extend _ _ hws0).
    by rewrite !(zero_extend_idem _ hws0) {hws0}.

  all: rewrite hseme0 hseme1 {hseme0 hseme1} /=.
  all: eexists; eexists; eexists; eexists;
         split;
    first done;
    first exact: hws0;
    first exact: hws1;
    first reflexivity.
  all: clear hws0 hws1.

  all: rewrite /get_gvar /=.
  all: repeat t_get_var => //.

  all: rewrite
    /sem_opN /= /sem_combine_flags /cf_xsem /NF_of_word /ZF_of_word /=
    1?wsub_wnot1
    1?nzcv_of_aluop_CF_sub
    1?wsigned_wsub_wnot1
    ?GRing.Theory.subr_eq0
    //.
  all: clear.
  all: set w0 := zero_extend _ w0'.
  all: set w1 := zero_extend _ w1'.

  (* Case [w0 <s w1]. *)
  - by rewrite wltsE.

  (* Case [w0 <u w1]. *)
  - by rewrite wleuE ltNge.

  (* Case [w0 <=s w1]. *)
  - by rewrite wlesE'.

  (* Case [w0 <=u w1]. *)
  - by rewrite wleuE'.

  (* Case [w0 >s w1]. *)
  - by rewrite wlesE' ltNge.

  (* Case [w0 >u w1]. *)
  - by rewrite wleuE' ltNge.

  (* Case [w0 >=s w1]. *)
  - by rewrite wltsE leNgt.

  (* Case [w0 >=u w1]. *)
  by rewrite -word.wltuE leNgt.
Qed.

Lemma sem_lower_condition_pexpr vi tag s0 s0' ii e v lvs aop es c :
  lower_condition_pexpr fv vi e = Some (lvs, aop, es, c)
  -> eq_fv s0' s0
  -> disj_fvars (read_e e)
  -> sem_pexpr true (p_globs p) s0 e = ok v
  -> exists s1',
       [/\ sem p' ev s0' [:: MkI ii (Copn lvs tag aop es) ] s1'
         , eq_fv s1' s0
         & sem_pexpr true (p_globs p) s1' c = ok v
       ].
Proof.
  apply: obindP => -[[op e0] e1] /is_Papp2P ?; subst.
  apply: obindP => -[[mn e] es'] h [????]; subst.

  move=> hs00 /disj_fvars_read_e_Papp2 [hfv0 hfv1] /=.
  t_xrbindP=> v0 hsem0 v1 hsem1 hsemop.

  have hsem0' := eeq_exc_sem_pexpr hfv0 hs00 hsem0.
  have hsem1' := eeq_exc_sem_pexpr hfv1 hs00 hsem1.
  clear hfv0 hsem0 hsem1 hfv1.

  have [ws0 [ws1 [w0 [w1 [hmn hws0 hws1 hsemes hseme]]]]] :=
    lower_condition_Papp2P h hsem0' hsem1' hsemop.
  clear h hsemop hsem0' hsem1'.

  have /= hsem' := sem_condition_mn ii vi tag hmn hws0 hws1 hsemes.
  clear hws0 hws1 hsemes.

  eexists;
    split;
    first exact: hsem';
    last exact: hseme.
  apply: (eeq_excT _ hs00).
  exact: (estate_of_condition_mn_eq_fv s0' _ _ hmn).
Qed.

Lemma sem_lower_condition vi s0 s0' ii e v pre e' :
  lower_condition fv vi e = (pre, e')
  -> eq_fv s0' s0
  -> disj_fvars (read_e e)
  -> sem_pexpr true (p_globs p) s0 e = ok v
  -> exists s1',
       [/\ sem p' ev s0' (map (MkI ii) pre) s1'
         , eq_fv s1' s0
         & sem_pexpr true (p_globs p) s1' e' = ok v
       ].
Proof.
  move=> h hs00 hfv hseme.

  move: h.
  rewrite /lower_condition.
  case h: lower_condition_pexpr => [[[[lvs op] es] c]|] [? ?];
    subst e' pre.

  - exact: sem_lower_condition_pexpr h hs00 hfv hseme.
  clear h.

  exists s0'.
  split;
    first exact: Eskip;
    first exact: hs00.

  exact: (eeq_exc_sem_pexpr hfv hs00 hseme).
Qed.


(* -------------------------------------------------------------------- *)
(* Lowering of assignments. *)

(* Note that the interpretation of the expression is [zero_extend reg_size w]
   due to the implicit castings in [sem]. *)
Lemma get_arg_shiftP s e ws w e' sh n :
  get_arg_shift ws [:: e ] = Some (e', sh, n)
  -> disj_fvars (read_e e)
  -> sem_pexpr true (p_globs p) s e = ok w
  -> exists ws1 (wbase : word ws1) (wsham : word U8),
       [/\ (ws <= ws1)%CMP
         , sem_pexpr true (p_globs p) s e' = ok (Vword wbase)
         , sem_pexpr true (p_globs p) s n = ok (Vword wsham)
         , to_word reg_size w
           = ok (shift_op sh (zero_extend reg_size wbase) (wunsigned wsham))
         & (disj_fvars (read_e e') /\ disj_fvars (read_e n))
       ].
Proof.
  move=> h hfve hseme.

  case: e hseme hfve h => // op.
  move=> [] //= gx.
  move=> [] //.
  move=> [[]||||||] //.
  move=> [] // z.

  rewrite /=.
  t_xrbindP=> vbase hget hsemop.
  move=> hfve.

  apply: obindP => sh' /oassertP [] /eqP ? hsh /oassertP [hchk [???]];
    subst ws e' sh' n.
  case: op hsemop hfve hsh hchk => // [[] | [|[]] | [|[]] | []] //= hsemop hfve.
  all: move=> [?]; subst sh.
  all: move=> /andP [] /ZleP hlo /ZleP hhi.

  all: move: hsemop
         => /sem_sop2I /= [wbase' [wsham' [wres [hbase hsham hop hw]]]].

  all: move: hbase => /to_wordI [ws1 [wbase [? /truncate_wordP [hws1 ?]]]];
         subst vbase wbase'.

  all: move: hsham.
  all: rewrite truncate_word_le //.
  all: move=> [?]; subst wsham'.
  all: move: hop => [?]; subst wres w.
  all: rewrite hget {hget} /= zero_extend_u truncate_word_u.
  all: eexists; eexists; eexists; split; by eauto.
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

(* TODO_ARM: This is an invariant of [lower_pexpr_aux] needed for the [Pif] case
   in the proof of [lower_pexpr].
   Is there a better way of keeping track of it? *)
#[ local ]
Definition inv_lower_pexpr_aux
  (ws : wsize) (op : sopn) (es : seq pexpr) : Prop :=
  [/\ disj_fvars (read_es es)
    , match op with
      | Oasm (BaseOp (None, ARM_op _ opts)) =>
          ~~ set_flags opts && ~~ is_conditional opts
      | _ => true
      end
    & sopn_tout op = [:: sword ws ]
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
  move=> /chk_ws_regP [? [? ?]]; subst aop es ws.
  case: is_var_in_memory.

  all: split; last done.
  all: clear hfvx.

  all: rewrite /= hget {hget} /=.
  all: eexists; first reflexivity.
  all: rewrite /exec_sopn /=.
  all: rewrite truncate_word_le // {hws} /=.
  all: by rewrite ?zero_extend_u.
Qed.

Lemma lower_loadP e :
  match e with Pload _ _ _ _ | Pget _ _ _ _ _ => Plower_pexpr_aux e
  | _ => True end.
Proof.
  case: e => // [ al aa | al ] ws x e s ws' ws'' aop es w.
  all: rewrite /lower_pexpr_aux /lower_load.
  all: move=> /chk_ws_regP [? [??]] hws hfve; subst ws' aop es.
  all: rewrite /sem_pexpr -/(sem_pexpr _ _ s e).

  - apply: on_arr_gvarP => n t hty ok_t.
    apply: rbindP => idx.
    apply: rbindP => ? ok_idx /to_intI ?; subst.
    apply: rbindP => r ok_r /ok_inj /Vword_inj[] ??; subst => /=.
    split.
    + rewrite /= ok_t /= ok_idx /= ok_r /=.
      eexists; first reflexivity.
      by rewrite /exec_sopn /= truncate_word_le // /= zero_extend_u.
    done.

  t_xrbindP=> wbase' vbase hgetx hbase woff' voff hseme hoff wres hread ? hw;
    subst ws''.
  move: hbase => /to_wordI [ws0 [wbase [? /truncate_wordP [hws0 ?]]]];
    subst wbase' vbase.
  move: hoff => /to_wordI [ws1 [woff [? /truncate_wordP [hws1 ?]]]];
    subst woff' voff.
  move: hw => [?]; subst wres.

  split; last done.
  clear hfve.

  rewrite /sem_pexprs /=.
  rewrite hgetx hseme {hgetx hseme} /=.
  rewrite !truncate_word_le // {hws0 hws1} /=.
  rewrite hread {hread} /=.

  eexists; first reflexivity.

  rewrite /exec_sopn /=.
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
  move=> /chk_ws_regP [?]; subst ws.
  case: op hw hfve => [ ws'' || [] ws'' | [] ws'' || [] |] // hw hfve.

  (* Case: [Oword_of_int]. *)
  - move: hw => /sem_sop1I /= [w' hw' hw].
    move: hw => /Vword_inj [?]; subst ws'.
    move=> /= ?; subst w.
    rewrite hws /= /mov_imm_op.
    {
      case: isSome => -[??]; subst op' es.
      all: split; last done.
      all: eexists; first by [|rewrite /= hseme /= /sem_sop1 /= hw'].
      all: by rewrite /exec_sopn /= truncate_word_u zero_extend_wrepr.
    }

  (* TODO_ARM: The following two cases are the same. *)

  (* Case: [Osignext]. *)
  - case: is_load; last by [].
    move: hw => /sem_sop1I /= [w' hw' hw].
    move: hw => /Vword_inj [?]; subst ws'.
    move=> /= ?; subst w.
    {
      case: ws'' hfve w' hw' => //= hfve w' hw'.
      all: move=> [? ?]; subst op' es.
      all: split; last done.
      all: clear hfve.
      all: rewrite /= -/(sem_pexpr _ _ s (Pload _ _ _ _)).
      all: rewrite hseme {hseme} /=.
      all: eexists; first reflexivity.
      all: rewrite /exec_sopn /=.
      all: rewrite hw' {hw'} /=.
      all: by rewrite !zero_extend_u.
    }

  (* Case: [Ozeroext]. *)
  - case: is_load; last by [].
    move: hw => /sem_sop1I /= [w' hw' hw].
    move: hw => /Vword_inj [?]; subst ws'.
    move=> /= ?; subst w.
    {
      case: ws'' hfve w' hw' => //= hfve w' hw'.
      all: move=> [? ?]; subst op' es.
      all: split; last done.
      all: clear hfve.
      all: rewrite /= -/(sem_pexpr _ _ s (Pload _ _ _ _)).
      all: rewrite hseme {hseme} /=.
      all: eexists; first reflexivity.
      all: rewrite /exec_sopn /=.
      all: rewrite hw' {hw'} /=.
      all: by rewrite !zero_extend_u.
    }

  (* Case: [Olnot]. *)
  move: hw => /sem_sop1I /= [w' hw' hw].
  move: hw hws => /Vword_inj [?]; subst ws'.
  move=> /= ? _; subst w.

  rewrite /arg_shift.
  case hshift: get_arg_shift => [[[e' sh] sham]|] /=.

  - have [ws1 [wbase [wsham [hws1 hbase hsham hv [hfvbase hfvsham]]]]] :=
      get_arg_shiftP hshift hfve hseme.
    case/to_wordI': hv => ws [] w'' []  hws ? hv; subst v.
    case/truncate_wordP: hw' => hws0 ?; subst w'.
    clear hshift hseme hfve.
    move=> [? ?]; subst op' es.
    have hfves := disj_fvars_read_es2 hfvbase hfvsham.
    clear hfvbase hfvsham.
    split; last done.
    clear hfves.
    rewrite /=.
    rewrite hbase hsham {hbase hsham} /=.
    eexists; first reflexivity.
    rewrite /exec_sopn /=.
    rewrite !truncate_word_le // {hws1} /=.
    by rewrite !zero_extend_u hv.

  clear hshift.
  move=> [? ?]; subst op' es.
  split; last done.
  rewrite /=.
  rewrite hseme {hseme} /=.
  eexists; first reflexivity.
  rewrite /exec_sopn /=.
  by rewrite hw' /= zero_extend_u.

  (* Case: [Oneg] *)
  case: hw hfve => // - [] //.
  apply: rbindP => /= w' ok_w' /ok_inj /Vword_inj[] ?? hfve /Some_inj[] ??; subst => /=.
  split; last by [].
  exists [:: v; @Vword U32 0 ].
  - by rewrite /= hseme wrepr0.
  by rewrite /exec_sopn /= /sopn_sem ok_w' truncate_word_u /= GRing.add0r wnot1_wopp zero_extend_u.
Qed.

Lemma mk_sem_divmodP ws op (w0 w1 : word ws) w :
  mk_sem_divmod op w0 w1 = ok w
  -> [/\ (w1 <> 0%R)
       , (wsigned w0 <> wmin_signed ws) \/ (w1 <> (-1)%R)
       & w = op w0 w1
     ].
Proof.
  rewrite /mk_sem_divmod.
  case: ifP => // hdiv hw.
  move: hdiv => /Bool.orb_false_elim [h0 h1].
  move: h0 => /eqP h0.
  move: h1 => /Bool.andb_false_elim h1.
  move: hw => [?]; subst w.

  case: h1 => /eqP h1.
  all: split.
  all: by auto.
Qed.

Section IS_MUL.

Variant is_mul_spec (e: pexpr) : option (pexpr * pexpr) -> Type :=
  | IsMulSome x y : e = Papp2 (Omul (Op_w U32)) x y -> is_mul_spec e (Some (x, y))
  | IsMulNone : is_mul_spec e None.

#[local] Hint Constructors is_mul_spec : core.

Lemma is_mulP e : is_mul_spec e (is_mul e).
Proof. by case: e => // - [] // - [] // - [] // x y; left. Qed.

End IS_MUL.

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

  case: ws hws => // hws.
  case hop: lower_Papp2_op => [[[mn' e0'] e1']|] //.
  rewrite /arg_shift /=.

  case hhas_shift: (mn' \in has_shift_mnemonics).
  - case hget_arg_shift: get_arg_shift => [[[b' sh] n]|].
    {
      (* TODO_ARM: This block is exactly the same in the unshifted case. *)
      (* The problem is that we can't abstract
         [to_word ws v0 = ok w0 -> to_word ws v1 = ok w1 -> sem_sop2_typed op w0 w1]
         as a hypothesis because of the dependent type in [sem_sop2_typed]. *)

      move=> -[??]; subst op' es.
      case: op hop hsemop => //;
        rewrite /lower_Papp2_op /=.

      all:
        match goal with
        | [ |- forall (_ : op_kind), _ -> _ ] => move=> [|ws''] //
        | [ |- forall (_ : cmp_kind), _ -> _ ] => move=> [|[] ws''] //
        | [ |- forall (_ : wsize), _ -> _ ] => move=> ws'' //
        end.

      (* TODO_ARM: These cases should go like the others. *)
      all:
        try
          match goal with
          | [ |- context[Odiv] ] => case: ws'' => //
          | [ |- context[Olsr] ] => case: ws'' => //
          | [ |- context[Olsl] ] => case: ws'' => //
          | [ |- context[Oasr] ] => case: ws'' => //
          | [ |- context[Oror] ] => case: ws'' => //
          | [ |- context[Orol] ] => case: ws'' => //
          end.
      all:
        try
          match goal with
          | [ |- context[ Oadd ] ] => rewrite /=
          | [ |- context[ Osub ] ] => rewrite /=
          | [ |- context[ Olsr ] ] => rewrite /=; case: is_zeroP => hzero
          | [ |- context[ Oasr ] ] => rewrite /=; case: is_zeroP => hzero
          | [ |- context[ Oror ] ] => rewrite /=; case: is_zeroP => hzero
          | [ |- context[ Orol ] ] => rewrite /=; case hconst: is_wconst => [ c | // ]; case: eqP => ?; [ subst c | ]
        end.

      all:
        repeat
          match goal with
          | [ |- context[ is_mul ] ] => case: is_mulP => [???|]; subst
          end.
      6: case: ifP => _.
      all: move=> [???] hsemop; subst mn' e0' e1'.
      all: discriminate hhas_shift || clear hhas_shift.

      all: move: hsemop => /sem_sop2I /= [w0' [w1' [w2 [hw0 hw1 hop hw]]]].
      all: move: hw0 => /to_wordI [ws0 [w0 [? /truncate_wordP [hws0 ?]]]];
             subst v0 w0'.
      all: move: hw1 => /to_wordI [ws1 [w1 [? /truncate_wordP [hws1 ?]]]];
             subst v1 w1'.
      all: move: hop => [?]; subst w2.
      all: move: hw => /Vword_inj [?]; subst ws'.
      all: move=> /= ?; subst w.
      all: have {hws0} hws0 := cmp_le_trans hws hws0.
      all: have {hws1} hws1 := cmp_le_trans hws hws1.

      2:{
        have [ws2 [wbase [wsham [hws2 hbase hsham hw1 [hfvbase hfvsham]]]]] :=
          get_arg_shiftP hget_arg_shift hfve0 hseme0.
        have hfves := disj_fvars_read_es3 hfve1 hfvbase hfvsham.
        split; last done.
        clear hfve1 hfvbase hfvsham hfves.
        case/truncate_wordP: hw1 => _ hw1.
        rewrite /= hseme1 hbase hsham {hseme1 hbase hsham} /=.
        eexists; first reflexivity.
        rewrite /exec_sopn /= /sopn_sem /= !truncate_word_le // {hws1 hws2} /=.
        rewrite (wsub_zero_extend _ _ hws) wsub_wnot1.
        rewrite !(zero_extend_idem _ hws).
        by rewrite zero_extend_u hw1.
      }
      all:
        have [ws2 [wbase [wsham [hws2 hbase hsham hw1 [hfvbase hfvsham]]]]] :=
          get_arg_shiftP hget_arg_shift hfve1 hseme1.
    
      all: have hfves := disj_fvars_read_es3 hfve0 hfvbase hfvsham.
      all: split; last done.
      all: clear hfve0 hfvbase hfvsham hfves.
      all: case/truncate_wordP: hw1 => _ hw1.

      all: rewrite /=.
      all: rewrite hseme0 hbase hsham {hseme0 hbase hsham} /=.
      all: eexists; first reflexivity.

      all: rewrite /exec_sopn /=.
      all: rewrite /sopn_sem /=.
      all: rewrite !truncate_word_le // {hws0 hws2} /=.

      1: rewrite (wadd_zero_extend _ _ hws).
      2: rewrite (wsub_zero_extend _ _ hws) wsub_wnot1.
      3: rewrite -(wand_zero_extend _ _ hws).
      4: rewrite -(wor_zero_extend _ _ hws).
      5: rewrite -(wxor_zero_extend _ _ hws).

      all: rewrite !(zero_extend_idem _ hws).
      all: by rewrite zero_extend_u hw1.
   }

  all: move=> [??]; subst op' es.
  all: case: op hop hsemop => //; rewrite /lower_Papp2_op /=.
  all:
    match goal with
    | [ |- forall _ : op_kind, _ -> _ ] => move=> [|ws''] //
    | [ |- forall (_ : cmp_kind), _ -> _ ] => move=> [|[] ws''] //
    | [ |- forall _ : wsize, _ -> _ ] => move=> ws'' //
    end.

  (* TODO_ARM: Can these cases go like the others? *)
  all:
    try
      match goal with
      | [ |- context[Odiv] ] => case: ws'' => //
      | [ |- context[Olsr] ] => case: ws'' => //
      | [ |- context[Olsl] ] => case: ws'' => //
      | [ |- context[Oasr] ] => case: ws'' => //
      | [ |- context[Oror] ] => case: ws'' => //
      | [ |- context[Orol] ] => case: ws'' => //
      end.

  Local Ltac on_is_zero h :=
    rewrite /=; case: is_zeroP;
      [ move => ?; subst; case: h => ?; subst
      | move => hzero ].

  all:
    try
      match goal with
      | [ |- context[ Oadd ] ] => rewrite /=
      | [ |- context[ Osub ] ] => rewrite /=
      | [ |- context[ Olsr ] ] => on_is_zero hseme1
      | [ |- context[ Oasr ] ] => on_is_zero hseme1
      | [ |- context[ Oror ] ] => on_is_zero hseme1
      | [ |- context[ Orol ] ] => rewrite /=; case hconst: is_wconst => [ c | // ]; case: eqP => ?; [ subst c | ]
      end.

  all:
    repeat
      match goal with
      | [ |- context[ is_mul ] ] => case: is_mulP => [???|]; subst
      end.
  all:
    repeat
      match goal with
      | [ |- context[ if _ then _ else _] ] => case: ifP => _
      end.

  all: move=> [???] hsemop; subst mn' e0' e1'.
  all: discriminate hhas_shift || clear hhas_shift.

  all: move: hsemop => /sem_sop2I /= [w0' [w1' [w2 [hw0 hw1 hop hw]]]].
  all: move: hw0 => /to_wordI [ws0 [w0 [? /truncate_wordP [hws0 ?]]]];
         subst v0 w0'.
  all: move: hw1.
  all: try case/to_wordI => ws1 [w1] [?].
  all: case/truncate_wordP => hws1 ?.
  all: subst.

  all: rewrite /=.
  all: match goal with
       | [ h : mk_sem_divmod _ _ _ = _ |- _ ] =>
           move: hop => /mk_sem_divmodP [hdiv0 hdiv1 ?]; subst w2
       end
       || (move: hop => [?]; subst w2).
  all: move: hw => /Vword_inj [?]; subst ws'.
  all: move=> /= ?; subst w.

  all: have hfves := disj_fvars_read_es2 hfve0 hfve1.
  2: have hfves' := disj_fvars_read_es2 hfve1 hfve0.
  7: have hfves' := disj_fvars_read_es2_app2 hfve1 hfve0.
  8, 10: have hfves' := disj_fvars_read_es2_app2 hfve0 hfve1.
  all: split; last done.

  all: clear hfve0 hfve1 hfves.

  all: rewrite /=.
  7: move: hseme0 => /=; t_xrbindP => ? -> ? -> /= hseme0.
  8, 9: move: hseme1 => /=; t_xrbindP => ? -> ? -> /= hseme1.
  all: try rewrite hseme0 {hseme0} /=.
  all: try rewrite hseme1 {hseme1} /=.

  all: eexists; first reflexivity.

  all: rewrite /exec_sopn /=.
  all: repeat (rewrite truncate_word_le /=; [ | by rewrite ?(cmp_le_trans hws hws0) ?(cmp_le_trans hws hws1) ]).

  (* Shift instructions take a byte as second argument. *)
  all:
    try
      match goal with
      | [ |- context[LSL] ] => rewrite hws1
      | [ |- context[LSR] ] => rewrite hws1
      | [ |- context[ASR] ] => rewrite hws1
      | [ |- context[ROR] ] => rewrite hws1
      end.

  (* The rest need [e32 <= ws1]. *)
  all: try rewrite (cmp_le_trans hws hws1).

  all: rewrite /=.

  1: rewrite (wadd_zero_extend _ _ hws).
  2,3: rewrite (wsub_zero_extend _ _ hws) wsub_wnot1.
  4: rewrite -(wand_zero_extend _ _ hws).
  5: rewrite -(wor_zero_extend _ _ hws).
  6: rewrite -(wxor_zero_extend _ _ hws).
  10: rewrite (wmul_zero_extend _ _ hws).
  1-6, 10: by rewrite !(zero_extend_idem _ hws).

  1: move: hseme0.
  2, 3: move: hseme1.
  1-3: rewrite /sem_sop2 /=; apply: rbindP => ? ->; apply: rbindP => ? -> /ok_inj/Vword_inj[] ??; subst => /=.
  1: have ? := cmp_le_antisym hws hws0; subst.
  2, 3: have ? := cmp_le_antisym hws hws1; subst.
  2: rewrite GRing.addrC.
  1-3: by rewrite !zero_extend_u.

  3: rewrite /sem_shr /sem_shift wshr0.
  6: rewrite /sem_sar /sem_shift wsar0.
  8: rewrite /sem_ror /sem_shift wror0.
  10, 11: have! := (is_wconstP true (p_globs p) s hconst); rewrite hseme1 => /truncate_wordP[] _.
  10: move => <-; rewrite /sem_rol /sem_shift wrol0.

  11: {
    move => ?; subst c.
    do 3 f_equal.
    rewrite /sem_rol /sem_shift !zero_extend_u wrepr_unsigned -wror_opp.
    apply: wror_m.
    change (wsize_bits _) with (wsize_size U256).
    by rewrite wunsigned_sub_mod.
  }

  all: by rewrite !zero_extend_u.
Qed.

Lemma lower_pexpr_auxP e :
  Plower_pexpr_aux e.
Proof.
  move=> s ws ws' aop es w.
  case: e => [||| gx | al aa ws0 x e || al ws0 x e | op e | op e0 e1 ||] //.

  - exact: lower_PvarP.
  - exact: (lower_loadP (Pget _ _ _ _ _)).
  - exact: (lower_loadP (Pload _ _ _ _)).
  - exact: lower_Papp1P.
  exact: lower_Papp2P.
Qed.

Lemma sem_i_lower_pexpr_aux s0 s1 s0' ws ws' e op es (w : word ws') lv tag :
  lower_pexpr_aux ws e = Some (op, es)
  -> eq_fv s0' s0
  -> (ws <= ws')%CMP
  -> disj_fvars (read_e e)
  -> disj_fvars (vars_lval lv)
  -> sem_pexpr true (p_globs p) s0 e = ok (Vword w)
  -> write_lval true (p_globs p) lv (Vword (zero_extend ws w)) s0 = ok s1
  -> exists2 s1',
       sem_i p' ev s0' (Copn [:: lv ] tag op es) s1'
       & eq_fv s1' s1.
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

  apply: Eopn.
  rewrite /sem_sopn /=.
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
  -> eq_fv s0' s0
  -> (ws <= ws')%CMP
  -> disj_fvars (read_e e)
  -> disj_fvars (vars_lval lv)
  -> sem_pexpr true (p_globs p) s0 e = ok (Vword w)
  -> write_lval true (p_globs p) lv (Vword (zero_extend ws w)) s0 = ok s1
  -> exists2 s1',
       let cmd := map (MkI ii) (pre ++ [:: Copn [:: lv ] tag op es ]) in
       sem p' ev s0' cmd s1' & eq_fv s1' s1.
Proof.
  move=> h hs00 hws hfve hfvlv hseme hwrite.

  move: s0 ws' pre op es w h hs00 hws hfve hfvlv hseme hwrite.
  case: e =>
    [||| gx | al aa ws0 x e || al ws0 x e | op e | op e0 e1 || ty c e0 e1] //
    s0 ws' pre aop es w h hs00 hws hfve hfvlv hseme hwrite.

  1-5: move: h => /no_preP [? h]; subst pre.
  1-5: have [s1' hsem' hs11] :=
    sem_i_lower_pexpr_aux tag h hs00 hws hfve hfvlv hseme hwrite.
  1-5: clear s0 ws w h hs00 hws hfve hfvlv hseme hwrite.
  1-5: exists s1'; last exact: hs11.
  1-5: clear hs11.
  1-5: apply: sem_seq1.
  1-5: exact: (EmkI ii hsem').

  clear hws.
  move: h.
  case: ty hfve hfvlv hseme => // ws0 hfve hfvlv hseme.

  rewrite /lower_pexpr.
  move=> /oassertP [] /eqP ?; subst ws0.
  case h: lower_pexpr_aux => [[op es']|] //.
  case hcond: sopn_set_is_conditional => [op' | //].
  case hc: lower_condition => [pre' c'] [? ? ?]; subst pre aop es.
  rename es' into es, pre' into pre.

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

  have [[ves hsemes hexeces] [hfves hopts htout]] :=
    lower_pexpr_auxP h hws0 hfve0 hseme0.

  set vres := [:: Vword (zero_extend ws w0) ].
  set vprev' := [:: Vword (zero_extend ws w1) ].

  have [s2' hwrite12' hs21] :
    exists2 s2',
      (if b
       then write_lvals true (p_globs p) s1' [:: lv ] vres = ok s2'
       else write_lvals true (p_globs p) s1' [:: lv ] vprev' = ok s2')
      & eq_fv s2' s1.
  {
    case: b hw hsemc' => hw _.
    all: move: hw => /Vword_inj [?]; subst ws'.
    all: move=> /= ?; subst w.
    all: rewrite zero_extend_u in hwrite.
    all: have [s2' hwrite12' hs21] := eeq_exc_write_lval hfvlv hs10 hwrite.
    all: exists s2'; last exact: hs21.
    all: by rewrite hwrite12'.
  }

  exists s2'; last exact: hs21.
  rewrite map_cat /=.
  apply: (sem_app hsem01').
  clear hsem01'.
  apply: sem_seq_ir.

  case: op hopts h hcond hexeces htout => //= -[[[//|] [mn opts]] | [] // ws''].
  - move: opts => [sf ic osh].
    set opts := {| set_flags := _; |}.
    move=> /= /andP [/negPf ? /negPf ?] h [?] hexeces htout; subst op' sf ic.
    apply: (sem_i_conditional (p := p') ev tag _ hsemc' _ _ hexeces hwrite12').
    - exact: (eeq_exc_sem_pexprs hfves hs10 hsemes).
    - by rewrite /= (eeq_exc_sem_pexpr hfve1 hs10 hseme1).
    rewrite /truncate_args /truncate_val /=.
    rewrite htout /=.
    by rewrite truncate_word_le.

  move=> _ h [?] hexeces htout; subst op'.
  constructor.
  rewrite /= /sem_sopn /= /sem_pexprs mapM_cat /= -/(sem_pexprs _ _ _ _) /=.
  rewrite (eeq_exc_sem_pexprs hfves hs10 hsemes) /= hsemc' /=
    (eeq_exc_sem_pexpr hfve1 hs10 hseme1) /=.
  clear hfves hfve1 hs10 hsemes hsemc' hseme1.
  case: b hw hwrite12' => hw hwrite12'.
  - move: hexeces.
    rewrite /exec_sopn /=.
    case: ves => [// | ? []]; t_xrbindP=> //= v _ -> /= [->] ?; subst ws''.
    move=> [?]; subst v.
    by rewrite truncate_word_le.
  move: hexeces.
  rewrite /exec_sopn /=.
  case: ves => [// | ? []]; t_xrbindP=> //= v _ -> /= [->] ?; subst ws''.
  move=> [?]; subst v.
  by rewrite truncate_word_le.
Qed.

Lemma sem_i_lower_store s0 s1 s0' ws ws' e aop es (w : word ws') lv tag :
  lower_store ws e = Some (aop, es)
  -> eq_fv s0' s0
  -> (ws <= ws')%CMP
  -> disj_fvars (read_e e)
  -> sem_pexpr true (p_globs p) s0 e = ok (Vword w)
  -> write_lval true (p_globs p) lv (Vword (zero_extend ws w)) s0' = ok s1
  -> sem_i p' ev s0' (Copn [:: lv ] tag (Oarm aop) es) s1.
Proof.
  move=> h hs00 hws hfv hseme hwrite.

  move: h.
  rewrite /lower_store.
  case hmn: store_mn_of_wsize => [mn|] //.

  case: e hseme hfv => [||| gx ||||||| ty c e0 e1] // hseme hfv [? ?];
    subst aop es.

  all: apply: Eopn.
  all: rewrite /sem_sopn /=.
  all: have /= := eeq_exc_sem_pexpr hfv hs00 hseme.
  all: clear hs00 hfv hseme.

  (* Case: unconditional execution. *)
  - move=> -> /=.
    all: cycle 1.

  (* Case: conditional execution. *)
  - t_xrbindP=> b vb hsemc hb vw0 v0 hseme0 hw0 vw1 v1 hseme1 hw1 hw.
    move: hb => /to_boolI ?; subst vb.
    case: b hsemc hw => hsemc ?.

    (* Subcase: condition is true. *)
    + subst vw0.
      move: hw0 => /truncate_valI [ws0 [w0 [? /truncate_wordP [hws0 ?] ?]]];
        subst ty w v0.
      move: hw1.
      rewrite /truncate_val /=.
      t_xrbindP.
      move=> w1 /to_wordI [ws1 [w1' [? /truncate_wordP [hws1 ?]]]] ?;
        subst v1 w1 vw1.
      all: cycle 1.

    (* Subcase: condition is false. *)
    + subst vw1.
      move: hw1 => /truncate_valI [ws1 [w1 [? /truncate_wordP [hws1 ?] ?]]];
        subst ty w v1.
      move: hw0.
      rewrite /truncate_val /=.
      t_xrbindP.
      move=> w0 /to_wordI [ws0 [w0' [? /truncate_wordP [hws0 ?]]]] ?;
        subst v0 w0 vw0.
      all: cycle 1.

  all: case: ws hws hwrite hmn => // hws hwrite [?]; subst mn.
  all: rewrite /exec_sopn /=.
  all: rewrite /sopn_sem /=.
  all: rewrite ?truncate_word_le //.

  1-3: rewrite /= zero_extend_u.
  1-3: by rewrite hwrite {hwrite}.

  all: rewrite hseme0 hsemc hseme1 {hseme0 hsemc hseme1} /=.
  all: rewrite truncate_word_le.
  2, 4, 6, 8, 10, 12: exact: cmp_le_trans hws hws1.
  all: rewrite truncate_word_le /=.
  2, 4, 6, 8, 10, 12: exact: cmp_le_trans hws hws0.
  all: rewrite (zero_extend_idem _ hws) {hws} /= in hwrite.
  1-3: rewrite zero_extend_u.
  all: by rewrite hwrite {hwrite}.
Qed.

Lemma lower_cassgn_wordP ii s0 lv tag ws e v v' s0' s1' pre lvs op es :
  lower_cassgn_word fv lv ws e = Some (pre, (lvs, op, es))
  -> sem_pexpr true (p_globs p) s0 e = ok v
  -> truncate_val (sword ws) v = ok v'
  -> write_lval true (p_globs p) lv v' s0' = ok s1'
  -> eq_fv s0' s0
  -> disj_fvars (read_e e)
  -> disj_fvars (vars_lval lv)
  -> sem_i p' ev s0' (Cassgn lv tag (sword ws) e) s1'
  -> exists2 s2',
       sem p' ev s0' (map (MkI ii) (pre ++ [:: Copn lvs tag op es ])) s2'
       & eq_fv s1' s2'.
Proof.
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
    apply: sem_seq_ir.
    exact: (sem_i_lower_store tag h hs00 hws hfve hseme hwrite01').

  case h: lower_pexpr => [[[pre' op'] es']|] // [? ? ? ?];
    subst pre lvs op es.

  have [s2 hwrite02 hs21] :=
    eeq_exc_write_lval hfvlv (eeq_excS hs00) hwrite01'.
  clear hwrite01'.

  have /= [s3' hsem03' hs32] :=
    sem_lower_pexpr ii tag h hs00 hws hfve hfvlv hseme hwrite02.
  exists s3'; last exact: (eeq_excS (eeq_excT hs32 hs21)).
  exact: hsem03'.
Qed.

Lemma lower_cassgn_boolP ii s0 lv tag e v v' s0' s1' irs :
  lower_cassgn_bool fv lv tag e = Some irs
  -> sem_pexpr true (p_globs p) s0 e = ok v
  -> truncate_val sbool v = ok v'
  -> write_lval true (p_globs p) lv v' s0' = ok s1'
  -> eq_fv s0' s0
  -> disj_fvars (read_e e)
  -> disj_fvars (vars_lval lv)
  -> sem_i p' ev s0' (Cassgn lv tag sbool e) s1'
  -> exists2 s2',
       sem p' ev s0' (map (MkI ii) irs) s2'
       & eq_fv s1' s2'.
Proof.
  rewrite /lower_cassgn_bool => h ok_v ok_v' ok_s1' hs00 hfve hfvlv hsem01'.
  case h: lower_condition_pexpr h => [ [] [] [] lvs op es c | // ] /Some_inj <-{irs}.
  have [ si [] hsem0i hs0i {} ok_v ] := sem_lower_condition_pexpr tag ii h hs00 hfve ok_v.
  have hsi0' : eq_fv si s0' := eeq_excT hs0i (eeq_excS hs00).
  have [ sj ok_sj hsj1' ] := eeq_exc_write_lval hfvlv hsi0' ok_s1'.
  eexists.
  - rewrite /= -cat1s.
    apply: (sem_app hsem0i).
    apply: sem_seq1.
    constructor.
    apply: Eassgn.
    + exact: ok_v.
    + exact: ok_v'.
    exact: ok_sj.
  exact: eeq_excS.
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

Lemma lower_add_carryP s0 s1 lvs tag es lvs' op' es' :
  sem_i p' ev s0 (Copn lvs tag (sopn_addcarry U32) es) s1
  -> lower_add_carry lvs es = Some (lvs', op', es')
  -> sem_i p' ev s0 (Copn lvs' tag op' es') s1.
Proof.
  case: lvs => [] // lv0 [] // lv1 [] //.
  case: es => [] // e0 [] // e1 [] // e2 [] //.
  move=> hsemi h.

  move: hsemi => /sem_iE.
  rewrite /sem_sopn /=.
  t_xrbindP=> res _ v0 hseme0 _ v1 hseme1 _ v2 hseme2 <- <- <- hexec hwrite.

  move: hexec.
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

  apply: Eopn.
  rewrite /sem_sopn /=.

  move: hwrite1.
  rewrite !wrepr_add !wrepr_unsigned.
  move=> hwrite1.

  move: h.
  case: e2 hseme2 => [| [] || gx |||||||] //= hseme2 [???];
    subst lvs' op' es'.
  all: rewrite /= hseme0 hseme1 /= {hseme0 hseme1}.

  2: rewrite hseme2 /= {hseme2}.

  all: rewrite /exec_sopn /=.
  all: rewrite !truncate_word_le // {hws hws'} /=.
  all: move: hwrite00 hwrite1.
  all: rewrite wunsigned_carry.

  1: move: hseme2 => [?]; subst b.
  1: rewrite /= Z.add_0_r wrepr0 GRing.addr0.

  all: by move=> -> /= ->.
Qed.

Section WITH_SHIFT_OP.

#[ local ]
Ltac intro_opn_args :=
  rewrite /sem_tuple /=;
  repeat
    match goal with
    | [ |- forall (_ : _ * _), _ ] => move=> []
    | [ |- forall (_ : option bool), _ ] => move=> ?
    | [ |- forall (_ : _ (word _)), _ ] => move=> ?
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
  let mytac := move=> /ok_inj; (move=> <- || move=> [] *; subst) in
  match goal with
  | [ b : bool |- context [{| is_conditional := true |}] ] =>
      case: b; mytac; last done
  end
  || mytac;
  rewrite /= !zero_extend_u.

Lemma with_shift_unop s eb ea ts (b: word ts) (a: u8) x vs sh opts r :
  (U32 ≤ ts)%CMP ->
  has_shift opts = None ->
  sem_pexpr true (p_globs p) s eb = ok (Vword b) ->
  sem_pexpr true (p_globs p) s ea = ok (Vword a) ->
  to_word reg_size x = ok (shift_op sh (zero_extend reg_size b) (wunsigned a)) ->
  exec_sopn (Oasm (BaseOp (None, ARM_op MVN opts))) [:: x & vs] = ok r ->
  exec_sopn (Oasm (BaseOp (None, ARM_op MVN (with_shift opts sh) ))) [:: Vword b, Vword a & vs] = ok r.
Proof.
  case: opts => S cc /= _ hts -> ok_b ok_a /to_wordI'[] xs [] wx [] hxs ->{x} hx.
  case: cc S => - [].
  all: rewrite /exec_sopn /=; t_xrbindP.
  all: intro_opn_args; rewrite !truncate_word_le // {hxs hts} => /ok_inj <-.
  all: destruct_args_wrapper vs.
  all: rewrite_exec.
  all: by rewrite hx.
Qed.

Lemma with_shift_binop mn s eb ea ts (b: word ts) (a: u8) x y vs sh opts r :
  mn \in [:: ADD; SUB; RSB; AND; BIC; EOR; ORR; CMP; TST] ->
  (U32 ≤ ts)%CMP ->
  has_shift opts = None ->
  sem_pexpr true (p_globs p) s eb = ok (Vword b) ->
  sem_pexpr true (p_globs p) s ea = ok (Vword a) ->
  to_word reg_size y = ok (shift_op sh (zero_extend reg_size b) (wunsigned a)) ->
  exec_sopn (Oasm (BaseOp (None, ARM_op mn opts))) [:: x, y & vs] = ok r ->
  exec_sopn (Oasm (BaseOp (None, ARM_op mn (with_shift opts sh) ))) [:: x, Vword b, Vword a & vs] = ok r.
Proof.
  rewrite !inE.
  case: opts => S cc /= _ mn_binop hts -> ok_b ok_a /to_wordI'[] ys [] wy [] hys ->{y} hy.
  case: cc S => - [].
  all: repeat case/orP: mn_binop => [ /eqP -> { mn } | mn_binop ]; last move/eqP: mn_binop => -> { mn }.
  all: rewrite /exec_sopn /=; t_xrbindP.
  all: intro_args_wrapper => {hys hts}.
  all: destruct_args_wrapper vs.
  all: rewrite_exec.
  all: by rewrite hy.
Qed.

Lemma with_shift_terop s eb ea ts (b: word ts) (a: u8) x y z vs sh opts r :
  (U32 ≤ ts)%CMP ->
  has_shift opts = None ->
  sem_pexpr true (p_globs p) s eb = ok (Vword b) ->
  sem_pexpr true (p_globs p) s ea = ok (Vword a) ->
  to_word reg_size y = ok (shift_op sh (zero_extend reg_size b) (wunsigned a)) ->
  exec_sopn (Oasm (BaseOp (None, ARM_op ADC opts))) [:: x, y, z & vs] = ok r ->
  exec_sopn (Oasm (BaseOp (None, ARM_op ADC (with_shift opts sh) ))) [:: x, Vword b, z, Vword a & vs] = ok r.
Proof.
  case: opts => S cc /= _ hts -> ok_b ok_a /to_wordI'[] ys [] wy [] hys ->{y} hy.
  case: S cc => - [].
  all: rewrite /exec_sopn /=; t_xrbindP.
  all: intro_args_wrapper => {hys hts}.
  all: destruct_args_wrapper vs.
  all: rewrite_exec.
  all: by rewrite hy.
Qed.

End WITH_SHIFT_OP.

Lemma lower_base_op s0 s1 lvs tag aop es lvs' op' es' :
  disj_fvars (read_es es)
  -> sem_i p' ev s0 (Copn lvs tag (Oasm (BaseOp (None, aop))) es) s1
  -> lower_base_op lvs aop es = Some (lvs', op', es')
  -> sem_i p' ev s0 (Copn lvs' tag op' es') s1.
Proof.
  move: aop => [mn opts].
  move=> hfve hsemi.
  rewrite /lower_base_op.
  assert (default : forall lvs' op' es', Some (lvs, Oasm (BaseOp (None, ARM_op mn opts)), es) = Some (lvs', op', es') -> sem_i p' ev s0 (Copn lvs' tag op' es') s1).
  - move: hsemi; clear => hsemi lvs' op' es' /Some_inj[? ? ?]; subst lvs' op' es'.
    exact: hsemi.
  case: ifP.
  - case: (_ \in _) => // _.
    exact: default.
  move/eqP => no_shift.
  case: eqP => mn_mvn.
  - subst mn.
    case: es hsemi hfve default => // x es hsemi hfve default.
    case x_has_shift: get_arg_shift => [ [ [] ebase sh esham ] | ] ; last exact: default.
    case/Some_inj => <-{lvs'} <-{op'} <-{es'}.
    constructor.
    have {} hfve : disj_fvars (read_e x).
    + move: hfve; clear.
      by rewrite /disj_fvars read_es_cons => /disjoint_union[].
    move/sem_iE: hsemi.
    rewrite /sem_sopn /=; t_xrbindP => r _ w hx ws hes <- hr hwrite.
    have [ ts [] t [] wsham [] hts ht hwsham hw [] hfb hfa ] := get_arg_shiftP x_has_shift hfve hx.
    rewrite ht hwsham hes /=.
    have -> /= := with_shift_unop hts no_shift ht hwsham hw hr.
    exact: hwrite.
  case: ifP => mn_binop.
  - case: es hsemi hfve default => // x [] // y es hsemi hfve default.
    case y_has_shift: get_arg_shift => [ [ [] ebase sh esham ] | ] ; last exact: default.
    case/Some_inj => <-{lvs'} <-{op'} <-{es'}.
    constructor.
    have {} hfve : disj_fvars (read_e y).
    + move: hfve; clear.
      by rewrite /disj_fvars !read_es_cons => /disjoint_union[] _ /disjoint_union[].
    move/sem_iE: hsemi.
    rewrite /sem_sopn /=; t_xrbindP => r _ w -> _ z hy ws hes <- <- hr hwrite.
    have [ ts [] t [] wsham [] hts ht hwsham hw [] hfb hfa ] := get_arg_shiftP y_has_shift hfve hy.
    rewrite ht hwsham hes /=.
    have -> /= := with_shift_binop mn_binop hts no_shift ht hwsham hw hr.
    exact: hwrite.
  case: eqP => // ?.
  subst mn.
  case: es hsemi hfve default => // x [] // y [] // z es hsemi hfve default.
  case y_has_shift: get_arg_shift => [ [ [] ebase sh esham ] | ] ; last exact: default.
  case/Some_inj => <-{lvs'} <-{op'} <-{es'}.
  constructor.
  have {} hfve : disj_fvars (read_e y).
  + move: hfve; clear.
    by rewrite /disj_fvars !read_es_cons => /disjoint_union[] _ /disjoint_union[].
  move/sem_iE: hsemi.
  rewrite /sem_sopn; t_xrbindP => r ws hes hr hwrite.
  move: hes; rewrite /=; t_xrbindP => ? -> /= _ ? hy _ ? -> ? hes <- <- ?; subst ws.
  have [ ts [] t [] wsham [] hts ht hwsham hw [] hfb hfa ] := get_arg_shiftP y_has_shift hfve hy.
  rewrite ht hwsham hes /=.
  have -> /= := with_shift_terop hts no_shift ht hwsham hw hr.
  exact: hwrite.
Qed.

Lemma lower_muluP s0 s1 lvs tag es lvs' op' es' :
  sem_i p' ev s0 (Copn lvs tag (sopn_mulu U32) es) s1
  -> lower_mulu lvs es = Some (lvs', op', es')
  -> sem_i p' ev s0 (Copn lvs' tag op' es') s1.
Proof.
  rewrite /lower_mulu => /sem_iE hsemi /Some_inj[] <- <- <- {lvs' op' es'}.
  apply: Eopn.
  move: hsemi.
  rewrite /sem_sopn /= /exec_sopn /= /sopn_sem /=.
  t_xrbindP => ? [] // x; t_xrbindP => - [] // y; t_xrbindP => - [] // ok_vs.
  move => ? a ok_a b ok_b /ok_inj <- <- ok_write.
  by rewrite ok_vs /= ok_a /= ok_b /=.
Qed.

Lemma lower_copnP s0 s1 lvs tag op es lvs' op' es' :
  disj_fvars (read_es es)
  -> sem_i p' ev s0 (Copn lvs tag op es) s1
  -> lower_copn lvs op es = Some (lvs', op', es')
  -> sem_i p' ev s0 (Copn lvs' tag op' es') s1.
Proof.
  case: op => // [[] // [] | [[[] aop]|]] //.
  - move=> ?; exact: lower_muluP.
  - move=> ?; exact: lower_add_carryP.
  - by move=> len hfve h [<- <- <-].
  - by move=> w hfve /sem_iE hsem /=; case: ifP => // hcmp [<- <- <-]; constructor.
  exact: lower_base_op.
Qed.

(* -------------------------------------------------------------------- *)

#[ local ]
Definition Pi (s0 : estate) (i : instr) (s1 : estate) :=
  disj_fvars (vars_I i)
  -> forall s0',
       eq_fv s0' s0
       -> exists2 s1',
            sem p' ev s0' (lower_i i) s1' & eq_fv s1' s1.

#[ local ]
Definition Pi_r (s0 : estate) (i : instr_r) (s1 : estate) :=
  forall ii, Pi s0 (MkI ii i) s1.

#[ local ]
Definition Pc (s0 : estate) (c : cmd) (s1 : estate) :=
  disj_fvars (vars_c c)
  -> forall s0',
       eq_fv s0' s0
       -> exists2 s1',
            sem p' ev s0' (lower_cmd c) s1' & eq_fv s1' s1.

#[ local ]
Definition Pfor
  (i : var_i) (rng : seq Z) (s0 : estate) (c : cmd) (s1 : estate) :=
  disj_fvars (Sv.add i (vars_c c))
  -> forall s0',
       eq_fv s0' s0
       -> exists2 s1',
            sem_for p' ev i rng s0' (lower_cmd c) s1' & eq_fv s1' s1.

#[ local ]
Definition Pfun
  scs0 (m0 : mem) (fn : funname) (vargs : seq value) scs1 (m1 : mem) (vres : seq value) :=
  sem_call p' ev scs0 m0 fn vargs scs1 m1 vres.


#[ local ]
Lemma Hskip : sem_Ind_nil Pc.
Proof.
  move=> s0 hfv s1 hs10.
  exists s1; last exact: hs10.
  exact: (Eskip p' ev s1).
Qed.

#[ local ]
Lemma Hcons : sem_Ind_cons p ev Pc Pi.
Proof.
  move=> s1 s2 s3 i c _ hpi _ hpc.
  move=> hfv s1' hs11.

  move: hfv => /disj_fvars_vars_c_cons [hfvi hfvc].
  have [s2' hsem12' hs22] := hpi hfvi s1' hs11.
  have [s3' hsem23' hs32] := hpc hfvc s2' hs22.
  clear s1 s2 hpi hpc hs11 hfvi hfvc hs22.

  exists s3'; last exact: hs32.
  clear hs32.

  exact: (sem_app hsem12' hsem23').
Qed.

#[ local ]
Lemma HmkI : sem_Ind_mkI p ev Pi_r Pi.
Proof.
  move=> ii i s1 s2 _ hi. exact: hi.
Qed.

#[ local ]
Lemma Hassgn : sem_Ind_assgn p Pi_r.
Proof.
  move=> s0 s1 lv tag ty e v v' hseme htrunc hwrite.
  move=> ii hfv s0' hs00.

  move: hfv => /disj_fvars_vars_I_Cassgn [hfvlv hfve].

  have [s1' hwrite' hs11] := eeq_exc_write_lval hfvlv hs00 hwrite.
  clear hwrite.

  assert (hassgn : sem_i p' ev s0' (Cassgn lv tag ty e) s1').
  - apply: Eassgn.
    + exact: (eeq_exc_sem_pexpr hfve hs00 hseme).
    + exact: htrunc.
    exact: hwrite'.

  assert (default: exists2 s1'0 : estate, sem p' ev s0' [:: MkI ii (Cassgn lv tag ty e)] s1'0 & eq_fv s1'0 s1).
  - exists s1'; last exact: hs11.
    by apply: sem_seq1; apply: EmkI.

  rewrite /lower_i.
  case: ty htrunc hassgn default => // [ | ws ] htrunc hassgn default.
  - case h: lower_cassgn_bool => [ irs | ]; last by [].
    have [ sj hsemj hs1j ] := lower_cassgn_boolP ii h hseme htrunc hwrite' hs00 hfve hfvlv hassgn.
    exists sj; first exact: hsemj.
    apply: eeq_excS.
    apply: eeq_excT hs1j.
    exact: eeq_excS.

  case h: lower_cassgn_word => [[pre [[lvs op] es]]|]; last by [].
  have [s2' hsem02' hs12'] :=
    lower_cassgn_wordP ii h hseme htrunc hwrite' hs00 hfve hfvlv hassgn.
  exists s2'; last exact: (eeq_excT (eeq_excS hs12') hs11).
  exact: hsem02'.
Qed.

#[ local ]
Lemma Hopn : sem_Ind_opn p Pi_r.
Proof.
  move=> s0 s1 tag op lvs es hsem01.
  move=> ii hfv s0' hs00.

  move: hfv => /disj_fvars_vars_I_Copn [hfvlvs hfve].

  move: hsem01.
  rewrite /sem_sopn.
  t_xrbindP=> vs xs hsemes hexec hwrite.

  have [s1' hwrite' hs11] := eeq_exc_write_lvals hfvlvs hs00 hwrite.
  clear hfvlvs hwrite.

  exists s1'; last exact: hs11.
  clear hs11.
  apply: sem_seq_ir.

  assert (hcopn : sem_i p' ev s0' (Copn lvs tag op es) s1').
  - apply: Eopn.
    rewrite /sem_sopn /=.
    rewrite (eeq_exc_sem_pexprs hfve hs00 hsemes) {hfve hs00 hsemes} /=.
    rewrite hexec /=.
    exact: hwrite'.
  clear hs00 hsemes hwrite'.

  case h: lower_copn => [[[lvs' op'] es']|].
  - exact: (lower_copnP hfve hcopn h).
  exact: hcopn.
Qed.

#[ local ]
Lemma Hsyscall : sem_Ind_syscall p Pi_r.
Proof.
  move=> s1 scs m s2 o xs es ves vs hes ho hw.
  move=> ii hdisj s1' hs1' /=.

  move: hdisj;
    rewrite /disj_fvars vars_I_syscall => /disjoint_union [hdisjx hdisje].
  have hes' := eeq_exc_sem_pexprs hdisje hs1' hes.
  have hs1'w:
    eq_fv (with_scs (with_mem s1' m) scs) (with_scs (with_mem s1 m) scs).
  + by rewrite /eq_fv /estate_eq_except /=; case: hs1' => ?? ->.
  have [s2' hw' hs2'] := eeq_exc_write_lvals hdisjx hs1'w hw.
  exists s2' => //.
  apply: sem_seq_ir; econstructor; eauto.
  by case: hs1' => -> -> _.
Qed.

#[ local ]
Lemma Hif_true : sem_Ind_if_true p ev Pc Pi_r.
Proof.
  move=> s0 s1 e c0 c1 hseme _ hc.
  move=> ii hfv s0' hs00.

  move: hfv => /disj_fvars_vars_I_Cif [hfve hfv0 _].

  rewrite /=.
  case h: lower_condition => [pre e'].
  have [s1' [hsem01' hs10 hseme']] := sem_lower_condition ii h hs00 hfve hseme.
  clear hseme hfve h.

  have [s2' hsem12' hs21] := hc hfv0 s1' hs10.
  clear hc hs00 hfv0 hs10.

  exists s2'; last exact: hs21.
  clear hs21.

  rewrite map_cat.
  apply: (sem_app hsem01').
  apply: sem_seq_ir. apply: Eif_true.
  - exact: hseme'.
  exact: hsem12'.
Qed.

#[ local ]
Lemma Hif_false : sem_Ind_if_false p ev Pc Pi_r.
Proof.
  move=> s0 s1 e c0 c1 hseme _ hc.
  move=> ii hfv s0' hs00.

  move: hfv => /disj_fvars_vars_I_Cif [hfve _ hfv1].

  rewrite /=.
  case h: lower_condition => [pre e'].
  have [s1' [hsem01' hs10 hseme']] := sem_lower_condition ii h hs00 hfve hseme.
  clear hseme hs00 hfve h.

  have [s2' hsem12' hs21] := hc hfv1 s1' hs10.
  clear hc hfv1 hs10.

  exists s2'; last exact: hs21.
  clear hs21.

  rewrite map_cat.
  apply: (sem_app hsem01').
  apply: sem_seq_ir. apply: Eif_false.
  - exact: hseme'.
  exact: hsem12'.
Qed.

#[ local ]
Lemma Hwhile_true : sem_Ind_while_true p ev Pc Pi_r.
Proof.
  move=> s0 s1 s2 s3 al c0 e c1 _ hc0 hseme _ hc1 _ hwhile.
  move=> ii hfv s0' hs00.

  have [hfv0 hfve hfv1] := disj_fvars_vars_I_Cwhile hfv.

  rewrite /=.
  case h: lower_condition => [pre e'].

  have [s1' hsem01' hs11] := hc0 hfv0 s0' hs00.
  have [s2' [hsem12' hs21 hseme']] := sem_lower_condition ii h hs11 hfve hseme.
  have [s3' hsem23' hs32] := hc1 hfv1 s2' hs21.
  have [s4' hsem34' hs43] := hwhile ii hfv s3' hs32.
  clear hc0 hseme hc1 hwhile hs00 hfv0 hfve hfv1 hs11 hs21 hs32.

  exists s4'; last exact: hs43.
  clear hs43.

  apply: sem_seq_ir. apply: Ewhile_true.
  - exact: (sem_app hsem01' hsem12').
  - exact: hseme'.
  - exact: hsem23'.
  clear hsem01' hsem12' hseme' hsem23'.

  move: hsem34' => /semE /=.
  rewrite h.
  move=> [s5' [hsemI34' hsem44']].
  rewrite (semE hsem44').
  exact: (sem_IE hsemI34').
Qed.

#[ local ]
Lemma Hwhile_false : sem_Ind_while_false p ev Pc Pi_r.
Proof.
  move=> s0 s1 al c0 e c1 _ hc0 hseme.
  move=> ii hfv s0' hs00.

  move: hfv => /disj_fvars_vars_I_Cwhile [hfv0 hfve _].

  rewrite /=.
  case h: lower_condition => [pre e'].

  have [s1' hsem01' hs11] := hc0 hfv0 s0' hs00.
  have [s2' [hsem12' hs21 hseme']] := sem_lower_condition ii h hs11 hfve hseme.
  clear hc0 hseme hs00 hfv0 hfve hs11.

  exists s2'; last exact: hs21.
  clear hs21.

  apply: sem_seq_ir. apply: Ewhile_false.
  - apply: (sem_app hsem01' hsem12').
  exact: hseme'.
Qed.

#[ local ]
Lemma Hfor : sem_Ind_for p ev Pi_r Pfor.
Proof.
  move=> s0 s1 i d lo hi c vlo vhi hlo hhi _ hfor.
  move=> ii hfv s0' hs00.

  move: hfv => /disj_fvars_vars_I_Cfor [hfvc hfvlo hfvhi].

  have [s1' hsemf01' hs11] := hfor hfvc s0' hs00.

  rewrite /=.
  exists s1'; last exact: hs11.
  clear hs11.

  apply: sem_seq_ir. apply: Efor.
  - exact: (eeq_exc_sem_pexpr hfvlo hs00 hlo).
  - exact: (eeq_exc_sem_pexpr hfvhi hs00 hhi).
  exact: hsemf01'.
Qed.

#[ local ]
Lemma Hfor_nil : sem_Ind_for_nil Pfor.
Proof.
  move=> s0 i c.
  move=> _ s0' hs00.
  exists s0'; last exact: hs00.
  clear hs00.
  exact: EForDone.
Qed.

#[ local ]
Lemma Hfor_cons : sem_Ind_for_cons p ev Pc Pfor.
Proof.
  move=> s0 s1 s2 s3 i v vs c hwrite hsem hc hsemf hfor.
  move=> hfv s0' hs00.

  have {hwrite} hwrite : write_lval true (p_globs p) i v s0 = ok s1.
  - exact: hwrite.

  have [hfvi hfvc] := disj_fvars_Cfor_c hfv.

  have [s1' hwrite01' hs11] := eeq_exc_write_lval hfvi hs00 hwrite.
  clear hfvi hs00 hwrite.

  have [s2' hsem12' hs22] := hc hfvc s1' hs11.
  have [s3' hsem23' hs33] := hfor hfv s2' hs22.
  clear hs11 hs22.

  exists s3'; last exact: hs33.
  clear hs33.

  apply: EForOne.
  - exact: hwrite01'.
  - exact: hsem12'.
  exact: hsem23'.
Qed.

#[ local ]
Lemma Hcall : sem_Ind_call p ev Pi_r Pfun.
Proof.
  move=> s0 scs0 m0 s1 lvs fn args vargs vs hsemargs _ hfun hwrite.
  move=> ii hfv s0' hs0'.
  rewrite /=.

  have hwith_s0' : eq_fv (with_scs (with_mem s0' m0) scs0) (with_scs (with_mem s0 m0) scs0).
  - split=> //. move: hs0' => [_ _ hvm0']. exact: hvm0'.

  move: hfv => /disj_fvars_vars_I_Ccall [hfvlvs hfvargs].

  have [s1' hwrite01' hs11] := eeq_exc_write_lvals hfvlvs hwith_s0' hwrite.
  clear hfvlvs hwith_s0' hwrite.

  exists s1'; last exact: hs11.
  clear hs11.

  apply: sem_seq_ir. apply: Ecall.
  - exact: (eeq_exc_sem_pexprs hfvargs hs0' hsemargs).
  - move: hs0' => [-> -> _]. exact: hfun.
  - exact: hwrite01'.
Qed.

#[ local ]
Lemma Hproc : sem_Ind_proc p ev Pc Pfun.
Proof.
  move=> scs0 m0 scs1 m1 fn fd vargs vargs' s0 s1 s2 vres vres'.
  move=> hget htruncargs hinit hwrite _ hc hres htruncres hscs hfin.

  have [_ hfvres hfvc] := disj_fvars_get_fundef hget.

  have [s2' hsem12' hs22] := hc hfvc s1 (eeq_excR fvars s1).
  clear hfvc.

  apply: EcallRun.
  - by rewrite get_map_prog hget.
  - exact: htruncargs.
  - exact: hinit.
  - exact: hwrite.
  - exact: hsem12'.
  - rewrite -(sem_pexprs_get_var _ (p_globs p)).
    rewrite -(sem_pexprs_get_var _ (p_globs p)) in hres.
    exact: (eeq_exc_sem_pexprs (disj_fvars_vars_l_read_es hfvres) hs22 hres).
  - exact: htruncres.
  - move: hs22 => [-> _ _]. done.
  - move: hs22 => [_ -> _]. exact: hfin.
Qed.

Lemma lower_callP
  (f : funname) scs mem scs' mem' (va vr : seq value) :
  sem_call p ev scs mem f va scs' mem' vr
  -> sem_call (lower_prog p) ev scs mem f va scs' mem' vr.
Proof.
  exact:
    (sem_call_Ind
       Hskip
       Hcons
       HmkI
       Hassgn
       Hopn
       Hsyscall
       Hif_true
       Hif_false
       Hwhile_true
       Hwhile_false
       Hfor
       Hfor_nil
       Hfor_cons
       Hcall
       Hproc).
Qed.

End PROOF.
