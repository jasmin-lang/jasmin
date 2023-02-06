From mathcomp Require Import
  all_ssreflect
  all_algebra.
Import
  Order.POrderTheory
  Order.TotalTheory.
From mathcomp.word Require Import ssrZ.
Require Import Psatz.

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

(* TODO_ARM: Move? *)
Lemma get_arg_shiftP_aux z :
  (0 <= z <= 31)%Z
  -> wunsigned (wand (wrepr U8 z) (wrepr U8 31)) = wunsigned (wrepr U8 z).
Proof.
  move=> hrange.
  change 31%Z with (2 ^ Z.of_nat 5 - 1)%Z.
  rewrite wand_modulo.
  rewrite wunsigned_repr_small.
  - apply: Z.mod_small. lia.
  change (wbase U8) with 256%Z.
  lia.
Qed.

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
  {syscall_state : Type}
  {sc_sem : syscall_sem syscall_state}
  {eft : eqType}
  {pT : progT eft}
  {sCP : semCallParams}
  (p : prog)
  (ev : extra_val_t)
  (options : lowering_options)
  (warning : instr_info -> warning_msg -> instr_info)
  (fv : fresh_vars)
  (is_var_in_memory : var_i -> bool)
  (fv_correct : fvars_correct (all_fresh_vars fv) (fvars fv) (p_funcs p)).

Notation fvars := (fvars fv).
Notation lower_Pvar := (lower_Pvar is_var_in_memory).
Notation lower_pexpr_aux := (lower_pexpr_aux is_var_in_memory).
Notation lower_pexpr := (lower_pexpr fv is_var_in_memory).
Notation lower_cmd :=
  (lower_cmd
     (fun _ _ => lower_i)
     options
     warning
     fv
     is_var_in_memory).
Notation lower_prog :=
  (lower_prog
     (fun _ _ => lower_i)
     options
     warning
     fv
     is_var_in_memory).
Notation lower_i := (lower_i fv is_var_in_memory).
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
      .[fvNF fv <- ok (NF_of_word res)]
      .[fvZF fv <- ok (ZF_of_word res)]
      .[fvCF fv <- ok (wunsigned res != res_unsigned)]
      .[fvVF fv <- ok (wsigned res != res_signed)]%vmap
  in
  with_vm s vm'.

Definition estate_of_TST s (w0 w1 : wreg) : estate :=
  let res := wand w0 w1 in
  let vm' :=
    (evm s)
      .[fvNF fv <- ok (NF_of_word res)]
      .[fvZF fv <- ok (ZF_of_word res)]
      .[fvCF fv <- ok false]%vmap
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
  all: rewrite !Fv.setP_neq; first reflexivity.

  all: apply/eqP.
  all: move=> ?; subst x.
  all: apply: hx.

  all: by move: fvars_NF fvars_ZF fvars_CF fvars_VF.
Qed.

Lemma sem_condition_mn ii mn s es ws0 ws1 (w0 : word ws0) (w1 : word ws1) :
  mn \in condition_mnemonics
  -> (reg_size <= ws0)%CMP
  -> (reg_size <= ws1)%CMP
  -> sem_pexprs (p_globs p) s es = ok [:: Vword w0; Vword w1 ]
  -> let w0' := zero_extend reg_size w0 in
     let w1' := zero_extend reg_size w1 in
     let aop := Oarm (ARM_op mn default_opts) in
     let i := Copn (lflags_of_mn fv mn) AT_none aop es in
     sem p' ev s [:: MkI ii i ] (estate_of_condition_mn mn s w0' w1').
Proof.
  move=> hmn hws0 hws1 hsemes /=.
  apply: sem_seq1. apply: EmkI. apply: Eopn.
  rewrite /sem_sopn /=.
  rewrite hsemes {hsemes} /=.

  case: mn hmn => // _.
  all: rewrite /exec_sopn /=.
  all: by rewrite /truncate_word hws0 hws1 {hws0 hws1} /=.
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

Lemma lower_condition_Papp2P s op e0 e1 mn e es v0 v1 v :
  lower_condition_Papp2 fv op e0 e1 = Some (mn, e, es)
  -> sem_pexpr (p_globs p) s e0 = ok v0
  -> sem_pexpr (p_globs p) s e1 = ok v1
  -> sem_sop2 op v0 v1 = ok v
  -> exists (ws0 ws1 : wsize) (w0 : word ws0) (w1 : word ws1),
      let w0' := zero_extend reg_size w0 in
      let w1' := zero_extend reg_size w1 in
      [/\ mn \in condition_mnemonics
        , (reg_size <= ws0)%CMP
        , (reg_size <= ws1)%CMP
        , sem_pexprs (p_globs p) s es = ok [:: Vword w0; Vword w1 ]
        & sem_pexpr (p_globs p) (estate_of_condition_mn mn s w0' w1') e = ok v
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

  1: case hTST: lower_TST => [es'|] //.
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

    rewrite /get_gvar /=.
    repeat t_get_var.

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
  all: repeat t_get_var.

  (* Case [w0 == w1]. *)
  - by rewrite wsub_wnot1 -GRing.Theory.subr_eq0.

  (* Case [w0 != w1]. *)
  - by rewrite wsub_wnot1 -GRing.Theory.subr_eq0.

  (* Case [w0 <s w1]. *)
  - rewrite /sem_sop1 /NF_of_word /=.
    rewrite wsub_wnot1 wsigned_wsub_wnot1.
    by rewrite -wltsE.

  (* Case [w0 <u w1]. *)
  - rewrite /sem_sop1 /=.
    rewrite wsub_wnot1.
    rewrite nzcv_of_aluop_CF_sub.
    rewrite -wleuE.
    by rewrite ltNge.

  (* Case [w0 <=s w1]. *)
  - rewrite /sem_sop2 /NF_of_word /ZF_of_word /=.
    rewrite wsub_wnot1 wsigned_wsub_wnot1.
    rewrite GRing.subr_eq0.
    rewrite -wltsE.
    by rewrite le_eqVlt eqtype.inj_eq; last exact: word.srepr_inj.

  (* Case [w0 <=u w1]. *)
  - rewrite /sem_sop2 /ZF_of_word /=.
    rewrite wsub_wnot1.
    rewrite nzcv_of_aluop_CF_sub.
    rewrite -wleuE.
    rewrite GRing.subr_eq0.
    by rewrite le_eqVlt ltNge orbC.

  (* Case [w0 >s w1]. *)
  - rewrite /sem_sop2 /NF_of_word /ZF_of_word /=.
    rewrite wsub_wnot1 wsigned_wsub_wnot1.
    rewrite GRing.subr_eq0.
    rewrite -(Bool.negb_involutive (_ && _)) negb_and Bool.negb_involutive.
    rewrite -wltsE.
    by rewrite ltNge le_eqVlt eqtype.inj_eq; last exact: word.srepr_inj.

  (* Case [w0 >u w1]. *)
  - rewrite /sem_sop2 /ZF_of_word /=.
    rewrite wsub_wnot1.
    rewrite nzcv_of_aluop_CF_sub.
    rewrite GRing.subr_eq0.
    rewrite -wleuE.
    by rewrite lt_def andbC.

  (* Case [w0 >=s w1]. *)
  - rewrite /sem_sop2 /NF_of_word /=.
    rewrite wsub_wnot1 wsigned_wsub_wnot1.
    rewrite -(Bool.negb_involutive (_ == _)).
    rewrite -wltsE.
    by rewrite leNgt.

  (* Case [w0 >=u w1]. *)
  - rewrite wsub_wnot1.
    rewrite nzcv_of_aluop_CF_sub.
    by rewrite -wleuE.
Qed.

Lemma sem_lower_condition_pexpr s0 s0' ii e v lvs aop es c :
  lower_condition_pexpr fv e = Some (lvs, aop, es, c)
  -> eq_fv s0' s0
  -> disj_fvars (read_e e)
  -> sem_pexpr (p_globs p) s0 e = ok v
  -> exists s1',
       [/\ sem p' ev s0' [:: MkI ii (Copn lvs AT_none aop es) ] s1'
         , eq_fv s1' s0
         & sem_pexpr (p_globs p) s1' c = ok v
       ].
Proof.
  move=> h hs00 hfv hseme.

  move: h.
  case: e hseme hfv => //= [op e0 e1].
  t_xrbindP=> v0 hsem0 v1 hsem1.
  move=> hsemop hfv.

  case h: lower_condition_Papp2 => [[[mn e] es']|] // [? ? ? ?];
    subst lvs aop es c.

  move: hfv => /disj_fvars_read_e_Papp2 [hfv0 hfv1].

  have hsem0' := eeq_exc_sem_pexpr hfv0 hs00 hsem0.
  have hsem1' := eeq_exc_sem_pexpr hfv1 hs00 hsem1.
  clear hfv0 hsem0 hsem1 hfv1.

  have [ws0 [ws1 [w0 [w1 [hmn hws0 hws1 hsemes hseme]]]]] :=
    lower_condition_Papp2P h hsem0' hsem1' hsemop.
  clear h hsemop hsem0' hsem1'.

  have /= hsem' := sem_condition_mn ii hmn hws0 hws1 hsemes.
  clear hws0 hws1 hsemes.

  all: eexists;
    split;
    first exact: hsem';
    last exact: hseme.
  all: clear hsem' hseme.

  all: apply: (eeq_excT _ hs00).
  all: exact: (estate_of_condition_mn_eq_fv s0' _ _ hmn).
Qed.

Lemma sem_lower_condition s0 s0' ii e v pre e' :
  lower_condition fv e = (pre, e')
  -> eq_fv s0' s0
  -> disj_fvars (read_e e)
  -> sem_pexpr (p_globs p) s0 e = ok v
  -> exists s1',
       [/\ sem p' ev s0' (map (MkI ii) pre) s1'
         , eq_fv s1' s0
         & sem_pexpr (p_globs p) s1' e' = ok v
       ].
Proof.
  move=> h hs00 hfv hseme.

  move: h.
  rewrite /lower_condition.
  case h: lower_condition_pexpr => [[[[lvs op] es] c]|] [? ?];
    subst e' pre.

  - exact: (sem_lower_condition_pexpr ii h hs00 hfv hseme).
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
Lemma get_arg_shiftP s e ws ws0 (w : word ws0) e' sh n :
  get_arg_shift ws [:: e ] = Some (e', sh, n)
  -> disj_fvars (read_e e)
  -> sem_pexpr (p_globs p) s e = ok (Vword w)
  -> exists ws1 (wbase : word ws1) (wsham : word U8),
       [/\ (ws <= ws1)%CMP
         , sem_pexpr (p_globs p) s e' = ok (Vword wbase)
         , sem_pexpr (p_globs p) s n = ok (Vword wsham)
         , zero_extend reg_size w
           = shift_op sh (zero_extend reg_size wbase) (wunsigned wsham)
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

  case: ws w hsemop => // w hsemop.
  case: op hsemop hfve => // [[] | [|[]] | [|[]] | []] //= hsemop hfve.
  all: case: ifP => // /andP [] /ZleP hlo /ZleP hhi.
  all: move=> [? ? ?]; subst e' sh n.

  all: move: hsemop
         => /sem_sop2I /= [wbase' [wsham' [wres [hbase hsham hop hw]]]].

  all: move: hbase => /to_wordI [ws1 [wbase [? /truncate_wordP [hws1 ?]]]];
         subst vbase wbase'.

  all: move: hsham.
  all: rewrite /truncate_word wsize_le_U8 /=.
  all: move=> [?]; subst wsham'.

  all: move: hop.
  all: rewrite /mk_sem_sop2 /=.
  all: move=> [?]; subst wres.

  all: move: hw => /Vword_inj [?]; subst ws0.
  all: move=> /= ?; subst w.

  all: rewrite hget {hget} /=.

  all: eexists; eexists; eexists;
         split;
         first exact: hws1;
         first reflexivity;
         first reflexivity;
         move=> //.
  all: clear hws1 hfve.

  all: rewrite /sem_shr /sem_shl /sem_sar /sem_ror /=.
  all: rewrite /sem_shift /=.
  all: rewrite !zero_extend_u.
  all: rewrite get_arg_shiftP_aux; first reflexivity.
  all: lia.
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
  (ws : wsize) (aop : arm_op) (es : seq pexpr) : Prop :=
  [/\ disj_fvars (read_es es)
    , let '(ARM_op _ opts) := aop in
      (set_flags opts = false /\ is_conditional opts = false)
    & sopn_tout (Oarm aop) = [:: sword ws ]
  ].

(* We prove the following for each case of [lower_pexpr_aux]. *)
#[ local ]
Definition ok_lower_pexpr_aux
  (s : estate) (ws ws' : wsize) (aop : arm_op) (es : seq pexpr) (w : word ws') :
  Prop :=
  (exists2 vs,
     sem_pexprs (p_globs p) s es = ok vs
     & exec_sopn (Oarm aop) vs = ok [:: Vword (zero_extend ws w) ])
  /\ inv_lower_pexpr_aux ws aop es.

#[ local ]
Definition Plower_pexpr_aux (e : pexpr) : Prop :=
  forall s ws ws' aop es (w : word ws'),
    lower_pexpr_aux ws e = Some (aop, es)
    -> (ws <= ws')%CMP
    -> disj_fvars (read_e e)
    -> sem_pexpr (p_globs p) s e = ok (Vword w)
    -> ok_lower_pexpr_aux s ws aop es w.

Lemma lower_PvarP gx :
  Plower_pexpr_aux (Pvar gx).
Proof.
  move=> s ws ws' aop es w.
  move=> h hws hfvx /= hget.
  move: h.
  rewrite /lower_pexpr_aux /lower_Pvar.
  case: ws hws => //= hws [? ?]; subst aop es.
  case: is_var_in_memory.

  all: split; last done.
  all: clear hfvx.

  all: rewrite /= hget {hget} /=.
  all: eexists; first reflexivity.
  all: rewrite /exec_sopn /=.
  all: rewrite /truncate_word hws {hws} /=.
  all: by rewrite ?zero_extend_u.
Qed.

Lemma lower_PloadP ws x e :
  Plower_pexpr_aux (Pload ws x e).
Proof.
  move=> s ws' ws'' aop es w.
  move=> h hws' hfve hseme.

  move: hseme.
  rewrite /sem_pexpr -/(sem_pexpr _ s e).
  t_xrbindP=> wbase' vbase hgetx hbase woff' voff hseme hoff wres hread ? hw;
    subst ws''.
  move: hbase => /to_wordI [ws0 [wbase [? /truncate_wordP [hws0 ?]]]];
    subst wbase' vbase.
  move: hoff => /to_wordI [ws1 [woff [? /truncate_wordP [hws1 ?]]]];
    subst woff' voff.
  move: hw => [?]; subst wres.

  move: h.
  rewrite /lower_pexpr_aux /lower_Pload.
  case: ws' hws' => // hws -[? ?]; subst aop es.

  split; last done.
  clear hfve.

  rewrite /sem_pexprs /=.
  rewrite hgetx hseme {hgetx hseme} /=.
  rewrite /truncate_word hws0 hws1 {hws0 hws1} /=.
  rewrite hread {hread} /=.

  eexists; first reflexivity.

  rewrite /exec_sopn /=.
  rewrite /truncate_word hws {hws} /=.
  by rewrite zero_extend_u.
Qed.

Lemma lower_Papp1P op e:
  Plower_pexpr_aux (Papp1 op e).
Proof.
  move=> s ws ws' aop es w.
  move=> h hws hfve.

  rewrite /sem_pexpr -/(sem_pexpr _ s e).
  t_xrbindP=> v hseme hw.

  move: h.
  rewrite /lower_pexpr_aux /lower_Papp1.
  case: ws hws => // hws'.
  case: op hw hfve => [[] || [] ws'' | [] ws'' || [] |] // hw hfve.

  (* Case: [Oword_of_int]. *)
  - move: hw => /sem_sop1I /= [w' hw' hw].
    move: hw => /Vword_inj [?]; subst ws'.
    move=> /= ?; subst w.
    move=> [? ?]; subst aop es.
    split; last done.
    clear hfve.

    rewrite /=.
    rewrite hseme {hseme} /=.

    rewrite /sem_sop1 /=.
    rewrite hw' {hw'} /=.
    eexists; first reflexivity.
    by rewrite /exec_sopn /=.

  (* TODO_ARM: The following two cases are the same. *)

  (* Case: [Osignext]. *)
  - case: is_load; last by [].
    move: hw => /sem_sop1I /= [w' hw' hw].
    move: hw => /Vword_inj [?]; subst ws'.
    move=> /= ?; subst w.
    {
      case: ws'' hfve w' hw' => //= hfve w' hw'.
      all: move=> [? ?]; subst aop es.
      all: split; last done.
      all: clear hfve.
      all: rewrite /= -/(sem_pexpr _ s (Pload _ _ _)).
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
      all: move=> [? ?]; subst aop es.
      all: split; last done.
      all: clear hfve.
      all: rewrite /= -/(sem_pexpr _ s (Pload _ _ _)).
      all: rewrite hseme {hseme} /=.
      all: eexists; first reflexivity.
      all: rewrite /exec_sopn /=.
      all: rewrite hw' {hw'} /=.
      all: by rewrite !zero_extend_u.
    }

  (* Case: [Olnot]. *)
  move: hw => /sem_sop1I /= [w' hw' hw].
  move: hw => /Vword_inj [?]; subst ws'.
  move=> /= ?; subst w.

  move: hw' => /to_wordI [ws0 [w0' [? /truncate_wordP [hws0 ?]]]]; subst v w'.
  rewrite /arg_shift.
  case hshift: get_arg_shift => [[[e' sh] sham]|] /=.

  - have [ws1 [wbase [wsham [hws1 hbase hsham -> [hfvbase hfvsham]]]]] :=
      get_arg_shiftP hshift hfve hseme.
    clear hshift hseme hfve w0'.
    move=> [? ?]; subst aop es.
    have hfves := disj_fvars_read_es2 hfvbase hfvsham.
    clear hfvbase hfvsham.
    split; last done.
    clear hfves.
    rewrite /=.
    rewrite hbase hsham {hbase hsham} /=.
    eexists; first reflexivity.
    rewrite /exec_sopn /=.
    rewrite /truncate_word hws1 {hws1} /=.
    by rewrite !zero_extend_u.

  clear hshift.
  move=> [? ?]; subst aop es.
  split; last done.
  rewrite /=.
  rewrite hseme {hseme} /=.
  eexists; first reflexivity.
  rewrite /exec_sopn /=.
  rewrite /truncate_word hws0 /=.
  by rewrite zero_extend_u.
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

Lemma lower_Papp2P op e0 e1 :
  Plower_pexpr_aux (Papp2 op e0 e1).
Proof.
  move=> s ws ws' [mn opts] es w.
  move=> h hws hfve hseme.

  move: hseme.
  rewrite /sem_pexpr -!/(sem_pexpr _ s _).
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

      move=> [? ? ?]; subst mn' opts es.
      case: op hop hsemop => //.

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
          end.
      all:
        try
          match goal with
          | [ |- context[ Olsr ] ] => rewrite /=; case: is_zeroP => hzero
          | [ |- context[ Oasr ] ] => rewrite /=; case: is_zeroP => hzero
          | [ |- context[ Oror ] ] => rewrite /=; case: is_zeroP => hzero
        end.

      all: move=> [? ? ?] hsemop; subst mn e0' e1'.
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

      all:
        have [ws2 [wbase [wsham [hws2 hbase hsham hw1 [hfvbase hfvsham]]]]] :=
          get_arg_shiftP hget_arg_shift hfve1 hseme1.
      all: clear hfve1 hseme1 hget_arg_shift.
      all: have hfves := disj_fvars_read_es3 hfve0 hfvbase hfvsham.
      all: split; last done.
      all: clear hfve0 hfvbase hfvsham hfves.

      all: rewrite /=.
      all: rewrite hseme0 hbase hsham {hseme0 hbase hsham} /=.
      all: eexists; first reflexivity.

      all: rewrite /exec_sopn /=.
      all: rewrite /sopn_sem /=.
      all: rewrite /truncate_word hws0 hws2 {hws0 hws2} /=.

      1: rewrite (wadd_zero_extend _ _ hws).
      2: rewrite (wsub_zero_extend _ _ hws) wsub_wnot1.
      3: rewrite -(wand_zero_extend _ _ hws).
      4: rewrite -(wor_zero_extend _ _ hws).
      5: rewrite -(wxor_zero_extend _ _ hws).

      all: rewrite !(zero_extend_idem _ hws).
      all: rewrite hw1 {hw1} /=.
      all: by rewrite !zero_extend_u.
   }

  all: move=> [? ? ?]; subst mn' opts es.
  all: case: op hop hsemop => //.
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
      end.

  Local Ltac on_is_zero h :=
    rewrite /=; case: is_zeroP;
      [ move => ?; subst; case: h => ?; subst
      | move => hzero ].

  all:
    try
      match goal with
      | [ |- context[ Olsr ] ] => on_is_zero hseme1
      | [ |- context[ Oasr ] ] => on_is_zero hseme1
      | [ |- context[ Oror ] ] => on_is_zero hseme1
      end.

  all: move=> [? ? ?] hsemop; subst mn e0' e1'.
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
  all: split; last done.
  all: clear hfve0 hfve1 hfves.

  all: rewrite /=.
  all: rewrite hseme0 {hseme0} /=.
  all: try rewrite hseme1 {hseme1} /=.
  all: eexists; first reflexivity.

  all: rewrite /exec_sopn /=.
  all: rewrite /truncate_word /=.

  all: rewrite (cmp_le_trans hws hws0).

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
  2: rewrite (wsub_zero_extend _ _ hws) wsub_wnot1.
  3: rewrite -(wand_zero_extend _ _ hws).
  4: rewrite -(wor_zero_extend _ _ hws).
  5: rewrite -(wxor_zero_extend _ _ hws).
  6: rewrite (wmul_zero_extend _ _ hws).
  1-6: by rewrite !(zero_extend_idem _ hws).

  3: rewrite /sem_shr /sem_shift wshr0.
  6: rewrite /sem_sar /sem_shift wsar0.
  8: rewrite /sem_ror /sem_shift wror0.

  all: by rewrite !zero_extend_u.
Qed.

Lemma lower_pexpr_auxP e :
  Plower_pexpr_aux e.
Proof.
  move=> s ws ws' aop es w.
  case: e => [||| gx ||| ws0 x e | op e | op e0 e1 ||] // h hws hfve hseme.

  - exact: (lower_PvarP h hws hfve hseme).
  - exact: (lower_PloadP h hws hfve hseme).
  - exact: (lower_Papp1P h hws hfve hseme).
  exact: (lower_Papp2P h hws hfve hseme).
Qed.

Lemma sem_i_lower_pexpr_aux s0 s1 s0' ws ws' e aop es (w : word ws') lv tag :
  lower_pexpr_aux ws e = Some (aop, es)
  -> eq_fv s0' s0
  -> (ws <= ws')%CMP
  -> disj_fvars (read_e e)
  -> disj_fvars (vars_lval lv)
  -> sem_pexpr (p_globs p) s0 e = ok (Vword w)
  -> write_lval (p_globs p) lv (Vword (zero_extend ws w)) s0 = ok s1
  -> exists2 s1',
       sem_i p' ev s0' (Copn [:: lv ] tag (Oarm aop) es) s1'
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
  s0 s1 s0' ii ws ws' e pre aop es (w : word ws') lv tag :
  lower_pexpr ws e = Some (pre, aop, es)
  -> eq_fv s0' s0
  -> (ws <= ws')%CMP
  -> disj_fvars (read_e e)
  -> disj_fvars (vars_lval lv)
  -> sem_pexpr (p_globs p) s0 e = ok (Vword w)
  -> write_lval (p_globs p) lv (Vword (zero_extend ws w)) s0 = ok s1
  -> exists2 s1',
       let cmd := map (MkI ii) (pre ++ [:: Copn [:: lv ] tag (Oarm aop) es ]) in
       sem p' ev s0' cmd s1' & eq_fv s1' s1.
Proof.
  move=> h hs00 hws hfve hfvlv hseme hwrite.

  move: s0 ws' pre aop es w h hs00 hws hfve hfvlv hseme hwrite.
  case: e => [||| gx ||| ws0 x e | op e | op e0 e1 || ty c e0 e1] //
    s0 ws' pre aop es w h hs00 hws hfve hfvlv hseme hwrite.

  1-4: move: h => /no_preP [? h]; subst pre.
  1-4: have [s1' hsem' hs11] :=
    sem_i_lower_pexpr_aux tag h hs00 hws hfve hfvlv hseme hwrite.
  1-4: clear s0 ws w h hs00 hws hfve hfvlv hseme hwrite.
  1-4: exists s1'; last exact: hs11.
  1-4: clear hs11.
  1-4: apply: sem_seq1.
  1-4: exact: (EmkI ii hsem').

  clear hws.
  move: h.
  case: ty hfve hfvlv hseme => // ws0 hfve hfvlv hseme.

  rewrite /lower_pexpr.
  case h: lower_pexpr_aux => [[[mn opts] es']|] //.
  case: (ws =P ws0) => // ?; subst ws0.
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

  move: opts hopts h hexeces htout=> [sf ic osh].
  set opts := {| set_flags := _; |}.
  move=> /= [? ?] h hexeces htout; subst sf ic.

  set aop := ARM_op mn opts.
  set vres := [:: Vword (zero_extend ws w0) ].
  set vprev' := [:: Vword (zero_extend ws w1) ].

  have [s2' hwrite12' hs21] :
    exists2 s2',
      (if b
       then write_lvals (p_globs p) s1' [:: lv ] vres = ok s2'
       else write_lvals (p_globs p) s1' [:: lv ] vprev' = ok s2')
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
  apply: sem_seq1. apply: EmkI.

  apply: (sem_i_conditional (p := p') ev tag _ hsemc' _ _ hexeces hwrite12').

  - exact: (eeq_exc_sem_pexprs hfves hs10 hsemes).
  - rewrite /=. by rewrite (eeq_exc_sem_pexpr hfve1 hs10 hseme1).
  rewrite /truncate_args /truncate_val /=.
  rewrite htout /=.
  by rewrite /truncate_word hws1 /=.
Qed.

Lemma sem_i_lower_store s0 s1 s0' ws ws' e aop es (w : word ws') lv tag :
  lower_store ws e = Some (aop, es)
  -> eq_fv s0' s0
  -> (ws <= ws')%CMP
  -> disj_fvars (read_e e)
  -> sem_pexpr (p_globs p) s0 e = ok (Vword w)
  -> write_lval (p_globs p) lv (Vword (zero_extend ws w)) s0' = ok s1
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
  all: rewrite /truncate_word.

  1-3: rewrite hws {hws} /=.
  1-3: rewrite zero_extend_u.
  1-3: by rewrite hwrite {hwrite}.

  all: rewrite hseme0 hsemc hseme1 {hseme0 hsemc hseme1} /=.
  all: rewrite /truncate_word.
  all: rewrite (cmp_le_trans hws hws0) {hws0} /=.
  all: rewrite (cmp_le_trans hws hws1) {hws1} /=.
  all: rewrite (zero_extend_idem _ hws) {hws} /= in hwrite.
  1-3: rewrite zero_extend_u.
  all: by rewrite hwrite {hwrite}.
Qed.

Lemma lower_cassgnP ii s0 lv tag ty e v v' s0' s1' pre lvs op es :
  lower_cassgn fv is_var_in_memory lv ty e = Some (pre, (lvs, op, es))
  -> sem_pexpr (p_globs p) s0 e = ok v
  -> truncate_val ty v = ok v'
  -> write_lval (p_globs p) lv v' s0' = ok s1'
  -> eq_fv s0' s0
  -> disj_fvars (read_e e)
  -> disj_fvars (vars_lval lv)
  -> sem_i p' ev s0' (Cassgn lv tag ty e) s1'
  -> exists2 s2',
       sem p' ev s0' (map (MkI ii) (pre ++ [:: Copn lvs tag op es ])) s2'
       & eq_fv s1' s2'.
Proof.
  move=> h hseme htrunc hwrite01' hs00 hfve hfvlv hsem01'.

  move: h.
  rewrite /lower_cassgn.
  case: ty hsem01' htrunc => [|||ws] // hsem01' htrunc.

  move: htrunc.
  rewrite /truncate_val.
  t_xrbindP=> w' hw' ?; subst v'.
  move: hw' => /to_wordI [ws' [w [? /truncate_wordP [hws ?]]]]; subst v w'.

  case: is_lval_in_memory.
  - case h: lower_store => [[op' es']|] // [? ? ? ?]; subst pre lvs op es.
    exists s1'; last exact: eeq_excR.
    apply: sem_seq1. apply: EmkI.
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
  sem_i p' ev s0 (Copn lvs tag (Oaddcarry U32) es) s1
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
  all: rewrite /truncate_word hws hws' /=.
  all: move: hwrite00 hwrite1.
  all: rewrite wunsigned_carry.

  1: move: hseme2 => [?]; subst b.
  1: rewrite /= Z.add_0_r wrepr0 GRing.addr0.

  all: by move=> -> /= ->.
Qed.

Lemma lower_base_op s0 s1 lvs tag aop es lvs' op' es' :
  sem_i p' ev s0 (Copn lvs tag (Oasm (BaseOp (None, aop))) es) s1
  -> lower_base_op lvs aop es = Some (lvs', op', es')
  -> sem_i p' ev s0 (Copn lvs' tag op' es') s1.
Proof.
  move: aop => [mn opts].
  move=> hsemi.
  rewrite /lower_base_op.
  case: (_ \in _) => //.
  move=> [? ? ?]; subst lvs' op' es'.
  exact: hsemi.
Qed.

Lemma lower_copnP s0 s1 lvs tag op es lvs' op' es' :
  sem_i p' ev s0 (Copn lvs tag op es) s1
  -> lower_copn lvs op es = Some (lvs', op', es')
  -> sem_i p' ev s0 (Copn lvs' tag op' es') s1.
Proof.
  case: op => // [[] | [[[] aop]|]] //.
  - exact: lower_add_carryP.
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

  rewrite /lower_i.
  case h: lower_cassgn => [[pre [[lvs op] es]]|].
  - have [s2' hsem02' hs12'] :=
      lower_cassgnP ii h hseme htrunc hwrite' hs00 hfve hfvlv hassgn.
    exists s2'; last exact: (eeq_excT (eeq_excS hs12') hs11).
    exact: hsem02'.

  exists s1'; last exact: hs11.
  clear hs11.

  apply: sem_seq1. apply: EmkI.
  exact: hassgn.
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
  apply: sem_seq1. apply: EmkI.

  assert (hcopn : sem_i p' ev s0' (Copn lvs tag op es) s1').
  - apply: Eopn.
    rewrite /sem_sopn /=.
    rewrite (eeq_exc_sem_pexprs hfve hs00 hsemes) {hfve hs00 hsemes} /=.
    rewrite hexec /=.
    exact: hwrite'.
  clear hfve hs00 hsemes hwrite'.

  case h: lower_copn => [[[lvs' op'] es']|].
  - exact: (lower_copnP hcopn h).
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
  apply: sem_seq1; constructor; econstructor; eauto.
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
  apply: sem_seq1. apply: EmkI. apply: Eif_true.
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
  apply: sem_seq1. apply: EmkI. apply: Eif_false.
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

  apply: sem_seq1. apply: EmkI. apply: Ewhile_true.
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

  apply: sem_seq1. apply: EmkI. apply: Ewhile_false.
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

  apply: sem_seq1. apply: EmkI. apply: Efor.
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

  have {hwrite} hwrite : write_lval (p_globs p) i v s0 = ok s1.
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
  move=> s0 scs0 m0 s1 inli lvs fn args vargs vs hsemargs _ hfun hwrite.
  move=> ii hfv s0' hs0'.
  rewrite /=.

  have hwith_s0' : eq_fv (with_scs (with_mem s0' m0) scs0) (with_scs (with_mem s0 m0) scs0).
  - split=> //. move: hs0' => [_ _ hvm0']. exact: hvm0'.

  move: hfv => /disj_fvars_vars_I_Ccall [hfvlvs hfvargs].

  have [s1' hwrite01' hs11] := eeq_exc_write_lvals hfvlvs hwith_s0' hwrite.
  clear hfvlvs hwith_s0' hwrite.

  exists s1'; last exact: hs11.
  clear hs11.

  apply: sem_seq1. apply: EmkI. apply: Ecall.
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
  - rewrite -(sem_pexprs_get_var (p_globs p)).
    rewrite -(sem_pexprs_get_var (p_globs p)) in hres.
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
