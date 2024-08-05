From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype.
From mathcomp Require Import fintype finfun ssralg.
From Coq Require Import Relation_Operators.
Require Import
  oseq
  compiler_util
  psem
  psem_facts
  label
  lea_proof
  one_varmap sem_one_varmap
  linear
  linear_sem
  fexpr
  fexpr_sem.
Require Import
  arch_decl
  arch_extra
  arch_sem
  sem_params_of_arch_extra.
Require Export asm_gen.
Import Utf8.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section ASM_EXTRA.

#[local] Existing Instance withsubword.

Context {syscall_state : Type} {sc_sem : syscall_sem syscall_state}
        `{asm_e : asm_extra} {call_conv: calling_convention}
         {asm_scsem : asm_syscall_sem}.

(* -------------------------------------------------------------------- *)
Lemma xreg_of_varI {ii x y} :
  xreg_of_var ii x = ok y →
  match y with
  | Reg r => of_var x = Some r
  | Regx r => of_var x = Some r
  | XReg r => of_var x = Some r
  | _ => False
  end. 
Proof.
  rewrite /xreg_of_var.
  case heqxr: (to_xreg x) => [ r | ]; first by move=> [<-].
  case heqrx: (to_reg x) => [ r | ]; first by move=> [<-].
  by case heqr: (to_regx x) => [ r | // ]; move=> [<-].
Qed.

(* -------------------------------------------------------------------- *)
Definition of_rbool (v : rflagv) :=
  if v is Def b then Vbool b else undef_b.

(* -------------------------------------------------------------------- *)
Definition eqflags (m: estate) (rf: rflagmap) : Prop :=
  ∀ (f: rflag), value_uincl (evm m).[to_var f] (of_rbool (rf f)).

Variant disj_rip rip :=
  | Drip of
    (∀ (r:reg_t), to_var r <> rip) &
    (∀ (r:regx_t), to_var r <> rip) &
    (∀ (r:xreg_t), to_var r <> rip) &
    (∀ (f:rflag_t), to_var f <> rip).

Variant lom_eqv rip (m : estate) (lom : asmmem) :=
  | MEqv of
      escs m = asm_scs lom
    & emem m = asm_mem lom
    & (evm m).[rip] = Vword lom.(asm_rip)
    & disj_rip rip
    & (∀ r, value_uincl (evm m).[to_var r] (Vword (asm_reg lom r)))
    & (∀ r, value_uincl (evm m).[to_var r] (Vword (asm_regx lom r)))
    & (∀ r, value_uincl (evm m).[to_var r] (Vword (asm_xreg lom r)))
    & eqflags m (asm_flag lom).

(* -------------------------------------------------------------------- *)
Definition value_of_bool (b: exec bool) : exec value :=
  match b with
  | Ok b => ok (Vbool b)
  | Error ErrAddrUndef => ok undef_b
  | Error e => Error e
  end.

Lemma value_of_bool_bool eb b :
  value_of_bool eb = ok (Vbool b)
  -> eb = ok b.
Proof.
  case: eb.
  - by move=> ? [<-].
  by move=> [].
Qed.

Lemma value_uincl_to_bool_value_of_bool ve ve' eb b :
  value_uincl ve ve'
  -> to_bool ve = ok b
  -> value_of_bool eb = ok ve'
  -> eb = ok b.
Proof.
  move=> hincl hto_bool hof_bool.
  have ? := to_boolI hto_bool; subst ve.
  have ? := value_uinclE hincl; subst ve'.
  exact: value_of_bool_bool hof_bool.
Qed.

(* Equivalent to [value_uincl_to_bool_value_of_bool], but stated as it is used
   in proofs. *)
Lemma value_of_bool_uincl ve eb b :
  to_bool ve = ok b
  -> (exists2 ve', value_of_bool eb = ok ve' & value_uincl ve ve')
  -> eb = ok b.
Proof.
  move=> hto_bool [ve' hof_bool hincl].
  exact: value_uincl_to_bool_value_of_bool hincl hto_bool hof_bool.
Qed.

Lemma value_of_bool_to_bool_of_rbool x :
  value_of_bool (to_bool (of_rbool x)) = ok (of_rbool x).
Proof. by case: x. Qed.

(* -------------------------------------------------------------------- *)
Lemma getreg wdb rip r v s xs :
  lom_eqv rip s xs →
  get_var wdb s.(evm) (to_var r) = ok v →
  value_uincl v (Vword (xs.(asm_reg) r)).
Proof. by case => _ _ _ _ eqv _ _ _ /get_varP [-> _ _]. Qed.

Lemma ofgetreg wdb rip x r v s xs :
  lom_eqv rip s xs →
  of_var x = Some r →
  get_var wdb s.(evm) x = ok v →
  value_uincl v (Vword (xs.(asm_reg) r)).
Proof. move=> lom h; have <- := of_varI h; apply: getreg lom. Qed.

(* -------------------------------------------------------------------- *)
Lemma getregx wdb rip r v s xs :
  lom_eqv rip s xs →
  get_var wdb s.(evm) (to_var r) = ok v →
  value_uincl v (Vword (xs.(asm_regx) r)).
Proof. by case => _ _ _ _ _ eqv' _ _ /get_varP [-> _ _]. Qed.

Lemma ofgetregx wdb rip x r v s xs :
  lom_eqv rip s xs →
  of_var x = Some r →
  get_var wdb s.(evm) x = ok v →
  value_uincl v (Vword (xs.(asm_regx) r)).
Proof. move=> lom h; have <- := of_varI h; apply: getregx lom. Qed.

(* -------------------------------------------------------------------- *)
Lemma getxreg wdb rip r v s xs :
  lom_eqv rip s xs →
  get_var wdb (evm s) (to_var r) = ok v →
  value_uincl v (Vword (asm_xreg xs r)).
Proof. by case => _ _ _ _ _ _ eqv _ /get_varP [-> _ _]. Qed.

Lemma ofgetxreg wdb rip x r v s xs :
  lom_eqv rip s xs →
  of_var x = Some r →
  get_var wdb (evm s) x = ok v →
  value_uincl v (Vword (asm_xreg xs r)).
Proof. move=> lom h; have <- := of_varI h; apply: getxreg lom. Qed.

(* -------------------------------------------------------------------- *)

Lemma getflag wdb rip f v s xs :
  lom_eqv rip s xs →
  get_var wdb (evm s) (to_var f) = ok v →
  value_uincl v (of_rbool (asm_flag xs f)).
Proof. by case => _ _ _ _ _ _ _ eqf /get_varP [-> _ _]. Qed.

Lemma xgetflag_ex wdb ii m rf x f v :
  eqflags m rf →
  of_var_e ii x = ok f →
  get_var wdb (evm m) x = ok v →
  value_uincl v (of_rbool (rf f)).
Proof. by move => eqm /of_var_eI <- /get_varP [ -> _ _ ]. Qed.

Corollary xgetflag wdb ii m rf x f v b :
  eqflags m rf →
  of_var_e ii x = ok f →
  get_var wdb (evm m) x = ok v →
  to_bool v = ok b →
  rf f = Def b.
Proof.
move => eqm ok_f ok_v /to_boolI ?; subst v.
by have /value_uinclE := xgetflag_ex eqm ok_f ok_v; case: (rf _) => //= ? [] <-.
Qed.


(* -------------------------------------------------------------------- *)
Lemma lom_rip wdb rip s xs :
  lom_eqv rip s xs →
  get_var wdb (evm s) rip = ok (Vword (asm_rip xs)).
Proof. by rewrite /get_var orbC => -[_ _ -> *] /=. Qed.

(* -------------------------------------------------------------------- *)

Context
  (agparams : asm_gen_params).

Notation assemble_cond := (agp_assemble_cond agparams).

Lemma xscale_ok ii z sc :
  scale_of_z ii z = ok sc ->
  wunsigned (word_of_scale sc) = z.
Proof.
  case: z => //.
  case => [ [] | [] | ] //.
  case => //.
  case => //.
  all: move => /ok_inj <-.
  all: rewrite wunsigned_repr_small //.
  all: split => //.
  all: apply: Z.lt_le_trans (wbase_m (wsize_le_U8 Uptr)).
  all: done.
Qed.

Lemma assemble_leaP rip ii sz sz' (w:word sz') lea adr m s:
  (sz ≤ Uptr)%CMP →
  (sz ≤ sz')%CMP →
  lom_eqv rip m s →
  sem_lea sz (evm m) lea = ok (zero_extend sz w) →
  assemble_lea ii lea = ok adr →
  zero_extend sz (decode_addr s adr) = zero_extend sz w.
Proof.
  move=> hsz64 hsz lom hsem; rewrite /assemble_lea.
  t_xrbindP => ob hob oo hoo sc hsc <- /=.
  rewrite /decode_reg_addr /=.
  move: hsem; rewrite /sem_lea.
  apply rbindP => wb hwb; apply rbindP => wo hwo heq.
  have <- := ok_inj heq.
  rewrite !(wadd_zero_extend, wmul_zero_extend) // GRing.addrA.
  congr (_ + _ + _ * _)%R.
  + by rewrite zero_extend_wrepr.
  + case: lea_base hob hwb => /= [vo | [<-] [<-] /=]; last by apply zero_extend0.
    t_xrbindP => r /of_var_eP h <- v /= /(ofgetreg lom h) + h1.
    by have [? [? [-> /word_uincl_truncate h2 /h2 /truncate_wordP []]]] := to_wordI h1.
  + by rewrite -(xscale_ok hsc).
  case: lea_offset hoo hwo => /= [vo | [<-] [<-] /=]; last by apply zero_extend0.
  t_xrbindP => r /of_var_eP h <- v /= /(ofgetreg lom h) + h1.
  by have [? [? [-> /word_uincl_truncate h2 /h2 /truncate_wordP []]]] := to_wordI h1.
Qed.

Lemma addr_of_fexprP rip ii sz sz' (w: word sz') e adr m s:
  (sz ≤ sz')%CMP →
  lom_eqv rip m s →
  sem_fexpr m.(evm) e = ok (Vword w) ->
  addr_of_fexpr rip ii sz e = ok adr ->
  zero_extend sz (decode_addr s adr) = zero_extend sz w.
Proof.
  rewrite /addr_of_fexpr => hsz lom he.
  t_xrbindP => hsz64.
  case heq: mk_lea_rec => [lea | //].
  assert (hsemlea := mk_lea_recP hsz64 hsz heq he).
  case hb: lea_base => [b | ]; last by apply (assemble_leaP hsz64 hsz lom hsemlea).
  case: eqP => [ | _]; last by apply (assemble_leaP hsz64 hsz lom hsemlea).
  t_xrbindP => hbrip.
  case ho: lea_offset => [ // | ] _ <- /=.
  move: hsemlea; rewrite /sem_lea ho hb /= hbrip (lom_rip _ lom) /= truncate_word_le //= => /ok_inj <-.
  by rewrite GRing.mulr0 GRing.addr0 GRing.addrC wadd_zero_extend // zero_extend_wrepr.
Qed.

Lemma addr_of_xpexprP rip m s ii x p r vx wx vp wp:
  lom_eqv rip m s →
  addr_of_xpexpr rip ii Uptr x p = ok r ->
  get_var true (evm m) x = ok vx ->
  to_pointer vx = ok wx ->
  sem_fexpr m.(evm) p = ok vp ->
  to_pointer vp = ok wp ->
  decode_addr s r = (wx + wp)%R.
Proof.
  rewrite /addr_of_xpexpr => eqm ha hx hvx hp hvp.
  have he: sem_fexpr m.(evm) (Fapp2 (Oadd (Op_w Uptr)) (Fvar x) p) = ok (Vword (wx + wp)).
  + by rewrite /= /get_gvar /= hx /= hp /= /sem_sop2 /= hvx hvp.
  have := addr_of_fexprP _ eqm he ha.
  by rewrite !zero_extend_u => h;apply h.
Qed.

Variant check_sopn_argI rip ii args e : arg_desc -> stype -> Prop :=
| CSA_Implicit i ty :
       is_implicit i e
    -> check_sopn_argI rip ii args e (ADImplicit i) ty

| CSA_Explicit k n o a a' ty :
       onth args n = Some a
    -> arg_of_rexpr agparams k rip ii ty e = ok a'
    -> compat_imm ty a a'
    -> check_oreg o a
    -> check_sopn_argI rip ii args e (ADExplicit k n o) ty.

Lemma check_sopn_argP rip ii args e sp :
  check_sopn_arg agparams rip ii args e sp ->
  check_sopn_argI rip ii args e sp.1 sp.2.
Proof.
case: sp => -[i|k n o] ty; first by apply: CSA_Implicit.
rewrite /check_sopn_arg /=; case Enth: onth => [a|] //.
case E: arg_of_rexpr => [a'|] // /andP[??].
by apply: (CSA_Explicit (a := a) (a' := a')).
Qed.

Lemma var_of_flagP rip m s f v ty vt:
  lom_eqv rip m s
  -> get_var true (evm m) (to_var f) = ok v
  -> of_val ty v = ok vt
  -> exists2 v' : value,
      Let b := st_get_rflag s f in ok (Vbool b) = ok v'
      & of_val ty v' = ok vt.
Proof.
  move=> lom h; rewrite /st_get_rflag.
  have [b ?]:= get_varE h; subst v.
  have /value_uinclE <- := getflag lom h.
  move=> /of_valE; case: (asm_flag s f) => //= ?[]? <-; subst => /=; eauto.
Qed.

Lemma var_of_regP rip E m s r v ty vt:
  lom_eqv rip m s
  -> get_var true (evm m) (to_var r) = ok v
  -> of_val ty v = ok vt
  -> exists2 v' : value,
      Ok E (Vword ((asm_reg s) r)) = ok v'
      & of_val ty v' = ok vt.
Proof. move=> lom /(getreg lom) hg /(of_value_uincl hg) <-; eauto. Qed.

Lemma var_of_regP_eq rip m s (r:reg_t) v vt:
  lom_eqv rip m s
  -> get_var true (evm m) (to_var r) = ok v
  -> to_pointer v = ok vt
  -> asm_reg s r = vt.
Proof.
  move=> lom /(getreg lom) /of_value_uincl h1 /(h1 (sword Uptr)) /=.
  by rewrite truncate_word_u => -[].
Qed.

Lemma is_implicitP i e :
  is_implicit i e →
  ∃ vi, e = Rexpr (Fvar {| v_var := var_of_implicit_arg i ; v_info := vi |}).
Proof. by case: e => //- [] // [] x vi //= /eqP ->; exists vi. Qed.

Section EVAL_ASSEMBLE_COND.

Definition get_rf (rf : rflagmap) (x : rflag) : exec bool :=
  if rf x is Def b then ok b else undef_error.

Definition get_rf_to_bool_of_rbool rf x :
  get_rf rf x = to_bool (of_rbool (rf x)).
Proof.
  rewrite /get_rf. by case: (rf x).
Qed.

Definition assemble_cond_spec :=
  forall ii m rr rf e c v,
    (∀ r, value_uincl (evm m).[to_var r] (Vword (rr r))) ->
    eqflags m rf
    -> agp_assemble_cond agparams ii e = ok c
    -> sem_fexpr m.(evm) e = ok v
    -> exists2 v',
         value_of_bool (eval_cond rr (get_rf rf) c) = ok v' & value_uincl v v'.

Context
  (eval_assemble_cond : assemble_cond_spec).

Lemma check_sopn_arg_sem_eval rip m s ii args e ad ty v vt :
  lom_eqv rip m s
  -> check_sopn_arg agparams rip ii args e (ad,ty)
  -> sem_rexpr m.(emem) m.(evm) e = ok v
  -> of_val ty v = ok vt
  -> exists2 v', eval_arg_in_v s args ad ty = ok v'
     & of_val ty v' = ok vt.
Proof.
  move=> eqm /check_sopn_argP /= h.
  case: h vt.
  + move=> i {ty} ty /is_implicitP[] vi -> vt /=.
    case: i => /= [f | r]; first by apply: var_of_flagP eqm.
    by apply: var_of_regP eqm.
  move=> k n o a a' [ | | | ws] //= ->.
  + case: e; first by [].
    t_xrbindP => e _ <- c hac <-.
    rewrite /compat_imm orbF => /eqP <- -> /= b hb.
    case: eqm => ???? eqr ?? eqf.
    have [v'] := eval_assemble_cond eqr eqf hac hb.
    rewrite /eval_cond_mem; case: eval_cond => /=;
      last by case=> // [[<-]] /[swap] /to_boolI ->.
    move=> b' [<-] {hb}; case: v => // [b1 | [] //] -> ?.
    by exists b'.
  move=> haw hcomp -> /=.
  case: k haw => /=.
  + case: e; first by [].
    t_xrbindP=> e _ <- adr hadr ? w he /to_wordI' [ws' [w' [hws ? ->]]].
    subst a' v.
    move: hcomp; rewrite /compat_imm orbF => /eqP ?; subst a => /=.
    rewrite (addr_of_fexprP hws eqm he hadr); eexists; first reflexivity.
    by rewrite /= truncate_word_u.
  case: e => //=.
  + move=> al sz x p al'; t_xrbindP => /eqP <- ok_al' r hr ?; subst a'.
    move: hcomp; rewrite /compat_imm orbF => /eqP <-.
    move=> w1 wp vp hget htop wp' vp' hp hp' wr hwr <- /= htr.
    have -> := addr_of_xpexprP eqm hr hget htop hp hp'.
    by case: eqm => ? <- ??????; rewrite (aligned_le_read ok_al' hwr) /=; eauto.
  case => //.
  + move=> x al.
    move=> /xreg_of_varI; case: a' hcomp => // r;
      rewrite /compat_imm orbF => /eqP <- {a} h; have /= <- := of_varI h =>
      w ok_v /to_wordI[? [? [? ok_w]]];
      (eexists; first reflexivity); apply: (word_uincl_truncate _ ok_w); subst.
    + exact: getreg eqm ok_v.
    + exact: getregx eqm ok_v.
    exact: getxreg eqm ok_v.
  case => //= w' [] //= z al.
  t_xrbindP => /eqP _ h; move: hcomp; rewrite -h /compat_imm /eval_asm_arg => -/orP [/eqP <- | ].
  + move=> w [] <- /truncate_wordP [hsz ->].
    eexists; first reflexivity.
    by rewrite /to_word truncate_word_u sign_extend_truncate.
  case: a => // sz' w2 /eqP heq2 w [] <- /truncate_wordP [hsz ->].
  eexists; first reflexivity.
  rewrite -heq2.
  by rewrite /to_word truncate_word_u sign_extend_truncate.
Qed.

End EVAL_ASSEMBLE_COND.

(* word_uincl_update_u256 *)
Lemma word_extend_CLEAR sz szo (w : word sz) (old : word szo) :
  word_extend MSB_CLEAR old w = zero_extend szo w.
Proof. by rewrite /word_extend /= /arch_sem.mask_word wandC wand0 wxor0. Qed.

Lemma word_uincl_word_extend sz sz' szo (w: word sz) (w': word sz') fl (old:word szo) :
  (sz' <= szo)%CMP ->
  word_uincl w w' →
  word_uincl w (word_extend fl old w').
Proof.
  move=> hsz' /dup [] /andP[hsz_sz' /eqP ->] h.
  case: fl.
  + (* MSB_CLEAR *)
    rewrite word_extend_CLEAR; apply: (word_uincl_trans h).
    by apply: word_uincl_zero_extR.
  (* MSB_MERGE *)
  have hsz := cmp_le_trans hsz_sz' hsz'.
  apply/andP; split => //; rewrite /word_extend /arch_sem.mask_word.
  rewrite -wxor_zero_extend // -wand_zero_extend //.
  rewrite zero_extend_wshl // zero_extend_idem // wshl_ovf; last first.
  + by apply/leP; case: (sz) (sz') hsz_sz'=> -[].
  + by [].
  by rewrite wandC wand0 wxor0.
Qed.

Lemma word_extend_big sz szo f (w : word sz) (old : word szo) :
  ~(sz <= szo)%CMP ->
  (word_extend f old w) = zero_extend szo w.
Proof.
  move=> h; case: f; first by rewrite word_extend_CLEAR.
  rewrite /word_extend /arch_sem.mask_word wshl_ovf; last first.
  + by apply/leP; case: (sz) (szo) h => -[].
  + by [].
  by rewrite wandC wand0 wxor0.
Qed.

Lemma lom_eqv_write_var f rip s xs (x : var_i) sz (w : word sz) s' r :
  lom_eqv rip s xs
  -> write_var true x (Vword w) s = ok s'
  -> to_var r = x
  -> lom_eqv rip s' (mem_write_reg f r w xs).
Proof.
  case => eqscs eqm ok_rip [dr drx dx df] eqr eqrx eqx eqf.
  case: x => x xi /=.
  rewrite /mem_write_reg => /write_varP [-> hdb htr] ?; subst x.
  constructor => //=.
  + by rewrite Vm.setP_neq //; apply /eqP.
  + move=> r'; rewrite Vm.setP /RegMap.set ffunE eq_sym.
    have -> : (to_var r' == to_var r) = (r' == r ::>).
    + by apply/eqtype.inj_eq/inj_to_var.
    case: eqP => [<- /= | hne]; last by apply eqr.
    case: ifPn => hsz /=.
    + by apply word_uincl_word_extend => //; apply cmp_lt_le.
    by rewrite word_extend_big //;apply /negP.
  + move=> r'; rewrite Vm.setP_neq; first by apply eqrx.
    by apply/eqP/to_var_reg_neq_regx.
  + move=> r'; rewrite Vm.setP_neq; first by apply eqx.
    by apply/eqP/to_var_reg_neq_xreg.
  by move=> ?; rewrite Vm.setP_neq.
Qed.

Lemma lom_eqv_write_reg rip msbf r s xs ws ws0 (w : word ws0) :
  lom_eqv rip s xs ->
  (ws0 = ws \/ msbf = MSB_CLEAR) ->
  lom_eqv
    rip
    (with_vm s (evm s).[to_var r <- Vword (zero_extend ws w)])
    (mem_write_reg msbf r w xs).
Proof.
  move=> [hscs h1 hrip hnrip h2 h3 h4 h5] h.
  constructor => //=.

  - rewrite /get_var Vm.setP_neq //. apply/eqP. by move: hnrip => [].

  - move=> r'.
    rewrite /RegMap.set ffunE.
    case: eqP => [-> | hne].
    + rewrite Vm.setP_eq => /=.
      case: h => h;  subst;
        first rewrite zero_extend_u;
        last rewrite word_extend_CLEAR;
        case: ifP => /= hsz.
      * exact: word_uincl_word_extend.
      * by rewrite word_extend_big // hsz.
      * rewrite -(zero_extend_idem _ hsz). exact: (word_uincl_zero_ext _ hsz).
      rewrite zero_extend_idem; first done.
      apply: cmp_lt_le.
      by rewrite -cmp_nle_lt hsz.

    rewrite Vm.setP_neq; first exact: h2.
    apply/eqP => ?.
    apply hne.
    exact: inj_to_var.

  - move=> r'.
    rewrite Vm.setP_neq; first exact: h3.
    rewrite /to_var /= /rtype /=; apply/eqP => -[].
    exact: inj_toI_reg_regx.

  - move=> r'; rewrite Vm.setP_neq //; apply/eqP; apply to_var_reg_neq_xreg.

  by move=> f; rewrite Vm.setP_neq.
Qed.

Lemma compile_lval rip ii msb_flag loargs ad ty (vt:sem_ot ty) m m' s lv1 e1:
  lom_eqv rip m s ->
  check_arg_dest ad ty ->
  write_lexpr lv1 (oto_val vt) m = ok m' ->
  rexpr_of_lexpr lv1 = e1 ->
  check_sopn_dest agparams rip ii loargs e1 (ad, ty) ->
  exists s', mem_write_val msb_flag loargs (ad, ty) (oto_val vt) s = ok s' /\ lom_eqv rip m' s'.
Proof.
  move=> hlom; case:(hlom) => [hscs h1 hrip hnrip h2 h3 h4 h5]; case: ad => [ai _ | k n o]; rewrite /check_sopn_dest /=.
  case: ai => [f | r].
  + case: lv1 => //=; first by move=> ????? <-.
    t_xrbindP => x vm hvm <- <- /is_implicitP[] xi [] ?; subst x.
    case: ty vt hvm => //= vt /set_varP [_ htr ->]; rewrite /mem_write_val /=.
    have -> /= :
      match match vt with Some b => Vbool b | None => undef_b end with
      | Vbool b => ok (Some b)
      | Vundef sbool _ => ok None
      | _ => type_error
      end = ok vt.
    + by case: vt htr.
    eexists; split; first reflexivity.
    constructor => //=.
    + by case:hlom => ? ? hget hd _ _ _; rewrite Vm.setP_neq //; apply/eqP; case: hd.
    1-3: by move=> r; rewrite Vm.setP_neq.
    move=> f'; rewrite /RflagMap.set /= ffunE Vm.setP eq_sym.
    have -> : (to_var f' == to_var f) = (f' == f ::>).
    + by apply/eqtype.inj_eq/inj_to_var.
    case: eqP => [<- | hne] //.
    by move: (vm_truncate_valE htr) => {htr}; case: vt  => [ b | ] [+ ->].
  + case: lv1 => //=; first by move=> ????? <-.
    move=> x hw <- /is_implicitP [] xi [] ?; subst x.
    case: ty vt hw=> //; first by case.
    move=> ws vt hw.
    have /(_ r erefl) := lom_eqv_write_var msb_flag hlom hw.
    rewrite /mem_write_val /= truncate_word_u /=; eauto.
  case heq1: onth => [a | //].
  case heq3: k => [ // | al ].
  case heq2: arg_of_rexpr => [ a' | //] hty hw he1 /andP[] /eqP ? hc; subst a'.
  rewrite /mem_write_val /mem_write_ty.
  case: lv1 hw he1 heq2=> //=; cycle 1.
  + move=> [x xii] hw <-; rewrite /arg_of_rexpr.
    case: ty hty vt hw => //= sz _ vt hw.
    rewrite truncate_word_u /= heq1 hc => /xreg_of_varI {heq1 hc}.
    case: a => // r h; have {h}/=h := of_varI h; subst x.
    + have hw' : write_var true {| v_var := to_var r; v_info := xii|} (Vword vt) m = ok m' by done.
      have /(_ r erefl) := lom_eqv_write_var msb_flag hlom hw'; eauto.
    + move: hw; t_xrbindP => vm /set_varP [_ htr ->] <-.
      eexists; split; first reflexivity.
      constructor => //=.
      + by case:hlom => ? ? hget hd _ _ _ _;rewrite Vm.setP_neq //; apply/eqP; case: hd.
      + move=> r'; rewrite Vm.setP_neq //.
        by apply/eqP/nesym/to_var_reg_neq_regx.
      + move=> r'; rewrite Vm.setP /RegMap.set ffunE eq_sym.
        have -> : (to_var r' == to_var r) = (r' == r ::>).
        + by apply/eqtype.inj_eq/inj_to_var.
        case: eqP => [<- /= | hne]; last by apply h3.
        case: ifPn => hsz /=.
        + by apply word_uincl_word_extend => //; apply cmp_lt_le.
        by rewrite word_extend_big //;apply /negP.
      + move=> r'; rewrite Vm.setP_neq //.
        by apply/eqP/to_var_regx_neq_xreg.
      by move=> f; rewrite Vm.setP_neq.
    move: hw; t_xrbindP => vm /set_varP [_ htr ->] <-.
    eexists; split; first reflexivity.
    constructor => //=.
    + by case:hlom => ? ? hget hd _ _ _ _;rewrite Vm.setP_neq //; apply /eqP; case: hd.
    + move=> r'; rewrite Vm.setP_neq //.
      by apply/eqP/nesym/to_var_reg_neq_xreg.
    + move=> r'; rewrite Vm.setP_neq //.
      by apply/eqP/nesym/to_var_regx_neq_xreg.
    + move=> r'; rewrite Vm.setP /RegMap.set ffunE eq_sym.
      have -> : (to_var r' == to_var r) = (r' == r ::>).
      + by apply/eqtype.inj_eq/inj_to_var.
      case: eqP => [<- /= | hne]; last by apply h4.
      case: ifPn => hsz /=.
      + by apply word_uincl_word_extend => //; apply cmp_lt_le.
      by rewrite word_extend_big //;apply /negP.
    by move=> f; rewrite Vm.setP_neq.
  move=> al' sz [x xii] /= e; t_xrbindP.
  move=> wp vp hget hp wofs vofs he hofs w hw m1 hm1 ??; subst m' e1.
  case: ty hty vt hw => //= sz' _ vt hw.
  t_xrbindP => /eqP ? hal; subst sz'.
  move: hw; rewrite truncate_word_u => -[?]; subst vt.
  move => adr hadr ?; subst a => /=.
  rewrite /= heq1 hc /= /mem_write_mem -h1.
  have -> := addr_of_xpexprP hlom hadr hget hp he hofs.
  rewrite (aligned_le_write hal hm1) /=; eexists; split; first by reflexivity.
  by constructor.
Qed.

Lemma compile_lvals rip ii m lvs m' s loargs
  id_out id_tout (vt:sem_tuple id_tout) msb_flag:
  size id_out = size id_tout ->
  write_lexprs lvs (list_ltuple vt) m = ok m' ->
  lom_eqv rip m s ->
  check_sopn_dests agparams rip ii loargs lvs (zip id_out id_tout) ->
  all2 check_arg_dest id_out id_tout ->
  exists2 s',
    mem_write_vals msb_flag s loargs id_out id_tout (list_ltuple vt) = ok s' & lom_eqv rip m' s'.
Proof.
  elim : id_out id_tout lvs vt m s.
  + by move=> [] //= []//= _ m s _ [<-] hleq _; exists s.
  move=> ad ads hrec []// ty tys lvs vt m s [] heqs.
  have [vt1 [vtn ->]] /=: exists (vt1: sem_ot ty) (vtn: sem_tuple tys),
    list_ltuple vt = oto_val vt1 :: list_ltuple vtn.
  + move=>{heqs}; case: tys vt => /=.
    + by move=> vt; exists vt, tt.
    by move=> ty2 tys vt; exists vt.1, vt.2.
  rewrite /write_lvals /=.
  case: lvs => //= lv1 lvs; t_xrbindP => m1 hw1 hwn hlo /=.
  rewrite /check_sopn_dests /= => h /andP [] hca hcall.
  case/andP: h => hce1 hces.
  rewrite /mem_write_vals /=.
  have [s1 [-> /= h2]]:= compile_lval msb_flag hlo hca hw1 erefl hce1.
  exact: (hrec _  _ _ _ _ heqs hwn h2 _ hcall).
Qed.

(* ------------------------------------------------------------------------ *)

Lemma compile_asm_opn_aux (condspec : assemble_cond_spec) rip ii (loargs : seq asm_arg) op m s args lvs xs ys m' :
  let id := instr_desc op in
  let csa := check_sopn_args agparams rip ii loargs args in
  let csd := check_sopn_dests agparams rip ii loargs lvs in
  sem_rexprs m args = ok xs
  -> exec_sopn (Oasm (BaseOp op)) xs = ok ys
  -> write_lexprs lvs ys m = ok m'
  -> csa (zip (id_in id) (id_tin id))
  -> csd (zip (id_out id) (id_tout id))
  -> check_i_args_kinds (id_args_kinds id) loargs
  -> lom_eqv rip m s
  -> exists2 s', exec_instr_op id loargs s = ok s' & lom_eqv rip m' s'.
Proof.
  move=> id ; rewrite /exec_sopn.
  t_xrbindP => Hxs vt Hvt <-{ys} Hm' Hargs Hdest Hid Hlomeqv.
  rewrite /exec_instr_op /eval_instr_op Hid /=.
  move: vt Hvt Hm'; rewrite /sopn_sem /get_instr_desc /= -/id => {Hid}.
  case: id Hargs Hdest => /= msb_flag id_tin
   id_in id_tout id_out id_semi id_args_kinds id_nargs /andP[] /eqP hsin /eqP hsout
   _ id_str_jas id_check_dest id_safe id_wsize id_pp Hargs Hdest vt happ Hm'.
  elim: id_in id_tin hsin id_semi args xs Hargs happ Hxs; rewrite /sem_prod.
  + move=> [] //= _ id_semi [|a1 args] [|v1 vs] //= _ -> _ /=.
    exact: (compile_lvals _ hsout Hm' Hlomeqv Hdest).
  move=> a id_in hrec [] //= ty id_tin [] heqs id_semi [ | arg args] //=
    [ // | v vs];
    rewrite /check_sopn_args /= => /andP[] hcheck1 hcheckn.
  t_xrbindP => vt1 hvt happ v' hv vs' hvs ??; subst v' vs'.
  have [s'] := hrec _ heqs (id_semi vt1) _ _ hcheckn happ hvs.
  have [ v' hev' hv' ]:= check_sopn_arg_sem_eval condspec Hlomeqv hcheck1 hv hvt.
  t_xrbindP => v1 v2 -> vt' /= happ1 ? hmw hlom; subst v1.
  by rewrite hev' /= hv' /= happ1 /=; eauto.
Qed.

(* Converting [extra_op]s into [asm_op]s, assembling them and evaluating
   must be equivalent to computing their semantics. *)
Definition assemble_extra_correct op : Prop :=
  forall rip ii lvs args m xs ys m' s ops ops',
    sem_rexprs m args = ok xs
    -> exec_sopn (Oasm (ExtOp op)) xs = ok ys
    -> write_lexprs lvs ys m = ok m'
    -> to_asm ii op lvs args = ok ops
    -> mapM (assemble_asm_args agparams rip ii) ops = ok ops'
    -> lom_eqv rip m s
    -> exists2 s',
         foldM (fun '(op, args) s => eval_op op args s) s ops' = ok s'
         & lom_eqv rip m' s'.

Record h_asm_gen_params :=
  {
    (* Calling [assemble_cond] and [eval_cond] must respect the semantics
       of the expression.
       That is, if [m] is a state, and [rf] a flag map with matching values,
       assembling and evaluating with [rf] is equivalent to computing the
       semantics with a [m]. *)
    hagp_eval_assemble_cond : assemble_cond_spec;

    hagp_assemble_extra_op : forall op, assemble_extra_correct op;
  }.

Context
  (hagparams : h_asm_gen_params).

Lemma compile_asm_opn rip ii (loargs : seq asm_arg) op m s args lvs xs ys m' :
  let id := instr_desc op in
  let csa := check_sopn_args agparams rip ii loargs args in
  let csd := check_sopn_dests agparams rip ii loargs lvs in
  sem_rexprs m args = ok xs
  -> exec_sopn (Oasm (BaseOp op)) xs = ok ys
  -> write_lexprs lvs ys m = ok m'
  -> csa (zip (id_in id) (id_tin id))
  -> csd (zip (id_out id) (id_tout id))
  -> check_i_args_kinds (id_args_kinds id) loargs
  -> lom_eqv rip m s
  -> exists2 s', exec_instr_op id loargs s = ok s' & lom_eqv rip m' s'.
Proof. apply (compile_asm_opn_aux (hagp_eval_assemble_cond hagparams)). Qed.

Lemma app_sopn_apply_lprod T1 T2 tys (f : T1 -> T2) g vs :
  app_sopn tys (apply_lprod (rmap f) g) vs = rmap f (app_sopn tys g vs).
Proof. elim: tys vs g => [ | ty tys hrec] [ | v vs] //= g; case: of_val => //=. Qed.

Definition check_not_mem_args_kinds (d : arg_desc) (cond : args_kinds) :=
  match d with
  | ADExplicit _ i _ =>
    match onth cond i with
    | Some c => all is_not_CAmem c
    | _ => true
    end
  | _ => true
  end.

Definition check_not_mem_i_args_kinds (cond : i_args_kinds) (d : arg_desc) :=
  all (check_not_mem_args_kinds d) cond.

Definition check_not_mem (cond : i_args_kinds) (d : seq arg_desc) :=
  all (check_not_mem_i_args_kinds cond) d.

Lemma exclude_mem_args_kinds_subseq d cond' :
  all2 subseq (exclude_mem_args_kinds d cond') cond'.
Proof.
  rewrite /exclude_mem_args_kinds.
  case: d => [_|_ i _].
  + by apply all2_refl.
  rewrite all2E size_mapi eq_refl /=.
  apply /(all_nthP ([::],[::])) => k /=.
  rewrite size_zip size_mapi minnn => hk.
  rewrite nth_zip ?size_mapi // (nth_mapi [::]) //=.
  case: eq_op => //.
  by apply filter_subseq.
Qed.

Lemma exclude_mem_args_kinds_check d cond' :
  check_not_mem_args_kinds d (exclude_mem_args_kinds d cond').
Proof.
  rewrite /check_not_mem_args_kinds /exclude_mem_args_kinds.
  case: d => // _ i _.
  case heq: onth => [c|//].
  move /(onthP [::]) : heq => /andP [].
  rewrite size_mapi => hsize.
  rewrite (nth_mapi [::]) // eq_refl.
  move=> /eqP <-.
  by apply filter_all.
Qed.

Lemma exclude_mem_i_args_kinds_subseq d cond' :
  all2 (all2 subseq) (exclude_mem_i_args_kinds d cond') cond'.
Proof.
  elim: cond' => //= c cond' ih.
  apply /andP; split=> //.
  by apply exclude_mem_args_kinds_subseq.
Qed.

Lemma exclude_mem_i_args_kinds_check d cond' :
  check_not_mem_i_args_kinds (exclude_mem_i_args_kinds d cond') d.
Proof.
  elim: cond' => //= c cond' ih.
  apply /andP; split=> //.
  by apply exclude_mem_args_kinds_check.
Qed.

Lemma check_not_mem_args_kinds_subseq cond1 cond2 d :
  all2 subseq cond1 cond2 ->
  check_not_mem_args_kinds d cond2 ->
  check_not_mem_args_kinds d cond1.
Proof.
  case: d => // _ i _ /=.
  rewrite all2E => /andP [/eqP hsize hsubseq].
  move: hsubseq => /all_nthP -/(_ ([::], [::])) /= hsubseq.
  case heq2: onth => [c2|].
  + move=> hnmem2.
    move: heq2 => /onthP -/(_ [::]) /andP [hi /eqP hnth2].
    rewrite (onth_nth_size [::]) ?hsize //.
    apply: subseq_all hnmem2.
    rewrite -hnth2.
    move: (hsubseq i).
    rewrite size_zip hsize minnn => /(_ hi) /=.
    by rewrite nth_zip.
  case heq1: onth => //.
  move: heq1 => /(onthP [::]) /andP [hi _].
  rewrite hsize in hi.
  by rewrite (onth_nth_size [::] hi) in heq2.
Qed.

Lemma check_not_mem_i_args_kinds_subseq cond1 cond2 d :
  all2 (all2 subseq) cond1 cond2 ->
  check_not_mem_i_args_kinds cond2 d ->
  check_not_mem_i_args_kinds cond1 d.
Proof.
  elim/list_all2_ind {cond1 cond2} => // c1 cond1 c2 cond2 hall2 _ ih /=.
  move=> /andP [hcheck /ih{ih}ih].
  apply /andP; split=> //.
  by apply: check_not_mem_args_kinds_subseq hcheck.
Qed.

Lemma exclude_mem_aux_subseq cond' ds :
  all2 (all2 subseq) (exclude_mem_aux cond' ds) cond'.
Proof.
  elim: ds cond' => /=.
  + by apply /all2_refl /all2_refl.
  move=> d ds ih cond'.
  apply: (all2_trans (all2_trans (@subseq_trans _)) (ih _)).
  by apply exclude_mem_i_args_kinds_subseq.
Qed.

Lemma exclude_mem_aux_check cond' ds :
  check_not_mem (exclude_mem_aux cond' ds) ds.
Proof.
  elim: ds cond' => //= d ds ih cond'.
  apply /andP; split=> //.
  apply (check_not_mem_i_args_kinds_subseq (exclude_mem_aux_subseq _ _)).
  by apply exclude_mem_i_args_kinds_check.
Qed.

Lemma exclude_mem_check cond' ds :
  check_not_mem (exclude_mem cond' ds) ds.
Proof.
  apply: sub_all (exclude_mem_aux_check cond' ds).
  move=> d.
  by apply: (subseq_all (filter_subseq _ _)).
Qed.

Definition is_not_Addr (a : asm_arg) :=
  match a with
  | Addr _ => false
  | _ => true
  end.

Definition check_not_addr1 (args : asm_args) (d:arg_desc) :=
  match d with
  | ADExplicit _ i _ =>
    match onth args i with
    | Some a => is_not_Addr a
    | _ => true
    end
  | _ => true
  end.

Definition check_not_addr (id_out : seq arg_desc) (args : asm_args) :=
  all (check_not_addr1 args) id_out.

Lemma check_arg_kind_not_Addr a c :
  check_arg_kind a c ->
  is_not_CAmem c ->
  is_not_Addr a.
Proof. by case: a; case: c. Qed.

Lemma check_arg_kinds_subseq cond1 cond2 a :
  subseq cond1 cond2 ->
  check_arg_kinds a cond1 ->
  check_arg_kinds a cond2.
Proof. by apply subseq_has. Qed.

Lemma check_arg_kinds_not_Addr a cond' :
  check_arg_kinds a cond' ->
  all is_not_CAmem cond' ->
  is_not_Addr a.
Proof.
  elim: cond' => //= c cond' ih /orP [].
  + by move=> /check_arg_kind_not_Addr h /andP [/h ? _].
  by move=> /ih{ih}ih /andP [_ /ih].
Qed.

Lemma check_args_kinds_subseq cond1 cond2 args :
  all2 subseq cond1 cond2 ->
  check_args_kinds args cond1 ->
  check_args_kinds args cond2.
Proof.
  elim: cond1 cond2 args; first by case.
  move=> c1 cond1 ih [//|c2 cond2] [//|a args] /= /andP [hsub /ih{ih}ih] /andP [hcheck /ih{ih}ih].
  apply /andP; split =>//.
  by apply (check_arg_kinds_subseq hsub).
Qed.

(* [Imm (wrepr U8 0)] is just used as a default [asm_arg] value. *)
Lemma check_args_kinds_not_addr1 args cond' d :
  check_args_kinds args cond' ->
  check_not_mem_args_kinds d cond' ->
  check_not_addr1 args d.
Proof.
  case: d => //= _ i _.
  rewrite /check_args_kinds all2E => /andP [/eqP hsize hnth].
  case heqc: onth => [c|]; last first.
  + move=> _.
    case heqa: onth => [a|//].
    move /(onthP (Imm (wrepr U8 0))) : heqa => /andP [hi _].
    by move: heqc; rewrite (onth_nth_size [::]) // -hsize.
  move /(onthP [::]) : heqc => /andP [hi /eqP hnthc].
  move /all_nthP : hnth => /(_ (Imm (wrepr U8 0), [::]) i) /=.
  rewrite size_zip hsize minnn nth_zip //= hnthc => /(_ hi).
  rewrite (onth_nth_size (Imm (wrepr U8 0))) ?hsize //.
  by apply check_arg_kinds_not_Addr.
Qed.

Lemma check_i_args_kinds_subseq cond1 cond2 args :
  all2 (all2 subseq) cond1 cond2 ->
  check_i_args_kinds cond1 args ->
  check_i_args_kinds cond2 args.
Proof.
  rewrite all2E => /andP [/eqP hsize hnth].
  move=> /(has_nthP [::]) [i hi hcheck].
  apply /(has_nthP [::]).
  exists i; first by rewrite -hsize.
  move /(all_nthP ([::],[::])) : hnth => /(_ i) /=.
  rewrite size_zip -hsize minnn nth_zip //= => /(_ hi) hall2.
  by apply (check_args_kinds_subseq hall2 hcheck).
Qed.

Lemma check_i_args_kinds_not_addr1 cond' args d :
  check_i_args_kinds cond' args ->
  check_not_mem_i_args_kinds cond' d ->
  check_not_addr1 args d.
Proof.
  rewrite /check_i_args_kinds /check_not_mem_i_args_kinds.
  move=> /hasP /= [c hin hcheck].
  move=> /allP -/(_ c hin).
  by apply check_args_kinds_not_addr1.
Qed.

Lemma check_i_args_kinds_not_addr cond' args ds :
  check_i_args_kinds cond' args ->
  check_not_mem cond' ds ->
  check_not_addr ds args.
Proof.
  move=> hcheck.
  elim: ds => //= d ds ih /andP [hnmem /ih{ih}ih].
  apply /andP; split=> //.
  by apply (check_i_args_kinds_not_addr1 hcheck hnmem).
Qed.

Lemma exclude_mem_correct args_kinds out asm_args:
  check_i_args_kinds (exclude_mem args_kinds out) asm_args ->
  check_i_args_kinds args_kinds asm_args /\ check_not_addr out asm_args.
Proof.
  move=> hcheck.
  split.
  + apply: (check_i_args_kinds_subseq (exclude_mem_aux_subseq args_kinds out)).
    by apply (subseq_has (filter_subseq _ _) hcheck).
  apply (check_i_args_kinds_not_addr hcheck).
  by apply exclude_mem_check.
Qed.

Lemma check_not_addr1_write asm_args ad ws ty (v: sem_ot ty) s :
  check_not_addr1 asm_args ad ->
  mem_write_val MSB_CLEAR asm_args (ad, extend_size ws ty)
       (oto_val (wextend_size ws v)) s =
  mem_write_val MSB_CLEAR asm_args (ad, ty) (oto_val v) s.
Proof.
  case: ty v => // ws' v; rewrite /extend_size /wextend_size.
  case heq: (ws' ≤ ws)%CMP => //=.
  rewrite /mem_write_val /= !truncate_word_u /=.
  case: ad => //= [[] // r _| k n or].
  + by rewrite /= /mem_write_reg !word_extend_CLEAR zero_extend_cut.
  case: onth => // -[] // r _; case: check_oreg => //=.
  + by rewrite /mem_write_reg !word_extend_CLEAR zero_extend_cut.
  + by rewrite /mem_write_regx !word_extend_CLEAR zero_extend_cut.
  by rewrite /mem_write_xreg !word_extend_CLEAR zero_extend_cut.
Qed.

Lemma check_not_addr_write s ws asm_args id_out id_tout (t : sem_tuple id_tout) :
  size id_out = size id_tout →
  check_not_addr id_out asm_args →
  mem_write_vals MSB_CLEAR s asm_args id_out [seq extend_size ws i | i <- id_tout]
        (list_ltuple (extend_tuple ws t)) =
  mem_write_vals MSB_CLEAR s asm_args id_out id_tout (list_ltuple t).
Proof.
  rewrite /mem_write_vals.
  elim: id_out id_tout t s => [ | ad id_out hrec] [ | ty id_tout] //= t s []
     hsize /andP [] hc1 hcs.
  case: id_tout t hsize hcs.
  + by move=> {hrec}; case: id_out => //= v _ _; rewrite check_not_addr1_write.
  move=> a l [] v t hsz hc.
  have := hrec (a::l) t _ hsz hc.
  rewrite /= check_not_addr1_write //.
  case: mem_write_val => //=.
Qed.

Lemma exec_desc_desc_op op asm_args s :
  check_i_args_kinds (instr_desc op).(id_args_kinds) asm_args ->
  exec_instr_op (instr_desc op) asm_args s = exec_instr_op (instr_desc_op op.2) asm_args s.
Proof.
  case: op => -[ws |] //= op.
  case: eqP => //= hclear /dup[] hcheck /exclude_mem_correct [hc hnaddr].
  rewrite /exec_instr_op /= /eval_instr_op /= hcheck hc hclear /=.
  case heq : eval_args_in => [vargs | ] //=.
  rewrite app_sopn_apply_lprod.
  case: app_sopn => //= t.
  apply check_not_addr_write => //.
  assert (hsize:= id_eq_size (instr_desc_op op)).
  by move: hsize => /andP [_ /eqP].
Qed.

Lemma enforce_imm_arg_kind_correct a c a' :
  enforce_imm_arg_kind a c = Some a' ->
  check_arg_kind a' c.
Proof.
  case: a; case: c => [|||| b |] //=; try by move=> ? [<-].
  move=> ws1 ws2 w.
  by case: eqP => // -> [<-] /=.
Qed.

Lemma enforce_imm_arg_kinds_correct a cond' a' :
  enforce_imm_arg_kinds a cond' = Some a' ->
  check_arg_kinds a' cond'.
Proof.
  move=> /find_map_correct [c hin /enforce_imm_arg_kind_correct hc].
  by apply /hasP; exists c.
Qed.

Lemma enforce_imm_args_kinds_correct args cond' args' :
  enforce_imm_args_kinds args cond' = Some args' ->
  check_args_kinds args' cond'.
Proof.
  rewrite /enforce_imm_args_kinds.
  case heq: mapM2 => {args'} [args'|//] [<-].
  elim: args cond' args' heq => /=.
  + by move=> [|//] _ [<-].
  move=> a args ih [//|c cond'].
  t_xrbindP=> _ arg' hok args' hmap <- /=.
  apply /andP; split; last by apply ih.
  case henforce: enforce_imm_arg_kinds hok => {arg'} [arg'|//] /= [<-].
  by apply: enforce_imm_arg_kinds_correct henforce.
Qed.

Lemma enforce_imm_i_args_kinds_correct args cond' args' :
  enforce_imm_i_args_kinds cond' args = Some args' ->
  check_i_args_kinds cond' args'.
Proof.
  move=> /find_map_correct [c hin /enforce_imm_args_kinds_correct hc].
  by apply /hasP; exists c.
Qed.

Lemma filter_arg_kinds_no_imm_subseq args cond1 cond2 :
  filter_arg_kinds_no_imm args cond1 = ok cond2 ->
  subseq cond2 cond1.
Proof.
  rewrite /filter_arg_kinds_no_imm.
  case: {1}filter => [//|_ _] [<-].
  by apply filter_subseq.
Qed.

Lemma filter_args_kinds_no_imm_subseq args cond1 cond2 :
  filter_args_kinds_no_imm args cond1 = Some cond2 ->
  all2 subseq cond2 cond1.
Proof.
  rewrite /filter_args_kinds_no_imm.
  case heq: mapM2 => {cond2} [cond2|//] [<-].
  elim: args cond1 cond2 heq => /=.
  + by move=> [|//] _ [<-].
  move=> a args ih [//|c1 cond1].
  t_xrbindP=> ? c2 hfilter cond2 hmap <- /=.
  apply /andP; split; last by apply ih.
  by apply (filter_arg_kinds_no_imm_subseq hfilter).
Qed.

Lemma filter_i_args_kinds_no_imm_correct args cond' args' :
  check_i_args_kinds (filter_i_args_kinds_no_imm cond' args) args' ->
  check_i_args_kinds cond' args'.
Proof.
  move=> /hasP /= [c hin hcheck].
  move: hin; rewrite mem_pmap => /mapP /= [c' hin' /esym hfilter].
  apply /hasP; exists c' => //.
  apply: check_args_kinds_subseq hcheck.
  by apply (filter_args_kinds_no_imm_subseq hfilter).
Qed.

Lemma assemble_asm_opI rip ii op lvs args op' asm_args:
  assemble_asm_op agparams rip ii op lvs args = ok (op', asm_args) ->
  [/\ check_sopn_args agparams rip ii asm_args args (zip (id_in (instr_desc op)) (id_tin (instr_desc op))),
      check_sopn_dests agparams rip ii asm_args lvs (zip (id_out (instr_desc op)) (id_tout (instr_desc op))),
      check_i_args_kinds (id_args_kinds (instr_desc op)) asm_args &
      op' = op.2].
Proof.
  rewrite /assemble_asm_op; t_xrbindP => asm_args' hass _ z0.
  case hci: enforce_imm_i_args_kinds => [asm_args1|//] [?] /andP [hca hcd] ??.
  have hidc := filter_i_args_kinds_no_imm_correct (enforce_imm_i_args_kinds_correct hci).
  by subst op' asm_args1 z0.
Qed.

Lemma assemble_asm_opP rip ii op lvs args op' asm_args s m xs ys m' :
  sem_rexprs m args = ok xs ->
  exec_sopn (Oasm (BaseOp op)) xs = ok ys ->
  write_lexprs lvs ys m = ok m' ->
  assemble_asm_op agparams rip ii op lvs args = ok (op', asm_args) ->
  lom_eqv rip m s ->
  exists2 s', eval_op op' asm_args s = ok s' & lom_eqv rip m' s'.
Proof.
  rewrite /eval_op => ok_xs ok_ys hsem /assemble_asm_opI [hca hcd hidc ->] hlo.
  have [s' he' hlo'] := compile_asm_opn ok_xs ok_ys hsem hca hcd hidc hlo.
  exists s'; last done.
  by rewrite -exec_desc_desc_op.
Qed.

Lemma assemble_sopnP rip ii op lvs args ops m xs ys m' s:
  sem_rexprs m args = ok xs ->
  exec_sopn op xs = ok ys ->
  write_lexprs lvs ys m = ok m' ->
  assemble_sopn agparams rip ii op lvs args = ok ops ->
  lom_eqv rip m s ->
  exists2 s', foldM (fun '(op'', asm_args) s => eval_op op'' asm_args s) s ops = ok s' & lom_eqv rip m' s'.
Proof.
  case: op => //=.
  case=> //=.
  + move=> a h1 h2 h3; t_xrbindP => -[op' args'] h4 <- h5.
    by have [s' hs' heq] := assemble_asm_opP h1 h2 h3 h4 h5; exists s' => //=; rewrite hs'.
  t_xrbindP=> op ok_xs ok_ys hsem ops'.
  exact: (hagp_assemble_extra_op hagparams ok_xs ok_ys).
Qed.

Section WITH_RIP_RSP.

(* FIXME: move up? *)
Context (rip rsp : var).

Lemma assemble_fdI fd fd' :
  assemble_fd agparams rip rsp fd = ok fd'
  -> [/\ rsp \notin [seq v_var x | x <- lfd_arg fd ],
      all is_typed_reg (lfd_callee_saved fd)
       & exists c arg res,
           [/\ assemble_c agparams rip (lfd_body fd) = ok c
             , mapM typed_reg_of_vari (lfd_arg fd) = ok arg
             , mapM typed_reg_of_vari (lfd_res fd) = ok res
             , fd' = {| asm_fd_align := lfd_align fd
                      ; asm_fd_arg := arg
                      ; asm_fd_body := c
                      ; asm_fd_res := res
                      ; asm_fd_export := lfd_export fd
                      ; asm_fd_total_stack := lfd_total_stack fd
                      ; asm_fd_align_args := lfd_align_args fd
                     |}
             & check_call_conv fd'
           ]
    ].
Proof.
  rewrite /assemble_fd; t_xrbindP
    => c ok_c ok_rsp ok_callee_saved arg ok_arg res ok_res ok_call_conv <-;
    split => //.
  by exists c, arg, res.
Qed.

(* -------------------------------------------------------------------- *)
(* Labels are preserved. *)

Lemma assemble_c_labels (lc : lcmd) (ac : asm_code) :
  assemble_c agparams rip lc = ok ac
  -> label_in_lcmd lc = label_in_asm ac.
Proof.
  rewrite /assemble_c; t_xrbindP => z /mapM_Forall2 hall <-.
  elim: hall => // { lc ac }.
  move=> li ai lc ac ok_ai _.
  rewrite /label_in_lcmd -cat1s pmap_cat -(cat1s ai) flatten_cat /label_in_asm pmap_cat => ->; f_equal.
  case: li ok_ai => ii [ l o es| | [] | | | | | | | ] /=; try (by t_xrbindP => *; subst).
  t_xrbindP => ops hops <-.
  by case: o hops => //= -[a | e] //=; t_xrbindP => *; subst => //=; elim: (ops).
Qed.

Lemma assemble_fd_labels (fn : funname) (fd : lfundef) (fd' : asm_fundef) :
  assemble_fd agparams rip rsp fd = ok fd'
  -> [seq (fn, lbl) | lbl <- label_in_lcmd (lfd_body fd)]
     = [seq (fn, lbl) | lbl <- label_in_asm (asm_fd_body fd')].
Proof.
  case/assemble_fdI => _ _ [] c [] _ [] _ [] ok_c _ _ -> _ /=.
  by rewrite (assemble_c_labels ok_c).
Qed.

Lemma assemble_i_is_label (li : linstr) ai lbl :
  assemble_i agparams rip li = ok ai
  -> linear.is_label lbl li = has (arch_sem.is_label lbl) ai.
Proof.
  rewrite /assemble_i /linear.is_label ; case li =>  ii
   [es o xs | s [<-]| xi r | [<-]| [<-] | lk l [<-]| r [<-]| x | x l | e l] //=; t_xrbindP.
  + by move=> z _ <-; elim z.
  + by case xi => [lr| > [<-] //]; case: to_reg => //= > [<-].
  + by rewrite orbC.
  + by move=> _ ? _ <-.
  + by move=> z _ <-.
  by move=> z _ <-.
Qed.

Definition asm_pos p (lc:lcmd) :=
  match assemble_c agparams rip (take p lc) with
  | Ok l => size l
  | _ => 0  (* absurd *)
  end.

Definition label_pos lbl (lc:lcmd) :=
  asm_pos (find (linear.is_label lbl) lc) lc.

Lemma assemble_c_find_is_label (lc : lcmd) (ac : asm_code) lbl :
  assemble_c agparams rip lc = ok ac
  -> label_pos lbl lc = find (arch_sem.is_label lbl) ac.
Proof.
  rewrite /assemble_c /label_pos /asm_pos /arch_sem.find_label; t_xrbindP => z heq <- {ac}.
  elim: lc z heq => [ | i lc hrec] z /=; first by move=> [<-].
  t_xrbindP => i1 hi1 z1 hlc <-.
  rewrite -(cat1s i1) flatten_cat find_cat.
  rewrite -(cat1s i) find_cat /= cats0 -(assemble_i_is_label lbl hi1).
  case heq: linear.is_label => /=.
  + by case: i hi1 heq => [? []] //= lk l [<-]; rewrite /linear.is_label /is_label /= => ->.
  rewrite /assemble_c /= hi1 /=.
  have heq1 := mapM_take (find (linear.is_label lbl) lc) hlc.
  by have := hrec _ hlc; rewrite /assemble_c heq1 /= size_cat => ->.
Qed.

Lemma assemble_c_find_label (lc : lcmd) (ac : asm_code) lbl p :
  assemble_c agparams rip lc = ok ac
  -> linear.find_label lbl lc = ok p
  -> arch_sem.find_label lbl ac = ok (asm_pos p lc).
Proof.
  move=> /dup [] /assemble_c_find_is_label -/(_ lbl).
  rewrite /label_pos /linear.find_label /arch_sem.find_label => <- hac.
  case: ltnP => //;rewrite -has_find /asm_pos => hlt [<-].
  move: hac; rewrite /assemble_c; t_xrbindP => li hli <-.
  move: hli; have [i lc1 lc2 h1 h2] := split_find hlt.
  rewrite -cats1 !mapM_cat /=; t_xrbindP => li2 li1 -> h3 /= li3 h4 <- <- li4 ? <-.
  rewrite -catA !flatten_cat !size_cat /=.
  case: i h1 h4 => ? [] //= lk ? _ [<-] /=.
  by rewrite addn0 add1n -ltn_subLR // subnn.
Qed.

(* -------------------------------------------------------------------- *)
(* Assembling machine words. *)

Lemma eval_assemble_word ii al sz e a s xs v :
  lom_eqv rip s xs
  -> is_not_app1 e
  -> assemble_word_load rip ii al sz e = ok a
  -> sem_rexpr s.(emem) s.(evm) e = ok v
  -> exists2 v',
       eval_asm_arg (AK_mem al) xs a (sword sz) = ok v'
       & value_uincl v v'.
Proof.
  rewrite /assemble_word /eval_asm_arg => eqm.
  case: e => //; last case => //=; t_xrbindP; last first.
  - move => x _ /xreg_of_varI h ok_v.
    case: a h => // r ok_r; (eexists; first reflexivity).
    + exact: (ofgetreg eqm ok_r ok_v).
    + exact: (ofgetregx eqm ok_r ok_v).
    exact: (ofgetxreg eqm ok_r ok_v).
  move => al' sz' ? ? _ /=; t_xrbindP => /eqP <-{sz'} ok_al' d ok_d <- ptr w ok_w ok_ptr uptr u ok_u ok_uptr ? ok_rd ?; subst v => /=.
  case: (eqm) => _ eqmem _ _ _ _ _.
  rewrite (addr_of_xpexprP eqm ok_d ok_w ok_ptr ok_u ok_uptr) -eqmem (aligned_le_read ok_al' ok_rd).
  eexists; first reflexivity.
  exact: word_uincl_refl.
Qed.

End WITH_RIP_RSP.

(* -------------------------------------------------------------------- *)

Section PROG.

Context
  (p : lprog)
  (p' : asm_prog)
  (ok_p' : assemble_prog agparams p = ok p').

Notation rip := (mk_ptr (lp_rip p)).
Notation rsp := (mk_ptr (lp_rsp p)).

Lemma assemble_progP :
  let rip := mk_ptr (lp_rip p) in
  let rsp := mk_ptr (lp_rsp p) in
  let assemble_fd := assemble_fd agparams rip rsp in
  [/\ disj_rip rip
    , to_ident ad_rsp = lp_rsp p
    , asm_globs p' = lp_globs p
    & map_cfprog_linear assemble_fd (lp_funcs p)
      = ok (asm_funcs p')
  ].
Proof.
  move: ok_p'.
  rewrite /assemble_prog.
  t_xrbindP => /andP [/eqP ok_rip /eqP ok_ripx] /eqP ok_rsp fds ok_fds <-.
  split => //.
  split => r heq //.
  - move: ok_rip.
    by rewrite -heq /to_reg to_varK.
  - move: ok_ripx.
    by rewrite -heq /to_regx to_varK.
  - move: heq.
    rewrite /to_var /rtype.
    move=> [] hsz _.
    assert (H := reg_size_neq_xreg_size).
    rewrite hsz in H.
    by rewrite eqxx in H.
  exact: of_identI ok_rsp.
Qed.

Lemma assemble_prog_labels :
  label_in_lprog p = label_in_asm_prog p'.
Proof.
  case: assemble_progP => _ _ _ /mapM_Forall2.
  rewrite /label_in_lprog /label_in_asm_prog.
  elim => //.
  t_xrbindP => - [] fn lfd fn' lfds xfds xfd /= ok_xfd <- {fn'} _ ih.
  congr (_ ++ _); last exact: ih.
  move: ok_xfd.
  case ok_xfd: assemble_fd => // /ok_inj ?; subst.
  exact: assemble_fd_labels ok_xfd.
Qed.

Lemma ok_get_fundef fn fd :
  get_fundef (lp_funcs p) fn = Some fd
  -> exists2 fd',
       get_fundef (asm_funcs p') fn = Some fd'
       & assemble_fd agparams rip rsp fd = ok fd'.
Proof.
  move=> hfd.
  have [_ _ _ x] := assemble_progP.
  have [fd' ??] := get_map_cfprog_gen x hfd.
  by exists fd'.
Qed.

Variant match_state
  (rip : var) (ls : lstate) (lc : lcmd) (xs : asm_state) : Prop :=
| MS
  `(lom_eqv rip (to_estate ls) (asm_m xs))
  `(lfn ls = asm_f xs)
  `(assemble_c agparams rip lc = ok (asm_c xs))
  `(asm_pos rip (lpc ls) lc = asm_ip xs).

Lemma reg_in_all (r:reg_t): Sv.In (to_var r) all_vars.
Proof. apply: enum_in_Sv => ??. rewrite /all_vars !Sv.union_spec. by auto. Qed.

Lemma regx_in_all (r:regx_t): Sv.In (to_var r) all_vars.
Proof. apply: enum_in_Sv => ??. rewrite /all_vars !Sv.union_spec. by auto. Qed.

Lemma xreg_in_all (r:xreg_t): Sv.In (to_var r) all_vars.
Proof. apply: enum_in_Sv => ??. rewrite /all_vars !Sv.union_spec. by auto. Qed.

Lemma flag_in_all (r:rflag_t): Sv.In (to_var r) all_vars.
Proof. apply: enum_in_Sv => ??. rewrite /all_vars !Sv.union_spec. by auto. Qed.

Lemma to_var_typed_reg r x : to_var r = var_of_asm_typed_reg x -> x = ARReg r.
Proof.
  case: x => //= r'.
  + by move=> h; have -> := inj_to_var h.
  + by move=> h; elim (to_var_reg_neq_regx h).
  by move=> h; elim (to_var_reg_neq_xreg h).
Qed.

Lemma to_var_typed_regx r x : to_var r = var_of_asm_typed_reg x -> x = ARegX r.
Proof.
  case: x => //= r'.
  + by move=> h; elim (to_var_reg_neq_regx (sym_eq h)).
  + by move=> h; have -> := inj_to_var h.
  by move=> h; elim (to_var_regx_neq_xreg h).
Qed.

Lemma to_var_typed_xreg r x : to_var r = var_of_asm_typed_reg x -> x = AXReg r.
Proof.
  case: x => //= r'.
  + by move=> h; elim (to_var_reg_neq_xreg (sym_eq h)).
  + by move=> h; elim (to_var_regx_neq_xreg (sym_eq h)).
  by move=> h; have -> := inj_to_var h.
Qed.

Lemma to_var_typed_flag r x : to_var r = var_of_asm_typed_reg x -> x = ABReg r.
Proof. by case: x => //= r' h; have -> := inj_to_var h. Qed.

Lemma to_var_rsp : {| vtype := sword reg_size; vname := lp_rsp p |} = to_var ad_rsp.
Proof.
  move: ok_p'; rewrite /assemble_prog; t_xrbindP => _ /eqP h _ _ _.
  by symmetry; apply: of_varI; rewrite /of_var /= eqxx.
Qed.

Lemma find_label_asm_posS lbl c xc pc :
     linear.find_label lbl c = ok pc
  -> assemble_c agparams rip c = ok xc
  -> asm_pos rip pc.+1 c = (asm_pos rip pc c).+1.
Proof.
  rewrite /linear.find_label /asm_pos.
  case: ltnP => //;rewrite -has_find /asm_pos => hlt [<-].
  have [i lc1 lc2 h1 h2] := split_find hlt.
  rewrite /assemble_c; t_xrbindP => z.
  rewrite -cats1 !mapM_cat /=; t_xrbindP => li2 li1 heqi1 li3 li heqi <- <- li4 heqi4 _ _.
  rewrite -catA find_cat (negbTE h2) /= h1 addn0 -cat_rcons take_size_cat ?size_rcons //.
  rewrite mapM_rcons heqi1 /= heqi /= flatten_rcons size_cat -addn1.
  by case: i h1 heqi => ? -[] //= ?? _ [<-].
Qed.

Lemma eval_jumpP r (xs : asm_state) ls ls' :
   lom_eqv rip (to_estate ls) xs ->
   eval_jump p r ls = ok ls' ->
   exists2 xs' : asm_state,
      eval_JMP p' r xs = ok xs' &
      exists2 lc' : lcmd,
        ssrfun.omap lfd_body (get_fundef (lp_funcs p) (lfn ls')) = Some lc' & match_state rip ls' lc' xs'.
Proof.
  case: r => fn lbl /= heqm; t_xrbindP => body.
  case ok_fd: get_fundef => [ fd | // ] [ ] <-{body} pc ok_pc <-{ls'}.
  case/ok_get_fundef: (ok_fd) => fd' ->.
  case/assemble_fdI => rsp_not_in_args _ [] xc [] _ [] _ [] ok_xc _ _ ->{fd'} _ /=.
  rewrite (assemble_c_find_label ok_xc ok_pc) ok_fd /=.
  do 2 (eexists; first reflexivity).
  constructor => //=; apply: find_label_asm_posS ok_pc ok_xc.
Qed.

Lemma onth_split (T:Type) (c: list T) n i:
  onth c n = Some i ->
  c = take n c ++ i :: drop n.+1 c.
Proof.
  case: (ltnP n (size c)) => [hn | /onth_default -> //].
  rewrite -{1 2 4}(cat_take_drop n c).
  rewrite onth_cat drop_cat size_take hn ltnn /= ltnNge leqnSn /= subSnn subnn.
  by case: drop => //= ? ? [->]; rewrite drop0.
Qed.

Lemma asm_pos_incr i ai c n ac0 ac1 xs:
  assemble_i agparams rip i = ok [:: ai] ->
  onth c n = Some i ->
  mapM (assemble_i agparams rip) (take n c) = ok ac0 ->
  flatten ac0 ++ [::ai] ++ flatten ac1 = asm_c xs ->
  asm_pos rip n c = asm_ip xs ->
  asm_pos rip n.+1 c = (asm_ip xs).+1.
Proof.
  move=> hi hnth hhd hf hip.
  rewrite -hip (onth_split hnth) /asm_pos /assemble_c !take_cat !size_take.
  case: (ltnP n (size c)) hnth => [hn hnth| /onth_default -> //].
  by rewrite ltnn ltnNge leqnSn /= !mapM_cat subSnn hhd /= hi subnn take0 /= flatten_cat cats0 size_cat addn1.
Qed.

Lemma assemble_get_label_after_pc i ai lc xs ls l:
  assemble_c agparams rip lc = ok (asm_c xs)
  → onth lc (lpc ls) = Some i
  → assemble_i agparams rip i = ok [::ai]
  → lfn ls = asm_f xs
  → asm_pos rip (lpc ls) lc = asm_ip xs
  → ssrfun.omap lfd_body (get_fundef (lp_funcs p) (lfn ls)) = Some lc
  → get_label_after_pc p ls = ok l
  → ∃ ii, onth (asm_c xs) (asm_ip xs).+1 = Some {| asmi_i := LABEL ExternalLabel l ; asmi_ii := ii |}.
Proof.
  move=> eqc honth hassi eqfn eqpc omap_lc; rewrite /get_label_after_pc /find_instr /= -eqpc.
  case: get_fundef omap_lc => // _ [->] {eqpc}; move: eqc.
  rewrite (onth_split honth) -{2}cat_rcons /asm_pos /assemble_c mapM_cat.
  t_xrbindP => c c1 hc1 c' /=; rewrite hassi /=; t_xrbindP => c2 hc2 <- <- <-.
  rewrite take_cat onth_cat size_rcons size_take.
  case: (ltnP (lpc ls) (size lc)) honth => [hn ok_i| /onth_default -> //].
  rewrite !ltnn !subnn take0 cats0 hc1 /= -cat_rcons flatten_cat onth_cat.
  rewrite flatten_rcons size_cat /= addn1 ltnn subnn.
  by case: drop hc2 => //= -[ii []//=] []// lbl c2'; t_xrbindP => ? _ <- <-; eexists.
Qed.

Lemma match_state_step1 xs ls' i:
  onth (asm_c xs) (asm_ip xs) = Some i ->
  (exists2 xs', arch_sem.eval_instr p' i.(asmi_i) xs = ok xs'
     & exists2 lc', ssrfun.omap lfd_body (get_fundef (lp_funcs p) (lfn ls')) = Some lc'
         & match_state rip ls' lc' xs') ->
  (exists2 xs', asmsem p' xs xs'
     & exists2 lc', ssrfun.omap lfd_body (get_fundef (lp_funcs p) (lfn ls')) = Some lc'
         & match_state rip ls' lc' xs').
Proof.
  move=> hnth [xs' hev hex]; exists xs' => //.
  by apply rt_step; rewrite /asmsem1 /fetch_and_eval hnth hev.
Qed.

Lemma asm_pos_AsmOp fd ls ii les op res c ac0 :
  onth (lfd_body fd) (lpc ls) = Some (MkLI ii (Lopn les op res)) ->
  mapM (assemble_i agparams rip) (take (lpc ls) (lfd_body fd)) = ok ac0 ->
  assemble_sopn agparams rip ii op les res = ok c ->
  asm_pos rip (lpc ls) (lfd_body fd) = size (flatten ac0)
  /\ asm_pos rip (lpc ls).+1 (lfd_body fd) = size (flatten ac0) + size c.
Proof.
  move=> honth hac0 hc.
  + rewrite /asm_pos (onth_split honth) !take_cat !size_take.
    case: (ltnP (lpc ls) (size (lfd_body fd))) honth => [hn ok_i |];
      last by move=> /onth_default ->.
    rewrite ltnn ltnNge leqnSn /= subnn subSnn /= take0.
    rewrite /assemble_c !mapM_cat hac0 /= hc /=.
    by rewrite cats0 flatten_cat /= cats0 size_cat size_map.
Qed.

Lemma step_AsmOp fd ii ac0 ac1 c c' ls s xm xm' :
  let: xbody :=
    flatten ac0 ++ [seq {| asmi_ii := ii ; asmi_i := AsmOp x.1 x.2 |} | x <- c' ++ c] ++ flatten ac1
  in
  let: pc := (size (flatten ac0) + size c')%nat in
  let: xs :=
    {|
      asm_m := xm;
      asm_f := lfn ls;
      asm_c := xbody;
      asm_ip := pc;
    |}
  in
  let: xs' :=
    {|
      asm_m := xm';
      asm_f := lfn ls;
      asm_c := xbody;
      asm_ip := pc + size c;
    |}
  in
  let: ls' := of_estate s (lfn ls) (lpc ls).+1 in
  assemble_c agparams rip (lfd_body fd) = ok xbody ->
  lom_eqv rip s xm' ->
  asm_pos rip (lpc ls).+1 (lfd_body fd) = pc + size c ->
  foldM (fun '(op, args) => eval_op op args) xm c = ok xm' ->
  asmsem p' xs xs'
  /\ match_state rip ls' (lfd_body fd) xs'.
Proof.
  elim: c c' ls xm => [|[op args] c hrec] c' ls xm /= hass heq hpos.

  - move=> [?]; subst xm'.
    rewrite addn0.
    split; first exact: rt_refl.
    split=> //=.
    - by rewrite to_estate_of_estate.
    by rewrite hpos addn0.

  t_xrbindP=> xm0 heval hf.
  have := hrec (rcons c' (op, args)) ls xm0.
  rewrite cat_rcons size_rcons addnS addSnnS.
  move=> /(_ hass heq hpos hf) [hsem hmatch].
  split=> //.
  apply: (rt_trans _ _ _ _ _ _ hsem).
  apply: rt_step.
  rewrite /asmsem1 /fetch_and_eval /=.
  rewrite onth_cat lt_nm_n sub_nmn map_cat /=.
  rewrite -!catA onth_cat size_map ltnn subnn /=.
  by rewrite heval.
Qed.

Lemma match_state_SysCall fd ls ls' ii sc ac0 ac1 xs :
  let: li := MkLI ii (Lsyscall sc) in
  lom_eqv rip (to_estate ls) (asm_m xs) ->
  get_fundef (lp_funcs p) (lfn ls) = Some fd ->
  lfn ls = asm_f xs ->
  assemble_c agparams rip (lfd_body fd) = ok (asm_c xs) ->
  mapM (assemble_i agparams rip) (take (lpc ls) (lfd_body fd)) = ok ac0 ->
  flatten ac0 ++ [:: {| asmi_ii := ii ; asmi_i := SysCall sc |} ] ++ flatten ac1 = asm_c xs ->
  asm_pos rip (lpc ls) (lfd_body fd) = asm_ip xs ->
  onth (asm_c xs) (asm_ip xs) = onth ({| asmi_ii := ii ; asmi_i := SysCall sc |} :: flatten ac1) 0 ->
  onth (lfd_body fd) (lpc ls) = Some li ->
  linear_sem.eval_instr p li ls = ok ls' ->
  exists2 xs',
    asmsem p' xs xs'
    & exists2 lc',
        ssrfun.omap lfd_body (get_fundef (lp_funcs p) (lfn ls')) = Some lc'
        & match_state rip ls' lc' xs'.
Proof.
  move=> hloeq ok_fd hfn hass hac heq hip hnth ok_i.
  rewrite /linear_sem.eval_instr /=.
  t_xrbindP=> ves hves [[scs m] vs] ho; t_xrbindP=> s hw ?; subst ls' => /=.
  apply (match_state_step1 (ls':= ((of_estate s (lfn ls) (lpc ls).+1))) hnth).
  rewrite ok_fd /=.
  case: (hloeq) ho => /= -> -> _ _ _ _ _ _ ho.
  have [xs' hxs'] := (eval_syscall_spec2 ho).
  rewrite hxs' /=.
  eexists; first reflexivity.
  exists (lfd_body fd) => //.
  have [hex hpr hrip] := eval_syscall_spec1 hxs'.
  move: hex; rewrite (exec_syscallPs_eq ho); last first.
  - move: hves => {vs hw ho}.
    elim: (take (size (syscall_sig_s sc).(scs_tin)) call_reg_args) ves
        => [ | r rs ih] /= _vs.
    + by move=> [<-].
    t_xrbindP => v hv vs /ih ? <-; constructor => //.
    by apply : getreg hloeq hv.
  move=> [???]; subst scs m vs.
  split => //=; last by apply: asm_pos_incr ok_i hac heq hip.
  rewrite to_estate_of_estate.
  case: hloeq => /= hscs hmem hgetrip hdisjrip hreg hregx hxreg hflag.
  set R := vrvs (to_lvals (syscall_sig sc).(scs_vout)).
  set X := Sv.union syscall_kill R.

  have heqx: evm s =[\ X ] lvm ls.
  - rewrite /X; apply: (eq_exT (vm2 := vm_after_syscall (lvm ls))).
    + apply: eq_exI; last by apply eq_exS; apply: vrvsP hw => /=. SvD.fsetdec.
    apply: (eq_exI (s2:= syscall_kill)); first SvD.fsetdec.
    by move=> z /Sv_memP/negPf hz; rewrite /vm_after_syscall kill_varsE hz.

  have hres:
    forall r,
      Sv.In (to_var r) R ->
      value_uincl (evm s).[to_var r] (Vword (asm_reg xs' r)).
  - move=> r.
    rewrite /R vrvs_to_lvals => /sv_of_listP.
    rewrite mem_map; last exact: inj_to_var.
    have! h :=
      (take_uniq (size (scs_tout (syscall_sig_s sc))) call_reg_ret_uniq).
    move: hw r.
    elim:
      (take (size (syscall_sig_s sc).(scs_tout)) call_reg_ret)
      {ho} {| evm := vm_after_syscall (lvm ls); |} h
      => //= r rs ih s1 /andP [hnin huniq] hw r0.
    rewrite (in_cons (T:= @ceqT_eqType _ _)) => /orP [];
      last by apply: (ih _ huniq hw).
    move=> /eqP ?; subst r0.
    have h: ~ Sv.In (to_var r) (vrvs (to_lvals [seq to_var i | i <- rs])).
    + rewrite vrvs_to_lvals.
      move=> /sv_of_listP /(mapP (T1:= @ceqT_eqType _ _)) [r'] hr' h.
      have ? := inj_to_var h; subst r'.
      by rewrite hr' in hnin.
    have [<-] := get_var_eq_ex false h (vrvsP hw).
    by rewrite Vm.setP_eq /= cmp_le_refl.

  have hkill :
    forall x,
      Sv.In x syscall_kill ->
      ~ Sv.In x R ->
      ~~ is_sarr (vtype x) ->
      (evm s).[x] = undef_addr (vtype x).
  - move=> x /Sv_memP hin hnin.
    have [<-] := get_var_eq_ex false hnin (vrvsP hw).
    rewrite /get_var kill_varsE hin; by case: (vtype x).

  constructor=> //=.
  - by rewrite (write_lvals_escs hw).

  - by apply: write_lvals_emem hw; apply: get_lvar_to_lvals.

  - rewrite heqx /X; first by rewrite hgetrip hrip.
    case: assemble_progP => -[] hripr hriprx hripxr hripf _ _ _.
    move=> /Sv.union_spec [] hin.
    + have := SvP.MP.FM.diff_1 hin.
      rewrite /= /all_vars !Sv.union_spec => -[ | [ | []]] /sv_of_listP
        /(mapP (T1:= @ceqT_eqType _ _)) => -[r _ hr];
        [elim: (hripr r)|elim: (hriprx r)|elim: (hripxr r)|elim: (hripf r)];
        by rewrite hr.
    move: hin.
    rewrite /R /= vrvs_to_lvals.
    move=> /sv_of_listP /(mapP (T1:= @ceqT_eqType _ _)) [r _] hr.
    by elim: (hripr r); rewrite hr.

  - move=> r.
    case: (Sv_memP (to_var r) R) => hinR; first by apply hres.
    case: (Sv_memP (to_var r) syscall_kill) => hinK.
    + by rewrite (hkill _ hinK hinR) /=.
    move: (hinK); rewrite /syscall_kill => hnin.
    have : Sv.In (to_var r) one_varmap.callee_saved.
    + by have := reg_in_all r; SvD.fsetdec.
    rewrite /one_varmap.callee_saved /= => /sv_of_listP /mapP [x] /hpr.
    move=> h /to_var_typed_reg ?; subst x.
    rewrite -h heqx // /X.
    SvD.fsetdec.

  - move=> r.
    have hinR : ~ Sv.In (to_var r) R.
    + rewrite /R /= vrvs_to_lvals => /sv_of_listP.
      move=> /(mapP (T1 := @ceqT_eqType _ _)) [x _] /(@sym_eq var).
      exact: to_var_reg_neq_regx.
    case: (Sv_memP (to_var r) syscall_kill) => hinK.
    + by have /(_ erefl) -> /= := hkill _ hinK hinR.
    move: (hinK); rewrite /syscall_kill => hnin.
    have : Sv.In (to_var r) one_varmap.callee_saved.
    + have := regx_in_all r; SvD.fsetdec.
    rewrite /one_varmap.callee_saved /= => /sv_of_listP /mapP [x] /hpr.
    move=> h /to_var_typed_regx ?; subst x.
    rewrite -h heqx // /X.
    SvD.fsetdec.

  - move=> r.
    have hinR : ~ Sv.In (to_var r) R.
    + rewrite /R /= vrvs_to_lvals => /sv_of_listP.
      move=> /(mapP (T1 := @ceqT_eqType _ _)) [x _] /(@sym_eq var).
      exact: to_var_reg_neq_xreg.
    case: (Sv_memP (to_var r) syscall_kill) => hinK.
    + by have /(_ erefl) -> /= := hkill _ hinK hinR.
    move: (hinK); rewrite /syscall_kill => hnin.
    have : Sv.In (to_var r) one_varmap.callee_saved.
    + have := xreg_in_all r. SvD.fsetdec.
    rewrite /one_varmap.callee_saved /= => /sv_of_listP /mapP [x] /hpr.
    move=> h /to_var_typed_xreg ?; subst x.
    rewrite -h heqx // /X.
    SvD.fsetdec.

  move=> r.
  have hinR : ~Sv.In (to_var r) R.
  + rewrite /R /= vrvs_to_lvals => /sv_of_listP.
    by move=> /(mapP (T1 := @ceqT_eqType _ _)) [x _].
  have hnc: ~ Sv.In (to_var r) one_varmap.callee_saved.
  + move=>
      /= /sv_of_listP /mapP [] f /(allP callee_saved_not_bool) h
      /to_var_typed_flag ?.
    by subst f.
  have hinK : Sv.In (to_var r) syscall_kill.
  + by rewrite /syscall_kill Sv.diff_spec;split => //; apply flag_in_all.
  have /(_ erefl) -> /= := hkill _ hinK hinR.
  by case: (asm_flag _ _).
Qed.

Lemma match_state_step ls ls' lc xs :
  ssrfun.omap lfd_body (get_fundef (lp_funcs p) (lfn ls)) = Some lc
  -> match_state rip ls lc xs
  -> step p ls = ok ls'
  -> exists2 xs',
       asmsem p' xs xs'
       & exists2 lc',
           ssrfun.omap lfd_body (get_fundef (lp_funcs p) (lfn ls')) = Some lc'
           & match_state rip ls' lc' xs'.
Proof.
  move=> omap_lc.
  move=> ms;
    rewrite /step /find_instr.
  case ok_fd: get_fundef omap_lc => [fd|] //= [?]; subst lc.
  case ok_i: (oseq.onth (lfd_body _) _) => [ i | // ].
  case: (ms) => hloeq heqf hass hip.
  move: (hass); rewrite (onth_split ok_i) /assemble_c mapM_cat /=; t_xrbindP.
  move=> ac ac0 hac ac' aci haci ac1 hac1 <- <-.
  rewrite flatten_cat /= => heq hsem.
  have hnth : onth (asm_c xs) (asm_ip xs) = onth (aci ++ flatten ac1) 0.
  + rewrite -hip (onth_split ok_i) /asm_pos /assemble_c take_cat size_take.
    case: (ltnP (lpc ls) (size (lfd_body fd))) ok_i => [hn ok_i| /onth_default -> //].
    by rewrite ltnn subnn take0 cats0 hac /= -heq onth_cat ltnn subnn.
  case: i ok_i haci hsem => /= li_ii [].
  - move=> lvs op pes; rewrite /linear_sem.eval_instr /=; t_xrbindP.
    move=> honth c hopc ? args ok_args res ok_res m hw ?; subst aci ls'.
    have [m' hf hloeq'] := assemble_sopnP ok_args ok_res hw hopc hloeq.
    rewrite /= ok_fd /=.

    have [???] :
      let: ls' := of_estate m (lfn ls) (lpc ls).+1 in
      exists2 xs',
        asmsem p' xs xs'
        & match_state rip ls' (lfd_body fd) xs';
      last first.
    + eexists; first by eauto. eexists; by eauto.

    move=> {hloeq hnth}.
    case: xs ms hass hf hip heqf heq => /= m0 f c0 ip ms hass hf ???; subst f ip c0.
    have [heq1 heq2] := asm_pos_AsmOp honth hac hopc.
    have := step_AsmOp (c' := [::]) (ls := ls) hass hloeq' _ hf.
    rewrite /= addn0 heq1.
    move=> []; by eauto.

  - move=> sc ok_i [?]; subst aci. by eauto using match_state_SysCall.

  - move=> [xlr | ] r ok_i.
    + case heqlr: to_reg => [lr /= | //] [?]; subst aci.
      rewrite /linear_sem.eval_instr => /=; t_xrbindP => l hgetpc.
      t_xrbindP=> ptr /o2rP ptr_eq vm hset hjump.
      apply (match_state_step1 (ls' := ls') hnth) => /=.
      rewrite /return_address_from.
      have /= := assemble_get_label_after_pc hass ok_i _ heqf hip _ hgetpc.
      rewrite heqlr ok_fd /= => /(_ _ erefl erefl) [] _ ->.
      rewrite -assemble_prog_labels -heqf ptr_eq.
      apply: eval_jumpP; last by apply hjump.
      rewrite /st_update_next /=.
      have : write_var true xlr (Vword ptr) (to_estate ls) = ok {| escs := lscs ls; emem := lmem ls; evm := vm |}.
      + by rewrite /write_var /= hset.
      have {heqlr} heqlr := of_varI heqlr.
      by move=> /(lom_eqv_write_var MSB_CLEAR hloeq) -/(_ _ heqlr).
    move=> [?]; subst aci.
    rewrite /linear_sem.eval_instr => /=; t_xrbindP=> wsp vsp hsp htow_sp l hgetpc.
    rewrite heqf.
    t_xrbindP=> ptr /o2rP ptr_eq m1 hm1 /= => hjump.
    apply (match_state_step1 (ls' := ls') hnth) => /=.
    rewrite /return_address_from.
    have /= := assemble_get_label_after_pc hass ok_i _ heqf hip _ hgetpc.
    rewrite ok_fd /= => /(_ _ erefl erefl) [] _ ->.
    rewrite -assemble_prog_labels ptr_eq.
    rewrite /eval_PUSH truncate_word_u /=.
    rewrite to_var_rsp in hsp.
    have -> := var_of_regP_eq hloeq hsp htow_sp.
    rewrite /mem_write_mem; case: (hloeq) => /= _ <- _ _ _ _ _ _.
    rewrite hm1 /=; apply: eval_jumpP; last by apply hjump.
    set vi := {| v_var := to_var ad_rsp; v_info := dummy_var_info |}.
    set ls1 := (X in to_estate X).
    have : write_var true vi (Vword (wsp -  wrepr reg_size (wsize_size reg_size))) (to_estate ls) = ok {| escs := lscs ls; emem := lmem ls; evm := lvm ls1 |}.
    + rewrite /write_var /= /to_estate //= /with_vm /=.
      by have [ ->] := to_var_rsp.
    move=> /(lom_eqv_write_var MSB_CLEAR hloeq) -/(_ ad_rsp erefl).
    by case=> *; constructor => //.
  - move=> hok_i [?]; subst aci; rewrite /linear_sem.eval_instr /=.
    t_xrbindP=> wsp vsp hsp htow_sp ptr ok_ptr r /o2rP ptr_eq hjump.
    apply (match_state_step1 (ls' := ls') hnth) => /=.
    rewrite /eval_POP truncate_word_u /=.
    rewrite to_var_rsp in hsp.
    have -> := var_of_regP_eq hloeq hsp htow_sp.
    case: (hloeq) => /= _ <- _ _ _ _ _ _.
    rewrite ok_ptr /=.
    change reg_size with Uptr in ptr.
    replace (decode_label _ ptr) with (Some r);
      last by rewrite -assemble_prog_labels.
    apply: eval_jumpP; last by apply hjump.
    set vi := {| v_var := to_var ad_rsp; v_info := dummy_var_info |}.
    set ls1 := (X in to_estate X).
    have : write_var true vi (Vword (wsp +  wrepr reg_size (wsize_size reg_size))) (to_estate ls) = ok {| escs := lscs ls; emem := lmem ls; evm := lvm ls1 |}.
    + rewrite /write_var /= /to_estate //= /with_vm /=.
      by have [ ->] := to_var_rsp.
    move=> /(lom_eqv_write_var MSB_CLEAR hloeq) -/(_ ad_rsp erefl).
    by case=> *; constructor => //.
  - move=> hok_i [?] [?]; subst aci ls'.
    apply (match_state_step1 (ls' := (setpc ls (lpc ls).+1)) hnth) => /=.
    eexists; first reflexivity.
    rewrite ok_fd /=; eexists; first eauto.
    constructor => //; rewrite /setpc /=.
    by apply: asm_pos_incr hok_i hac heq hip.
  - move=> k lbl hok_i [?] [?]; subst aci ls'.
    apply (match_state_step1 (ls' := (setpc ls (lpc ls).+1)) hnth) => /=.
    eexists; first reflexivity.
    rewrite ok_fd /=; eexists; first eauto.
    constructor => //; rewrite /setpc /=.
    by apply: asm_pos_incr hok_i hac heq hip.
  - move=> r hok_i [?] hi; subst aci.
    by apply (match_state_step1 (ls' := ls') hnth) => /=; apply: eval_jumpP; last by apply hi.
  - rewrite /linear_sem.eval_instr /=; t_xrbindP=> e hok_i ok_e.
    move => d ok_d ? ptr v ok_v /to_wordI[? [? [? /word_uincl_truncate hptr]]]; subst.
    move=> r /o2rP ptr_eq.
    change reg_size with Uptr in ptr => hdec.
    apply (match_state_step1 (ls' := ls') hnth) => /=; move: hdec.
    have [v' -> /value_uinclE /= [? [? [-> /hptr /= ->]]]] := eval_assemble_word hloeq ok_e ok_d ok_v.
    rewrite -assemble_prog_labels /= ptr_eq.
    by apply eval_jumpP.
  - move => x lbl hok_i.
    case ok_r_x': (of_var x) => [r|//]; have ok_r_x := of_varI ok_r_x'.
    move=> /= [?] hev; subst aci.
    apply (match_state_step1 (ls' := ls') hnth) => /=.
    move: hev; rewrite /linear_sem.eval_instr /=.
    rewrite heqf -assemble_prog_labels.
    t_xrbindP=> ptr /o2rP -> vm ok_vm <-{ls'}.
    eexists; first reflexivity.
    rewrite ok_fd /=; eexists; first by eauto.
    constructor => //=.
    + move: ok_r_x; change x with (v_var (VarI x dummy_var_info)).
      apply: lom_eqv_write_var; first exact: hloeq.
      by rewrite /write_var ok_vm.
    by apply: asm_pos_incr hok_i hac heq hip => /=; rewrite ok_r_x'.
  - rewrite /linear_sem.eval_instr => /=.
    t_xrbindP => cnd lbl hok_i cndt ok_c ? b v ok_v ok_b; subst aci.
    case: hloeq => eqscs eqm hrip hd eqr eqrx eqx eqf.
    have [v' ok_v' hvv'] := hagp_eval_assemble_cond hagparams eqr eqf ok_c ok_v.
    case: v ok_v ok_b hvv' => // [ b' | [] // ] ok_b [?]; subst b'.
    rewrite ok_fd /=; case: v' ok_v' => // b1 ok_v' ? h; subst b1.
    apply (match_state_step1 (ls' := ls') hnth) => /=; move: h.
    rewrite /eval_Jcc; case: b ok_b ok_v' => ok_b ok_v';
      rewrite /eval_cond_mem /=;
      case: (eval_cond _ _) ok_v' => // [ b | [] // ] [->] {b} /=.
    + t_xrbindP => pc ok_pc ?; subst ls' => /=.
      rewrite ok_fd /= (assemble_c_find_label hass ok_pc) /=.
      do 2 (eexists; first reflexivity).
      by constructor => //; apply: find_label_asm_posS ok_pc hass.
    move => [?]; subst ls'; rewrite ok_fd /=.
    do 2!(eexists; first reflexivity).
    constructor => //; rewrite /setpc /=.
    by apply: asm_pos_incr hok_i hac heq hip; rewrite /= ok_c.
Qed.

Lemma match_state_sem ls ls' lc xs :
  ssrfun.omap lfd_body (get_fundef (lp_funcs p) (lfn ls)) = Some lc
  -> lsem p ls ls'
  -> match_state rip ls lc xs
  -> exists xs' lc',
       [/\ asmsem p' xs xs'
         , ssrfun.omap lfd_body (get_fundef (lp_funcs p) (lfn ls')) = Some lc'
         & match_state rip ls' lc' xs'
       ].
Proof.
  move=> omap_lc.
  move=> h;
    elim/lsem_ind: h xs lc omap_lc => {ls ls'}.
  - move=> ls xs lc omap_lc h.
    exists xs, lc; split => //; exact: rt_refl.
  move=> ls1 ls2 ls3 h1 h ih xs1 lc omap_lc m1.
  have [xs2 x [ lc' omap_lc' m2 ]] := match_state_step omap_lc m1 h1.
  have [xs3 [lc''] [y omap_lc'' m3]] := ih _ _ omap_lc' m2.
  exists xs3; exists lc''; split => //.
  apply: asmsem_trans x y.
Qed.

(* ------------------------------------------------------------------------------ *)

Lemma asm_gen_exportcall fn scs m vm scs' m' vm' :
  lsem_exportcall p scs m fn vm scs' m' vm'
  -> vm_initialized_on vm (map var_of_asm_typed_reg callee_saved)
  -> forall xm,
      lom_eqv rip {| escs := scs; emem := m; evm := vm; |} xm
      -> exists2 xm',
           asmsem_exportcall p' fn xm xm'
           & lom_eqv rip {| escs := scs'; emem := m'; evm := vm'; |} xm'.
Proof.
  case=> fd ok_fd export lexec saved_registers /allP ok_vm xm M.
  have [ fd' ok_fd' ] := ok_get_fundef ok_fd.
  case/assemble_fdI => ok_sp _ [] c [] ? [] ? [] ok_c ? ? ? ok_call_conv;
    subst fd'.
  set s := {| asm_m := xm; asm_f := fn; asm_c := c; asm_ip := 0; |}.
  have /= := match_state_sem _ lexec.
  rewrite ok_fd => /(_ _ s erefl) [].
  + by constructor => //; rewrite /asm_pos take0.
  move=> [] xm' fn' c' pc' [] _ [] xexec /Some_inj <- [] /= M'.
  rewrite ok_c => ? /ok_inj ??; subst fn' c' pc'.
  exists xm'; last exact: M'.
  eexists; first exact: ok_fd'.
  - exact: export.
  - exact: ok_call_conv. 
  - by move: xexec; rewrite /asm_pos take_size ok_c.
  move=> r hr.
  assert (H: var_of_asm_typed_reg r \in map var_of_asm_typed_reg callee_saved).
  + by apply/in_map; exists r => //; apply/InP.
  move: H => {} hr.
  have /saved_registers E :
    Sv.In (var_of_asm_typed_reg r) (sv_of_list var_of_asm_typed_reg callee_saved).
  - by apply/sv_of_listP.
  case: M => /= _ _ _ _ Mr Mrx Mxr Mf.
  case: M' => /= _ _ _ _ Mr' Mrx' Mxr' Mf'.
  assert (h1 := Vm.getP vm (var_of_asm_typed_reg r)).
  move/ok_vm: hr h1.
  case: r E => r /= E;
    [ move: (Mr' r) (Mr r) | move: (Mrx' r) (Mrx r) | move: (Mxr' r) (Mxr r) | move: (Mf' r) (Mf r) ];
    rewrite /get_var E.
  1-3: by move=> + + + /compat_valEl /= h;
   case h => [-> //| [ws' [w ->]]] hle1 /= X' X /is_okP[] ? /truncate_wordP []
   /(cmp_le_antisym hle1) ? _; subst ws';
   rewrite -(word_uincl_eq X) -(word_uincl_eq X').
  move=> + + + /compat_valEl /= h /=.
  case h => [-> //| [b ->]] /=.
  by case: (asm_flag xm' r) => //= _ <-; case: (asm_flag xm r) => //= _ <-.
Qed.

Section VMAP_SET_VARS.

  Context {t : stype} {T: Type} {tS:ToString t T}  {tI:ToIdent T}.
  Let T_eqType := @ceqT_eqType T _. Canonical T_eqType.
  Context (fromT: T -> sem_ot t).

  Definition vmap_set_vars : Vm.t -> seq T -> Vm.t :=
    foldl (fun vm x => vm.[to_var x <- oto_val (fromT x)]).

  Lemma get_var_vmap_set_vars_other vm xs y :
    all (fun x => to_var x != y) xs
    -> (vmap_set_vars vm xs).[y] = vm.[y].
  Proof. by elim: xs vm => // x xs ih vm /= /andP[] x_neq_y /ih ->; apply: Vm.setP_neq. Qed.


  Lemma get_var_vmap_set_vars_other_type vm xs y :
    vtype y != t ->
    (vmap_set_vars vm xs).[y] = vm.[y].
  Proof.
    move=> /eqP neqt; apply: get_var_vmap_set_vars_other.
    by apply/allP => x _; apply/eqP => ?; subst y.
  Qed.

  Lemma get_var_vmap_set_vars_finite vm xs y :
    Finite.axiom xs ->
    (vmap_set_vars vm xs).[to_var y] = oto_val (fromT y).
  Proof.
    move=> finT; move: vm.
    have {finT} : y \in xs.
    - by rewrite -has_pred1 has_count finT.
    elim: xs => // x xs; rewrite inE.
    case y_xs: (y \in xs).
    - move=> /(_ erefl) ih _ vm; exact: ih.
    rewrite orbF => _ /eqP <-{x} vm /=.
    rewrite get_var_vmap_set_vars_other.
    + by rewrite Vm.setP_eq vm_truncate_val_eq // type_of_oto_val.
    apply/allP => x x_xs.
    apply/eqP => h; have ? := inj_to_var h.
    subst x.
    by rewrite x_xs in y_xs.
  Qed.

End VMAP_SET_VARS.

Definition vmap_of_asm_mem
  (sp : word Uptr) (rip rsp : Ident.ident) (s : asmmem) :=

  let pword_of_reg r   := (asm_reg s r : sem_ot (sword reg_size)) in
  let pword_of_regx rx := (asm_regx s rx: sem_ot (sword reg_size)) in
  let pword_of_xreg xr := (asm_xreg s xr: sem_ot (sword xreg_size)) in
  let pbool_of_flag f  := (if asm_flag s f is Def b then Some b else None : sem_ot sbool) in
  let vm := Vm.init.[mk_ptr rsp <- Vword sp]
                   .[mk_ptr rip <- Vword (asm_rip s)] in
  let vm := vmap_set_vars pword_of_reg vm registers in
  let vm := vmap_set_vars pword_of_regx vm registerxs in
  let vm := vmap_set_vars pword_of_xreg vm xregisters in
  let vm := vmap_set_vars (t := sbool) pbool_of_flag vm rflags in
  vm.

Definition get_typed_reg_value (st : asmmem) (r : asm_typed_reg) : value :=
  match r with
  | ARReg r => Vword (asm_reg  st r)
  | ARegX r => Vword (asm_regx st r)
  | AXReg r => Vword (asm_xreg st r)
  | ABReg r => of_rbool (asm_flag st r)
  end.

Definition get_typed_reg_values st rs : values :=
  map (get_typed_reg_value st) rs.

Lemma get_var_vmap_of_asm_mem sp rip rsp s (r : asm_typed_reg) :
  (vmap_of_asm_mem sp rip rsp s).[var_of_asm_typed_reg r] = get_typed_reg_value s r.
Proof.
  rewrite /vmap_of_asm_mem.
  assert (h := sword_reg_neq_xreg).
  case: r => r.
  all: repeat (rewrite get_var_vmap_set_vars_other_type; last done).
  + rewrite get_var_vmap_set_vars_other.
    + rewrite get_var_vmap_set_vars_finite //=; exact cenumP.
    by apply/allP => /= x _; rewrite eq_sym; apply/eqP/to_var_reg_neq_regx.  
  + by rewrite get_var_vmap_set_vars_finite //=; exact: cenumP.
  + by rewrite get_var_vmap_set_vars_finite //=; exact: cenumP.
  by rewrite get_var_vmap_set_vars_finite /=;[case: (asm_flag s r)| exact: cenumP].
Qed.

Definition estate_of_asm_mem
  (sp : word Uptr) (rip rsp : Ident.ident) (s : asmmem) : estate :=
  {| escs := asm_scs s; emem := asm_mem s; evm := vmap_of_asm_mem sp rip rsp s; |}.

Lemma lom_eqv_estate_of_asm_mem sp rip rsp s :
  disj_rip (mk_ptr rip)
  -> lom_eqv (mk_ptr rip) (estate_of_asm_mem sp rip rsp s) s.
Proof.
  case => rip_not_reg rip_not_regx rip_not_xreg rip_not_flag.
  split => //=.
  - rewrite /vmap_of_asm_mem.
    rewrite get_var_vmap_set_vars_other_type //.
    rewrite get_var_vmap_set_vars_other_type;
      last exact: sword_reg_neq_xreg.
    rewrite get_var_vmap_set_vars_other; last first.
    + apply/allP => /= r _; apply/eqP. exact: rip_not_regx.
    rewrite get_var_vmap_set_vars_other; last first.
    + apply/allP => /= r _; apply/eqP. exact: rip_not_reg.
    by rewrite Vm.setP_eq //= cmp_le_refl.
  - by move => r; rewrite (get_var_vmap_of_asm_mem _ _ _ _ (ARReg r)).
  - by move => r; rewrite (get_var_vmap_of_asm_mem _ _ _ _ (ARegX r)).
  - by move => r; rewrite (get_var_vmap_of_asm_mem _ _ _ _ (AXReg r)).
  by move => r; rewrite (get_var_vmap_of_asm_mem _ _ _ _ (ABReg r)).
Qed.

End PROG.

Lemma lom_eqv_ext rip s xs vm :
  (evm s =1 vm)%vm ->
  lom_eqv rip s xs ->
  lom_eqv rip (with_vm s vm) xs.
Proof.
  move=> heq [] h1 h2 h3 h4 h5 h6 h7 h8; split => //=;
   first (by rewrite -heq);
   by move=> r; rewrite -heq; auto.
Qed.

Definition sem_sopn_t '(o, xs, es) s :=
  Let args := sem_rexprs s es in
  Let res := exec_sopn (Oasm (BaseOp o)) args in
  write_lexprs xs res s.

Definition sem_sopns := foldM sem_sopn_t.

(* We take [assemble_cond_spec] explicitly because this lemma is useful to prove
   [hagp_assemble_extra_op]. *)
Lemma assemble_opsP rip ii ops ops' m m' s :
  assemble_cond_spec ->
  mapM (assemble_asm_args agparams rip ii) ops = ok ops' ->
  all (fun '(op, xs, es) => if fst op is None then true else false) ops ->
  sem_sopns m ops = ok m' ->
  lom_eqv rip m s ->
  exists2 s',
    foldM (fun '(op, asm_args) => eval_op op asm_args) s ops' = ok s'
    & lom_eqv rip m' s'.
Proof.
  move=> hcond.
  elim: ops ops' s m => [| [[[[]// o] xs] es] ops hrec ] /= ops' s m.
  + by move=> [<-] _ [<-] hlo /=; eexists; eauto.
  t_xrbindP=> -[op args] hass ops'' hmap <- hall m1 ves hes vxs hex hw hsem hlo.
  have h := assemble_asm_opI hass; case: h => hca hcd hidc -> /= {hass}.
  have [s1] := compile_asm_opn_aux hcond hes hex hw hca hcd hidc hlo.
  rewrite /eval_op /= => ->; apply: hrec hmap hall hsem.
Qed.

End ASM_EXTRA.
