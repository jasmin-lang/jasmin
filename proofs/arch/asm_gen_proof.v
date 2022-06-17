From mathcomp Require Import all_ssreflect all_algebra.
From Coq Require Import Relation_Operators.
Require Import
  oseq
  compiler_util
  psem
  label
  lea_proof
  one_varmap sem_one_varmap
  (* FIXME syscall : this is needed for write_lvars_escs write_lvars_emem *)
  merge_varmaps_proof
  linear
  linear_sem.
Require Import
  arch_decl
  arch_extra
  arch_sem.
Require Export asm_gen.
Import Utf8.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section ASM_EXTRA.

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
  ∀ (f: rflag) v, on_vu Vbool (ok undef_b) (evm m).[to_var f]%vmap = ok v → value_uincl v (of_rbool (rf f)).

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
    & get_var (evm m) rip = ok (Vword lom.(asm_rip))
    & disj_rip rip
    & (∀ r v, get_var (evm m) (to_var r) = ok v → value_uincl v (Vword (asm_reg lom r)))
    & (∀ r v, get_var (evm m) (to_var r) = ok v → value_uincl v (Vword (asm_regx lom r)))
    & (∀ r v, get_var (evm m) (to_var r) = ok v → value_uincl v (Vword (asm_xreg lom r)))
    & eqflags m (asm_flag lom).

(* -------------------------------------------------------------------- *)
Definition value_of_bool (b: exec bool) : exec value :=
  match b with
  | Ok b => ok (Vbool b)
  | Error ErrAddrUndef => ok undef_b
  | Error e => Error e
  end.

(* -------------------------------------------------------------------- *)
Lemma xgetreg_ex rip x r v s xs :
  lom_eqv rip s xs →
  of_var x = Some r →
  get_var s.(evm) x = ok v →
  value_uincl v (Vword (xs.(asm_reg) r)).
Proof. case => _ _ _ _ eqv _ _ _ /of_varI <-; exact: eqv. Qed.

(* -------------------------------------------------------------------- *)
Lemma xgetregx_ex rip x r v s xs :
  lom_eqv rip s xs →
  of_var x = Some r →
  get_var s.(evm) x = ok v →
  value_uincl v (Vword (xs.(asm_regx) r)).
Proof. case => _ _ _ _ eqv eqv' eqv'' _ /of_varI <-;exact: eqv'. Qed.

(* -------------------------------------------------------------------- *)
Lemma xxgetreg_ex rip x r v s xs :
  lom_eqv rip s xs →
  of_var x = Some r →
  get_var (evm s) x = ok v →
  value_uincl v (Vword (asm_xreg xs r)).
Proof. by case => _ _ _ _ _ _ eqv _  /of_varI <-; exact: eqv. Qed.

(* -------------------------------------------------------------------- *)
Lemma xgetflag_ex ii m rf x f v :
  eqflags m rf →
  of_var_e ii x = ok f →
  get_var (evm m) x = ok v →
  value_uincl v (of_rbool (rf f)).
Proof.
  move => eqm /of_var_eP /of_varI <-.
  rewrite get_varE; t_xrbindP => /= b ok_b <-.
  move: (eqm f b).
  by rewrite ok_b => /(_ erefl).
Qed.

Lemma gxgetflag_ex ii m rf (x:gvar) f v :
  eqflags m rf →
  of_var_e ii x.(gv) = ok f →
  get_gvar [::] (evm m) x = ok v →
  value_uincl v (of_rbool (rf f)).
Proof.
  by rewrite /get_gvar; case: ifP => // ?; apply: xgetflag_ex.
Qed.

Corollary xgetflag ii m rf x f v b :
  eqflags m rf →
  of_var_e ii x = ok f →
  get_var (evm m) x = ok v →
  to_bool v = ok b →
  rf f = Def b.
Proof.
move => eqm ok_f ok_v ok_b.
have := xgetflag_ex eqm ok_f ok_v.
case: {ok_v} v ok_b => //.
- by move => b' [<-]; case: (rf _) => // ? ->.
by case.
Qed.

Corollary gxgetflag ii m rf (x:gvar) f v b :
  eqflags m rf →
  of_var_e ii x.(gv) = ok f →
  get_gvar [::] (evm m) x = ok v →
  to_bool v = ok b →
  rf f = Def b.
Proof.
  by rewrite /get_gvar; case: ifP => // ?; apply: xgetflag.
Qed.

(* -------------------------------------------------------------------- *)
Lemma eq_get_gvar m x y vx vy:
  v_var (gv x) = v_var (gv y) -> get_gvar [::] m x = ok vx -> get_gvar [::] m y = ok vy -> vx = vy.
Proof.
  by rewrite /get_gvar; case:ifP => //; case: ifP => // ?? -> -> [->].
Qed.

(* -------------------------------------------------------------------- *)

Context
  (agparams : asm_gen_params).

Notation assemble_cond := (agp_assemble_cond agparams).

Lemma xscale_ok ii z sc :
  scale_of_z' ii z = ok sc ->
  z = word_of_scale sc.
Proof.
  rewrite /scale_of_z' -[X in _ -> X = _]wrepr_unsigned.
  case: (wunsigned z) => //.
  do! (case=> //; try by move=> <-).
Qed.

Lemma assemble_leaP rip ii sz sz' (w:word sz') lea adr m s:
  (sz ≤ Uptr)%CMP →
  (sz ≤ sz')%CMP →
  lom_eqv rip m s →
  sem_lea sz (evm m) lea = ok (zero_extend sz w) →
  assemble_lea ii lea = ok adr →
  zero_extend sz (decode_addr s adr) = zero_extend sz w.
Proof.
  move=> hsz64 hsz [_ _ _ _ hget _ _ _] hsem; rewrite /assemble_lea.
  t_xrbindP => ob hob oo hoo sc hsc <- /=.
  rewrite /decode_reg_addr /=.
  move: hsem; rewrite /sem_lea.
  apply rbindP => wb hwb; apply rbindP => wo hwo heq.
  have <- := ok_inj heq.
  rewrite !(wadd_zero_extend, wmul_zero_extend) // GRing.addrA; do 2 f_equal.
  + case: lea_base hob hwb => /= [vo | [<-] [<-] /=]; last by apply zero_extend0.
    by t_xrbindP => r /of_var_eI <- <- v /hget /[swap]
      /to_wordI [? [? [-> /word_uincl_truncate h]]] /= /h /truncate_wordP [].
  + by rewrite (xscale_ok hsc).
  case: lea_offset hoo hwo => /= [vo | [<-] [<-] /=]; last by apply zero_extend0.
  by t_xrbindP => r /of_var_eI <- <- v /hget /[swap]
    /to_wordI [? [? [-> /word_uincl_truncate h]]] /= /h /truncate_wordP [].
Qed.

Lemma addr_of_pexprP rip ii sz sz' (w:word sz') e adr m s:
  (sz ≤ sz')%CMP →
  lom_eqv rip m s →
  sem_pexpr [::] m e = ok (Vword w) ->
  addr_of_pexpr rip ii sz e = ok adr ->
  zero_extend sz (decode_addr s adr) = zero_extend sz w.
Proof.
  rewrite /addr_of_pexpr => hsz lom he.
  t_xrbindP => hsz64.
  case heq: mk_lea => [lea | //].
  have hsemlea := mk_leaP hsz64 hsz heq he.
  case hb: lea_base => [b | ]; last by apply (assemble_leaP hsz64 hsz lom hsemlea).
  case: eqP => [ | _]; last by apply (assemble_leaP hsz64 hsz lom hsemlea).
  t_xrbindP => hbrip /eqP ho <- /=.
  case: lom => _ _ hrip _ _ _.
  move: hsemlea; rewrite /sem_lea ho hb /= hbrip hrip /= /truncate_word hsz64 /= => h.
  have <- := ok_inj h.
  by rewrite GRing.mulr0 GRing.addr0 GRing.addrC wadd_zero_extend.
Qed.

Lemma addr_of_xpexprP rip m s ii x p r vx wx vp wp:
  lom_eqv rip m s →
  addr_of_xpexpr rip ii Uptr x p = ok r ->
  get_var (evm m) x = ok vx ->
  to_pointer vx = ok wx ->
  sem_pexpr [::] m p = ok vp ->
  to_pointer vp = ok wp ->
  decode_addr s r = (wx + wp)%R.
Proof.
  rewrite /addr_of_xpexpr => eqm ha hx hvx hp hvp.
  have he: sem_pexpr [::] m (Papp2 (Oadd (Op_w Uptr)) (Plvar x) p) = ok (Vword (wx + wp)).
  + by rewrite /= /get_gvar /= hx /= hp /= /sem_sop2 /= hvx hvp.
  have := addr_of_pexprP _ eqm he ha.
  by rewrite !zero_extend_u => h;apply h.
Qed.

Variant check_sopn_argI rip ii args e : arg_desc -> stype -> Prop :=
| CSA_Implicit i ty :
       (eq_expr e (Plvar {| v_var := var_of_implicit i; v_info := 1%positive |}))
    -> check_sopn_argI rip ii args e (ADImplicit i) ty

| CSA_Explicit k n o a a' ty :
       onth args n = Some a
    -> arg_of_pexpr agparams k rip ii ty e = ok a'
    -> compat_imm ty a a'
    -> check_oreg o a
    -> check_sopn_argI rip ii args e (ADExplicit k n o) ty.

Lemma check_sopn_argP rip ii args e sp :
  check_sopn_arg agparams rip ii args e sp ->
  check_sopn_argI rip ii args e sp.1 sp.2.
Proof.
case: sp => -[i|k n o] ty; first by apply: CSA_Implicit.
rewrite /check_sopn_arg /=; case Enth: onth => [a|] //.
case E: arg_of_pexpr => [a'|] // /andP[??].
by apply: (CSA_Explicit (a := a) (a' := a')).
Qed.

Lemma var_of_flagP rip m s f v ty vt:
  lom_eqv rip m s
  -> get_var (evm m) (to_var f) = ok v
  -> of_val ty v = ok vt
  -> exists2 v' : value,
      Let b := st_get_rflag s f in ok (Vbool b) = ok v'
      & of_val ty v' = ok vt.
Proof.
  move=> [_ _ _ _ _ _ _ h].
  rewrite get_varE; t_xrbindP => /= b ok_b <-{v} /of_valE[? ]; subst=> /= ->.
  move: (h f b); rewrite ok_b => /(_ erefl).
  rewrite /st_get_rflag.
  by case: (asm_flag s f) => // _ <-; exists b.
Qed.

Lemma var_of_regP rip E m s r v ty vt:
  lom_eqv rip m s
  -> get_var (evm m) (to_var r) = ok v
  -> of_val ty v = ok vt
  -> exists2 v' : value,
      Ok E (Vword ((asm_reg s) r)) = ok v'
      & of_val ty v' = ok vt.
Proof. by move=> [???? h ???] /h /of_value_uincl h1 /h1 <-; eauto. Qed.

Section EVAL_ASSEMBLE_COND.

Context
  (eval_assemble_cond :
     forall ii m rf e c v,
       eqflags m rf
       -> agp_assemble_cond agparams ii e = ok c
       -> sem_pexpr [::] m e = ok v
       -> let get x :=
            if rf x is Def b
            then ok b
            else undef_error
          in
          exists2 v',
            value_of_bool (eval_cond get c) = ok v'
            & value_uincl v v').

Lemma check_sopn_arg_sem_eval rip m s ii args e ad ty v vt :
  lom_eqv rip m s
  -> check_sopn_arg agparams rip ii args e (ad,ty)
  -> sem_pexpr [::] m e = ok v
  -> of_val ty v = ok vt
  -> exists2 v', eval_arg_in_v s args ad ty = ok v'
     & of_val ty v' = ok vt.
Proof.
  move=> eqm /check_sopn_argP /= h.
  case: h vt.
  + move=> i {ty} ty /eq_exprP -> vt /=.
    case: i => /= [f | r]; first by apply: var_of_flagP eqm.
    by apply: var_of_regP eqm.
  move=> k n o a a' [ | | | ws] //= ->.
  + t_xrbindP => c hac <-.
    rewrite /compat_imm orbF => /eqP <- -> /= b hb.
    case: eqm => ??????? eqf.
    have [v'] := eval_assemble_cond eqf hac hb.
    rewrite /eval_cond_mem; case: eval_cond => /=;
      last by case=> // [[<-]] /[swap] /to_boolI ->.
    move=> b' [<-] {hb}; case: v => // [b1 | [] //] -> ?.
    by exists b'.
  move=> haw hcomp -> /=.
  case: k haw => /=.
  + t_xrbindP=> adr hadr ? w he /to_wordI' [ws' [w' [hws ? ->]]].
    subst a' v.
    move: hcomp; rewrite /compat_imm orbF => /eqP ?; subst a => /=.
    rewrite (addr_of_pexprP hws eqm he hadr); eexists; first reflexivity.
    by rewrite /= truncate_word_u.
  case: e => //=.
  + rewrite /get_gvar /eval_asm_arg => x; t_xrbindP => ->.
    case: eqm => _ _ _ _ eqr eqrx eqx _.
    move=> /xreg_of_varI; case: a' hcomp => // r;
      rewrite /compat_imm orbF => /eqP <- {a} /of_varI <- w ok_v /to_wordI[? [? [? ok_w]]];
      (eexists; first reflexivity); apply: (word_uincl_truncate _ ok_w); subst.
    + exact: (eqr _ _ ok_v).
    + exact: (eqrx _ _ ok_v).
    exact: (eqx _ _ ok_v).
  + move=> sz x p; t_xrbindP => /eqP <- r hr ?; subst a'.
    move: hcomp; rewrite /compat_imm orbF => /eqP <-.
    move=> w1 wp vp hget htop wp' vp' hp hp' wr hwr <- /= htr.
    have -> := addr_of_xpexprP eqm hr hget htop hp hp'.
    by case: eqm => ? <- ?????; rewrite hwr /=; eauto.
  case => //= w' [] //= z.
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

(*
Lemma zero_extend_mask_word sz sz' :
  (sz ≤ sz')%CMP →
  zero_extend sz (mask_word sz') = 0%R.
Proof.
case: sz'.
+ 1-2: case: sz => // _; exact: word_ext.
all: exact: (λ _, zero_extend0 sz _).
Qed.

Lemma word_uincl_ze_mw sz sz' (w: word sz) (u: u64) :
  (sz' ≤ sz)%CMP →
  (sz' ≤ U64)%CMP →
  word_uincl (zero_extend sz' w) (merge_word u w).
Proof.
move => hle hle'.
by rewrite /word_uincl hle' /= /merge_word -wxor_zero_extend // zero_extend_idem // -wand_zero_extend // zero_extend_mask_word // wand0 wxor0.
Qed.
*)

(*Definition mask_word (f : msb_flag) (sz szr : wsize) (old : word szr) : word szr :=
  let mask := if f is MSB_MERGE then wshl (-1)%R (wsize_bits sz)
             else 0%R in
  wand old mask.

Definition word_extend
   (f:msb_flag) (sz szr : wsize) (old : word szr) (new : word sz) : word szr :=
 wxor (mask_word f sz old) (zero_extend szr new).
*)
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
  by rewrite wandC wand0 wxor0.
Qed.

Lemma word_extend_big sz szo f (w : word sz) (old : word szo) :
  ~(sz <= szo)%CMP ->
  (word_extend f old w) = zero_extend szo w.
Proof.
  move=> h; case: f; first by rewrite word_extend_CLEAR.
  rewrite /word_extend /arch_sem.mask_word wshl_ovf; last first.
  + by apply/leP; case: (sz) (szo) h => -[].
  by rewrite wandC wand0 wxor0.
Qed.
(*
Search to_var.
Lemma of_reg_neq_of_xreg (r:reg_t) (x:xreg_t) : to_var r <> to_var x.
Proof.
  move=> [] hsize _; assert (h:= reg_size_neq_xreg_size).
  by move: h; rewrite hsize eqxx.
Qed.

Lemma of_regx_neq_of_xreg (r:regx_t) (x:xreg_t) : to_var r <> to_var x.
Proof.
  move=> [] hsize _; assert (h:= reg_size_neq_xreg_size).
  by move: h; rewrite hsize eqxx.
Qed.

Lemma of_reg_neq_of_regx (r:reg_t) (x:regx_t) : to_var r <> to_var x.
Proof.
Search to_var.
  move=> [] hsize _; assert (h:= reg_size_neq_xreg_size).
  by move: h; rewrite hsize eqxx.
Qed.

Lemma of_regx_neq_of_xreg (r:regx_t) (x:xreg_t) : to_var r <> to_var x.
Proof.
  move=> [] hsize _; assert (h:= reg_size_neq_xreg_size).
  by move: h; rewrite hsize eqxx.
Qed.
*)

Lemma compile_lval rip ii msb_flag loargs ad ty (vt:sem_ot ty) m m' s lv1 e1:
  lom_eqv rip m s ->
  check_arg_dest ad ty ->
  write_lval [::] lv1 (oto_val vt) m = ok m' ->
  pexpr_of_lval ii lv1 = ok e1 ->
  check_sopn_dest agparams rip ii loargs e1 (ad, ty) ->
  exists s', mem_write_val msb_flag loargs (ad, ty) (oto_val vt) s = ok s' /\ lom_eqv rip m' s'.
Proof.
  move=> hlom; case:(hlom) => [hscs h1 hrip hnrip h2 h3 h4 h5]; case: ad => [ai _ | k n o]; rewrite /check_sopn_dest /=.
  case: ai => [f | r].
  + case: lv1 => //=; last by move=> ???? [<-].
    move=> x hw [] <- /= /eqP heq.
    move: hw; rewrite /write_var heq; t_xrbindP => vm hvm <- /= {heq}.
    move: hvm; rewrite /mem_write_val /set_var /on_vu /= /oof_val.
    case: ty vt => //= vt h.
    have -> :
      match match vt with Some b => Vbool b | None => undef_b end with
      | Vbool b => ok (Some b)
      | Vundef sbool _ => ok None
      | _ => type_error
      end = ok vt.
    + by case: vt h.
    have -> /= : vm =  ((evm m).[to_var (tS:=toS_f) f <- match vt with Some b => ok b | None => undef_error end])%vmap.
    + by case: vt h => [b | ] /= [<-].
    eexists; split; first reflexivity.
    constructor => //=.
    + by case:hlom => ? ? hget hd _ _ _;rewrite /get_var Fv.setP_neq //; apply /eqP;case: hd.
    + move=> r v; rewrite /get_var /=; apply on_vuP => //= w.
      rewrite Fv.setP_neq // => hg hv.
      by apply (h2 r); rewrite /get_var /on_vu hg -hv.
    + move=> r v; rewrite /get_var /=; apply on_vuP => //= w.
      rewrite Fv.setP_neq // => hg hv.
      by apply (h3 r); rewrite /get_var /on_vu hg -hv.  
    + move=> r v; rewrite /get_var /=; apply on_vuP => //= w.
      rewrite Fv.setP_neq // => hg hv.
      by apply (h4 r); rewrite /get_var /on_vu hg -hv.  
    rewrite /eqflags => f' v; rewrite /get_var /on_vu /=.
    rewrite /RflagMap.set /= ffunE.
    case: eqP => [-> | hne] {h}.
    + by rewrite Fv.setP_eq; case: vt => [ b | ] /ok_inj <-.
    rewrite Fv.setP_neq; last by apply /eqP => h; apply hne; apply inj_to_var.
    by apply h5.
  + case: lv1 => //=; last by move=> ???? [<-].
    move=> x hw [<-] /eqP /= hx.
    move: hw; rewrite /write_var hx /= /set_var /=.
    t_xrbindP => vm; rewrite /on_vu.
    case heq : to_pword => [v | e]; last by case e.
    move=> [<-] <-; rewrite /mem_write_val /=.
    case: ty vt heq => //=; first by case.
    move=> sz w [<-]; rewrite truncate_word_u /=.
    eexists; split; first reflexivity.
    constructor => //=.
    + by case:hlom => ? ? hget hd _ _ _ _;rewrite /get_var Fv.setP_neq //; apply /eqP;case: hd.
    + move=> r' v'; rewrite /get_var /on_vu /= /RegMap.set ffunE.
      case: eqP => [-> | hne].
      + rewrite Fv.setP_eq => -[<-] /=.
        case : Sumbool.sumbool_of_bool => /= hsz; first by apply word_uincl_word_extend.
        by rewrite word_extend_big // hsz.
      rewrite Fv.setP_neq; last by apply /eqP => h; apply hne; apply inj_to_var.
      by apply h2.
    + move=> r' v'; rewrite get_var_neq; last first. 
      - rewrite /to_var /= /rtype /=. move=> []. exact: inj_toS_reg_regx.
      by apply h3.
    + move=> r' v'; rewrite get_var_neq; last by apply to_var_reg_neq_xreg.
      by apply h4.
    move=> f v'; rewrite /get_var /on_vu /=.
    by rewrite Fv.setP_neq //; apply h5.
  case heq1: onth => [a | //].
  case heq2: arg_of_pexpr => [ a' | //] hty hw he1 /andP[] /eqP ? hc; subst a'.
  rewrite /mem_write_val /= /mem_write_ty.
  case: lv1 hw he1 heq2=> //=.
  + move=> [x xii] /= hw [<-]; rewrite /arg_of_pexpr.
    case: ty hty vt hw => //= sz _ vt.
    rewrite /write_var; t_xrbindP => vm hset <-.
    apply: set_varP hset; last by move=> /eqP heq heq'; rewrite heq in heq'.
    move=> t ht <-; rewrite truncate_word_u /= heq1 hc /= => /xreg_of_varI.
    case: a heq1 hc => // r heq1 hc /of_varI /= h; subst x;
      (eexists; split; first reflexivity); constructor=> //=. 
    2-5, 7-10, 12-15: move => r' v'.
    1-15: rewrite /get_var/on_vu.
    1, 14, 15: rewrite Fv.setP_neq; first exact: hrip; by apply/eqP; case: hnrip.
    1: rewrite /RegMap.set ffunE; case: eqP.
       * move => ->{r'}; rewrite Fv.setP_eq => -[<-]{v'}.
         case: ht => <-{t}; case: Sumbool.sumbool_of_bool => hsz /=.
         + by apply word_uincl_word_extend.
         by rewrite word_extend_big // hsz.
       * move => hne; rewrite Fv.setP_neq; first exact: h2.
         by apply/eqP => /inj_to_var ?; apply: hne.
    1,2,3,4, 6-9, 11: rewrite Fv.setP_neq //.
    2, 4, 7, 9, 12, 14: rewrite eq_sym. 
    1: exact: h3.
    1: rewrite /to_var /= /rtype /=; apply /eqP; move=> []. apply nesym. 
       exact: inj_toS_reg_regx.
    1: apply /eqP. apply nesym. by apply to_var_reg_neq_xreg.
    1: rewrite /to_var /= /rtype /=; apply /eqP; move=> []. 
       exact: inj_toS_reg_regx.
    1: rewrite eq_sym; by apply /eqP /to_var_regx_neq_xreg.
    1: apply /eqP. by apply /to_var_reg_neq_xreg.
    1: by apply /eqP /to_var_regx_neq_xreg.
    1: exact: h4.
    1: exact: h5.
    1: exact: h2.
    1: exact: h4.
    1: exact: h5.
    1: exact: h2.
    1: exact: h3.
    1: exact: h5.
    1: rewrite /XRegMap.set ffunE; case: eqP. 
       + move => ->{r'}. rewrite Fv.setP_eq => -[<-]{v'}.
         case: ht => <-.
         case : Sumbool.sumbool_of_bool => /= hsz; first by apply word_uincl_word_extend.
         by rewrite word_extend_big // hsz.
       move => hne; rewrite Fv.setP_neq; first exact: h3.
       apply/eqP => /inj_to_var ?; exact: hne.
    rewrite /XRegMap.set ffunE; case: eqP.
    + move => ->{r'}; rewrite Fv.setP_eq => -[<-]{v'}.
      case: ht => <-.
      case : Sumbool.sumbool_of_bool => /= hsz; first by apply word_uincl_word_extend.
      by rewrite word_extend_big // hsz.
    move => hne; rewrite Fv.setP_neq; first exact: h4.
    apply/eqP => /inj_to_var ?; exact: hne. 
  move=> sz [x xii] /= e; t_xrbindP.
  move=> wp vp hget hp wofs vofs he hofs w hw m1 hm1 ??; subst m' e1.
  case: ty hty vt hw => //= sz' _ vt hw.
  case: eqP => // ?; subst sz'.
  move: hw; rewrite truncate_word_u => -[?]; subst vt.
  t_xrbindP => /= _ adr hadr ?; subst a => /=.
  rewrite /= heq1 hc /= /mem_write_mem -h1.
  have -> := addr_of_xpexprP hlom hadr hget hp he hofs.
  rewrite hm1 /=; eexists; split; first by reflexivity.
  by constructor.
Qed.

Lemma compile_lvals rip ii m lvs m' s loargs
  id_out id_tout (vt:sem_tuple id_tout) msb_flag:
  size id_out = size id_tout ->
  write_lvals [::] m lvs (list_ltuple vt) = ok m' ->
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
  have [e1 [es [he1 hes hce1 hces {h} /=]]]:
    exists e1 es,
      [/\ pexpr_of_lval ii lv1 = ok e1
        , mapM (pexpr_of_lval ii) lvs = ok es
        , check_sopn_dest agparams rip ii loargs e1 (ad, ty)
        & all2 (check_sopn_dest agparams rip ii loargs) es (zip ads tys)
      ].
  + by case: pexpr_of_lval h => //= e1; case: mapM => //= es /andP [] ??; exists e1, es.
  rewrite /mem_write_vals /=.
  have [s1 [-> /= h2]]:= compile_lval msb_flag hlo hca hw1 he1 hce1.
  apply: (hrec _  _ _ _ _ heqs hwn h2 _ hcall).
  by rewrite /check_sopn_dests hes.
Qed.

(* ------------------------------------------------------------------------ *)

Record h_asm_gen_params (agparams : asm_gen_params) :=
  {
    (* Calling [assemble_cond] and [eval_cond] must respect the semantics
       of the expression.
       That is, if [m] is a state, and [rf] a flag map with matching values,
       assembling and evaluating with [rf] is equivalent to computing the
       semantics with a [m]. *)
    hagp_eval_assemble_cond :
      forall ii m rf e c v,
        eqflags m rf
        -> agp_assemble_cond agparams ii e = ok c
        -> sem_pexpr [::] m e = ok v
        -> let
             get x := if rf x is Def b
                      then ok b
                      else undef_error
           in
           exists2 v',
             value_of_bool (eval_cond get c) = ok v' & value_uincl v v';

    (* Converting [extra_op]s into [asm_op]s, assembling them and evaluating
       must be equivalent to computing their semantics. *)
    hagp_assemble_extra_op :
      forall rip ii op lvs args op' lvs' args' op'' asm_args m m' s,
        sem_sopn [::] (Oasm (ExtOp op)) m lvs args = ok m'
        -> to_asm ii op lvs args = ok (op', lvs', args')
        -> assemble_asm_op agparams rip ii op' lvs' args'
           = ok (op'', asm_args)
        -> lom_eqv rip m s
        -> exists2 s', eval_op op'' asm_args s = ok s' & lom_eqv rip m' s';
  }.

Context
  (hagparams : h_asm_gen_params agparams).

Lemma compile_asm_opn rip ii (loargs : seq asm_arg) op m s args lvs m' :
  let id := instr_desc op in
  let csa := check_sopn_args agparams rip ii loargs args in
  let csd := check_sopn_dests agparams rip ii loargs lvs in
  sem_sopn [::] (Oasm (BaseOp op)) m lvs args = ok m'
  -> csa (zip (id_in id) (id_tin id))
  -> csd (zip (id_out id) (id_tout id))
  -> check_i_args_kinds (id_args_kinds id) loargs
  -> lom_eqv rip m s
  -> exists2 s', exec_instr_op id loargs s = ok s' & lom_eqv rip m' s'.
Proof.
  move=> id ; rewrite /sem_sopn /exec_sopn.
  t_xrbindP => x vs Hvs vt Hvt Htuplet Hm' Hargs Hdest Hid Hlomeqv.
  rewrite /exec_instr_op /eval_instr_op Hid /=.
  move: vt Hvt Htuplet; rewrite /sopn_sem /get_instr_desc /= -/id => {Hid}.
  case: id Hargs Hdest =>
    /= msb_flag id_tin id_in id_tout id_out id_semi id_args_kinds id_nargs
    /andP[] /eqP hsin /eqP hsout
    _ id_str_jas id_check_dest id_safe id_wsize id_pp
    Hargs Hdest vt happ ?;
    subst x.
  elim: id_in id_tin hsin id_semi args vs Hargs happ Hvs; rewrite /sem_prod.
  - move=> [] //= _ id_semi [|a1 args] [|v1 vs] //= _ -> _ /=.
    by apply: compile_lvals Hm' Hlomeqv Hdest id_check_dest.
  move=> a id_in hrec [] //= ty id_tin [] heqs id_semi [ | arg args] //=
    [ // | v vs];
    rewrite /check_sopn_args /= => /andP[] hcheck1 hcheckn.
  t_xrbindP => vt1 hvt happ v' hv vs' hvs ??; subst v' vs'.
  have [s'] := hrec _ heqs (id_semi vt1) _ _ hcheckn happ hvs.
  have [v' hev' hv'] :=
    check_sopn_arg_sem_eval
      (hagp_eval_assemble_cond hagparams)
      Hlomeqv
      hcheck1
      hv
      hvt.
  t_xrbindP => v1 v2 -> vt' /= happ1 ? hmw hlom; subst v1.
  by rewrite hev' /= hv' /= happ1 /=; eauto.
Qed.

Lemma app_sopn_apply_lprod T1 T2 tys (f : T1 -> T2) g vs :
  app_sopn tys (apply_lprod (rmap f) g) vs = rmap f (app_sopn tys g vs).
Proof. elim: tys vs g => [ | ty tys hrec] [ | v vs] //= g; case: of_val => //=. Qed.

(* TODO: move *)
Lemma zero_extend_comp sz sz' szo (v : word sz') :
  (sz' ≤ sz)%CMP ->
  zero_extend szo (zero_extend sz v) =
  zero_extend szo v.
Proof.
  move=> h; rewrite /zero_extend wunsigned_repr_small //.
  have := wbase_m h.
  have := wunsigned_range v; Psatz.lia.
Qed.

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
  + by rewrite /= /mem_write_reg !word_extend_CLEAR zero_extend_comp.
  case: onth => // -[] // r _; case: check_oreg => //=.
  + by rewrite /mem_write_reg !word_extend_CLEAR zero_extend_comp.
  + by rewrite /mem_write_regx !word_extend_CLEAR zero_extend_comp.
  by rewrite /mem_write_xreg !word_extend_CLEAR zero_extend_comp.
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

Lemma assemble_asm_opP rip ii op lvs args op' asm_args s m m' :
  sem_sopn [::] (Oasm (BaseOp op)) m lvs args = ok m' ->
  assemble_asm_op agparams rip ii op lvs args = ok (op', asm_args) ->
  lom_eqv rip m s ->
  exists2 s', eval_op op' asm_args s = ok s' & lom_eqv rip m' s'.
Proof.
  rewrite /assemble_asm_op /eval_op => hsem.
  t_xrbindP => asm_args' ? hc.
  case hci: enforce_imm_i_args_kinds =>
    {asm_args} [asm_args|//] _ [<-] /andP [hca hcd] <- <- hlo.
  have hidc := filter_i_args_kinds_no_imm_correct (enforce_imm_i_args_kinds_correct hci).
  have [s' he' hlo'] := compile_asm_opn hsem hca hcd hidc hlo.
  exists s'; last done.
  by rewrite -exec_desc_desc_op.
Qed.

Lemma assemble_sopnP rip ii op lvs args op' asm_args m m' s:
  sem_sopn [::] op m lvs args = ok m' ->
  assemble_sopn agparams rip ii op lvs args = ok (op', asm_args) ->
  lom_eqv rip m s ->
  exists2 s', eval_op op' asm_args s = ok s' & lom_eqv rip m' s'.
Proof.
  case: op => //=.
  case=> //=.
  + by move=> a; apply: assemble_asm_opP.
  t_xrbindP=> op hsem [[op'' lvs'] args'].
  by apply (hagp_assemble_extra_op hagparams).
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
  move=> /mapM_Forall2. elim => // { lc ac }.
  move=> li ai lc ac ok_ai _ ih.
  rewrite /label_in_lcmd -cat1s pmap_cat.
  rewrite /label_in_asm -(cat1s ai) pmap_cat.
  congr (_ ++ _); last exact: ih.
  by case: li ok_ai { ih } => ii [] /=; t_xrbindP => *; subst.
Qed.

Lemma assemble_fd_labels (fn : funname) (fd : lfundef) (fd' : asm_fundef) :
  assemble_fd agparams rip rsp fd = ok fd'
  -> [seq (fn, lbl) | lbl <- label_in_lcmd (lfd_body fd)]
     = [seq (fn, lbl) | lbl <- label_in_asm (asm_fd_body fd')].
Proof.
  case/assemble_fdI => _ _ [] c [] _ [] _ [] ok_c _ _ -> _ /=.
  by rewrite (assemble_c_labels ok_c).
Qed.

Lemma assemble_i_is_label (li : linstr) (ai : asm_i) lbl :
  assemble_i agparams rip li = ok ai
  -> linear.is_label lbl li = arch_sem.is_label lbl ai.
Proof.
  by (rewrite /assemble_i /linear.is_label ; case li =>  ii []; t_xrbindP)
    => /= [ > _ <- | > <- | <- | ? <- | ? <- | ? _ ? _ <- | > _ <- | > _ <-].
Qed.

Lemma assemble_c_find_is_label (lc : lcmd) (ac : asm_code) lbl :
  assemble_c agparams rip lc = ok ac
  -> find (linear.is_label lbl) lc = find (arch_sem.is_label lbl) ac.
Proof.
  rewrite /assemble_c.
  elim: lc ac.
  - by move => ac [<-].
  move => li lc ih i' /=; t_xrbindP=> ai ok_ai ac ok_ac <- {i'} /=.
  by rewrite (ih ac ok_ac) (assemble_i_is_label lbl ok_ai).
Qed.

Lemma assemble_c_find_label (lc : lcmd) (ac : asm_code) lbl :
  assemble_c agparams rip lc = ok ac
  -> linear.find_label lbl lc = arch_sem.find_label lbl ac.
Proof.
  rewrite /assemble_c /linear.find_label /arch_sem.find_label => ok_ac.
  by rewrite (size_mapM ok_ac) (assemble_c_find_is_label lbl ok_ac).
Qed.

(* -------------------------------------------------------------------- *)
(* Assembling machine words. *)

Lemma eval_assemble_word ii sz e a s xs v :
  lom_eqv rip s xs
  -> is_app1 e = None
  -> assemble_word_load rip ii sz e = ok a
  -> sem_pexpr [::] s e = ok v
  -> exists2 v',
       eval_asm_arg AK_mem xs a (sword sz) = ok v'
       & value_uincl v v'.
Proof.
  rewrite /assemble_word /eval_asm_arg => eqm.
  case: e => //=; t_xrbindP.
  - move=> x _ ok_x /xreg_of_varI h.
    rewrite /get_gvar ok_x => ok_v.
    case: a h => // r ok_r; eexists.
    + reflexivity.
    + exact: xgetreg_ex eqm ok_r ok_v.
    + reflexivity.
    + exact: xgetregx_ex eqm ok_r ok_v.
    + reflexivity.
    + exact: xxgetreg_ex eqm ok_r ok_v.
  move=> sz' ??;
    case: eqP => // <-{sz'};
    t_xrbindP=> _ _ d ok_d <- ptr w ok_w ok_ptr uptr u ok_u ok_uptr ? ok_rd ?;
    subst v => /=.
  case: (eqm) => _ eqmem _ _ _ _ _.
  rewrite (addr_of_xpexprP eqm ok_d ok_w ok_ptr ok_u ok_uptr) -eqmem ok_rd.
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
    , to_string ad_rsp = lp_rsp p
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
  exact: of_stringI ok_rsp.
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

Lemma lom_eqv_write_var f rip s xs (x : var_i) sz (w : word sz) s' r :
  lom_eqv rip s xs
  -> write_var x (Vword w) s = ok s'
  -> to_var r = x
  -> lom_eqv rip s' (mem_write_reg f r w xs).
Proof.
  case => eqscs eqm ok_rip [dr drx dx df] eqr eqrx eqx eqf.
  rewrite /mem_write_reg /write_var; t_xrbindP.
  case: s' => scs m _ vm ok_vm [] <- <- <- hx.
  constructor => //=.

  2-5: move=> r' v'.
  1-4: rewrite (get_var_set_var _ ok_vm) -hx.

  - by move: dr => /(_ r) /eqP /negbTE ->.

  - rewrite /RegMap.set ffunE.
    case: eqP => h; last first.
    + case: eqP => [ ? | _ ]; last exact: eqr.
      by elim h; congr to_var.
    move /inj_to_var : h => ->; rewrite eqxx; t_xrbindP => /= w' ok_w' <- /=.
    case: Sumbool.sumbool_of_bool ok_w' => hsz [] <-{w'} /=.
    + by apply word_uincl_word_extend.
    by rewrite word_extend_big // hsz.

  - by have /eqP/negbTE-> := to_var_reg_neq_regx (r := r) (x := r'); apply: eqrx.
  - by have /eqP/negbTE-> := to_var_reg_neq_xreg (r := r) (x := r'); apply: eqx.
 
  - by rewrite /= (get_set_var _ ok_vm) -hx /= => /eqf.
Qed.

Lemma value_of_bool_uincl (vb : value) (ve : exec bool) (b : bool) :
  to_bool vb = ok b
  -> (exists2 v', value_of_bool ve = ok v' & value_uincl vb v')
  -> ve = ok b.
Proof.
  move=> /to_boolI -> [v' + /value_uinclE ?]; subst.
  by case: ve => [? [->]| []].
Qed.

Variant match_state
  (rip : var) (ls : lstate) (lc : lcmd) (xs : asm_state) : Prop :=
| MS
  `(lom_eqv rip (to_estate ls) (asm_m xs))
  `(lfn ls = asm_f xs)
  `(assemble_c agparams rip lc = ok (asm_c xs))
  `(lpc ls = asm_ip xs).

(* FIXME move this *)
Lemma sv_of_list_cons (T:Type) (f: T->var) x xs:
  Sv.Equal (sv_of_list f (x :: xs)) (Sv.add (f x) (sv_of_list f xs)).
Proof.
  by move=> z; rewrite Sv.add_spec !(rwP (sv_of_listP _ _ _)) /= in_cons -(rwP orP) (rwP eqP).
Qed.

Lemma vrvs_to_lvals (l:seq reg_t) :
  Sv.Equal (vrvs (to_lvals (List.map to_var l))) (sv_of_list to_var l).
Proof.
  elim: l => //= r rs ih z; rewrite vrvs_cons /= ih sv_of_list_cons; clear.
  move: (to_var _) (sv_of_list _ _); SvD.fsetdec.
Qed.

Lemma get_var_eq_except vm1 vm2 x X :
   ~Sv.In x X ->
   vm1 = vm2 [\X] ->
   get_var vm1 x = get_var vm2 x.
Proof. by rewrite /get_var => hnin -> //. Qed.

Lemma get_lvar_to_lvals xs :
  mapM get_lvar (to_lvals xs) = ok xs.
Proof. by elim : xs => //= ?? ->. Qed.

(* END FIXME *)

Lemma reg_in_all (r:reg_t): Sv.In (to_var r) all_vars.
Proof.
  move: r; rewrite /reg_t => /= => r.
  rewrite /all_vars /= !Sv.union_spec; left.
  apply/sv_of_listP/(map_f (T1:= @ceqT_eqType _ _)).
  by rewrite mem_cenum.
Qed.

Lemma regx_in_all (r:regx_t): Sv.In (to_var r) all_vars.
Proof.
  move: r; rewrite /reg_t => /= => r.
  rewrite /all_vars /= !Sv.union_spec; right; left.
  apply/sv_of_listP /(map_f (T1:= @ceqT_eqType _ _)).
  by rewrite mem_cenum.
Qed.

Lemma xreg_in_all (r:xreg_t): Sv.In (to_var r) all_vars.
Proof.
  move: r; rewrite /xreg_t => /= => r.
  rewrite /all_vars /= !Sv.union_spec; right; right; left.
  apply/sv_of_listP /(map_f (T1:= @ceqT_eqType _ _)).
  by rewrite mem_cenum.
Qed.

Lemma flag_in_all (r:rflag_t): Sv.In (to_var r) all_vars.
Proof.
  move: r; rewrite /rflag_t => /= => r.
  rewrite /all_vars /= !Sv.union_spec; right; right; right.
  apply/sv_of_listP /(map_f (T1:= @ceqT_eqType _ _)).
  by rewrite mem_cenum.
Qed.

Lemma to_var_typed_reg r x : to_var r = var_of_asm_typed_reg x -> x = ARReg r.
Proof.
  case: x => //= r'.
  + by move=> /inj_to_var ->.
  + by move=> h; elim (to_var_reg_neq_regx h).
  by move=> h; elim (to_var_reg_neq_xreg h).
Qed.

Lemma to_var_typed_regx r x : to_var r = var_of_asm_typed_reg x -> x = ARegX r.
Proof.
  case: x => //= r'.
  + by move=> h; elim (to_var_reg_neq_regx (sym_eq h)).
  + by move=> /inj_to_var ->.
  by move=> h; elim (to_var_regx_neq_xreg h).
Qed.

Lemma to_var_typed_xreg r x : to_var r = var_of_asm_typed_reg x -> x = AXReg r.
Proof.
  case: x => //= r'.
  + by move=> h; elim (to_var_reg_neq_xreg (sym_eq h)).
  + by move=> h; elim (to_var_regx_neq_xreg (sym_eq h)).
  by move=> /inj_to_var ->.
Qed.

Lemma to_var_typed_flag r x : to_var r = var_of_asm_typed_reg x -> x = ABReg r.
Proof. by case: x => //= r' /inj_to_var ->. Qed.

Lemma assemble_iP i j ls ls' lc xs :
  ssrfun.omap lfd_body (get_fundef (lp_funcs p) (lfn ls)) = Some lc
  -> match_state rip ls lc xs
  -> assemble_i agparams rip i = ok j
  -> linear_sem.eval_instr p i ls = ok ls'
  -> exists2 xs',
       arch_sem.eval_instr p' j xs = ok xs'
       & exists2 lc',
           ssrfun.omap lfd_body (get_fundef (lp_funcs p) (lfn ls')) = Some lc'
           & match_state rip ls' lc' xs'.
Proof.
  move=> omap_lc.
  rewrite /linear_sem.eval_instr /arch_sem.eval_instr;
    case => eqm eqfn eqc eqpc.
  case: i => ii [] /=.
  - move=> lvs op pes;
      t_xrbindP => -[op' asm_args] hass <- m hsem ?;
      subst ls'.
    have [s -> eqm' /=] := assemble_sopnP hsem hass eqm.
    eexists; first reflexivity.
    eexists; first exact: omap_lc.
    by constructor => //=; rewrite ?to_estate_of_estate ?eqpc.
  - move=> o [<-]; t_xrbindP => ves hves [[scs m] vs] ho; t_xrbindP => s hw ?; subst ls'.
    case: (eqm) ho => /= -> -> _ _ _ _ _ _ ho.
    have [xs' hxs'] := (eval_syscall_spec2 ho); rewrite hxs' /=; eexists; first reflexivity.
    exists lc => //.
    have [hex hpr hrip] := eval_syscall_spec1 hxs'.
    move: hex; rewrite (exec_syscallPs_eq ho); last first.
    + move: hves => {vs hw ho}; elim: (take (size (syscall_sig_s o).(scs_tin)) call_reg_args) ves => [ | r rs ih] /= _vs.
      + by move=> [<-].
      t_xrbindP => v hv vs /ih ? <-; constructor => //.
      by case: eqm => _ _ _ _ /(_ _ _ hv).
    move=> [???]; subst scs m vs; split => //=; last by rewrite eqpc.
    rewrite to_estate_of_estate.
    case: eqm => /= hscs hmem hgetrip hdisjrip hreg hregx hxreg hflag.
    set R := vrvs (to_lvals (syscall_sig o).(scs_vout)).
    set X := Sv.union syscall_kill R.
    have heqx: evm s = lvm ls [\ X].
    + rewrite /X; apply: (vmap_eq_exceptT (vm2 := vm_after_syscall (lvm ls))).
      + apply: vmap_eq_exceptI; last by apply vmap_eq_exceptS; apply: vrvsP hw.
        by rewrite /=; SvD.fsetdec.
      apply: (vmap_eq_exceptI (s1:= syscall_kill)); first SvD.fsetdec.
      by move=> z /Sv_memP/negPf hz; rewrite /vm_after_syscall kill_varsE hz.
    have hinj : injective (to_var (T:= reg_t)) by move=> ??; apply: inj_to_var.
    have hres: forall r v, Sv.In (to_var r) R ->
             get_var (evm s) (to_var r) = ok v -> value_uincl v (Vword (asm_reg xs' r)).
    + move=> r v; rewrite /R vrvs_to_lvals => /sv_of_listP; rewrite mem_map //.
      assert (h := take_uniq (size (syscall_sig_s o).(scs_tout)) call_reg_ret_uniq).
      move: hw r v.
      elim: (take (size (syscall_sig_s o).(scs_tout)) call_reg_ret) {ho}
         {| evm := (vm_after_syscall (lvm ls)) |} h => //= r rs ih s1 /andP [hnin huniq].
      rewrite (sumbool_of_boolET (cmp_le_refl reg_size)) => hw r0 v.
      rewrite (in_cons (T:= @ceqT_eqType _ _)) => /orP []; last by apply: (ih _ huniq hw).
      move=> /eqP ?; subst r0; rewrite -(get_var_eq_except _ (vrvsP hw));last first.
      + rewrite vrvs_to_lvals => /sv_of_listP /(mapP (T1:= @ceqT_eqType _ _)) [r'] hr' /inj_to_var ?; subst r'.
        by rewrite hr' in hnin.
      rewrite /get_var /= Fv.setP_eq => -[] <-; apply value_uincl_refl.
    have hkill : forall x, Sv.In x syscall_kill -> ~Sv.In x R -> ~~is_sarr (vtype x) ->
      ~is_ok (get_var (evm s) x).
    + move=> x /Sv_memP hin hnin; rewrite -(get_var_eq_except _ (vrvsP hw)) //=.
      rewrite /get_var kill_varsE hin /on_vu; case: (vtype x) => //.
    constructor => //=.
    + by rewrite (write_lvals_escs hw).
    + by apply: write_lvals_emem hw; apply: get_lvar_to_lvals.
    + rewrite (get_var_eq_except _ heqx) // /X; first by rewrite hgetrip hrip.
      case: assemble_progP => -[] hripr hriprx hripxr hripf _ _ _.
      move=> /Sv.union_spec [] hin.
      + by have := SvP.MP.FM.diff_1 hin; rewrite /= /all_vars !Sv.union_spec => -[ | [ | []]] /sv_of_listP
          /(mapP (T1:= @ceqT_eqType _ _)) => -[r _ hr];
         [elim: (hripr r) | elim: (hriprx r) | elim: (hripxr r)| elim: (hripf r) ]; rewrite hr.
      move: hin; rewrite /R /= vrvs_to_lvals => /sv_of_listP /(mapP (T1:= @ceqT_eqType _ _)) [r _] hr.
      by elim: (hripr r); rewrite hr.
    + move=> r v.
      case: (Sv_memP (to_var r) R) => hinR; first by apply hres.
      case: (Sv_memP (to_var r) syscall_kill) => hinK heq.
      + by have /(_ erefl) := hkill _ hinK hinR; rewrite heq.
      move: (hinK); rewrite /syscall_kill => hnin.
      have : Sv.In (to_var r) one_varmap.callee_saved by have := reg_in_all r; SvD.fsetdec.
      rewrite /one_varmap.callee_saved /= => /sv_of_listP /mapP [x] /hpr.
      move=> h /to_var_typed_reg ?; subst x; rewrite -h; apply hreg.
      by rewrite -(get_var_eq_except _ heqx) // /X; SvD.fsetdec.
    + move=> r v heq.
      have hinR : ~Sv.In (to_var r) R.
      + rewrite /R /= vrvs_to_lvals => /sv_of_listP.
        by move=> /(mapP (T1 := @ceqT_eqType _ _)) [x _] /(@sym_eq var);apply: to_var_reg_neq_regx.
      case: (Sv_memP (to_var r) syscall_kill) => hinK.
      + by have /(_ erefl) := hkill _ hinK hinR; rewrite heq.
      move: (hinK); rewrite /syscall_kill => hnin.
      have : Sv.In (to_var r) one_varmap.callee_saved by have := regx_in_all r; SvD.fsetdec.
      rewrite /one_varmap.callee_saved /= => /sv_of_listP /mapP [x] /hpr.
      move=> h /to_var_typed_regx ?; subst x; rewrite -h; apply hregx.
      by rewrite -(get_var_eq_except _ heqx) // /X; SvD.fsetdec.
    + move=> r v heq.
      have hinR : ~Sv.In (to_var r) R.
      + rewrite /R /= vrvs_to_lvals => /sv_of_listP.
        by move=> /(mapP (T1 := @ceqT_eqType _ _)) [x _] /(@sym_eq var); apply: to_var_reg_neq_xreg.
      case: (Sv_memP (to_var r) syscall_kill) => hinK.
      + by have /(_ erefl) := hkill _ hinK hinR; rewrite heq.
      move: (hinK); rewrite /syscall_kill => hnin.
      have : Sv.In (to_var r) one_varmap.callee_saved by have := xreg_in_all r; SvD.fsetdec.
      rewrite /one_varmap.callee_saved /= => /sv_of_listP /mapP [x] /hpr.
      move=> h /to_var_typed_xreg ?; subst x; rewrite -h; apply hxreg.
      by rewrite -(get_var_eq_except _ heqx) // /X; SvD.fsetdec.
    + move=> r v.
      have hinR : ~Sv.In (to_var r) R.
      + rewrite /R /= vrvs_to_lvals => /sv_of_listP.
        by move=> /(mapP (T1 := @ceqT_eqType _ _)) [x _].
      have hnc: ~Sv.In (to_var r) one_varmap.callee_saved.
      + by rewrite /= => /sv_of_listP /mapP [] f /(allP callee_saved_not_bool) h /to_var_typed_flag ?; subst f.
      have hinK : Sv.In (to_var r) syscall_kill.
      + by rewrite /syscall_kill Sv.diff_spec;split => //; apply flag_in_all.
      have /(_ erefl) := hkill _ hinK hinR.
      rewrite /get_var /=.
      case: _.[_]%vmap => // - [] // _ /ok_inj <-.
      by case: (asm_flag _ _).
  - move=> [<-] [?]; subst ls'.
    eexists; first reflexivity.
    eexists; first eassumption.
    by constructor => //; rewrite /setpc eqpc.
  - move=> lbl [<-] [?]; subst ls'.
    eexists; first reflexivity.
    eexists; first eassumption.
    constructor => //.
    by rewrite /setpc /= eqpc.
  - case => fn lbl [<-] /=; t_xrbindP => body.
    case ok_fd: get_fundef => [ fd | // ] [ ] <-{body} pc ok_pc <-{ls'}.
    case/ok_get_fundef: (ok_fd) => fd' ->.
    case/assemble_fdI => rsp_not_in_args _ [] xc [] _ [] _ [] ok_xc _ _ ->{fd'} _ /=.
    rewrite -(assemble_c_find_label lbl ok_xc) ok_pc /=.
    rewrite ok_fd /=.
    do 2 (eexists; first reflexivity).
    by constructor.
  - t_xrbindP=> e /eqP ok_e d ok_d <- ptr v ok_v /to_wordI[? [? [? /word_uincl_truncate hptr]]]; subst.
    change reg_size with Uptr in ptr.
    have [v' -> /value_uinclE /=[? [? [-> /hptr /= ->]]]] := eval_assemble_word eqm ok_e ok_d ok_v.
    case ptr_eq: decode_label => [ [] fn lbl | // ] /=.
    replace (decode_label _ ptr) with (Some (fn, lbl));
      last by rewrite -assemble_prog_labels.
    rewrite /=.
    case get_fd: (get_fundef _) => [ fd | // ].
    have [fd' -> ] := ok_get_fundef get_fd.
    case/assemble_fdI => rsp_not_in_args _ [] xc [] _ [] _ [] ok_xc _ _ ->{fd'} _ /=.
    t_xrbindP => pc ok_pc <-{ls'}.
    rewrite -(assemble_c_find_label lbl ok_xc) ok_pc.
    rewrite get_fd /=.
    do 2 (eexists; first reflexivity).
    by constructor.
  - move => x lbl.
    case ok_r_x: (of_var x) => [r|//]; move /of_varI in ok_r_x.
    move=> /= [<-]{j}.
    rewrite eqfn.
    case ptr_eq: encode_label => [ ptr | ] //.
    replace (encode_label _ _) with (Some ptr);
      last by rewrite -assemble_prog_labels.

    t_xrbindP => vm ok_vm <-{ls'}.
    eexists; first reflexivity.
    rewrite /= -eqfn.
    exists lc; first exact: omap_lc.
    constructor => //=; last by congr _.+1.
    move: ok_r_x.
    change x with (v_var (VarI x xH)).
    apply: lom_eqv_write_var; first exact: eqm.
    by rewrite /write_var ok_vm.
  - t_xrbindP => cnd lbl cndt ok_c <- b v ok_v ok_b.
    case: eqm => eqscs eqm hrip hd eqr eqrx eqx eqf.
    have [v' ok_v' hvv'] := hagp_eval_assemble_cond hagparams eqf ok_c ok_v.
    case: v ok_v ok_b hvv' => // [ b' | [] // ] ok_b [?]; subst b'.
    rewrite /eval_Jcc.
    case: b ok_b => ok_b;
      case: v' ok_v' => // b ok_v' /= ?;
      subst b;
      rewrite /eval_cond_mem /=;
      case: (eval_cond _ _) ok_v' => // [ b | [] // ] [->] {b}.
    + t_xrbindP => lc'' ok_lc'' pc ok_pc ?; subst ls' => /=.
      move: omap_lc ok_lc''; rewrite /omap /obind /oapp => /=.
      rewrite /ssrfun.omap /ssrfun.obind /ssrfun.oapp.
      case: get_fundef => // lfu [->]  [?]; subst lc''; clear lfu.
      rewrite /eval_JMP -(assemble_c_find_label lbl eqc) ok_pc /=.
      do 2 (eexists; first reflexivity).
      by constructor.
    case => ?; subst ls' => /=.
    eexists; first reflexivity.
    exists lc; first exact: omap_lc.
    by constructor => //; rewrite /setpc /= eqpc.
Qed.

Lemma match_state_step ls ls' lc xs :
  ssrfun.omap lfd_body (get_fundef (lp_funcs p) (lfn ls)) = Some lc
  -> match_state rip ls lc xs
  -> step p ls = ok ls'
  -> exists2 xs',
       fetch_and_eval p' xs = ok xs'
       & exists2 lc',
           ssrfun.omap lfd_body (get_fundef (lp_funcs p) (lfn ls')) = Some lc'
           & match_state rip ls' lc' xs'.
Proof.
  move=> omap_lc.
  move=> ms;
    rewrite /step /find_instr /fetch_and_eval;
    case: (ms)=> _ _ eqc ->.
  case ok_fd: get_fundef omap_lc => [fd|] //= [?]; subst lc.
  case ok_i: (oseq.onth (lfd_body _) _) => [ i | // ].
  have [j [-> ok_j]] := mapM_onth eqc ok_i.
  apply: assemble_iP => //; last eassumption.
  by rewrite ok_fd.
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
    exists xs.
    exists lc.
    split => //.
    exact: rt_refl.

  move=> ls1 ls2 ls3 h1 h ih xs1 lc omap_lc m1.
  have [xs2 x [ lc' omap_lc' m2 ]] := match_state_step omap_lc m1 h1.
  have [xs3 [lc''] [y omap_lc'' m3]] := ih _ _ omap_lc' m2.
  exists xs3; exists lc''; split => //.
  apply: asmsem_trans; last by eauto.
  exact: rt_step.
Qed.

Lemma get_xreg_of_vars_uincl ii xs rs vm vs (rm : regmap) (rxm : regxmap) (xrm : xregmap) :
  (forall r v, get_var vm (to_var r) = ok v -> value_uincl v (Vword (rm r)))
  -> (forall r v, get_var vm (to_var r) = ok v -> value_uincl v (Vword (rxm r)))
  -> (forall r v, get_var vm (to_var r) = ok v -> value_uincl v (Vword (xrm r)))
  -> mapM (xreg_of_var ii) xs = ok rs
  -> mapM (λ x : var_i, get_var vm x) xs = ok vs
  -> let word_of_arg a := match a with
                          | Reg r => Vword (rm r)
                          | Regx r => Vword (rxm r) 
                          | XReg r => Vword (xrm r)
                          | _ => undef_w U64
                          end in
     List.Forall2 value_uincl vs (map word_of_arg rs).
Proof.
  move=> hr hrx hxr; elim: xs rs vs.
  - by move => _ _ [<-] [<-]; constructor.
  move=> x xs ih rs' vs' /=;
  t_xrbindP=> r /xreg_of_varI ok_r rs ok_rs <- {rs'} v ok_v vs ok_vs <- {vs'}.
  constructor; last exact: ih.
  case: r ok_r => // r => /of_varI rx.
  - by apply: hr; rewrite rx.
  - by apply: hrx; rewrite rx.
  by apply: hxr; rewrite rx.
Qed.


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
  rewrite ok_fd => /(_ _ s erefl) []; first by constructor.
  move=> [] xm' fn' c' pc' [] _ [] xexec /Some_inj <- [] /= M'.
  rewrite ok_c => ? /ok_inj ??; subst fn' c' pc'.
  exists xm'; last exact: M'.
  eexists; first exact: ok_fd'.
  - exact: export.
  - exact: ok_call_conv. 
  - rewrite /= -(size_mapM ok_c); exact: xexec.

  move=> r hr.
  assert (H: var_of_asm_typed_reg r \in map var_of_asm_typed_reg callee_saved).
  + by apply/in_map; exists r => //; apply/InP.
  move: H => {} hr.
  have /saved_registers E :
    Sv.In (var_of_asm_typed_reg r) (sv_of_list var_of_asm_typed_reg callee_saved).
  - by apply/sv_of_listP.
  case: M => /= _ _ _ _ Mr Mrx Mxr Mf.
  case: M' => /= _ _ _ _ Mr' Mrx' Mxr' Mf'.
  move/ok_vm: hr.
  case: r E => r /= E;
    [ move: (Mr' r) (Mr r) | move: (Mrx' r) (Mrx r) | move: (Mxr' r) (Mxr r) | move: (Mf' r) (Mf r) ];
    rewrite /get_var E.
  1-3: by case: _.[_]%vmap => [ | [] // ] /= [] sz w sz_le /(_ _ erefl) /= X' /(_ _ erefl) /= X;
       rewrite /truncate_word; case: ifP => // /(cmp_le_antisym sz_le) ? _; subst sz;
       rewrite -(word_uincl_eq X) -(word_uincl_eq X').
  case: _.[_]%vmap => [ | [] // ] /= b /(_ _ erefl) /= X' /(_ _ erefl) /= X _.
  case: (asm_flag xm' r) X' => //= _ <-.   
  by case: (asm_flag xm r) X => //= _ <-.
Qed.

Section VMAP_SET_VARS.

  Context {t : stype} {T: eqType} `{ToString t T}.
  Context (fromT: T -> exec (psem_t t)).

  Definition vmap_set_vars : vmap -> seq T -> vmap :=
    foldl (fun vm x => vm.[to_var x <- fromT x])%vmap.

  Definition is_ok_or_narr_undef x :=
    match fromT x with
    | Ok _ => true
    | Error ErrAddrUndef => if vtype (to_var x) is sarr _
                            then false
                            else true
    | Error _ => false
    end.

  Lemma wf_vmap_set_vars vm xs :
    wf_vm vm
    -> all is_ok_or_narr_undef xs
    -> wf_vm (vmap_set_vars vm xs).
  Proof.
    elim: xs vm => // x xs ih vm h /= /andP[] ok_x ok_xs;
      apply: ih ok_xs.
    move=> y; rewrite Fv.setP.
    case: eqP => ?; last exact: h.
    subst.
    rewrite /is_ok_or_narr_undef in ok_x.
    case: (fromT x) ok_x => // -[] //.
    by case: (vtype (to_var x)).
  Qed.

  Lemma get_var_vmap_set_vars_other vm xs y :
    all (fun x => to_var x != y) xs
    -> get_var (vmap_set_vars vm xs) y = get_var vm y.
  Proof.
    elim: xs vm => // x xs ih vm /= /andP[] x_neq_y /ih ->.
    apply: get_var_neq.
    exact/eqP.
  Qed.

  Lemma get_var_vmap_set_vars_other_type vm xs y :
    vtype y != t
    -> get_var (vmap_set_vars vm xs) y = get_var vm y.
  Proof.
    move=> /eqP neqt; apply: get_var_vmap_set_vars_other.
    by apply/allP => x _; apply/eqP => ?; subst y.
  Qed.

  Lemma get_var_vmap_set_vars_finite vm xs y :
    Finite.axiom xs
    -> get_var (vmap_set_vars vm xs) (to_var y)
       = on_vu (@pto_val t) undef_error (fromT y).
  Proof.
    move=> finT.
    move: vm.

    have {finT} : y \in xs.
    - by rewrite -has_pred1 has_count finT.

    elim: xs => // x xs; rewrite inE.
    case y_xs: (y \in xs).
    - move=> /(_ erefl) ih _ vm; exact: ih.
    rewrite orbF => _ /eqP <-{x} vm /=.
    rewrite get_var_vmap_set_vars_other; first exact: get_var_eq.
    apply/allP => x x_xs.
    apply/eqP => /inj_to_var ?.
    subst x.
    by rewrite x_xs in y_xs.
  Qed.

End VMAP_SET_VARS.

Lemma all_xpredT {A} (xs : seq A) : all xpredT xs.
Proof.
  elim: xs => [// | x xs IH].
  rewrite /all.
  apply/andP.
  split.
  + done.
  + exact: IH.
Qed.

Definition vmap_of_asm_mem
  (sp : word Uptr) (rip rsp : Ident.ident) (s : asmmem) : vmap :=
  let pword_of_reg  r  := ok (pword_of_word (asm_reg s r)) in
  let pword_of_regx rx := ok (pword_of_word (asm_regx s rx)) in
  let pword_of_xreg xr := ok (pword_of_word (asm_xreg s xr)) in
  let pbool_of_flag f  := if asm_flag s f is Def b
                          then ok b
                          else pundef_addr sbool in
  let vm := vmap0.[mk_ptr rsp <- ok (pword_of_word sp)]
                 .[mk_ptr rip <- ok (pword_of_word (asm_rip s))]%vmap in
  let vm := vmap_set_vars (t := sword _) pword_of_reg vm registers in
  let vm := vmap_set_vars (t := sword _) pword_of_regx vm registerxs in
  let vm := vmap_set_vars (t := sword _) pword_of_xreg vm xregisters in
  let vm := vmap_set_vars (t := sbool) pbool_of_flag vm rflags in
  vm.

Lemma wf_vmap_of_asm_mem sp rip rsp s :
  wf_vm (vmap_of_asm_mem sp rip rsp s).
Proof.
  repeat apply: wf_vmap_set_vars.
  1-5: rewrite /is_ok_or_narr_undef /=.

  - repeat apply: wf_vm_set. exact: wf_vmap0.
  - exact: all_xpredT.
  - exact: all_xpredT.
  - exact: all_xpredT.
  - elim: rflags => // r rflags IH.
    apply/andP.
    split.
    + by case: (asm_flag _ _).
    + exact: IH.
Qed.

Definition get_typed_reg_value (st : asmmem) (r : asm_typed_reg) : exec value :=
  match r with
  | ARReg r => ok (Vword (asm_reg  st r))
  | ARegX r => ok (Vword (asm_regx st r))
  | AXReg r => ok (Vword (asm_xreg st r))
  | ABReg r => if asm_flag st r is Def b
               then ok (Vbool b)
               else undef_error
  end.

Definition get_typed_reg_values st rs : exec values :=
  mapM (get_typed_reg_value st) rs.

Lemma get_var_vmap_of_asm_mem sp rip rsp s (r : asm_typed_reg) :
  get_var (vmap_of_asm_mem sp rip rsp s) (var_of_asm_typed_reg r)
  = get_typed_reg_value s r.
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
  by rewrite get_var_vmap_set_vars_finite //=; [case: (asm_flag s r) | exact: cenumP].
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
    by rewrite get_var_eq.
  - move => r v.
    by rewrite (get_var_vmap_of_asm_mem _ _ _ _ (ARReg r)) => /= /ok_inj <-.
  - move => r v.
    by rewrite (get_var_vmap_of_asm_mem _ _ _ _ (ARegX r)) => /= /ok_inj <-.
  - move => r v.
    by rewrite (get_var_vmap_of_asm_mem _ _ _ _ (AXReg r)) => /= /ok_inj <-.
  move => r v.
  rewrite /= /vmap_of_asm_mem.
  set q := (X in vmap_set_vars _ X).
  set pbool_of_flag := fun f => if asm_flag s f is Def b
                                then ok b
                                else pundef_addr sbool.
  generalize
    (get_var_vmap_set_vars_finite (t := sbool) pbool_of_flag q r cenumP).
  rewrite get_varE.
  rewrite /pbool_of_flag.
  case: _.[_]%vmap => /=;
    case: (asm_flag s r) => //=.
  - by move => ? ? /ok_inj -> /ok_inj ->.
  by move => _ [] -> /ok_inj ->.
Qed.

End PROG.
End ASM_EXTRA.
