From mathcomp Require Import all_ssreflect all_algebra.
Require Import oseq compiler_util psem lea_proof arch_decl arch_extra arch_sem.
Require Export asm_gen.
Import Utf8.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section ASM_EXTRA.

Context `{asm_e : asm_extra}.

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
         emem m = asm_mem lom
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
Proof. case => _ _ _ eqv _ _ _ /of_varI <-; exact: eqv. Qed.

(* -------------------------------------------------------------------- *)
Lemma xgetregx_ex rip x r v s xs :
  lom_eqv rip s xs →
  of_var x = Some r →
  get_var s.(evm) x = ok v →
  value_uincl v (Vword (xs.(asm_regx) r)).
Proof. case => _ _ _ eqv eqv' eqv'' _ /of_varI <-;exact: eqv'. Qed.

(* -------------------------------------------------------------------- *)
Lemma xxgetreg_ex rip x r v s xs :
  lom_eqv rip s xs →
  of_var x = Some r →
  get_var (evm s) x = ok v →
  value_uincl v (Vword (asm_xreg xs r)).
Proof. by case => _ _ _ _ _ eqv _  /of_varI <-; exact: eqv. Qed.

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

Context (assemble_cond : instr_info -> pexpr -> cexec cond_t).
Hypothesis eval_assemble_cond : forall ii m rf e c v,
  eqflags m rf →
  assemble_cond ii e = ok c →
  sem_pexpr [::] m e = ok v →
  let get x :=
    if rf x is Def b then ok b else undef_error in
  ∃ v', value_of_bool (eval_cond get c) = ok v' ∧ value_uincl v v'.

(* -------------------------------------------------------------------- *)
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
  move=> hsz64 hsz [_ _ _ hget _ _ _] hsem; rewrite /assemble_lea.
  t_xrbindP => ob hob oo hoo sc hsc <- /=.
  rewrite /decode_reg_addr /=.  
  move: hsem; rewrite /sem_lea.
  apply rbindP => wb hwb; apply rbindP => wo hwo heq.
  have <- := ok_inj heq.
  rewrite !(wadd_zero_extend, wmul_zero_extend) // GRing.addrA; do 2 f_equal.
  + case: lea_base hob hwb => /= [vo | [<-] [<-] /=]; last by apply zero_extend0.
    t_xrbindP => r /of_var_eI <- <- v /hget hv /=.
    move=> /(value_uincl_word hv) -/to_wordI [sz1 [w1 [hsz1]]] /Vword_inj [?];subst sz1.
    by move=> /= <- ->.
  + by rewrite (xscale_ok hsc).
  case: lea_offset hoo hwo => /= [vo | [<-] [<-] /=]; last by apply zero_extend0.
  t_xrbindP => r /of_var_eI <- <- v /hget hv /=.
  move=> /(value_uincl_word hv) -/to_wordI [sz1 [w1 [hsz1]]] /Vword_inj [?];subst sz1.
  by move=> /= <- ->.
Qed.

Lemma addr_of_pexprP rip ii sz sz' (w:word sz') e adr m s:
  (sz ≤ sz')%CMP →
  lom_eqv rip m s →
  sem_pexpr [::] m e = ok (Vword w) ->
  addr_of_pexpr rip ii sz e = ok adr ->
  zero_extend sz (decode_addr s adr) = zero_extend sz w.
Proof.
  rewrite /addr_of_pexpr => hsz lom he.
  t_xrbindP => _ /assertP hsz64.
  case heq: mk_lea => [lea | //].
  assert (hsemlea:=
     mk_leaP (p:= (Build_prog (pT := progUnit) [::] [::] tt)) hsz64 hsz heq he).
  case hb: lea_base => [b | ]; last by apply (assemble_leaP hsz64 hsz lom hsemlea).
  case: eqP => [ | _]; last by apply (assemble_leaP hsz64 hsz lom hsemlea).
  t_xrbindP => hbrip _ /assertP /eqP ho <- /=.
  case: lom => _ hrip _ _ _.
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
    -> arg_of_pexpr assemble_cond k rip ii ty e = ok a'
    -> compat_imm ty a a'
    -> check_oreg o a
    -> check_sopn_argI rip ii args e (ADExplicit k n o) ty.

Lemma check_sopn_argP rip ii args e sp :
  check_sopn_arg assemble_cond rip ii args e sp ->
  check_sopn_argI rip ii args e sp.1 sp.2.
Proof.
case: sp => -[i|k n o] ty; first by apply: CSA_Implicit.
rewrite /check_sopn_arg /=; case Enth: onth => [a|] //.
case E: arg_of_pexpr => [a'|] // /andP[??].
by apply: (CSA_Explicit (a := a) (a' := a')).
Qed.

Lemma var_of_flagP rip m s f v ty vt: 
  lom_eqv rip m s → 
  get_var (evm m) (to_var f) = ok v →
  of_val ty v = ok vt → 
  ∃ v' : value, Let b := st_get_rflag s f in ok (Vbool b) = ok v' ∧ of_val ty v' = ok vt.
Proof.
  move=> [_ _ _ _ _ _ h].
  rewrite get_varE; t_xrbindP => /= b ok_b <-{v} /of_vbool[] ??; subst.
  move: (h f b); rewrite ok_b => /(_ erefl).
  rewrite /st_get_rflag.
  by case: (asm_flag s f) => // _ <-; exists b.
Qed.

Lemma var_of_regP rip E m s r v ty vt:
  lom_eqv rip m s → 
  get_var (evm m) (to_var r) = ok v → 
  of_val ty v = ok vt → 
  ∃ v' : value, Ok E (Vword ((asm_reg s) r)) = ok v' ∧ of_val ty v' = ok vt.
Proof. move=> [??? h ???] /h -/value_uincl_word_of_val h1 /h1;eauto. Qed.

Lemma check_sopn_arg_sem_eval rip m s ii args e ad ty v vt:
     lom_eqv rip m s
  -> check_sopn_arg assemble_cond rip ii args e (ad,ty)
  -> sem_pexpr [::] m e = ok v
  -> of_val ty v = ok vt 
  -> exists v', eval_arg_in_v s args ad ty = ok v' /\ 
     of_val ty v' = ok vt.
Proof.
  move=> eqm /check_sopn_argP /= h.
  case: h vt.
  + move=> i {ty} ty /eq_exprP -> vt /=.
    case: i => /= [f | r]; first by apply: var_of_flagP eqm. 
    by apply: var_of_regP eqm.
  move=> k n o a a' [ | | | ws] //= ->.
  + t_xrbindP => c hac <-.
    rewrite /compat_imm orbF => /eqP <- -> /= b hb.
    case: eqm => ?????? eqf.
    have [v']:= eval_assemble_cond eqf hac hb.
    rewrite /eval_cond_mem.
    case: eval_cond => /= [ | [] [] // [] <- /value_uincl_undef [ty1 [he ->]] ]; last by case: ty1 he.
    move=> b' [[<-]] {hb}; case: v => // [b1 | [] //] -> ?.
    by exists b'.
  move=> haw hcomp -> /=.
  case: k haw => /=.
  + t_xrbindP => adr hadr ? w he /to_wordI [ws' [w' [hws ??]]]; subst a' v w.
    move: hcomp; rewrite /compat_imm orbF => /eqP ?; subst a => /=.
    rewrite (addr_of_pexprP hws eqm he hadr); eexists; split; first reflexivity.
    by rewrite /= truncate_word_u.
  case: e => //=.
  + rewrite /get_gvar /eval_asm_arg => x; t_xrbindP => _ /assertP => ->.
    case: eqm => _ _ _ eqr eqrx eqx _.
    move=> /xreg_of_varI; case: a' hcomp => // r; rewrite /compat_imm orbF => /eqP <- {a} xr w ok_v ok_w;
    (eexists; split; first reflexivity);
    apply: (value_uincl_word _ ok_w).
    + by apply: eqr; rewrite (of_varI xr). 
    + by apply: eqrx; rewrite (of_varI xr). 
    by apply: eqx; rewrite (of_varI xr).
  + move=> sz x p; t_xrbindP => _ /assertP /eqP <- r hr ?; subst a'.
    move: hcomp; rewrite /compat_imm orbF => /eqP <-.
    move=> w1 wp vp hget htop wp' vp' hp hp' wr hwr <- /= htr.
    have -> := addr_of_xpexprP eqm hr hget htop hp hp'.
    by case: eqm => <- ?????; rewrite hwr /=; eauto.
  case => //= w' [] //= z.
  t_xrbindP => _ /assertP /eqP _ h; move: hcomp; rewrite -h /compat_imm /eval_asm_arg => -/orP [/eqP <- | ].
  + move=> w [] <- /truncate_wordP [hsz ->].
    eexists; split; first reflexivity.
    by rewrite /to_word truncate_word_u sign_extend_truncate.
  case: a => // sz' w2 /eqP heq2 w [] <- /truncate_wordP [hsz ->].
  eexists; split; first reflexivity.
  rewrite -heq2.
  by rewrite /to_word truncate_word_u sign_extend_truncate.
Qed.


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

(* TODO: move in a class? *)
Hypothesis reg_size_lt_xreg_size : (reg_size < xreg_size)%CMP. 

Lemma of_reg_neq_of_xreg (r:reg_t) (x:xreg_t) : to_var r <> to_var x.
Proof.
  move=> [] hsize _.
  by move: reg_size_lt_xreg_size; rewrite hsize -cmp_nle_lt cmp_le_refl.
Qed.

Lemma of_reg_neq_of_regx (r:reg_t) (x:regx_t) : to_var r <> to_var x.
Proof.
Admitted.

Lemma compile_lval rip ii msb_flag loargs ad ty (vt:sem_ot ty) m m' s lv1 e1:
  lom_eqv rip m s ->
  check_arg_dest ad ty ->
  write_lval [::] lv1 (oto_val vt) m = ok m' ->
  pexpr_of_lval ii lv1 = ok e1 ->
  check_sopn_dest assemble_cond rip ii loargs e1 (ad, ty) ->
  exists s', mem_write_val msb_flag loargs (ad, ty) (oto_val vt) s = ok s' /\ lom_eqv rip m' s'.
Proof.
  move=> hlom; case:(hlom) => [h1 hrip hnrip h2 h3 h4 h5]; case: ad => [ai _ | k n o]; rewrite /check_sopn_dest /=.
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
    + by case:hlom => ? hget hd _ _ _;rewrite /get_var Fv.setP_neq //; apply /eqP;case: hd.      
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
    + by case:hlom => ? hget hd _ _ _ _;rewrite /get_var Fv.setP_neq //; apply /eqP;case: hd.
    + move=> r' v'; rewrite /get_var /on_vu /= /RegMap.set ffunE.
      case: eqP => [-> | hne].
      + rewrite Fv.setP_eq => -[<-] /=.
        case : Sumbool.sumbool_of_bool => /= hsz; first by apply word_uincl_word_extend.
        by rewrite word_extend_big // hsz.
      rewrite Fv.setP_neq; last by apply /eqP => h; apply hne; apply inj_to_var.
      by apply h2.
    + move=> r' v'; rewrite get_var_neq; last by apply of_reg_neq_of_regx.
      by apply h3.
    + move=> r' v'; rewrite get_var_neq; last by apply of_reg_neq_of_xreg.
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
    move=> /= t ht <-; rewrite truncate_word_u /= heq1 hc /= => /xreg_of_varI.
    case: a heq1 hc => // r heq1 hc /of_varI /= h; subst x;
      (eexists; split; first reflexivity); constructor=> //=. 
    2-4, 7-9, 12-15: move => r' v'.
    1-15: rewrite /get_var/on_vu.
    1, 13, 15: rewrite Fv.setP_neq; first exact: hrip; by apply/eqP; case: hnrip.
    (*1, 5, 9:*)
    1: rewrite /RegMap.set ffunE; case: eqP.
       * move => ->{r'}; rewrite Fv.setP_eq => -[<-]{v'}.
         case: ht => <-{t}; case: Sumbool.sumbool_of_bool => hsz /=.
         + by apply word_uincl_word_extend.
         by rewrite word_extend_big // hsz.
       * move => hne; rewrite Fv.setP_neq; first exact: h2.
         by apply/eqP => /inj_to_var ?; apply: hne.
    1-3, 5-8: rewrite Fv.setP_neq //.
    2, 4, 6, 8, 10, 12, 14: rewrite eq_sym.
    6: by apply /eqP /of_reg_neq_of_xreg.
    2, 3, 4, 5, 6, 7: admit.
    1, 6 : exact: h3.
    1, 3: exact: h4.
    1, 2: exact: h2.
    + admit.
    + rewrite /XRegMap.set ffunE; case: eqP.
      + move => ->{r'}; rewrite Fv.setP_eq => -[<-]{v'}.
        case: ht => <-.
        case : Sumbool.sumbool_of_bool => /= hsz; first by apply word_uincl_word_extend.
      by rewrite word_extend_big // hsz.
    + move => hne; rewrite Fv.setP_neq; first exact: h3.
      apply/eqP => /inj_to_var ?; exact: hne.
    + rewrite Fv.setP_neq //. by exact: h5.
    + move => r' v'. rewrite Fv.setP_neq //. by exact: h5.
    move => r' v'. rewrite Fv.setP_neq //. by exact: h5. 
   move=> sz [x xii] /= e; t_xrbindP.
  move=> wp vp hget hp wofs vofs he hofs w hw m1 hm1 ??; subst m' e1.
  case: ty hty vt hw => //= sz' _ vt hw.
  case: eqP => // ?; subst sz'.
  move: hw; rewrite truncate_word_u => -[?]; subst vt.
  t_xrbindP => /= _ _ adr hadr ?; subst a => /=.
  rewrite /= heq1 hc /= /mem_write_mem -h1.
  have -> := addr_of_xpexprP hlom hadr hget hp he hofs.
  rewrite hm1 /=; eexists; split; first by reflexivity.
  by constructor.
Admitted.

Lemma compile_lvals rip ii m lvs m' s loargs 
  id_out id_tout (vt:sem_tuple id_tout) msb_flag: 
  size id_out = size id_tout -> 
  write_lvals [::] m lvs (list_ltuple vt) = ok m' ->
  lom_eqv rip m s ->
  check_sopn_dests assemble_cond rip ii loargs lvs (zip id_out id_tout) ->
  all2 check_arg_dest id_out id_tout ->
  exists s', 
    mem_write_vals msb_flag s loargs id_out id_tout (list_ltuple vt) = ok s' ∧ lom_eqv rip m' s'.
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
    exists e1 es, [/\ pexpr_of_lval ii lv1 = ok e1, mapM (pexpr_of_lval ii) lvs = ok es,
                           check_sopn_dest assemble_cond rip ii loargs e1 (ad, ty) &
                           all2 (check_sopn_dest assemble_cond rip ii loargs) es (zip ads tys)].
  + by case: pexpr_of_lval h => //= e1; case: mapM => //= es /andP [] ??; exists e1, es. 
  rewrite /mem_write_vals /=.
  have [s1 [-> /= h2]]:= compile_lval msb_flag hlo hca hw1 he1 hce1.
  apply: (hrec _  _ _ _ _ heqs hwn h2 _ hcall).
  by rewrite /check_sopn_dests hes.
Qed.

Lemma compile_x86_opn rip ii (loargs : seq asm_arg) op m s args lvs m' :
let id := instr_desc op in
sem_sopn [::] (Oasm (BaseOp op)) m lvs args = ok m' ->
check_sopn_args assemble_cond rip ii loargs args (zip id.(id_in) id.(id_tin)) ->
check_sopn_dests assemble_cond rip ii loargs lvs (zip id.(id_out) id.(id_tout)) ->
check_i_args_kinds id.(id_args_kinds) loargs ->
lom_eqv rip m s ->
exists s', exec_instr_op id loargs s = ok s' /\ lom_eqv rip m' s'.
Proof.
move=> id ; rewrite /sem_sopn /exec_sopn.
t_xrbindP => x vs Hvs vt Hvt Htuplet Hm' Hargs Hdest Hid Hlomeqv.
rewrite /exec_instr_op /eval_instr_op Hid /=.
move: vt Hvt Htuplet; rewrite /sopn_sem /get_instr_desc /= -/id => {Hid}.
case: id Hargs Hdest => /= msb_flag id_tin 
 id_in id_tout id_out id_semi id_args_kinds id_nargs /andP[] /eqP hsin /eqP hsout
 _ id_str_jas id_check_dest id_safe id_wsize id_pp Hargs Hdest vt happ ?;subst x.
elim: id_in id_tin hsin id_semi args vs Hargs happ Hvs; rewrite /sem_prod.
+ move=> [] //= _ id_semi [|a1 args] [|v1 vs] //= _ -> _ /=.
  by apply: compile_lvals Hm' Hlomeqv Hdest id_check_dest.
move=> a id_in hrec [] //= ty id_tin [] heqs id_semi [ | arg args] //=
  [ // | v vs]; rewrite /check_sopn_args /= => /andP[] hcheck1 hcheckn.
t_xrbindP => vt1 hvt happ v' hv vs' hvs ??; subst v' vs'.
have [s' [] ]:= hrec _ heqs (id_semi vt1) _ _ hcheckn happ hvs. 
have [v' [hev' hv']]:= check_sopn_arg_sem_eval Hlomeqv hcheck1 hv hvt.
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
  assemble_asm_op assemble_cond rip ii op lvs args = ok (op', asm_args) ->
  lom_eqv rip m s ->
  exists s', eval_op op' asm_args s = ok s' /\ lom_eqv rip m' s'.
Proof.
  rewrite /assemble_asm_op /eval_op => hsem.
  t_xrbindP => asm_args' ? _ /assertP hc.
  case hci: enforce_imm_i_args_kinds =>
    {asm_args} [asm_args|//] _ [<-] _ /assertP /andP [hca hcd] <- <- hlo.
  have hidc := filter_i_args_kinds_no_imm_correct (enforce_imm_i_args_kinds_correct hci).
  have [s' [he' hlo']]:= compile_x86_opn hsem hca hcd hidc hlo.
  by exists s'; split => //; rewrite -exec_desc_desc_op.
Qed.

Hypothesis assemble_extra_op :
  forall rip ii op lvs args op' lvs' args' op'' asm_args m m' s,
    sem_sopn [::] (Oasm (ExtOp op)) m lvs args = ok m' ->
    to_asm ii op lvs args = ok (op', lvs', args') ->
    assemble_asm_op assemble_cond rip ii op' lvs' args' = ok (op'', asm_args) ->
    lom_eqv rip m s ->
    exists s', eval_op op'' asm_args s = ok s' /\ lom_eqv rip m' s'.

Lemma assemble_sopnP rip ii op lvs args op' asm_args m m' s: 
  sem_sopn [::] op m lvs args = ok m' ->
  assemble_sopn assemble_cond rip ii op lvs args = ok (op', asm_args) ->
  lom_eqv rip m s ->
  exists s', eval_op op' asm_args s = ok s' /\ lom_eqv rip m' s'.
Proof.
  case: op => //=.
  case=> //=.
  + by move=> a; apply: assemble_asm_opP.
  t_xrbindP=> op hsem [[op'' lvs'] args'].
  by apply assemble_extra_op.
Qed.

End ASM_EXTRA.
