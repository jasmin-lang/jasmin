From mathcomp Require Import all_ssreflect all_algebra.
Require Import low_memory psem x86_sem compiler_util lowering lowering_proof.
Require Import x86_variables_proofs.
Import Utf8.
Import oseq x86_variables.
Import GRing.
Require Import ssrring.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition pexpr_of_lval ii (lv:lval) : ciexec pexpr :=
  match lv with
  | Lvar x    => ok (Pvar x)
  | Lmem s x e  => ok (Pload s x e)
  | Lnone _ _
  | Laset _ _ _ => cierror ii (Cerr_assembler (AsmErr_string "pexpr_of_lval"))
  end.

Definition nmap (T:Type) := nat -> option T.
Definition nget (T:Type) (m:nmap T) (n:nat) := m n.
Definition nset (T:Type) (m:nmap T) (n:nat) (t:T) :=
  fun x => if x == n then Some t else nget m x.
Definition nempty (T:Type) := fun n:nat => @None T.

Definition var_of_implicit i :=
  match i with
  | IArflag f => var_of_flag f
  | IAreg r   => var_of_register r
  end.

Definition compile_arg ii max_imm (ade: (arg_desc * stype) * pexpr) (m: nmap asm_arg) : ciexec (nmap asm_arg) :=
  let ad := ade.1 in
  let e := ade.2 in
  match ad.1 with
  | ADImplicit i =>
    Let _ :=
      assert (eq_expr (Pvar (VarI (var_of_implicit i) xH)) e)
             (ii, Cerr_assembler (AsmErr_string "compile_arg : bad implicit")) in
    ok m
  | ADExplicit n o =>
    Let a := arg_of_pexpr ii ad.2 max_imm e in
    Let _ :=
      assert (check_oreg o a)
             (ii, Cerr_assembler (AsmErr_string "compile_arg : bad forced register")) in                 
    match nget m n with
    | None => ok (nset m n a)
    | Some a' =>
      if a == a' then ok m
      else cierror ii (Cerr_assembler (AsmErr_string "compile_arg : not compatible asm_arg"))
    end
  end.

Definition compile_args ii max_imm adts (es:pexprs) (m: nmap asm_arg) :=
  foldM (compile_arg ii max_imm) m (zip adts es).

Definition compat_imm ty a' a := 
  (a == a') || match ty, a, a' with
             | sword sz, Imm sz1 w1, Imm sz2 w2 => sign_extend sz w1 == sign_extend sz w2
             | _, _, _ => false
             end.
                
Definition check_sopn_arg ii max_imm (loargs : seq asm_arg) (x : pexpr) (adt : arg_desc * stype) :=
  match adt.1 with
  | ADImplicit i => eq_expr x (Pvar (VarI (var_of_implicit i) xH))
  | ADExplicit n o =>
    match onth loargs n with
    | Some a =>
      if arg_of_pexpr ii adt.2 max_imm x is Ok a' then compat_imm adt.2 a a' && check_oreg o a
      else false
    | None => false
    end
  end.

Definition check_sopn_dest ii max_imm (loargs : seq asm_arg) (x : pexpr) (adt : arg_desc * stype) :=
  match adt.1 with
  | ADImplicit i => eq_expr x (Pvar (VarI (var_of_implicit i) xH))
  | ADExplicit n o =>
    match onth loargs n with
    | Some a =>
      if arg_of_pexpr ii adt.2 max_imm x is Ok a' then (a == a') && check_oreg o a
      else false
    | None => false
    end
  end.

Definition error_imm := 
 Cerr_assembler (AsmErr_string "Invalid asm: cannot truncate the immediate to a 32 bits immediate, move it to a register first").

Definition assemble_x86_opn_aux ii op (outx : lvals) (inx : pexprs) :=
  let id := instr_desc op in
  let max_imm := id.(id_max_imm) in
  Let m := compile_args ii max_imm (zip id.(id_in) id.(id_tin)) inx (nempty _) in
  Let eoutx := mapM (pexpr_of_lval ii) outx in
  Let m := compile_args ii max_imm (zip id.(id_out) id.(id_tout)) eoutx m in
  match oseq.omap (nget m) (iota 0 id.(id_nargs)) with
  | None => cierror ii (Cerr_assembler (AsmErr_string "compile_arg : assert false nget"))
  | Some asm_args =>
      (* This should allows to fix the problem with "MOV addr (IMM U64 w)" *)
      Let asm_args := 
        match op, asm_args with
        | MOV U64, [:: Adr a; Imm U64 w] =>
          match truncate_word U32 w with
          | Ok w' => 
            Let _ := assert (sign_extend U64 w' == w) (ii, error_imm) in
            ok [::Adr a; Imm w']
          | _ => cierror ii error_imm 
          end
        | _, _ => ok asm_args 
        end in
      ok asm_args
  end.

Definition check_sopn_args ii max_imm (loargs : seq asm_arg) (xs : seq pexpr) (adt : seq (arg_desc * stype)) :=
  all2 (check_sopn_arg ii max_imm loargs) xs adt.

Definition check_sopn_dests ii max_imm (loargs : seq asm_arg) (outx : seq lval) (adt : seq (arg_desc * stype)) :=
  match mapM (pexpr_of_lval ii) outx with
  | Ok eoutx => all2 (check_sopn_dest ii max_imm loargs) eoutx adt
  | _  => false
  end.

Definition is_lea ii op (outx : lvals) (inx : pexprs) := 
  match op, outx, inx with
  | LEA sz, [:: Lvar x], [:: e] => 
    match lowering.mk_lea sz e with
    | Some lea => ok (Some (sz, x, lea))
    | None => cierror ii (Cerr_assembler (AsmErr_string "lea: not able to assemble address"))
    end
  | LEA _, _, _ => cierror ii (Cerr_assembler (AsmErr_string "lea: invalid lea instruction"))
  | _, _, _ => ok None
  end.

Definition reg_of_ovar ii (x:option var_i) := 
  match x with 
  | Some x => 
    Let r := reg_of_var ii x in
    ok (Some r)
  | None =>
    ok None
  end.

Definition assemble_x86_opn ii op (outx : lvals) (inx : pexprs) := 
  Let is_lea := is_lea ii op outx inx in
  match is_lea with
  | Some (sz, x, lea) =>
    Let r := reg_of_var ii x.(v_var) in
    Let base := reg_of_ovar ii lea.(lea_base) in
    Let offset := reg_of_ovar ii lea.(lea_offset) in
    Let scale := scale_of_z' ii lea.(lea_scale) in
    let adr := {|
      ad_disp := lea.(lea_disp);
      ad_base := base;
      ad_scale := scale;
      ad_offset := offset 
    |} in
    ok (LEA sz, [::Reg r; Adr adr])

  | None =>
    let id := instr_desc op in
    let max_imm := id.(id_max_imm) in
    Let asm_args := assemble_x86_opn_aux ii op outx inx in
    let s := id.(id_str_jas) tt in
    Let _ := assert (id_check id asm_args) 
       (ii, Cerr_assembler (AsmErr_string ("assemble_x86_opn : invalid instruction (check) " ++ s))) in 
    Let _ := assert (check_sopn_args ii max_imm asm_args inx (zip id.(id_in) id.(id_tin)) &&
                     check_sopn_dests ii max_imm asm_args outx (zip id.(id_out) id.(id_tout)))
       (ii, Cerr_assembler (AsmErr_string "assemble_x86_opn: cannot check, please repport")) in    
    ok (op, asm_args)
  end.

Definition assemble_sopn ii op (outx : lvals) (inx : pexprs) :=
  match op with
  | Omulu     _ 
  | Oaddcarry _ 
  | Osubcarry _ =>
    cierror ii (Cerr_assembler (AsmErr_string "assemble_sopn : invalid op"))
  (* Low level x86 operations *)
  | Oset0 sz => 
    let op := if (sz <= U64)%CMP then (XOR sz) else (VPXOR sz) in
    Let x := 
      match rev outx with 
      | Lvar x :: _ =>  ok x
      | _ => 
        cierror ii 
          (Cerr_assembler (AsmErr_string "assemble_sopn set0: destination is not a register")) 
      end in
    assemble_x86_opn ii op outx [::Pvar x; Pvar x]
  | Ox86MOVZX32 =>
    Let x := 
      match outx with 
      | [::Lvar x] =>  ok x
      | _ => 
        cierror ii 
          (Cerr_assembler (AsmErr_string "assemble_sopn Ox86MOVZX32: destination is not a register")) 
      end in
    assemble_x86_opn ii (MOV U32) outx inx 

  | Oconcat128 =>
    Let inx := 
        match inx with
        | [:: h; Pvar _ as l] => ok [:: l; h; @wconst U8 1%R]
        |  _ => 
          cierror ii 
            (Cerr_assembler (AsmErr_string "assemble_sopn Oconcat: assert false"))
        end in
    assemble_x86_opn ii VINSERTI128 outx inx
    
  | Ox86 op =>
    assemble_x86_opn ii op outx inx 
  end.

Lemma id_semi_sopn_sem op :
  let id := instr_desc op in
  id_semi id = sopn_sem (Ox86 op).
Proof. by []. Qed.

Lemma word_of_scale1 : word_of_scale Scale1 = 1%R.
Proof. by rewrite /word_of_scale /= /wrepr; apply/eqP. Qed.

Lemma assemble_leaP ii sz sz' (w:word sz') lea adr m s:
  (sz ≤ U64)%CMP → 
  (sz ≤ sz')%CMP →
  lom_eqv m s →
  sem_lea sz (evm m) lea = ok (zero_extend sz w) → 
  assemble_lea ii lea = ok adr → 
  zero_extend sz (decode_addr s adr) = zero_extend sz w.
Proof.
  move=> hsz64 hsz [_ hget _ _] hsem; rewrite /assemble_lea.
  t_xrbindP => ob hob oo hoo sc hsc <- /=.
  rewrite /decode_addr /=.  
  move: hsem; rewrite /sem_lea.
  apply rbindP => wb hwb; apply rbindP => wo hwo heq.
  have <- := ok_inj heq.
  rewrite !(wadd_zero_extend, wmul_zero_extend) // addrA; do 2 f_equal.
  + case: lea_base hob hwb => /= [vo | [<-] [<-] /=]; last by apply zero_extend0.
    t_xrbindP => r /reg_of_var_register_of_var -/var_of_register_of_var <- <- v /hget hv /=.
    move=> /(value_uincl_word hv) -/to_wordI [sz1 [w1 [hsz1]]] /Vword_inj [?];subst sz1.
    by move=> /= <- ->.
  + by rewrite (xscale_ok hsc).
  case: lea_offset hoo hwo => /= [vo | [<-] [<-] /=]; last by apply zero_extend0.
  t_xrbindP => r /reg_of_var_register_of_var -/var_of_register_of_var <- <- v /hget hv /=.
  move=> /(value_uincl_word hv) -/to_wordI [sz1 [w1 [hsz1]]] /Vword_inj [?];subst sz1.
  by move=> /= <- ->.
Qed.

Lemma addr_of_pexprP ii gd e a (x:var_i) o z o' z' m s:
  lom_eqv s m →
  get_var (evm s) x = ok o →
  to_pointer o = ok z →
  sem_pexpr gd s e = ok o' →
  to_pointer o' = ok z' →
  addr_of_pexpr ii Uptr x e = ok a →
  (z + z')%R = decode_addr m a.
Proof.
move => eqv ok_o ok_z ok_o' ok_z'.
rewrite /addr_of_pexpr.
case heq: mk_lea => [lea | //].
have hle : (U64 <= U64)%CMP by []. 
have /= := mk_leaP  (p:= (Build_prog gd [::])) (s:=s) hle hle heq.
rewrite ok_o /= ok_o' /= /sem_sop2 /= ok_z /= ok_z' /=.
move=> /(_ _ refl_equal) h1 h2.
have := assemble_leaP hle hle eqv h1 h2.
by rewrite !zero_extend_u => ->.
Qed.

Variant check_sopn_argI ii max_imm args e : arg_desc -> stype -> Prop :=
| CSA_Implicit i ty :
       (eq_expr e {| v_var := var_of_implicit i; v_info := 1%positive |})
    -> check_sopn_argI ii max_imm args e (ADImplicit i) ty

| CSA_Explicit n o a a' ty :
       onth args n = Some a
    -> arg_of_pexpr ii ty max_imm e = ok a'
    -> compat_imm ty a a'
    -> check_oreg o a
    -> check_sopn_argI ii max_imm args e (ADExplicit n o) ty.

Lemma check_sopn_argP ii max_imm args e sp :
  check_sopn_arg ii max_imm args e sp -> check_sopn_argI ii max_imm args e sp.1 sp.2.
Proof.
case: sp => -[i|n o] ty; first by apply: CSA_Implicit.
rewrite /check_sopn_arg /=; case Enth: onth => [a|] //.
case E: arg_of_pexpr => [a'|] // /andP[??].
by apply: (CSA_Explicit (a := a) (a' := a')).
Qed.

Lemma value_uincl_undef v ty : value_uincl v (Vundef ty) -> exists ty', v = Vundef ty'.
Proof. case: v => //; eauto. Qed.

Lemma value_uincl_word_of_val sz ty v w vt : 
  value_uincl v (@Vword sz w) → of_val ty v = ok vt → of_val ty (Vword w) = ok vt.
Proof.
  case: v => //=; last by move=> ??;rewrite of_val_undef.
  move=> sz' w' /andP[hsz1 /eqP ->] /of_val_Vword [sz1 [heq]]; subst ty => /= -[hsz ->].
  by rewrite zero_extend_idem // /truncate_word (cmp_le_trans hsz hsz1).
Qed.

Lemma var_of_flagP m s f v ty vt: 
  lom_eqv m s → 
  get_var (evm m) (var_of_flag f) = ok v →
  of_val ty v = ok vt → 
  ∃ v' : value, Let b := st_get_rflag f s in ok (Vbool b) = ok v' ∧ of_val ty v' = ok vt.
Proof.
  move=> [??? h] /h hu hv. 
  exists (of_rbool ((xrf s) f)); rewrite /st_get_rflag.
  case: (xrf s f) hu => //=.
  + move=> b; case: v hv => //= [?? <- //| ?].
    by rewrite of_val_undef.
  by case: v hv => // ?; rewrite of_val_undef.
Qed.

Lemma var_of_registerP E m s r v ty vt:
  lom_eqv m s → 
  get_var (evm m) (var_of_register r) = ok v → 
  of_val ty v = ok vt → 
  ∃ v' : value, Ok E (Vword ((xreg s) r)) = ok v' ∧ of_val ty v' = ok vt.
Proof. move=> [? h ??] /h -/value_uincl_word_of_val h1 /h1;eauto. Qed.

Lemma check_sopn_arg_sem_eval gd m s ii max_imm args e ad ty v vt:
     lom_eqv m s
  -> check_sopn_arg ii max_imm args e (ad,ty)
  -> sem_pexpr gd m e = ok v
  -> of_val ty v = ok vt 
  -> exists v', eval_arg_in_v gd s args ad ty = ok v' /\ 
     of_val ty v' = ok vt.
Proof.
  move=> eqm /check_sopn_argP /= h.
  case: h vt.
  + move=> i {ty} ty /eq_exprP -> vt /=.
    case: i => /= [f | r]; first by apply var_of_flagP. 
    by apply var_of_registerP.
  move=> n o a a' [ | | | ws] //= ->.
  + t_xrbindP => c hac <-. 
    rewrite /compat_imm orbF => /eqP <- -> /= b hb.
    case: eqm => ??? eqf.
    have [v']:= eval_assemble_cond eqf hac hb.
    case: eval_cond => /= [ | [] [] // [] <- /value_uincl_undef [ty1] -> ]; last by case: ty1.
    move=> b' [[<-]] {hb}; case: v => // [b1 | [] //] -> ?. 
    by exists b'.
  move=> haw hcomp -> /=; case: e haw => //=.
  + case: eqm => _ eqr eqx _.
    move=> x /xreg_of_varI; case: a' hcomp => // r; rewrite /compat_imm orbF => /eqP <- {a} xr w ok_v ok_w;
    (eexists; split; first reflexivity);
    apply: (value_uincl_word _ ok_w).
    + by apply: eqr; rewrite (var_of_register_of_var xr).
    by apply: eqx; rewrite (xmm_register_of_varI xr).
  + move=> g h; case: h hcomp => <-.
    rewrite /compat_imm orbF => /eqP <- w /get_globalI [z hz ->] /= ht.
    by rewrite /get_global_word hz /=; eauto.
  + move=> sz x p; case: eqP => [<- | //].
    t_xrbindP => r haddr ? w1 wp vp hget htop wp' vp' hp hp' wr hwr <- /= htr; subst a'.
    move: hcomp; rewrite /compat_imm orbF => /eqP <-.
    have <- := addr_of_pexprP eqm hget htop hp hp' haddr.
    by case: eqm => <- ???; rewrite hwr /=; eauto.
  case => //= w' [] //= z; case: max_imm => //= w1.
  t_xrbindP => ? /assertP /eqP heq h.
  case: h hcomp => <-; rewrite /compat_imm => /orP [/eqP <- | ].
  + move=> w [] <- /truncate_wordP [hsz ->].
    rewrite heq; eexists; split; first reflexivity.
    by rewrite /to_word truncate_word_u.
  case: a => // sz' w2 /eqP heq2 w [] <- /truncate_wordP [hsz ->].
  rewrite -heq2 heq; eexists; split; first reflexivity.
  by rewrite /to_word truncate_word_u.
Qed.

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

Lemma word_uincl_update_u256 sz sz' (w: word sz) (w': word sz') fl old :
  word_uincl w w' →
  word_uincl w (update_u256 fl old w').
Proof.
  case: fl => h /=.
  + (* MSB_CLEAR *)
    apply: (word_uincl_trans h).
    apply: word_uincl_zero_extR.
    exact: wsize_ge_U256.
  (* MSB_MERGE *)
  apply/andP; split; first exact: wsize_ge_U256.
  case/andP: h => hle /eqP -> {w}.
  rewrite -wxor_zero_extend; last exact: wsize_ge_U256.
  rewrite -wand_zero_extend; last exact: wsize_ge_U256.
  rewrite zero_extend_wshl; last exact: wsize_ge_U256.
  rewrite zero_extend_idem; last exact: wsize_ge_U256.
  rewrite wshl_ovf; last first.
  + by apply/leP; case: sz sz' {w' old} hle => -[].
  by rewrite wandC wand0 wxor0.
Qed.

(* TODO: move this *)
Lemma var_of_xmm_register_inj x y :
  var_of_xmm_register x = var_of_xmm_register y →
  x = y.
Proof. by move=> [];apply inj_string_of_xmm_register. Qed.

(* TODO: move and change def of reg_of_var *)
Lemma var_of_reg_of_var ii v r: reg_of_var ii v = ok r → var_of_register r = v.
Proof.
  rewrite /reg_of_var /var_of_register; case: v => -[] // [] // xn.
  case heq : reg_of_string => [r' | ] => // -[<-]; apply f_equal.
  by apply: inj_reg_of_string heq; apply reg_of_stringK.
Qed.

Lemma compile_lval ii gd msb_flag max_imm loargs ad ty (vt:sem_ot ty) m m' s lv1 e1:
  lom_eqv m s ->
  check_arg_dest ad ty ->
  write_lval gd lv1 (oto_val vt) m = ok m' ->
  pexpr_of_lval ii lv1 = ok e1 ->
  check_sopn_dest ii max_imm loargs e1 (ad, ty) ->
  exists s', mem_write_val msb_flag loargs (ad, ty) (oto_val vt) s = ok s' /\ lom_eqv m' s'.
Proof.
  move=> hlom; case:(hlom) => [h1 h2 h3 h4]; case: ad => [ai _ | n o]; rewrite /check_sopn_dest /=.
  case: ai => [f | r].
  + case: lv1 => //=; last by move=> ???? [<-].
    move=> x hw [] <- /= /eqP heq.
    move: hw; rewrite /write_var heq; t_xrbindP => vm hvm <- /= {heq}.
    move: hvm; rewrite /mem_write_val /set_var /on_vu /= /oof_val.
    case: ty vt => //= vt h.
    have -> :  match match vt with Some b => Vbool b | None => Vundef sbool end with
            | Vbool b => ok (Some b)
            | Vundef sbool => ok None
            | _ => type_error
            end = ok vt.
    + by case: vt h.
    have -> /= : vm =  ((evm m).[var_of_flag f <- match vt with Some b => ok b | None => undef_error end])%vmap.
    + by case: vt h => [b | ] /= [<-].
    eexists; split; first reflexivity.
    constructor => //=.
    + move=> r v; rewrite /get_var /=; apply on_vuP => //= w.
      rewrite Fv.setP_neq // => hg hv.
      by apply (h2 r); rewrite /get_var /on_vu hg -hv.
    + move=> r v; rewrite /get_var /=; apply on_vuP => //= w.
      rewrite Fv.setP_neq // => hg hv.
      by apply (h3 r); rewrite /get_var /on_vu hg -hv.         
    rewrite /eqflags => f' v; rewrite /get_var /on_vu /=.
    rewrite /RflagMap.oset /= ffunE.
    case: eqP => [-> | hne] {h}.
    + by rewrite Fv.setP_eq; case: vt => // b [<-].
    rewrite Fv.setP_neq; last by apply /eqP => h; apply hne; apply var_of_flag_inj.
    by apply h4.
  + case: lv1 => //=; last by move=> ???? [<-].
    move=> x hw [<-] /eqP hx /=.
    move: hw; rewrite /write_var hx /= /set_var /=.
    t_xrbindP => vm; rewrite /on_vu. 
    case heq : to_pword => [v | e]; last by case e.
    move=> [<-] <-; rewrite /mem_write_val /=.
    case: ty vt heq => //=; first by case.
    move=> sz w [<-]; rewrite truncate_word_u /=.
    eexists; split; first reflexivity.
    constructor => //=.
    + move=> r' v'; rewrite /get_var /on_vu /= /RegMap.set ffunE.
      case: eqP => [-> | hne].
      + rewrite Fv.setP_eq  /word_extend_reg=> -[<-] /= .
        case : Sumbool.sumbool_of_bool => /= hsz.
        + have heq := zero_extend_u w.
          by rewrite -{1}heq; apply word_uincl_ze_mw.
        rewrite -(@zero_extend_idem sz U64 sz w); last by apply cmp_nle_le; rewrite hsz.
        rewrite zero_extend_u. 
        by apply word_uincl_ze_mw => //; apply cmp_nle_le; rewrite hsz.
      rewrite Fv.setP_neq; last by apply /eqP => h; apply hne; apply var_of_register_inj.
      by apply h2. 
    + move=> r' v'; rewrite /get_var /on_vu /=.
      by rewrite Fv.setP_neq //; apply h3.
    move=> f v'; rewrite /get_var /on_vu /=.
    by rewrite Fv.setP_neq //; apply h4.
  case heq1: onth => [a | //].
  case heq2: arg_of_pexpr => [ a' | //] hty hw he1 /andP[] /eqP ? hc; subst a'.
  rewrite /mem_write_val /= /mem_write_ty.
  case: lv1 hw he1 heq2=> //=.
  + move=> [x xii] /= hw [<-]; rewrite /arg_of_pexpr.
    case: ty hty vt hw => //= sz _ vt.
    rewrite /write_var; t_xrbindP => vm hset <-.
    apply: set_varP hset; last by move=> /eqP heq heq'; rewrite heq in heq'.
    move=> t ht <-; rewrite truncate_word_u /= heq1 hc /= => /xreg_of_varI.
    case: a heq1 hc => // r heq1 hc => [ /var_of_register_of_var | /xmm_register_of_varI ] ?; subst x;
      (eexists; split; first reflexivity); constructor => //=.
    1-6: move => r' v'; rewrite /get_var/on_vu.
    + rewrite /RegMap.set ffunE; case: eqP.
      * move => ->{r'}; rewrite Fv.setP_eq => -[<-]{v'}.
        case: ht => <-{t}; case: Sumbool.sumbool_of_bool => hsz /=.
        - by rewrite -{1}(zero_extend_u vt); apply: word_uincl_ze_mw.
        apply: word_uincl_ze_mw => //.
        by apply: cmp_nle_le; rewrite hsz.
      * move => hne; rewrite Fv.setP_neq; first exact: h2.
        by apply/eqP => /var_of_register_inj ?; apply: hne.
    1-3, 5: rewrite Fv.setP_neq //.
    + exact: h3.
    1, 3: exact: h4.
    + exact: h2.
    rewrite /XRegMap.set ffunE; case: eqP.
    + move => ->{r'}; rewrite Fv.setP_eq => -[<-]{v'}.
      apply: word_uincl_update_u256.
      by case: ht => <-{t}; rewrite (sumbool_of_boolET (wsize_ge_U256 sz)).
    move => hne; rewrite Fv.setP_neq; first exact: h3.
    apply/eqP => /var_of_xmm_register_inj ?; exact: hne.
  move=> sz [x xii] /= e; t_xrbindP.
  move=> wp vp hget hp wofs vofs he hofs w hw m1 hm1 ??; subst m' e1.
  case: ty hty vt hw => //= sz' _ vt hw.
  case: eqP => // ?; subst sz'.
  move: hw; rewrite truncate_word_u => -[?]; subst vt.
  t_xrbindP => adr hadr ?; subst a.
  rewrite /= heq1 hc /= /mem_write_mem -h1.
  have /(_ hget) <-:= addr_of_pexprP hlom _ hp he hofs hadr.
  rewrite hm1 /=; eexists; split; first by reflexivity.
  by constructor.
Qed.

Lemma compile_lvals ii id_max_imm gd m lvs m' s loargs 
  id_out id_tout (vt:sem_tuple id_tout) msb_flag: 
  size id_out = size id_tout -> 
  write_lvals gd m lvs (list_ltuple vt) = ok m' ->
  lom_eqv m s ->
  check_sopn_dests ii id_max_imm loargs lvs (zip id_out id_tout) ->
  utils.all2 check_arg_dest id_out id_tout ->
  exists s', 
    mem_write_vals msb_flag s loargs id_out id_tout (list_ltuple vt) = ok s' ∧ lom_eqv m' s'.
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
                           check_sopn_dest ii id_max_imm loargs e1 (ad, ty) &
                           all2 (check_sopn_dest ii id_max_imm loargs) es (zip ads tys)].
  + by case: pexpr_of_lval h => //= e1; case: mapM => //= es /andP [] ??; exists e1, es. 
  rewrite /mem_write_vals /=.
  have [s1 [-> /= h2]]:= compile_lval msb_flag hlo hca hw1 he1 hce1.
  apply: (hrec _  _ _ _ _ heqs hwn h2 _ hcall).
  by rewrite /check_sopn_dests hes.
Qed.

Lemma compile_x86_opn ii (loargs : seq asm_arg) gd op m s args lvs m' :
let id := instr_desc op in
sem_sopn gd (Ox86 op) m lvs args = ok m' ->
check_sopn_args ii id.(id_max_imm) loargs args (zip id.(id_in) id.(id_tin)) ->
check_sopn_dests ii id.(id_max_imm) loargs lvs (zip id.(id_out) id.(id_tout)) ->
id.(id_check) loargs ->
lom_eqv m s ->
exists s', exec_instr_op gd id loargs s = ok s' /\ lom_eqv m' s'.
Proof.
move=> id ; rewrite /sem_sopn /exec_sopn.
t_xrbindP => x vs Hvs vt Hvt Htuplet Hm' Hargs Hdest Hid Hlomeqv.
rewrite /exec_instr_op /eval_instr_op Hid /=.
move: vt Hvt Htuplet; rewrite /sopn_sem /get_instr -/id => {Hid}.
case: id Hargs Hdest => /= msb_flag id_tin 
 id_in id_tout id_out id_semi id_check id_nargs /andP[] /eqP hsin /eqP hsout id_max_imm
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

Lemma is_leaP ii op outx inx lea:
  is_lea ii op outx inx = ok lea ->
  match lea with
  | Some(sz, x, lea) =>
    exists e, [/\ op = LEA sz, outx = [::Lvar x], inx = [:: e] & lowering.mk_lea sz e = Some lea]
  | None => is_special op = false
  end.
Proof.
  case: op outx inx => //=;
   try by move=> *; match goal with | H:ok _ = ok lea |- _ => case: H; move=> H;subst lea end.
  move=> sz [ | []] // x [] // [ | e []]//.
  by case heq: mk_lea => [lea' | //] [<-]; eexists.
Qed.
  
Lemma assemble_x86_opnP ii gd op lvs args op' asm_args s m m' : 
  sem_sopn gd (Ox86 op) m lvs args = ok m' ->
  assemble_x86_opn ii op lvs args = ok (op', asm_args) ->
  lom_eqv m s ->
  exists s', eval_op gd op' asm_args s = ok s' /\ lom_eqv m' s'.
Proof.
  rewrite /assemble_x86_opn.
  t_xrbindP => hsem lea /is_leaP.
  case: lea => [ [[sz x] lea] [e [??? hlea]]| hspe]. 
  + subst op lvs args; t_xrbindP => rx /reg_of_var_register_of_var -/var_of_register_of_var hrx rb hrb ro hro sc /xscale_ok hsc <- <- hlo.
    move: hsem; rewrite /eval_op /sem_sopn /exec_sopn /=.
    t_xrbindP => vs ? v he <- va.
    t_xrbindP => w hw; rewrite /sopn_sem /= /x86_LEA.
    rewrite /check_size_16_64; case: andP => //= -[hsz1 hsz2] -[<-] <-.
    t_xrbindP => m1 hwm ?; subst m1.
    move: hwm; rewrite /write_var /set_var -hrx /= => -[<-].
    rewrite (sumbool_of_boolET hsz2).
    eexists; split; first reflexivity.
    case: hlo => h1 h2 h3 h4.
    constructor => //=.
    + move=> r' v'; rewrite /get_var /on_vu /= /RegMap.set ffunE.
      have [sz' [w' [hsz' ??]]]:= to_wordI hw; subst v w.
      have hlea' := mk_leaP (p := {| p_globs := gd; p_funcs := [::] |}) hsz2 hsz' hlea he.
      case: eqP => [-> | hne].
      + rewrite Fv.setP_eq  /word_extend_reg => -[<-] /=.
        move: hlea'; rewrite /sem_lea /decode_addr /=.
        apply rbindP => wb hwb; apply rbindP => wo hwo h; have {h} <-:= ok_inj h.
        rewrite !(wadd_zero_extend, wmul_zero_extend) //.
        rewrite -(zero_extend_u (zero_extend sz _ + _)) GRing.addrA hsc.
        have -> : zero_extend sz (odflt 0%R (ssrfun.omap (xreg s) rb)) = wb.
        + case: lea_base hrb hwb => /=.
          + move=> x1; t_xrbindP => r /var_of_reg_of_var <- <- v.
            rewrite /ssrfun.omap /= => /h2 hu /(value_uincl_word hu) /=.
            by rewrite /truncate_word hsz2 => -[].
          by move=> [<-] [<-] /=; rewrite zero_extend0.
        have -> : zero_extend sz (odflt 0%R (ssrfun.omap (xreg s) ro)) = wo.
        + case: lea_offset hro hwo => /=.
          + move=> x1; t_xrbindP => r /var_of_reg_of_var <- <- v.
            rewrite /ssrfun.omap /= => /h2 hu /(value_uincl_word hu) /=.
            by rewrite /truncate_word hsz2 => -[].
          by move=> [<-] [<-] /=; rewrite zero_extend0.
        by apply word_uincl_ze_mw.
      rewrite Fv.setP_neq; last by apply /eqP => h; apply hne; apply var_of_register_inj.
      by apply h2. 
    + move=> r' v'; rewrite /get_var /on_vu /=.
      by rewrite Fv.setP_neq //; apply h3.
    move=> f v'; rewrite /get_var /on_vu /=.
    by rewrite Fv.setP_neq //; apply h4.
  t_xrbindP => asm_args' ?? /assertP hidc ? /assertP /andP [hca hcd] <- ?;subst asm_args'.
  rewrite /eval_op hspe.
  apply: compile_x86_opn hsem hca hcd hidc.
Qed.

Lemma assemble_sopnP gd ii op lvs args op' asm_args m m' s: 
  sem_sopn gd op m lvs args = ok m' ->
  assemble_sopn ii op lvs args = ok (op', asm_args) ->
  lom_eqv m s ->
  exists s', eval_op gd op' asm_args s = ok s' /\ lom_eqv m' s'.
Proof.
  case: op => //=.
  + move=> sz; rewrite /sem_sopn /exec_sopn /sopn_sem /=.
    rewrite /Oset0_instr; case: ifP => /= hsz64.
    + t_xrbindP => ? []// ?? [<-] /= <-.
      move=> hw x hx; rewrite /assemble_x86_opn /is_lea /=.
      t_xrbindP => asm_args' _ ? /assertP hidc ? /assertP /andP[hca hcd] ??;subst op' asm_args'.  
      move: hca; rewrite /check_sopn_args /= => /and3P [].
      rewrite /check_sopn_arg /=.
      case: asm_args hidc hcd => //= a0 [ // | ] a1 [] //= hidc hcd;
       last by rewrite /check_args_kinds /= !andbF. 
      case: xreg_of_var (@xreg_of_varI ii x) => // y /(_ _ erefl) ok_y.
      rewrite !andbT /compat_imm.
      case: y ok_y => // r xr; rewrite !orbF => /eqP ? /eqP ? _; subst a0 a1; last by [].
      rewrite /eval_op /exec_instr_op /= /eval_instr_op /=.
      rewrite /truncate_word /x86_XOR /check_size_8_64 hsz64 /= wxor_xx.
      set id := instr_desc (XOR sz) => hlo.
      rewrite /SF_of_word msb0.
      by apply: (@compile_lvals ii id.(id_max_imm) gd m lvs m' s [:: Reg r; Reg r]
             id.(id_out) id.(id_tout)
             (let vf := Some false in let: vt := Some true in (::vf, vf, vf, vt, vt & (0%R: word sz)))
             MSB_CLEAR (refl_equal _) hw hlo hcd id.(id_check_dest)).
    t_xrbindP => ? []// ?? [<-] /= <-.
    move=> hw x hx; rewrite /assemble_x86_opn /is_lea /=.
    t_xrbindP => asm_args' _ ? /assertP hidc ? /assertP /andP[hca hcd] ??;subst op' asm_args'.  
    move: hca; rewrite /check_sopn_args /= => /and3P [].
    rewrite /check_sopn_arg /=.
    case: asm_args hidc hcd => //= a0 [// | ] a1 [] //= a2 [] //=;
      last by rewrite /check_args_kinds /= !andbF.  
    rewrite orbF => hidc hcd.
    case: xreg_of_var (@xreg_of_varI ii x) => // y /(_ _ erefl) ok_y.
    rewrite !andbT /compat_imm.
    case: y ok_y => // r xr; rewrite !orbF => /eqP ? /eqP ? _; subst a1 a2.
    + by move: hidc; rewrite /check_args_kinds /= andbF.
    rewrite /eval_op /exec_instr_op /= /eval_instr_op /=.
    rewrite /truncate_word /x86_VPXOR hidc /= /x86_u128_binop /check_size_128_256 wsize_ge_U256. 
    have -> /= : (U128 ≤ sz)%CMP by case: (sz) hsz64. 
    rewrite wxor_xx; set id := instr_desc (VPXOR sz) => hlo.
    by apply: (@compile_lvals ii id.(id_max_imm) gd m lvs m' s [:: a0; XMM r; XMM r]
               id.(id_out) id.(id_tout)
               (0%R: word sz)
               MSB_CLEAR (refl_equal _) hw hlo hcd id.(id_check_dest)).
  + t_xrbindP.
    case: args => // h [] // [] // x [] //=.
    rewrite /sem_sopn /exec_sopn /sopn_sem /=.
    t_xrbindP => ?? vh hvh ? vl hvl <- <- /= vd.
    t_xrbindP => wh hwh wl hwl <- <- /= hwr ? <-.
    rewrite /assemble_x86_opn /=.
    t_xrbindP => asm_args' haux _ /assertP hch _ /assertP /andP[hca hcd] <- ? hlow.
    subst asm_args'.
    have [s' [hwm hlow']]:= 
      compile_lvals 
       (id_out := [:: E 0]) (id_tout := [:: sword256]) MSB_CLEAR refl_equal hwr hlow hcd refl_equal.
    exists s'; split => //.
    move: hca; rewrite /check_sopn_args /= => /and4P [] hE1 hE2 hE3 _.
Opaque eval_arg_in_v.
    rewrite /eval_op /exec_instr_op /= /eval_instr_op /= hch.
    have [vh' [-> /= hvh']]:= check_sopn_arg_sem_eval hlow hE2 hvh hwh.
    have [v1 [/= -> hv1 /=]] := 
       check_sopn_arg_sem_eval (gd:=gd) hlow hE3 refl_equal (truncate_word_u _).
Transparent eval_arg_in_v.
    move: hE1; rewrite /check_sopn_arg /=.
    case: onth => // a.
    case heq: xreg_of_var => [ a' | //] /andP[] hc _.
    have := xreg_of_varI heq => {heq}.
    case: a' hc => //= [ r | xmm].
    + rewrite /compat_imm; case:a => //= r' /orP [/eqP [?]|//] hr; subst r'.
      have heq := var_of_register_of_var hr. 
      rewrite -heq in hvl.
      case: hlow => _ /(_ _ _ hvl) hu _.
      move: hwl hu; rewrite /to_word.
      case: (vl) => // [ ws w /=| []//].
      rewrite /truncate_word /word_uincl.
      case: ifP => // h1 _ /andP [] h2.
      by have := cmp_le_trans h1 h2.

    rewrite /compat_imm; case:a => //= xmm' /orP [ /eqP[?]| //] hxmm;subst xmm'.
    rewrite hvh' hv1 /= -hwm /=; do 3! f_equal.
    have := xxgetreg_ex hlow hxmm hvl.
    rewrite zero_extend_u /winserti128 => hu.
    have -> : (lsb (wrepr U8 (wunsigned 1))) by done.
    do 2! f_equal; rewrite /split_vec /=.
    move: hwl hu; rewrite /to_word.
    case: (vl) => // [ws wl' /= | []//].
    rewrite /truncate_word /word_uincl mul0n.
    case: ifP => // hle.
    rewrite (@subword0 U128 U256) // => -[] <- /andP [] _ /eqP ->.
    by rewrite zero_extend_idem.
  + case: lvs => // -[] // x [] //.
    rewrite /sem_sopn /exec_sopn /sopn_sem /=.
    case: args => //= a args.
    t_xrbindP => vs1 vs2 va hva vs3 h <- /=.
    case: args h => /=; t_xrbindP; last by move=> *; subst.
    move => <- ? wa htwa [<-] <-; t_xrbindP => m1 hwx ?;subst m1.
    rewrite /assemble_x86_opn /is_lea /=.
    t_xrbindP => asm_args' _ ? /assertP hidc ? /assertP /andP[hca hcd] ?? hlo;subst op' asm_args'.  
    case: asm_args hidc hcd hca => // a0 [] // a1 []// hidc hcd;
      last by rewrite /check_args_kinds /= !andbF.                               
    rewrite /check_sopn_args /= andbT => hca1.
    rewrite /eval_op /exec_instr_op /= /eval_instr_op /=.
    rewrite /= in hidc;rewrite hidc.
    have [v' /= [-> /= ->] /=]:= check_sopn_arg_sem_eval hlo hca1 hva htwa.
    move: hcd; rewrite /check_sopn_dests /= /check_sopn_dest /= => /andP -[].
    case: xreg_of_var (@xreg_of_varI ii x) => // y /(_ _ erefl) ok_y.
    rewrite andbT => /eqP ? _; subst a0.
    case: y hidc hca1 ok_y => // r hidc hca1 /var_of_register_of_var xr.
    rewrite /mem_write_vals.
    eexists; split; first reflexivity.
    case: hlo => h1 h2 h3 h4.
    move: hwx; rewrite /write_var /set_var.
    rewrite -xr => -[<-]{m'}.
    constructor => //=.
    + move=> r' v''; rewrite /get_var /on_vu /= /RegMap.set ffunE.
      case: eqP => [-> | hne].
      + by rewrite Fv.setP_eq word_extend_reg_id // zero_extend_u => -[<-].
      rewrite Fv.setP_neq; last by apply /eqP => h; apply hne; apply var_of_register_inj.
      by apply h2. 
    + move=> r' v''; rewrite /get_var /on_vu /=.
      by rewrite Fv.setP_neq //; apply h3.
    move=> f v''; rewrite /get_var /on_vu /=.
    by rewrite Fv.setP_neq //; apply h4. 
  by move=> a; apply: assemble_x86_opnP.
Qed.

