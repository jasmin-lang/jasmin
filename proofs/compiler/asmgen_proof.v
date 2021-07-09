From mathcomp Require Import all_ssreflect all_algebra.
Require Import ssrring.
Require Import low_memory psem x86_sem compiler_util lowering lowering_proof x86_variables_proofs asmgen.

Import Utf8.
Import GRing.
Import oseq.
Import x86_variables psem.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma assemble_leaP rip ii sz sz' (w:word sz') lea adr m s:
  (sz ≤ Uptr)%CMP → 
  (sz ≤ sz')%CMP →
  lom_eqv rip m s →
  sem_lea sz (evm m) lea = ok (zero_extend sz w) → 
  assemble_lea ii lea = ok adr → 
  zero_extend sz (decode_addr s adr) = zero_extend sz w.
Proof.
  move=> hsz64 hsz [_ _ _ hget _ _] hsem; rewrite /assemble_lea.
  t_xrbindP => ob hob oo hoo sc hsc <- /=.
  rewrite /decode_reg_addr /=.  
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
  have hsemlea:= 
     mk_leaP (p:= (Build_prog (pT := progUnit) [::] [::] tt)) hsz64 hsz heq he.
  case hb: lea_base => [b | ];last by apply (assemble_leaP hsz64 hsz lom hsemlea).
  case: eqP => [ | _]; last by apply (assemble_leaP hsz64 hsz lom hsemlea).
  t_xrbindP => hbrip _ /assertP /eqP ho <- /=.
  case: lom => _ hrip _ _ _.
  move: hsemlea; rewrite /sem_lea ho hb /= hbrip hrip /= /truncate_word hsz64 /= => h.
  have <- := ok_inj h.
  by rewrite mulr0 addr0 addrC wadd_zero_extend.
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
  have he: sem_pexpr [::] m (Papp2 (Oadd (Op_w U64)) (Plvar x) p) = ok (Vword (wx + wp)).
  + by rewrite /= /get_gvar /= hx /= hp /= /sem_sop2 /= hvx hvp.
  have := addr_of_pexprP _ eqm he ha.
  by rewrite !zero_extend_u => h;apply h.
Qed.

Variant check_sopn_argI rip ii max_imm args e : arg_desc -> stype -> Prop :=
| CSA_Implicit i ty :
       (eq_expr e (Plvar {| v_var := var_of_implicit i; v_info := 1%positive |}))
    -> check_sopn_argI rip ii max_imm args e (ADImplicit i) ty

| CSA_Explicit k n o a a' ty :
       onth args n = Some a
    -> arg_of_pexpr k rip ii ty max_imm e = ok a'
    -> compat_imm ty a a'
    -> check_oreg o a
    -> check_sopn_argI rip ii max_imm args e (ADExplicit k n o) ty.

Lemma check_sopn_argP rip ii max_imm args e sp :
  check_sopn_arg rip ii max_imm args e sp -> check_sopn_argI rip ii max_imm args e sp.1 sp.2.
Proof.
case: sp => -[i|k n o] ty; first by apply: CSA_Implicit.
rewrite /check_sopn_arg /=; case Enth: onth => [a|] //.
case E: arg_of_pexpr => [a'|] // /andP[??].
by apply: (CSA_Explicit (a := a) (a' := a')).
Qed.

Lemma var_of_flagP rip m s f v ty vt: 
  lom_eqv rip m s → 
  get_var (evm m) (var_of_flag f) = ok v →
  of_val ty v = ok vt → 
  ∃ v' : value, Let b := st_get_rflag f s in ok (Vbool b) = ok v' ∧ of_val ty v' = ok vt.
Proof.
  move=> [????? h] /h hu hv. 
  exists (of_rbool ((xrf s) f)); rewrite /st_get_rflag.
  case: (xrf s f) hu => //=.
  + move=> b; case: v hv => //= [?? <- //| ? ?].
    by rewrite of_val_undef.
  by case: v hv => // ??; rewrite of_val_undef.
Qed.

Lemma var_of_registerP rip E m s r v ty vt:
  lom_eqv rip m s → 
  get_var (evm m) (var_of_register r) = ok v → 
  of_val ty v = ok vt → 
  ∃ v' : value, Ok E (Vword ((xreg s) r)) = ok v' ∧ of_val ty v' = ok vt.
Proof. move=> [??? h ??] /h -/value_uincl_word_of_val h1 /h1;eauto. Qed.

Lemma check_sopn_arg_sem_eval rip m s ii max_imm args e ad ty v vt:
     lom_eqv rip m s
  -> check_sopn_arg rip ii max_imm args e (ad,ty)
  -> sem_pexpr [::] m e = ok v
  -> of_val ty v = ok vt 
  -> exists v', eval_arg_in_v s args ad ty = ok v' /\ 
     of_val ty v' = ok vt.
Proof.
  move=> eqm /check_sopn_argP /= h.
  case: h vt.
  + move=> i {ty} ty /eq_exprP -> vt /=.
    case: i => /= [f | r]; first by apply: var_of_flagP eqm. 
    by apply: var_of_registerP eqm.
  move=> k n o a a' [ | | | ws] //= ->.
  + t_xrbindP => c hac <-. 
    rewrite /compat_imm orbF => /eqP <- -> /= b hb.
    case: eqm => ????? eqf.
    have [v']:= eval_assemble_cond eqf hac hb.
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
    case: eqm => _ _ _ eqr eqx _.
    move=> /xreg_of_varI; case: a' hcomp => // r; rewrite /compat_imm orbF => /eqP <- {a} xr w ok_v ok_w;
    (eexists; split; first reflexivity);
    apply: (value_uincl_word _ ok_w).
    + by apply: eqr; rewrite (var_of_register_of_var xr).
    by apply: eqx; rewrite (xmm_register_of_varI xr).
  + move=> sz x p; case: eqP => [<- | //].
    t_xrbindP => r hr ?; subst a'.
    move: hcomp; rewrite /compat_imm orbF => /eqP <-.
    move=> w1 wp vp hget htop wp' vp' hp hp' wr hwr <- /= htr.
    have -> := addr_of_xpexprP eqm hr hget htop hp hp'.
    by case: eqm => <- ?????; rewrite hwr /=; eauto.
  case => //= w' [] //= z; case: max_imm => //= w1.
  t_xrbindP => ? /assertP /eqP heq h.
  case: h hcomp => <-; rewrite /compat_imm /eval_asm_arg => /orP [/eqP <- | ].
  + move=> w [] <- /truncate_wordP [hsz ->].
    rewrite heq; eexists; split; first reflexivity.
    by rewrite /to_word truncate_word_u.
  case: a => // sz' w2 /eqP heq2 w [] <- /truncate_wordP [hsz ->].
  rewrite -heq2 heq; eexists; split; first reflexivity.
  by rewrite /to_word truncate_word_u.
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
Proof. by rewrite /word_extend /= /mask_word wandC wand0 wxor0. Qed.

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
  apply/andP; split => //; rewrite /word_extend /mask_word.
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
  rewrite /word_extend /mask_word wshl_ovf; last first.
  + by apply/leP; case: (sz) (szo) h => -[].
  by rewrite wandC wand0 wxor0.
Qed.

Lemma compile_lval rip ii msb_flag max_imm loargs ad ty (vt:sem_ot ty) m m' s lv1 e1:
  lom_eqv rip m s ->
  check_arg_dest ad ty ->
  write_lval [::] lv1 (oto_val vt) m = ok m' ->
  pexpr_of_lval ii lv1 = ok e1 ->
  check_sopn_dest rip ii max_imm loargs e1 (ad, ty) ->
  exists s', mem_write_val msb_flag loargs (ad, ty) (oto_val vt) s = ok s' /\ lom_eqv rip m' s'.
Proof.
  move=> hlom; case:(hlom) => [h1 hrip hnrip h2 h3 h4]; case: ad => [ai _ | k n o]; rewrite /check_sopn_dest /=.
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
    have -> /= : vm =  ((evm m).[var_of_flag f <- match vt with Some b => ok b | None => undef_error end])%vmap.
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
    rewrite /eqflags => f' v; rewrite /get_var /on_vu /=.
    rewrite /RflagMap.oset /= ffunE.
    case: eqP => [-> | hne] {h}.
    + by rewrite Fv.setP_eq; case: vt => // b [<-].
    rewrite Fv.setP_neq; last by apply /eqP => h; apply hne; apply var_of_flag_inj.
    by apply h4.
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
    + by case:hlom => ? hget hd _ _ _;rewrite /get_var Fv.setP_neq //; apply /eqP;case: hd.
    + move=> r' v'; rewrite /get_var /on_vu /= /RegMap.set ffunE.
      case: eqP => [-> | hne].
      + rewrite Fv.setP_eq => -[<-] /=.
        case : Sumbool.sumbool_of_bool => /= hsz; first by apply word_uincl_word_extend.
        by rewrite word_extend_big // hsz.
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
    2-4, 6-8: move => r' v'.
    1-8: rewrite /get_var/on_vu.
    1, 8: rewrite Fv.setP_neq; first exact: hrip; by apply/eqP; case: hnrip.
    + rewrite /RegMap.set ffunE; case: eqP.
      * move => ->{r'}; rewrite Fv.setP_eq => -[<-]{v'}.
        case: ht => <-{t}; case: Sumbool.sumbool_of_bool => hsz /=.
        + by apply word_uincl_word_extend.
        by rewrite word_extend_big // hsz.
      * move => hne; rewrite Fv.setP_neq; first exact: h2.
        by apply/eqP => /var_of_register_inj ?; apply: hne.
    1-3, 5: rewrite Fv.setP_neq //.
    + exact: h3.
    1, 3: exact: h4.
    + exact: h2.
    rewrite /XRegMap.set ffunE; case: eqP.
    + move => ->{r'}; rewrite Fv.setP_eq => -[<-]{v'}.
      apply word_uincl_word_extend; first by apply wsize_ge_U256.
      by case: ht => <-{t}; rewrite (sumbool_of_boolET (wsize_ge_U256 sz)).
    move => hne; rewrite Fv.setP_neq; first exact: h3.
    apply/eqP => /var_of_xmm_register_inj ?; exact: hne.
  move=> sz [x xii] /= e; t_xrbindP.
  move=> wp vp hget hp wofs vofs he hofs w hw m1 hm1 ??; subst m' e1.
  case: ty hty vt hw => //= sz' _ vt hw.
  case: eqP => // ?; subst sz'.
  move: hw; rewrite truncate_word_u => -[?]; subst vt.
  t_xrbindP => adr hadr ?;subst a => /=.
  rewrite /= heq1 hc /= /mem_write_mem -h1.
  have -> := addr_of_xpexprP hlom hadr hget hp he hofs.
  rewrite hm1 /=; eexists; split; first by reflexivity.
  by constructor.
Qed.

Lemma compile_lvals rip ii id_max_imm m lvs m' s loargs 
  id_out id_tout (vt:sem_tuple id_tout) msb_flag: 
  size id_out = size id_tout -> 
  write_lvals [::] m lvs (list_ltuple vt) = ok m' ->
  lom_eqv rip m s ->
  check_sopn_dests rip ii id_max_imm loargs lvs (zip id_out id_tout) ->
  utils.all2 check_arg_dest id_out id_tout ->
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
                           check_sopn_dest rip ii id_max_imm loargs e1 (ad, ty) &
                           all2 (check_sopn_dest rip ii id_max_imm loargs) es (zip ads tys)].
  + by case: pexpr_of_lval h => //= e1; case: mapM => //= es /andP [] ??; exists e1, es. 
  rewrite /mem_write_vals /=.
  have [s1 [-> /= h2]]:= compile_lval msb_flag hlo hca hw1 he1 hce1.
  apply: (hrec _  _ _ _ _ heqs hwn h2 _ hcall).
  by rewrite /check_sopn_dests hes.
Qed.

Lemma compile_x86_opn rip ii (loargs : seq asm_arg) op m s args lvs m' :
let id := instr_desc op in
sem_sopn [::] (Ox86' op) m lvs args = ok m' ->
check_sopn_args rip ii id.(id_max_imm) loargs args (zip id.(id_in) id.(id_tin)) ->
check_sopn_dests rip ii id.(id_max_imm) loargs lvs (zip id.(id_out) id.(id_tout)) ->
id.(id_check) loargs ->
lom_eqv rip m s ->
exists s', exec_instr_op id loargs s = ok s' /\ lom_eqv rip m' s'.
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
  (* TODO: add the lemma *)
  have ? : (wbase sz' <= wbase sz)%Z by case: sz (sz') h => -[].
  have := wunsigned_range v; Psatz.lia.
Qed.

Lemma check_check1_write asm_args ad ws ty (v: sem_ot ty) s : 
  clear_check1 asm_args ad ->
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
  by rewrite /mem_write_xreg !word_extend_CLEAR zero_extend_comp.
Qed.

Lemma clear_check_write s ws asm_args id_out id_tout (t : sem_tuple id_tout) :
  size id_out = size id_tout → 
  clear_check id_out asm_args → 
  mem_write_vals MSB_CLEAR s asm_args id_out [seq extend_size ws i | i <- id_tout]
        (list_ltuple (extend_tuple ws t)) =
  mem_write_vals MSB_CLEAR s asm_args id_out id_tout (list_ltuple t).
Proof.
  rewrite /mem_write_vals.
  elim: id_out id_tout t s => [ | ad id_out hrec] [ | ty id_tout] //= t s [] 
     hsize /andP [] hc1 hcs.
  case: id_tout t hsize hcs.
  + by move=> {hrec}; case: id_out => //= v _ _; rewrite check_check1_write.
  move=> a l [] v t hsz hc.
  have := hrec (a::l) t _ hsz hc.
  rewrite /= check_check1_write //.
  case: mem_write_val => //=.
Qed.

Lemma exec_desc_desc' op asm_args s :  
  id_check (instr_desc op) asm_args ->
  exec_instr_op (instr_desc op) asm_args s = exec_instr_op (instr_desc' op.2) asm_args s.
Proof.
  case: op => -[ws |] //= op.
  case: eqP => //= hclear /andP [hc hcc].
  rewrite /exec_instr_op /= /eval_instr_op /= hc hcc hclear /=.
  case heq : eval_args_in => [vargs | ] //=.
  rewrite app_sopn_apply_lprod.
  case: app_sopn => //= t.
  apply clear_check_write => //.
  by have /andP [_ /eqP]:= id_eq_size (instr_desc' op).
Qed.

Lemma assemble_x86_opnP rip ii op lvs args op' asm_args s m m' : 
  sem_sopn [::] (Ox86' op) m lvs args = ok m' ->
  assemble_x86_opn rip ii op lvs args = ok (op', asm_args) ->
  lom_eqv rip m s ->
  exists s', eval_op op' asm_args s = ok s' /\ lom_eqv rip m' s'.
Proof.
  rewrite /assemble_x86_opn /eval_op => hsem.
  t_xrbindP => asm_args' ?? /assertP hidc ? /assertP /andP [hca hcd] <- ? hlo; subst asm_args'.
  have [s' [he' hlo']]:= compile_x86_opn hsem hca hcd hidc hlo.
  by exists s'; split => //; rewrite -exec_desc_desc'.
Qed.

Lemma assemble_sopnP rip ii op lvs args op' asm_args m m' s: 
  sem_sopn [::] op m lvs args = ok m' ->
  assemble_sopn rip ii op lvs args = ok (op', asm_args) ->
  lom_eqv rip m s ->
  exists s', eval_op op' asm_args s = ok s' /\ lom_eqv rip m' s'.
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
      set id := instr_desc' (XOR sz) => hlo.
      rewrite /SF_of_word msb0.
      by apply: (@compile_lvals rip ii id.(id_max_imm) m lvs m' s [:: Reg r; Reg r]
             id.(id_out) id.(id_tout)
             (let vf := Some false in (::vf, vf, vf, vf, Some true & (0%R: word sz)))
             (reg_msb_flag sz) (refl_equal _) hw hlo hcd id.(id_check_dest)).
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
    rewrite wxor_xx; set id := instr_desc' (VPXOR sz) => hlo.
    by apply: (@compile_lvals rip ii id.(id_max_imm) m lvs m' s [:: a0; XMM r; XMM r]
               id.(id_out) id.(id_tout)
               (0%R: word sz)
               (reg_msb_flag sz) (refl_equal _) hw hlo hcd id.(id_check_dest)).
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
       check_sopn_arg_sem_eval hlow hE3 refl_equal (truncate_word_u _).
Transparent eval_arg_in_v.
    move: hE1; rewrite /check_sopn_arg /=.
    case: onth => // a.
    case: x hvl haux => x [] // hvl haux.
    case heq: xreg_of_var => [ a' | //] /andP[] hc _.
    have := xreg_of_varI heq => {heq}.
    case: a' hc => //= [ r | xmm].
    + rewrite /compat_imm; case:a => //= r' /orP [/eqP [?]|//] hr; subst r'.
      have heq := var_of_register_of_var hr. 
      move: hvl.
      rewrite /get_gvar /= -heq => hvl.
      case: hlow => _ _ _ /(_ _ _ hvl) hu _ _.
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
    case: hlo => h1 hrip hd h2 h3 h4.
    move: hwx; rewrite /write_var /set_var.
    rewrite -xr => -[<-]{m'}.
    constructor => //=.
    + by rewrite /get_var Fv.setP_neq //; apply /eqP;case: hd.
    + move=> r' v''; rewrite /get_var /on_vu /= /RegMap.set ffunE.
      case: eqP => [-> | hne].
      + by rewrite Fv.setP_eq /reg_msb_flag /= word_extend_CLEAR zero_extend_u => -[<-].
      rewrite Fv.setP_neq; last by apply /eqP => h; apply hne; apply var_of_register_inj.
      by apply h2. 
    + move=> r' v''; rewrite /get_var /on_vu /=.
      by rewrite Fv.setP_neq //; apply h3.
    move=> f v''; rewrite /get_var /on_vu /=.
    by rewrite Fv.setP_neq //; apply h4. 
  by move=> a; apply: assemble_x86_opnP.
Qed.
