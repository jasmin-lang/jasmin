Require Import asmgen.
Import Utf8.
Import all_ssreflect.
Import compiler_util sem x86_sem x86_variables x86_variables_proofs.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* -------------------------------------------------------------------- *)
(* Definitions of descriptors                                           *)

Definition implicit_flags :=
  map (ADImplicit \o var_of_flag) [::OF; CF; SF; PF; ZF].

Definition implicit_flags_noCF :=
  map (ADImplicit \o var_of_flag) [::OF; SF; PF; ZF].

Local Coercion E n := ADExplicit n None.
Local Coercion F f := ADImplicit (var_of_flag f).
Local Coercion R f := ADImplicit (var_of_register f).

Notation make_instr_desc gen_sem := (mk_instr_desc gen_sem erefl erefl).

Instance x86_mem_equiv_refl : Reflexive x86_mem_equiv.
Proof. by case => xm xr xf; constructor => //= f; case: (xf f) => /=. Qed.

Arguments x86_mem_equiv_refl [_].

Corollary x86_mem_eq_equiv m m' :
  m = m' → x86_mem_equiv m m'.
Proof. move => ->; reflexivity. Qed.

(* ----------------------------------------------------------------------------- *)
Lemma MOV_gsc :
  gen_sem_correct [:: TYoprd; TYoprd] Ox86_MOV [:: E 0] [:: E 1] [::] MOV.
Proof.
  move=> [] // => [ x | x] y; split => // gd m m';rewrite /low_sem_aux /= /eval_MOV /=;
  t_xrbindP => ???? -> <- <- [<-] h; exists m' => /=; split => //; reflexivity.
Qed.

Definition MOV_desc := make_instr_desc MOV_gsc.

(* ----------------------------------------------------------------------------- *)

Lemma RegMap_set_id rm x : rm = RegMap.set rm x (rm x).
Proof. by apply /ffunP;case;rewrite !ffunE;(case:eqP => [<- | ?]). Qed.

Lemma write_mem_id mem a vx :
  Memory.read_mem mem a = ok vx ->
  Memory.write_mem mem a vx = ok mem.
Proof.
  move=> Ha;have Hval: Memory.valid_addr mem a.
  + by apply /Memory.readV;exists vx.
  move: (Hval) => /Memory.writeV -/(_ vx) [m1] /= H;rewrite H;f_equal.
  apply Memory.eq_memP => w.
  case: (a =P w) => [<- | neq].
  + by have := Memory.writeP_eq vx Hval; rewrite Ha H /= => ->.
  by have := Memory.writeP_neq vx Hval neq; rewrite H /= => ->.
Qed.

Lemma CMOVcc_gsc :
  gen_sem_correct [:: TYcondt; TYoprd; TYoprd]
     Ox86_CMOVcc [:: E 1] [:: E 0; E 2; E 1] [::] CMOVcc.
Proof.
  move=> ct [] // => [x | x] y; split => // gd m m';
  rewrite /low_sem_aux /= /= /eval_CMOVcc /eval_MOV /=.
  + t_xrbindP => ? ? ? h ? ? ? -> <- <- <-.
    case: eval_cond h => [ | [] // ] /=; last by case => <-.
    move => ? [] <-.
    case:ifP => ? -[<-] [<-];rewrite ?Hy //; (eexists; split; last by reflexivity);
    by rewrite /mem_write_reg /=; f_equal;rewrite -RegMap_set_id;case:(m).
  t_xrbindP => ??? h ? ? ? Hy <- ? ? ? Hx <- <- <- <-.
  case: eval_cond h => [ | [] // ] /=; last by case => <-.
  move => ? [] <- /=.
  case:ifP => ? -[<-].
  + rewrite /sets_low /= Hy /= => ->; eexists; split; reflexivity.
  rewrite /sets_low /= /mem_write_mem => {Hy}.
  case: m (decode_addr _ _) Hx => xmem xreg xrf /= a.
  move=> /write_mem_id -> //= ->; eexists; split; reflexivity.
Qed.

Definition CMOVcc_desc := make_instr_desc CMOVcc_gsc.

(* ----------------------------------------------------------------------------- *)

Ltac know_it :=
  refine (ex_intro _ _ (conj _ x86_mem_equiv_refl));
  repeat match goal with
  | H : _ = ?a |- _ = ?a => rewrite - H => { H }
  end.

Ltac update_set' :=
  by rewrite /sets_low /= /mem_update_rflags /mem_unset_rflags /mem_set_rflags
             /mem_write_reg /=;
     repeat f_equal; apply /ffunP; case; rewrite !ffunE.

Ltac update_set := know_it; update_set'.

Lemma ADD_gsc :
   gen_sem_correct [:: TYoprd; TYoprd] Ox86_ADD
     (implicit_flags ++ [:: E 0])
     [:: E 0; E 1] [::] ADD.
Proof.
  move=> [] // => [ x | x] y; split => // gd m m'; rewrite /low_sem_aux /= /eval_ADD /=.
  + t_xrbindP => vs ??? vy -> <- <- <- [<-] [<-]; update_set.
  t_xrbindP => vs ??? -> <- ?? vy -> <- <- <-[<-] /= h; update_set.
Qed.

Definition ADD_desc := make_instr_desc ADD_gsc.

(* ----------------------------------------------------------------------------- *)
Lemma SUB_gsc :
   gen_sem_correct [:: TYoprd; TYoprd] Ox86_SUB
      (implicit_flags ++ [:: E 0]) [:: E 0; E 1] [::] SUB.
Proof.
  move=> [] // => [ x | x] y; split => // gd m m'; rewrite /low_sem_aux /= /eval_SUB /=.
  + by t_xrbindP => vs ??? vy -> <- <- <- [<-] [<-]; update_set.
  by t_xrbindP => vs ??? -> <- ?? vy -> <- <- <- [<-] h /=; update_set.
Qed.

Definition SUB_desc := make_instr_desc SUB_gsc.

(* ----------------------------------------------------------------------------- *)
Lemma MUL_gsc :
  gen_sem_correct [:: TYoprd] Ox86_MUL
      (implicit_flags ++ [:: R RDX; R RAX])
      [:: R RAX; E 0] [::] MUL.
Proof.
  rewrite /gen_sem_correct /low_sem_aux /= /eval_MUL => x; split => // gd m m'.
  by t_xrbindP => vs ? ? ? vy -> <- <- <- /= [<-] [<-] /=; update_set.
Qed.

Definition MUL_desc := make_instr_desc MUL_gsc.

(* ----------------------------------------------------------------------------- *)
Lemma IMUL_gsc :
  gen_sem_correct [:: TYoprd ] Ox86_IMUL (implicit_flags ++ [:: R RDX; R RAX])
                   [:: R RAX; E 0] [::] (λ x, IMUL x None).
Proof.
  rewrite /gen_sem_correct /low_sem_aux /= => x; split => // gd m m'.
  by t_xrbindP => vs ? ? ? vy -> <- <- <- /= [<-] [<-] /=; update_set.
Qed.

Definition IMUL_desc   := make_instr_desc IMUL_gsc.

(* ----------------------------------------------------------------------------- *)
Lemma IMUL64_gsc :
  gen_sem_correct [:: TYoprd ; TYoprd] Ox86_IMUL64
                   (implicit_flags ++ [:: E 0]) [:: E 0; E 1] [::]
                   (λ x y, IMUL x (Some (y, None))).
Proof.
  rewrite /gen_sem_correct /low_sem_aux /=.
  case => // x y; split => // gd m m' /=.
  + t_xrbindP => vs ? ? ? vy -> <- <- <-.
    t_xrbindP => vx [<-] ? [<-] [<-] [<-] /=; update_set.
  t_xrbindP => vs ? ? ? -> <- ? ? ? -> <- <- <-.
  t_xrbindP => ? [<-] ? [<-] [<-] h.
  update_set.
Qed.

Definition IMUL64_desc := make_instr_desc IMUL64_gsc.

Lemma IMUL64imm_gsc :
  gen_sem_correct [:: TYoprd ; TYoprd ; TYimm] Ox86_IMUL64imm
                   (implicit_flags ++ [:: E 0]) [:: E 1; E 2] [::]
    (λ (x y : interp_ty TYoprd) (z : interp_ty TYimm), IMUL x (Some (y, Some z))).
Proof.
  rewrite /gen_sem_correct /low_sem_aux /=.
  case => // d x y; split => // gd m m' /=.
  + t_xrbindP => vs ? ? ? -> <- <-.
    t_xrbindP => ? [<-] ? [<-] [<-] [<-] /=; update_set.
  t_xrbindP => vs ? ? ? -> <- <-.
  t_xrbindP => ? [<-] ? [<-] [<-] h.
  update_set.
Qed.

Definition IMUL64imm_desc := make_instr_desc IMUL64imm_gsc.

(* ----------------------------------------------------------------------------- *)
Lemma DIV_gsc :
  gen_sem_correct [:: TYoprd] Ox86_DIV
      (implicit_flags ++ [:: R RAX; R RDX])
      [:: R RDX; R RAX; E 0] [::] DIV.
Proof.
  rewrite /gen_sem_correct /low_sem_aux /= /eval_DIV /x86_div => x; split => // gd m m'.
  t_xrbindP => vs ? ? ? ? vy -> <- <- <- <- /=.
  by case: ifPn => //= ? [<-] /= [<-]; update_set.
Qed.

Definition DIV_desc := make_instr_desc DIV_gsc.

(* ----------------------------------------------------------------------------- *)
Lemma IDIV_gsc :
  gen_sem_correct [:: TYoprd] Ox86_IDIV
      (implicit_flags ++ [:: R RAX; R RDX])
      [:: R RDX; R RAX; E 0] [::] IDIV.
Proof.
  rewrite /gen_sem_correct /low_sem_aux /= /eval_IDIV /x86_idiv => x; split => // gd m m'.
  t_xrbindP => vs ? ? ? ? vy -> <- <- <- <- /=.
  by case: ifPn => //= ? [<-] /= [<-]; update_set.
Qed.

Definition IDIV_desc := make_instr_desc IDIV_gsc.

(* ----------------------------------------------------------------------------- *)
Lemma ADC_gsc :
   gen_sem_correct [:: TYoprd; TYoprd] Ox86_ADC
       (implicit_flags ++ [:: E 0])
       [:: E 0; E 1; F CF] [::] ADC.
Proof.
  move=> [] // => [ x | x] y; split => // gd m m'; rewrite /low_sem_aux /= /eval_ADC /=.
  + t_xrbindP => vs ??? vy -> <- ? ? h <- <- <- /=.
    case: st_get_rflag h => [ ? | [] //] /=; last by case => <-.
    by move => [<-] [<-] [<-]; update_set.
  t_xrbindP => vs ??? -> <- ?? vy -> <- ? ? h <- <- <- /=.
  case: st_get_rflag h => [ ? | [] //] /=; last by case => <-.
  by move => [<-] [<-] h; update_set.
Qed.

Definition ADC_desc := make_instr_desc ADC_gsc.

(* ----------------------------------------------------------------------------- *)
Lemma SBB_gsc :
   gen_sem_correct [:: TYoprd; TYoprd] Ox86_SBB
       (implicit_flags ++ [:: E 0])
       [:: E 0; E 1; F CF] [::] SBB.
Proof.
  move=> [] // => [ x | x] y; split => // gd m m'; rewrite /low_sem_aux /= /eval_SBB /=.
  + t_xrbindP => vs ??? vy -> <- ? ? h <- <- <- /=.
    case: st_get_rflag h => [ ? | [] //] /=; last by case => <-.
    by move => [<-] [<-] [<-]; update_set.
  t_xrbindP => vs ??? -> <- ?? vy -> <- ? ? h <- <- <- /=.
  case: st_get_rflag h => [ ? | [] //] /=; last by case => <-.
  by move => [<-] [<-] h; update_set.
Qed.

Definition SBB_desc := make_instr_desc SBB_gsc.

(* ----------------------------------------------------------------------------- *)
Lemma NEG_gsc :
  gen_sem_correct [:: TYoprd] Ox86_NEG
     (implicit_flags ++ [:: E 0])
     [:: E 0] [::] NEG.
Proof.
  move=> [] // => [ x | x ] ; split => // gd m m';rewrite /low_sem_aux /= /eval_NEG /=.
  + by move=> [<-];update_set.
  t_xrbindP => ???? -> <- <- /= [<-] h;update_set.
Qed.

Definition NEG_desc := make_instr_desc NEG_gsc.

(* ----------------------------------------------------------------------------- *)
Lemma INC_gsc :
  gen_sem_correct [:: TYoprd] Ox86_INC
     (implicit_flags_noCF ++ [:: E 0])
     [:: E 0] [::] INC.
Proof.
  move=> [] // => [ x | x ] ; split => // gd m m'; rewrite /low_sem_aux /= /eval_INC /=.
  + by move=> [<-]; update_set.
  by t_xrbindP => ???? -> <- <- /= [<-] h; update_set.
Qed.

Definition INC_desc := make_instr_desc INC_gsc.

(* ----------------------------------------------------------------------------- *)
Lemma DEC_gsc :
  gen_sem_correct [:: TYoprd] Ox86_DEC
     (implicit_flags_noCF ++ [:: E 0])
     [:: E 0] [::] DEC.
Proof.
  move=> [] // => [ x | x ] ; split => // gd m m';rewrite /low_sem_aux /= /eval_DEC /=.
  + by move=> [<-]; update_set.
  by t_xrbindP => ???? -> <- <- /= [<-] h; update_set.
Qed.

Definition DEC_desc := make_instr_desc DEC_gsc.

(* ----------------------------------------------------------------------------- *)
Lemma SETcc_gsc :
  gen_sem_correct [:: TYcondt; TYoprd] Ox86_SETcc
     [:: E 1]
     [:: E 0] [::] SETcc.
Proof.
  by move=> ct [] // => [ x | x]; split => // gd m m';rewrite /low_sem_aux /= /eval_SETcc /=;
  t_xrbindP => ??? h <-;
  (case: eval_cond h => [ ? | [] // ]; last by case => <-);
  case => <- [<-] h /=; know_it.
Qed.

Definition SETcc_desc := make_instr_desc SETcc_gsc.

(* ----------------------------------------------------------------------------- *)
Lemma BT_gsc :
  gen_sem_correct [:: TYoprd; TYireg] Ox86_BT
     [:: F CF]
     [:: E 0; E 1] [::] BT.
Proof.
  by move => o [i|r]; split => // gd m m'; rewrite /low_sem_aux /= /eval_BT /x86_bt;
  t_xrbindP => b ? ? v -> <- <-; t_xrbindP => v' [<-] {v'} n [<-] <- [<-]; know_it.
Qed.

Definition BT_desc := make_instr_desc BT_gsc.

(* ----------------------------------------------------------------------------- *)

Definition scale_of_z z :=
  match z with
  | 1 => Scale1
  | 2 => Scale2
  | 4 => Scale4
  | 8 => Scale8
  | _ => Scale1
  end%Z.

Definition mk_LEA (dest:register) (disp:word) (base:ireg) (scale:word) (offset:ireg) :=
  let addr :=
    let (disp, base) :=
      match base with
      | Reg_ir r => (disp, Some r)
      | Imm_ir w => (I64.add disp w, None)
      end in
    let (disp, offset) :=
      match offset with
      | Reg_ir r => (disp, Some r)
      | Imm_ir w => (I64.add disp (I64.mul scale w), None)
      end in
    let scale := scale_of_z scale in
    {| ad_disp := disp; ad_base := base; ad_scale := scale; ad_offset := offset |} in
  LEA dest (Adr_op addr).

Lemma read_oprd_ireg gd y m :
  read_oprd gd match y with
               | Imm_ir i => Imm_op i
               | Reg_ir r => Reg_op r
               end m = ok (read_ireg y m).
Proof. by case: y => //. Qed.

Definition I64_rw := (I64.mul_zero, I64.add_zero, I64.repr_unsigned, I64.add_assoc, I64.add_zero_l).

Lemma check_scale_of (scale:word) : check_scale scale -> scale = scale_of_z scale.
Proof.
  move=> H;apply /ueqP;apply /eqP.
  by case /orP: H => [ /orP [ /orP [] /eqP -> | /eqP -> ] | /eqP ->].
Qed.

Lemma LEA_gsc :
  gen_sem_correct [:: TYreg; TYimm; TYireg; TYimm; TYireg] Ox86_LEA
     [:: E 0]
     [:: E 1; E 2; E 3; E 4] [::] mk_LEA.
Proof.
  rewrite /gen_sem_correct /= /low_sem_aux /= => x disp base scale offset; split => // gd m m'.
  rewrite !read_oprd_ireg.
  t_xrbindP => ????? Hbase <- ???? Hoffset <- <- <- <- <- /=.
  rewrite /x86_lea; case: ifP => // Hscale [<-] [<-]; rewrite /mk_LEA /eval_LEA.
  case: base offset Hbase Hoffset => [base | base] [offset | offset] /= <- <-; know_it;
    rewrite /decode_addr //=;do 2 f_equal; rewrite !I64_rw -?(check_scale_of Hscale) //.
  f_equal; apply I64.add_commut.
Qed.

Definition LEA_desc := make_instr_desc LEA_gsc.

(* ----------------------------------------------------------------------------- *)
Lemma TEST_gsc :
  gen_sem_correct [:: TYoprd; TYoprd] Ox86_TEST
     implicit_flags
     [:: E 0; E 1] [::] TEST.
Proof.
  move=> x y; split => // gd m m'; rewrite /low_sem_aux /= /eval_TEST.
  by t_xrbindP => ???? -> <- ??? -> <- <- <- [<-] [<-] /=; update_set.
Qed.

Definition TEST_desc := make_instr_desc TEST_gsc.

(* ----------------------------------------------------------------------------- *)
Lemma CMP_gsc :
  gen_sem_correct [:: TYoprd; TYoprd] Ox86_CMP
     implicit_flags
     [:: E 0; E 1] [::] CMP.
Proof.
  move=> x y ; split => // gd m m'; rewrite /low_sem_aux /= /eval_CMP.
  by t_xrbindP => ???? -> <- ??? -> <- <- <- [<-] [<-] /=; update_set.
Qed.

Definition CMP_desc := make_instr_desc CMP_gsc.

(* ----------------------------------------------------------------------------- *)
Lemma AND_gsc :
  gen_sem_correct [:: TYoprd; TYoprd] Ox86_AND
     (implicit_flags ++ [:: E 0])
     [:: E 0; E 1] [::] AND.
Proof.
  move=> [] // => [x | x] y; split => // gd m m'; rewrite /low_sem_aux /= /eval_AND /=.
  + by t_xrbindP => ????? -> <- <- <- [<-] [<-] /=; update_set.
  by t_xrbindP => ???? -> <- ??? -> <- <- <- [<-] h /=; update_set.
Qed.

Definition AND_desc := make_instr_desc AND_gsc.

(* ----------------------------------------------------------------------------- *)
Lemma OR_gsc :
  gen_sem_correct [:: TYoprd; TYoprd] Ox86_OR
     (implicit_flags ++ [:: E 0])
     [:: E 0; E 1] [::] OR.
Proof.
  move=> [] // => [x | x] y; split => // gd m m'; rewrite /low_sem_aux /= /eval_OR /=.
  + by t_xrbindP => ????? -> <- <- <- [<-] [<-] /=; update_set.
  by t_xrbindP => ???? -> <- ??? -> <- <- <- [<-] h /=; update_set.
Qed.

Definition OR_desc := make_instr_desc OR_gsc.

(* ----------------------------------------------------------------------------- *)
Lemma XOR_gsc :
  gen_sem_correct [:: TYoprd; TYoprd] Ox86_XOR
     (implicit_flags ++ [:: E 0])
     [:: E 0; E 1] [::] XOR.
Proof.
  move=> [] // => [x | x] y; split => // gd m m'; rewrite /low_sem_aux /= /eval_XOR /=.
  + by t_xrbindP => ????? -> <- <- <- [<-] [<-] /=; update_set.
  by t_xrbindP => ???? -> <- ??? -> <- <- <- [<-] h /=; update_set.
Qed.

Definition XOR_desc := make_instr_desc XOR_gsc.

(* ----------------------------------------------------------------------------- *)
Lemma NOT_gsc :
  gen_sem_correct [:: TYoprd] Ox86_NOT
     [:: E 0]
     [:: E 0] [::] NOT.
Proof.
  case => // [ x | x ]; split => // gd m m'; rewrite /low_sem_aux /= /eval_NOT /=.
  + by move => h; know_it.
  t_xrbindP => ???? -> <- <- [<-] h /=; update_set.
Qed.

Definition NOT_desc := make_instr_desc NOT_gsc.

(* ----------------------------------------------------------------------------- *)
Lemma decode_addr_unset_rflags m f addr:
  decode_addr (mem_unset_rflags f m) addr = decode_addr m addr.
Proof. done. Qed.

Lemma decode_addr_set_rflags m f b addr:
  decode_addr (mem_set_rflags f b m) addr = decode_addr m addr.
Proof. done. Qed.

Lemma decode_addr_update_rflags m f addr:
  decode_addr (mem_update_rflags f m) addr = decode_addr m addr.
Proof. done. Qed.

Instance rflagv_leb_refl : Reflexive rflagv_leb.
Proof. case => // b /=; exact: eqxx. Qed.

Instance rflagv_leb_trans : Transitive rflagv_leb.
Proof. case => // b y z /eqP -> /eqP ->; reflexivity. Qed.

Lemma rflagv_leb_undef rf f f' :
  rflagv_leb (RflagMap.oset rf f Undef f') (rf f').
Proof. rewrite ffunE; case: eqP => // _; reflexivity. Qed.

Lemma ROL_gsc :
  gen_sem_correct [:: TYoprd; TYireg ] Ox86_ROL
    [:: ADImplicit (var_of_flag OF) ; ADImplicit (var_of_flag CF) ; E 0 ]
    [:: E 0 ; ADExplicit 1 (Some RCX) ]
    [::] ROL.
Proof.
move => x [ y | y ]; split => // gd m m'; rewrite /low_sem_aux /= /eval_ROL /= /x86_rol /sets_low.
+ case: x => //= [ x | x ].
  - case: eqP => hy /=.
    * case => <-; eexists; split; first reflexivity.
      constructor => //=; first by rewrite -RegMap_set_id.
      by move => f; etransitivity; apply/rflagv_leb_undef.
    case: eqP => hy' h; update_set.
  t_xrbindP => ??? w hw <- <- /=.
  case: ifP => hy [<-] /=.
  - rewrite /mem_write_mem write_mem_id //= hw => -[<-] /=.
    eexists; split; first reflexivity.
    constructor => //.
    by move => f; etransitivity; apply/rflagv_leb_undef.
  case: eqP => hy' h; rewrite hw /=; update_set.
case: eqP => // <- {y} /=.
(* Same as above *)
+ case: x => //= [ x | x ].
  - case: eqP => hy /=.
    * case => <-; eexists; split; first reflexivity.
      constructor => //=; first by rewrite -RegMap_set_id.
      by move => f; etransitivity; apply/rflagv_leb_undef.
    case: eqP => hy' h; update_set.
  t_xrbindP => ??? w hw <- <- /=.
  case: ifP => hy [<-] /=.
  - rewrite /mem_write_mem write_mem_id //= hw => -[<-] /=.
    eexists; split; first reflexivity.
    constructor => //.
    by move => f; etransitivity; apply/rflagv_leb_undef.
  case: eqP => hy' h; rewrite hw /=; update_set.
Qed.

Definition ROL_desc := make_instr_desc ROL_gsc.

Lemma ROR_gsc :
  gen_sem_correct [:: TYoprd; TYireg ] Ox86_ROR
    [:: ADImplicit (var_of_flag OF) ; ADImplicit (var_of_flag CF) ; E 0 ]
    [:: E 0 ; ADExplicit 1 (Some RCX) ]
    [::] ROR.
Proof.
move => x [ y | y ]; split => // gd m m'; rewrite /low_sem_aux /= /eval_ROR /= /x86_ror /sets_low.
+ case: x => //= [ x | x ].
  - case: eqP => hy /=.
    * case => <-; eexists; split; first reflexivity.
      constructor => //=; first by rewrite -RegMap_set_id.
      by move => f; etransitivity; apply/rflagv_leb_undef.
    case: eqP => hy' h; update_set.
  t_xrbindP => ??? w hw <- <- /=.
  case: ifP => hy [<-] /=.
  - rewrite /mem_write_mem write_mem_id //= hw => -[<-] /=.
    eexists; split; first reflexivity.
    constructor => //.
    by move => f; etransitivity; apply/rflagv_leb_undef.
  case: eqP => hy' h; rewrite hw /=; update_set.
case: eqP => // <- {y} /=.
(* Same as above *)
+ case: x => //= [ x | x ].
  - case: eqP => hy /=.
    * case => <-; eexists; split; first reflexivity.
      constructor => //=; first by rewrite -RegMap_set_id.
      by move => f; etransitivity; apply/rflagv_leb_undef.
    case: eqP => hy' h; update_set.
  t_xrbindP => ??? w hw <- <- /=.
  case: ifP => hy [<-] /=.
  - rewrite /mem_write_mem write_mem_id //= hw => -[<-] /=.
    eexists; split; first reflexivity.
    constructor => //.
    by move => f; etransitivity; apply/rflagv_leb_undef.
  case: eqP => hy' h; rewrite hw /=; update_set.
Qed.

Definition ROR_desc := make_instr_desc ROR_gsc.

Lemma SHL_gsc :
  gen_sem_correct [:: TYoprd; TYireg] Ox86_SHL
     (implicit_flags ++ [:: E 0])
     [:: E 0; E 1] [::] SHL.
Proof.
  move=> [] // => [x | x] y;split => // gd m m'; rewrite /low_sem_aux /= /eval_SHL /x86_shl /=.
  + t_xrbindP => ???? vy;rewrite read_oprd_ireg => -[->] <- <- <- /=.
    rewrite /rflags_of_sh /sets_low.
    case: ifP => Heq [<-] /=.
    + rewrite /mem_write_reg;case:m => ??? /= h.
      by know_it; rewrite -RegMap_set_id; update_set'.
    by case:ifPn => [/eqP | ] Hvy /= h; update_set.
  t_xrbindP => ???? Hread <- ???;rewrite Hread.
  rewrite read_oprd_ireg => -[<-] <- <- <- /= H.
  rewrite decode_addr_update_rflags.
  rewrite /sets_low /=; case:ifP H => Heq [<-] /=;rewrite /mem_write_mem /=.
  + by rewrite !decode_addr_unset_rflags write_mem_id //= => h;update_set.
  by rewrite /rflags_of_sh; case: ifP => ? /=;
    rewrite /mem_write_mem /= !decode_addr_set_rflags;
    case: Memory.write_mem => //= mem h; update_set.
Qed.

Definition SHL_desc := make_instr_desc SHL_gsc.

(* ----------------------------------------------------------------------------- *)
Lemma SHR_gsc :
  gen_sem_correct [:: TYoprd; TYireg] Ox86_SHR
     (implicit_flags ++ [:: E 0])
     [:: E 0; E 1] [::] SHR.
Proof.
  move=> [] // => [x | x] y;split => // gd m m'; rewrite /low_sem_aux /= /eval_SHR /x86_shr /=.
  + t_xrbindP => ???? vy;rewrite read_oprd_ireg => -[->] <- <- <- /=.
    rewrite /rflags_of_sh /sets_low.
    case: ifP => Heq [<-] /=.
    + rewrite /mem_write_reg;case:m => ??? /= h.
      by know_it; rewrite -RegMap_set_id; update_set'.
    by case:ifPn => [/eqP | ] Hvy /= h; update_set.
  t_xrbindP => ???? Hread <- ???;rewrite Hread.
  rewrite read_oprd_ireg => -[<-] <- <- <- /= H.
  rewrite decode_addr_update_rflags.
  rewrite /sets_low /=; case:ifP H => Heq [<-] /=;rewrite /mem_write_mem /=.
  + by rewrite !decode_addr_unset_rflags write_mem_id //= => h;update_set.
  by rewrite /rflags_of_sh; case: ifP => ? /=;
    rewrite /mem_write_mem /= !decode_addr_set_rflags;
    case: Memory.write_mem => //= mem h; update_set.
Qed.

Definition SHR_desc := make_instr_desc SHR_gsc.

(* ----------------------------------------------------------------------------- *)
Lemma SAR_gsc :
  gen_sem_correct [:: TYoprd; TYireg] Ox86_SAR
     (implicit_flags ++ [:: E 0])
     [:: E 0; E 1] [::] SAR.
Proof.
  move=> [] // => [x | x] y;split => // gd m m'; rewrite /low_sem_aux /= /eval_SAR /x86_sar /=.
  + t_xrbindP => ???? vy;rewrite read_oprd_ireg => -[->] <- <- <- /=.
    rewrite /rflags_of_sh /sets_low.
    case: ifP => Heq [<-] /=.
    + rewrite /mem_write_reg;case:m => ??? /= h.
      by know_it; rewrite -RegMap_set_id; update_set'.
    by case:ifPn => [/eqP | ] Hvy /= h; update_set.
  t_xrbindP => ???? Hread <- ???;rewrite Hread.
  rewrite read_oprd_ireg => -[<-] <- <- <- /= H.
  rewrite decode_addr_update_rflags.
  rewrite /sets_low /=; case:ifP H => Heq [<-] /=;rewrite /mem_write_mem /=.
  + by rewrite !decode_addr_unset_rflags write_mem_id //= => h;update_set.
  by rewrite /rflags_of_sh; case: ifP => ? /=;
    rewrite /mem_write_mem /= !decode_addr_set_rflags;
    case: Memory.write_mem => //= mem h; update_set.
Qed.

Definition SAR_desc := make_instr_desc SAR_gsc.

(* ----------------------------------------------------------------------------- *)
Lemma SHLD_gsc :
  gen_sem_correct [:: TYoprd; TYreg; TYireg] Ox86_SHLD
     (implicit_flags ++ [:: E 0])
     [:: E 0; E 1; E 2] [::] SHLD.
Proof.
  move=> [] // => [x | x] y;split => // gd m m'; rewrite /low_sem_aux /= /eval_SHLD /x86_shld /=.
  + t_xrbindP => ????? vy;rewrite read_oprd_ireg => -[->] <- <- <- <- /=.
    rewrite /rflags_of_sh /sets_low.
    case: ifP => Heq [<-] /=.
    + rewrite /mem_write_reg;case:m => ??? /= h.
      by know_it; rewrite -RegMap_set_id; update_set'.
    by case:ifPn => [/eqP | ] Hvy /= h; update_set.
  t_xrbindP => ???? Hread <- ????;rewrite Hread.
  rewrite read_oprd_ireg => -[<-] <- <- <- <- /= H.
  rewrite decode_addr_update_rflags.
  rewrite /sets_low /=; case:ifP H => Heq [<-] /=;rewrite /mem_write_mem /=.
  + by rewrite !decode_addr_unset_rflags write_mem_id //= => h;update_set.
  by rewrite /rflags_of_sh; case: ifP => ? /=;
    rewrite /mem_write_mem /= !decode_addr_set_rflags;
    case: Memory.write_mem => //= mem h; update_set.
Qed.

Definition SHLD_desc := make_instr_desc SHLD_gsc.

(* ----------------------------------------------------------------------------- *)
Lemma Set0_gsc :
  gen_sem_correct [:: TYoprd] Oset0
     (implicit_flags ++ [:: E 0])
     [::] [::] (fun x => XOR x x).
Proof.
  move=> []// => [x|x]; split => // gd m m'; rewrite /low_sem_aux /= /eval_XOR /=.
  + move=> [<-]; rewrite I64.xor_idem; update_set.
  rewrite /sets_low /= /decode_addr /=;set addr := I64.add _ _.
  rewrite /mem_write_mem; t_xrbindP => m1 /= Hw <-.
  have : Memory.valid_addr (xmem m) addr.
  + apply /Memory.writeV;eauto.
  move=> /Memory.readV [v ->] /=;rewrite I64.xor_idem Hw /=; update_set.
Qed.

Definition Set0_desc := make_instr_desc Set0_gsc.

(* ----------------------------------------------------------------------------- *)

Definition sopn_desc ii (c : sopn) : ciexec instr_desc :=
  match c with
  | Omulu | Oaddcarry | Osubcarry => cierror ii (Cerr_assembler (AsmErr_string "sopn_desc"))
  | Oset0 => ok Set0_desc
  | Ox86_MOV     => ok MOV_desc
  | Ox86_CMOVcc  => ok CMOVcc_desc
  | Ox86_ADD     => ok ADD_desc
  | Ox86_SUB     => ok SUB_desc
  | Ox86_MUL     => ok MUL_desc
  | Ox86_IMUL    => ok IMUL_desc
  | Ox86_IMUL64  => ok IMUL64_desc
  | Ox86_IMUL64imm  => ok IMUL64imm_desc
  | Ox86_DIV     => ok DIV_desc
  | Ox86_IDIV    => ok IDIV_desc
  | Ox86_ADC     => ok ADC_desc
  | Ox86_SBB     => ok SBB_desc
  | Ox86_NEG     => ok NEG_desc
  | Ox86_INC     => ok INC_desc
  | Ox86_DEC     => ok DEC_desc
  | Ox86_SETcc   => ok SETcc_desc
  | Ox86_BT   => ok BT_desc
  | Ox86_LEA     => ok LEA_desc
  | Ox86_TEST    => ok TEST_desc
  | Ox86_CMP     => ok CMP_desc
  | Ox86_AND     => ok AND_desc
  | Ox86_OR      => ok OR_desc
  | Ox86_XOR     => ok XOR_desc
  | Ox86_NOT     => ok NOT_desc
  | Ox86_ROL => ok ROL_desc
  | Ox86_ROR => ok ROR_desc
  | Ox86_SHL     => ok SHL_desc
  | Ox86_SHR     => ok SHR_desc
  | Ox86_SAR     => ok SAR_desc
  | Ox86_SHLD    => ok SHLD_desc
  end.

Lemma sopn_desc_name ii o d : sopn_desc ii o = ok d -> d.(id_name) = o.
Proof. by case: o => //= -[<-]. Qed.

(* ----------------------------------------------------------------------------- *)
Definition assemble_sopn (ii: instr_info) (out: lvals) (op: sopn) (args: pexprs) : ciexec asm :=
  Let d := sopn_desc ii op in
  Let hiargs := compile_hi_sopn ii d out args in
  Let loargs := compile_low_args ii (id_tys d) hiargs in
  typed_apply_gargs ii loargs (id_instr d).

Lemma type_apply_gargP ty T ii ga (iasm:interp_ty ty → T) ins: 
   typed_apply_garg ii ga iasm = ok ins ->
   ∃ x' : interp_ty ty, ga = mk_garg x' ∧ ins = iasm x'. 
Proof.
  case: ty iasm => //=; case: ga => //.
  + by move => c i' [<-]; eauto.
  + by move => o i' [<-]; eauto.
  + by case => // r i' [<-]; eauto.
  + case => // a i' [<-].
    + by exists (Imm_ir a).
    by exists (Reg_ir a).
  by case => // w i' [<-]; eauto.
Qed.

Lemma assemble_sopn_is_sopn ii out op args i :
  assemble_sopn ii out op args = ok i →
  is_sopn i.
Proof.
  rewrite /assemble_sopn.
  t_xrbindP => id _ iargs _ gargs _. 
  have := id_gen_sem id; move: [::].
  elim: (id_tys id) (id_in id) (id_out id) (id_instr id) gargs =>
     [ | ty tys ih] /= iin iout iasm [ | ga gargs] //= gargs'. 
  + by move=> [? ?] [<-].
  move=> hgen;t_xrbindP => ins Ha.
  apply (ih iin iout ins gargs (gargs' ++ [::ga])).
  by have [x' [-> ->]]:= type_apply_gargP Ha.
Qed.

Lemma lom_eqv_mem_equiv_trans s m1 m2 :
  lom_eqv s m1 →
  x86_mem_equiv m1 m2 →
  lom_eqv s m2.
Proof.
case: m1 m2 => m1 rg1 rf1 [] m2 rg2 rf2 [] /= ? hrg1 hrf1 [] /= <- <- hrf2.
constructor => //= f v hv.
move: (hrf1 f v hv) (hrf2 f) => {hv}.
case: (rf1 _) v => [ b | ] [] //=.
- by move => ? <- /eqP ->.
- by move => ? /eqP -> /eqP ->.
by move => ? /eqP -> _; case: (rf2 _).
Qed.

Theorem assemble_sopnP gd ii out op args i s1 m1 s2 :
  lom_eqv s1 m1 →
  assemble_sopn ii out op args = ok i →
  sem_sopn gd op s1 out args = ok s2 →
  ∃ m2,
    eval_instr_mem gd i m1 = ok m2
    ∧ lom_eqv s2 m2.
Proof.
  rewrite /assemble_sopn.
  t_xrbindP => eqm id hid hiargs ok_hi loargs ok_lo ok_i h.
  have hm := compile_hi_sopnP (sopn_desc_name hid) ok_hi h.
  have [m2 [ok_m2 hm2]] := mixed_to_low eqm ok_lo hm.
  suff : ∃ m0, eval_instr_mem gd i m1 = ok m0 ∧ x86_mem_equiv m2 m0.
  - case => m0 [hm0 eqm0].
    exists m0; split => //; exact: (lom_eqv_mem_equiv_trans hm2 eqm0).
  have := id_gen_sem id.
  move: ok_m2 => {h hid op ok_hi ok_lo eqm s1 s2 hm hm2}; rewrite /low_sem.
  rewrite -(cat0s loargs); move: [::] loargs ok_i.
  elim: (id_tys id) (id_in id) (id_out id) (id_name id) (id_instr id).
  - move => ins outs op i'.
    by move => acc [] // - [->] {i'} /=; rewrite cats0 => h [] _ /(_ gd m1 m2 h).
  move => ty tys ih ins outs op i' acc [] // g loargs /=; t_xrbindP => x ok_x hi /= h.
  have := ih ins outs op _ (acc ++ [:: g]) loargs hi.
  rewrite -catA => /(_ h) rec x0; apply: rec.
  by have [x' [-> ->]]:= type_apply_gargP ok_x.
Qed.
