From Coq Require Import Relations.
From Coq Require Import Psatz.
From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp.word Require Import ssrZ.

Require Import oseq.

Require Import
  arch_params_proof
  compiler_util
  expr
  fexpr
  fexpr_sem
  psem
  psem_facts
  sem_one_varmap.
Require Import
  linearization
  linearization_proof
  lowering
  propagate_inline_proof
  stack_alloc
  stack_alloc_proof.
Require
  arch_sem.
Require Import
  arch_decl
  arch_extra
  asm_gen
  asm_gen_proof
  sem_params_of_arch_extra.
Require Import
  arm_decl
  arm_extra
  arm_instr_decl
  arm_lowering
  arm_lowering_proof.
Require Export arm_params.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Lemma vmap_eq_except_wf_vm vm vm' x v :
  wf_vm vm
  -> vm' = vm [\ Sv.singleton x ]
  -> get_var vm' x = ok v
  -> wf_vm vm'.
Proof.
  move=> hwf_vm hvm' hgetx.
  move=> y.
  case: (x =P y) => hy.
  - subst y. move: hgetx. rewrite /get_var. by case: vm'.[x]%vmap => [|[]].
  rewrite hvm'; first by apply: hwf_vm.
  exact: (Sv_neq_not_in_singleton hy).
Qed.


Section Section.

Context
  {syscall_state : Type}
  {sc_sem : syscall_sem syscall_state}
  {call_conv : calling_convention}.

(* ------------------------------------------------------------------------ *)
(* Flag combination hypotheses. *)

Lemma arm_cf_xsemP gd s e0 e1 e2 e3 cf v :
  let: e := PappN (Ocombine_flags cf) [:: e0; e1; e2; e3 ] in
  let: e' := cf_xsem enot eand eor expr.eeq e0 e1 e2 e3 cf in
  sem_pexpr gd s e = ok v
  -> sem_pexpr gd s e' = ok v.
Proof.
  rewrite /=.

  t_xrbindP=> vs0 v0 hv0 vs1 v1 hv1 vs2 v2 hv2 vs3 v3 hv3 ? ? ? ?;
    subst vs0 vs1 vs2 vs3.
  rewrite /sem_opN /=.
  t_xrbindP=> b b0 hb0 b1 hb1 b2 hb2 b3 hb3 hb ?; subst v.
  move: hb0 => /to_boolI ?; subst v0.
  move: hb1 => /to_boolI ?; subst v1.
  move: hb2 => /to_boolI ?; subst v2.
  move: hb3 => /to_boolI ?; subst v3.

  move: hb.
  rewrite /sem_combine_flags.
  rewrite /cf_xsem.

  case: cf_tbl => -[] [] [?] /=; subst b.
  all: by rewrite ?hv0 ?hv1 ?hv2 ?hv3.
Qed.

Definition arm_hpiparams : h_propagate_inline_params :=
  {|
    pip_cf_xsemP := arm_cf_xsemP;
  |}.

(* ------------------------------------------------------------------------ *)
(* Stack alloc hypotheses. *)

Section STACK_ALLOC.

Context
  (P' : sprog)
  (P'_globs : p_globs P' = [::]).

End STACK_ALLOC.

Lemma arm_mov_ofsP (P': sprog) s1 e i x tag ofs w vpk s2 ins :
  p_globs P' = [::]
  -> (Let i' := sem_pexpr [::] s1 e in to_pointer i') = ok i
  -> sap_mov_ofs arm_saparams x tag vpk e ofs = Some ins
  -> write_lval [::] x (Vword (i + wrepr Uptr ofs)) s1 = ok s2
  -> psem.sem_i (pT := progStack) P' w s1 ins s2.
Proof.
  move=> P'_globs he [?] hx; subst ins.
  constructor.
  rewrite /sem_sopn /=.
  rewrite P'_globs.
  rewrite /exec_sopn /=.
  move: he.
  t_xrbindP=> ? -> /= -> /=.
  rewrite zero_extend_u.
  by rewrite hx.
Qed.

Definition arm_hsaparams is_regx :
  h_stack_alloc_params (ap_sap arm_params is_regx) :=
  {|
    mov_ofsP := arm_mov_ofsP;
  |}.


(* ------------------------------------------------------------------------ *)
(* Linearization hypotheses. *)

Section LINEARIZATION.

Section ARM_OP.

(* Linear state after executing a linear instruction [Lopn]. *)
Notation next_ls ls m vm :=
  {|
    lscs := lscs ls;
    lmem := m;
    lvm := vm;
    lfn := lfn ls;
    lpc := lpc ls + 1;
  |}
  (only parsing).

Notation next_vm_ls ls vm := (next_ls ls (lmem ls) vm) (only parsing).
Notation next_mem_ls ls m := (next_ls ls m (lvm ls)) (only parsing).

Context
  (xname : Ident.ident)
  (vi : var_info).

Notation x :=
  {|
    v_var := {| vname := xname; vtype := sword reg_size; |};
    v_info := vi;
  |}.

(* Try to rewrite and clear all equalities in the context. *)
Ltac t_rewrite_eqs :=
  repeat
    match goal with
    | [ h : _ = _ |- _ ] => rewrite !h /=; clear h
    end.

(* Most ARM instructions with default options are executed as follows:
   1. Unfold instruction execution definitions, e.g. [eval_instr].
   2. Rewrite argument hypotheses, i.e. [sem_pexpr].
   3. Unfold casting definitions in result, e.g. [zero_extend] and
      [pword_of_word].
   4. Rewrite result hypotheses, i.e. [write_lval].
 *)
Ltac t_arm_op :=
  rewrite /eval_instr /= /sem_sopn /= /get_gvar /=;
  t_rewrite_eqs;
  rewrite /of_estate /= /with_vm /=;
  rewrite ?zero_extend_u ?pword_of_wordE;
  t_rewrite_eqs.

Lemma arm_op_subi_eval_instr lp ls ii y imm wy :
  get_var (lvm ls) (v_var y) = ok (Vword wy)
  -> let: li := li_of_copn_args ii (arm_op_subi x y imm) in
     let: wx' := (wy - wrepr reg_size imm)%R in
     let: vm' := (lvm ls).[v_var x <- ok (pword_of_word wx')]%vmap in
     eval_instr lp li ls = ok (next_vm_ls ls vm').
Proof. move=> hgety. t_arm_op. by rewrite wsub_wnot1 addn1. Qed.

Lemma arm_op_align_eval_instr lp ls ii y al wy :
  get_var (lvm ls) (v_var y) = ok (Vword wy)
  -> let: li := li_of_copn_args ii (arm_op_align x y al) in
     let: wx' := align_word al wy in
     let: vm' := (lvm ls).[v_var x <- ok (pword_of_word wx')]%vmap in
     eval_instr lp li ls = ok (next_vm_ls ls vm').
Proof. move=> hgety. t_arm_op. by rewrite addn1. Qed.

Lemma arm_op_mov_eval_instr lp ls ii y wy :
  get_var (lvm ls) (v_var y) = ok (Vword wy)
  -> let: li := li_of_copn_args ii (arm_op_mov x y) in
     let: vm' := (lvm ls).[v_var x <- ok (pword_of_word wy)]%vmap in
     eval_instr lp li ls = ok (next_vm_ls ls vm').
Proof. move=> hgety. t_arm_op. by rewrite addn1. Qed.

Lemma arm_op_str_off_eval_instr lp ls m' ii y off wx (wy : word reg_size) :
  get_var (lvm ls) (v_var x) = ok (Vword wx)
  -> get_var (lvm ls) (v_var y) = ok (Vword wy)
  -> write (lmem ls) (wx + wrepr Uptr off)%R wy = ok m'
  -> let: li := li_of_copn_args ii (arm_op_str_off y x off) in
     eval_instr lp li ls = ok (next_mem_ls ls m').
Proof. move=> hgety hgetx hwrite. t_arm_op. by rewrite addn1. Qed.

End ARM_OP.

Lemma wbit_n_add_aux x y z :
  (0 < x)%Z
  -> (y < x)%Z
  -> (z < x)%Z
  -> (x * y + z < x * x)%Z.
Proof. nia. Qed.

Lemma wbit_n_add ws n lbs hbs (i : nat) :
  let: n2 := (2 ^ n)%Z in
  (n2 * n2 <= wbase ws)%Z
  -> (0 <= lbs < n2)%Z
  -> (0 <= hbs < n2)%Z
  -> let b :=
       if (i <? n)%Z
       then wbit_n (wrepr ws lbs) i
       else wbit_n (wrepr ws hbs) (i - Z.to_nat n)
     in
     wbit_n (wrepr ws (2 ^ n * hbs + lbs)) i = b.
Proof.
  move=> hn hlbs hhbs.

  have h0i : (0 <= i)%Z.
  - exact: Zle_0_nat.

  have h0n : (0 <= n)%Z.
  - case: (Z.le_gt_cases 0 n) => h; first done.
    rewrite (Z.pow_neg_r _ _  h) in hlbs.
    lia.

  have hrange : (0 <= 2 ^ n * hbs + lbs < wbase ws)%Z.
  - split; first lia.
    apply: (Z.lt_le_trans _ _ _ _ hn).
    apply: wbit_n_add_aux; lia.

  case: ZltP => hi /=.

  all: rewrite wbit_nE.
  all: rewrite (wunsigned_repr_small hrange).

  - rewrite -(Zplus_minus i n).
    rewrite Z.pow_add_r; last lia; last done.
    rewrite Z.add_comm -Z.mul_assoc Z.mul_comm.
    rewrite Z_div_plus; first last.
    + apply/Z.lt_gt. by apply: Z.pow_pos_nonneg.

    rewrite Z.odd_add.
    rewrite Z_odd_pow_2; last lia.
    rewrite Bool.xorb_false_r.

    rewrite wbit_nE.
    rewrite wunsigned_repr_small; first done.
    lia.

  rewrite -(Zplus_minus n i).
  rewrite (Z.pow_add_r _ _ _ h0n); last lia.
  rewrite -Z.div_div; last lia; last lia.
  rewrite Z.add_comm Z.mul_comm.
  rewrite Z_div_plus; last lia.
  rewrite (Zdiv_small _ _ hlbs) /=.

  rewrite wbit_nE.
  rewrite wunsigned_repr_small; first last.
  - split; first lia.
    apply: (Z.lt_le_trans _ _ _ _ hn).
    rewrite -Z.pow_twice_r.
    apply: (Z.lt_le_trans _ (2 ^ n)); first lia.
    apply: Z.pow_le_mono_r; lia.

  rewrite int_of_Z_PoszE.
  rewrite Nat2Z.n2zB; first by rewrite Z2Nat.id.
  apply/ZNleP.
  rewrite (Z2Nat.id _ h0n).
  by apply/Z.nlt_ge.
Qed.

Lemma mov_movt_aux n x y :
  (0 < n)%Z
  -> (0 <= y < n)%Z
  -> (0 <= n * x + y < n * n)%Z
  -> (0 <= x < n)%Z.
Proof. nia. Qed.

Lemma mov_movt n hbs lbs :
  (0 <= n < wbase reg_size)%Z
  -> Z.div_eucl n (wbase U16) = (hbs, lbs)
  -> let: h := wshl (zero_extend U32 (wrepr U16 hbs)) 16 in
     let: l := wand (wrepr U32 lbs) (zero_extend U32 (wrepr U16 (-1))) in
     wor h l = wrepr U32 n.
Proof.
  move=> hn.

  have := Z_div_mod n (wbase U16) (wbase_pos U16).
  case: Z.div_eucl => [h l] [? hlbs] [? ?]; subst n h l.

  rewrite wshl_sem; last done.
  rewrite (wand_small hlbs).
  rewrite -wrepr_mul.

  have hhbs : (0 <= hbs < wbase U16)%Z.
  - exact: (mov_movt_aux _ hlbs hn).

  rewrite (wunsigned_repr_small hhbs).
  Opaque Z.pow.
  rewrite wbaseE /=.

  apply/eqP/eq_from_wbit_n.
  move=> [i hrangei] /=.
  rewrite worE.

  rewrite wbit_n_add; first last.
  - by rewrite wbaseE /= in hhbs.
  - by rewrite wbaseE /= in hlbs.
  - done.

  case: ZltP => h.

  - rewrite wbit_lower_bits_0 /=; first done.
    + by have := Zle_0_nat i.
    rewrite wbaseE /= in hn.
    lia.

  rewrite (wbit_higher_bits_0 (n := 16) _ hlbs); first last.
  - split; last by apply/ZNltP. by apply/Z.nlt_ge.
  - done.

  rewrite orbF.
  rewrite wbit_pow_2; first done; first done.
  move: h => /Z.nlt_ge h.
  apply/andP.
  split.
  - apply/ZNleP. by rewrite Z2Nat.id.

  by apply: ltnSE.
Qed.

Lemma arm_cmd_load_large_imm_lsem lp fn s ii P Q xname imm :
  let: x := {| vname := xname; vtype := sword reg_size; |} in
  let: xi := {| v_var := x; v_info := dummy_var_info; |} in
  let: lcmd := map (li_of_copn_args ii) (arm_cmd_load_large_imm xi imm) in
  is_linear_of lp fn (P ++ lcmd ++ Q)
  -> (0 <= imm < wbase reg_size)%Z
  -> exists vm',
       let: ls := of_estate s fn (size P) in
       let: ls' :=
         {|
           lscs := lscs ls;
           lmem := lmem ls;
           lvm := vm';
           lfn := fn;
           lpc := size P + size lcmd;
         |}
       in
       [/\ lsem lp ls ls'
         , vm' = lvm ls [\ Sv.singleton x ]
         & get_var vm' x = ok (Vword (wrepr reg_size imm))
       ].
Proof.
  set x := {| v_var := _; |}.
  rewrite /arm_cmd_load_large_imm /=.

  case hdivmod: Z.div_eucl => [hbs lbs] /=.
  move=> hbody himm.

  eexists.
  split.
  - apply: lsem_step2; rewrite /lsem1 /step /of_estate.
    + rewrite -(addn0 (size P)).
      rewrite (find_instr_skip hbody) /=.
      rewrite /eval_instr /= /with_vm /= /of_estate /=.
      rewrite zero_extend_u pword_of_wordE addn0.
      reflexivity.

    rewrite -addn1.
    rewrite (find_instr_skip hbody) /=.
    rewrite /eval_instr /=.
    rewrite /sem_sopn /= /get_gvar /=.
    rewrite get_var_eq /=.
    rewrite /with_vm /= /of_estate /=.
    rewrite !zero_extend_u.
    rewrite (mov_movt himm hdivmod).
    rewrite pword_of_wordE.
    rewrite addn1 -addn2.
    reflexivity.

  - move=> v hv. move: hv => /Sv.singleton_spec ?. by t_vm_get.

  by t_get_var.
Qed.

Lemma arm_cmd_large_subi_lsem lp fn s ii P Q xname y imm wy :
  let: x := {| vname := xname; vtype := sword Uptr; |} in
  let: xi := {| v_var := x; v_info := dummy_var_info; |} in
  let: lcmd := map (li_of_copn_args ii) (arm_cmd_large_subi xi y imm) in
  is_linear_of lp fn (P ++ lcmd ++ Q)
  -> x <> v_var y
  -> get_var (evm s) (v_var y) = ok (Vword wy)
  -> (0 <= imm < wbase reg_size)%Z
  -> exists vm',
       let: ls := of_estate s fn (size P) in
       let: ls' :=
         {|
           lscs := lscs ls;
           lmem := lmem ls;
           lvm := vm';
           lfn := fn;
           lpc := size P + size lcmd;
         |}
       in
       [/\ lsem lp ls ls'
         , vm' = evm s [\ Sv.singleton x ]
         & get_var vm' x = ok (Vword (wy - wrepr reg_size imm)%R)
       ].
Proof.
  set x := {| v_var := _; |}.
  move=> hbody hxy hgety himm.

  move: hbody.
  rewrite /arm_cmd_large_subi /=.
  rewrite /arm_cmd_large_arith_imm /=.
  rewrite map_cat.
  rewrite -(catA _ _ Q).
  move=> hbody.

  have [vm' [hsem hvm hgetx]] := arm_cmd_load_large_imm_lsem s hbody himm.

  eexists.
  split.
  - apply: (lsem_trans hsem).
    rewrite /of_estate /= -/x.
    apply: LSem_step.
    rewrite /lsem1 /step /=.

    rewrite catA in hbody.
    rewrite -!size_cat.
    rewrite -(addn0 (size _)).
    rewrite (find_instr_skip hbody) /=.

    have {hgety} hgety :
      get_var vm' y = ok (Vword wy).
    + rewrite (get_var_eq_except _ hvm) /=; first exact: hgety.
      exact: (Sv_neq_not_in_singleton hxy).

    rewrite /eval_instr /=.
    rewrite /sem_sopn /=.
    rewrite /get_gvar /=.
    rewrite hgetx hgety {hgetx hgety} /=.
    rewrite pword_of_wordE !zero_extend_u.
    rewrite /of_estate /with_vm /=.
    rewrite wsub_wnot1.
    rewrite !size_cat addn0 -addn1 addnA /=.
    reflexivity.

  - move=> z hz.
    rewrite Fv.setP_neq.
    + rewrite -(hvm z hz) /=; first done.
    apply/eqP.
    SvD.fsetdec.

  by t_get_var.
Qed.

Context
  (lp : lprog)
  (sp_rsp : Ident.ident)
  (fn : funname).

Let vrsp : var := mk_ptr sp_rsp.
Let vrspi : var_i := VarI vrsp dummy_var_info.
Let vtmp : var := mk_ptr (lip_tmp arm_liparams).
Let vtmpi : var_i := VarI vtmp dummy_var_info.

Lemma arm_spec_lip_allocate_stack_frame s pc ii ts sz :
  let args := lip_allocate_stack_frame arm_liparams vrspi sz in
  let i := MkLI ii (Lopn args.1.1 args.1.2 args.2) in
  let ts' := pword_of_word (ts - wrepr Uptr sz) in
  let s' := with_vm s (evm s).[vrsp <- ok ts']%vmap in
  (evm s).[vrsp]%vmap = ok (pword_of_word ts)
  -> eval_instr lp i (of_estate s fn pc)
     = ok (of_estate s' fn pc.+1).
Proof.
  move=> /= hvm.
  rewrite /eval_instr /=.
  rewrite /sem_sopn /=.
  rewrite /get_gvar /get_var /on_vu /=.
  rewrite hvm /=.
  rewrite pword_of_wordE.
  rewrite wsub_wnot1.
  by rewrite zero_extend_u zero_extend_wrepr.
Qed.

Lemma arm_spec_lip_free_stack_frame s pc ii ts sz :
  let args := lip_free_stack_frame arm_liparams vrspi sz in
  let i := MkLI ii (Lopn args.1.1 args.1.2 args.2) in
  let ts' := pword_of_word (ts + wrepr Uptr sz) in
  let s' := with_vm s (evm s).[vrsp <- ok ts']%vmap in
  (evm s).[vrsp]%vmap = ok (pword_of_word ts)
  -> eval_instr lp i (of_estate s fn pc)
     = ok (of_estate s' fn pc.+1).
Proof.
  move=> /= hvm.
  rewrite /eval_instr /=.
  rewrite /sem_sopn /=.
  rewrite /get_gvar /get_var /on_vu /=.
  rewrite hvm /=.
  rewrite pword_of_wordE.
  by rewrite zero_extend_u zero_extend_wrepr.
Qed.

Lemma arm_spec_lip_set_up_sp_register s r ts al sz P Q :
  let: ts' := align_word al (ts - wrepr Uptr sz) in
  let: lcmd := set_up_sp_register arm_liparams vrspi sz al r in
  is_linear_of lp fn (P ++ lcmd ++ Q)
  -> isSome (lip_set_up_sp_register arm_liparams vrspi sz al r)
  -> vtype r = sword reg_size
  -> vtmp <> vrsp
  -> vname (v_var r) \notin (lip_not_saved_stack arm_liparams)
  -> v_var r <> vrsp
  -> get_var (evm s) vrspi = ok (Vword ts)
  -> wf_vm (evm s)
  -> exists vm',
       let: ls := of_estate s fn (size P) in
       let: s' := with_vm s vm' in
       let: ls' := of_estate s' fn (size P + size lcmd) in
       let: vars := Sv.add (v_var r) (Sv.add vtmp (Sv.add vrsp vflags)) in
       [/\ lsem lp ls ls'
         , wf_vm vm'
         , vm' = (evm s) [\ vars ]
         , get_var vm' vrspi = ok (Vword ts')
         , get_var vm' r = ok (Vword ts)
         & forall x,
             Sv.In x vflags
             -> ~ is_ok (vm'.[x]%vmap)
             -> (evm s).[x]%vmap = vm'.[x]%vmap
       ].
Proof.
  set ts' := align_word _ _.
  move: r => [[rtype rname] rinfo] /=.
  set r := {| v_info := rinfo; |}.

  move=>
    hbody hset_up ? hneq_tmp_rsp hnot_saved_stack hneq_r_rsp hgetrsp hwf_vm;
    subst rtype.

  move: hset_up.
  rewrite /arm_set_up_sp_register.
  case: ifP => // hset_up _.

  have hneq_r_tmp :
    v_var r <> vtmp.
  - move=> [h]. move: hnot_saved_stack. by rewrite mem_seq1 h.
  clear hnot_saved_stack.

  move: hbody.
  rewrite /set_up_sp_register /= /arm_set_up_sp_register hset_up /= -/vtmpi.
  rewrite map_cat.
  rewrite -catA /=.
  set cmd_large_subi := _ _ (arm_cmd_large_subi _ _ _).
  set i_mov_r := _ _ (arm_op_mov _ _).
  set i_align_tmp := _ _ (arm_op_align _ _ _).
  set i_mov_rsp := _ _ (arm_op_mov _ _).
  rewrite -[i_mov_r :: _]/([:: i_mov_r ] ++ _).
  rewrite catA.
  move=> hbody.

  (* We need [vm1] before [eexists]. *)
  set vm0 := (evm s).[v_var r <- ok (pword_of_word ts)]%vmap.

  have hsz : (0 <= sz < wbase reg_size)%Z.
  - by move: hset_up => /andP [] /ZleP hlo /ZltP hhi.
  clear hset_up.

  have hgetrsp0 :
    get_var vm0 vrsp = ok (Vword ts).
  + rewrite get_var_neq; first exact: hgetrsp.
    exact: hneq_r_rsp.

  have [vm1 [hsem hvm1 hgettmp1]] :=
    arm_cmd_large_subi_lsem
      (s := with_vm s vm0)
      hbody
      hneq_tmp_rsp
      hgetrsp0
      hsz.

  set vm2 := vm1.[vtmp <- ok (pword_of_word ts')]%vmap.
  set vm3 := vm2.[vrsp <- ok (pword_of_word ts')]%vmap.

  exists vm3; split.

  - apply: lsem_step.

    (* R[r] := R[rsp]; *)
    + rewrite /lsem1 /step.
      rewrite /of_estate.
      rewrite -catA in hbody.
      rewrite -{1}(addn0 (size P)).
      rewrite (find_instr_skip hbody) /=.

      exact:
        (arm_op_mov_eval_instr
           _
           (ls := {| lvm := evm s; |})
           _ _ _
           (y := vrspi)
           hgetrsp).

    (* R[tmp] := R[rsp] - off; *)
    rewrite /=.

    have -> :
      size P + 1 = size (P ++ [:: i_mov_r ]).
    - by rewrite size_cat.

    rewrite -(add1n (size _)) addnA.
    apply: (lsem_trans hsem).
    clear hsem.
    rewrite /of_estate /=.
    apply: lsem_step2; rewrite /lsem1 /step.

    (* R[tmp] := R[tmp] & alignment; *)
    + rewrite (find_instr_skip hbody) /=.
      clear hbody.
      rewrite onth_cat -/cmd_large_subi ltnn subnn /=.
      exact:
        (arm_op_align_eval_instr
           _
           (ls := {| lvm := vm1; |})
           _ _ _
           (y := vtmpi)
           _
           hgettmp1).

    (* R[rsp] := R[tmp]; *)
    + rewrite /= -addnA.
      rewrite (find_instr_skip hbody) /=.
      clear hbody.
      rewrite onth_cat lt_nm_n sub_nmn /=.

      have hgettmp2 :
        get_var vm2 vtmp = ok (Vword ts').
      * by rewrite get_var_eq.

     rewrite !size_cat /=.
     rewrite
       -(addn1 1)
       (addnA _ 1 1)
       (addn1 (_ + 1))
       (addnS (_ + _) _)
       -(addn1 (_ + _ + _)).
     exact:
        (arm_op_mov_eval_instr
           _
           (ls := {| lvm := vm2; |})
           _ _ _
           (y := vtmpi)
           hgettmp2).

  - repeat apply: wf_vm_set.
    apply: (vmap_eq_except_wf_vm _ hvm1 hgettmp1).
    exact: (wf_vm_set _ hwf_vm).

  - move=> x.
    t_notin_add.
    t_vm_get.
    rewrite hvm1; first by t_vm_get.
    apply: Sv_neq_not_in_singleton.
    by apply/nesym.

  - by t_get_var.

  - t_get_var.
    rewrite (get_var_eq_except _ hvm1); first by t_get_var.
    apply: Sv_neq_not_in_singleton.
    by apply/nesym.

  rewrite /= -/vm3.
  move=> x hx _.
  move: hx => /vflagsP hxtype.

  have ? : v_var r <> x.
  - apply/eqP. apply: vtype_diff. by rewrite hxtype.

  have ? : vrsp <> x.
  - apply/eqP. apply: vtype_diff. by rewrite hxtype.

  have ? : vtmp <> x.
  - apply/eqP. apply: vtype_diff. by rewrite hxtype.

  t_vm_get.
  rewrite hvm1 /=; first by t_vm_get.
  by apply: Sv_neq_not_in_singleton.
Qed.

Lemma arm_spec_lip_set_up_sp_stack s ts m' al sz off P Q :
  let: ts' := align_word al (ts - wrepr Uptr sz) in
  let: lcmd := set_up_sp_stack arm_liparams vrspi sz al off in
  is_linear_of lp fn (P ++ lcmd ++ Q)
  -> isSome (lip_set_up_sp_stack arm_liparams vrspi sz al off)
  -> vtmp <> vrsp
  -> get_var (evm s) vrspi = ok (Vword ts)
  -> wf_vm (evm s)
  -> write (emem s) (ts' + wrepr Uptr off)%R ts = ok m'
  -> exists vm',
       let: ls := of_estate s fn (size P) in
       let: s' := {| escs := escs s; evm := vm'; emem := m'; |} in
       let: ls' := of_estate s' fn (size P + size lcmd) in
       let: vars := Sv.add vtmpi (Sv.add vrspi vflags) in
       [/\ lsem lp ls ls'
         , wf_vm vm'
         , vm' = (evm s) [\ vars ]
         , get_var vm' vrspi = ok (Vword ts')
         & forall x,
             Sv.In x vflags
             -> ~ is_ok (vm'.[x]%vmap)
             -> (evm s).[x]%vmap = vm'.[x]%vmap
       ].
Proof.
  set ts' := align_word _ _.
  move=> hbody hset_up hneq_tmp_rsp hgetrsp hwf_vm hwrite.

  move: hset_up.
  rewrite /= /arm_set_up_sp_stack.
  case: ifP => // hset_up _.

  move: hbody.
  rewrite /set_up_sp_stack /= /arm_set_up_sp_stack hset_up /= -/vtmpi.
  rewrite map_cat /=.
  set cmd_large_subi := map _ (arm_cmd_large_subi _ _ _).
  set i_align_tmp := li_of_copn_args _ (arm_op_align _ _ _).
  set i_str_rsp := li_of_copn_args _ (arm_op_str_off _ _ _).
  set i_mov_rsp := li_of_copn_args _ (arm_op_mov _ _).
  rewrite -catA.
  move=> hbody.

  (* We need [vm0] before [eexists]. *)

  have hsz : (0 <= sz < wbase reg_size)%Z.
  - by move: hset_up => /andP [] /ZleP hlo /ZltP hhi.
  clear hset_up.

  have [vm0 [hsem hvm0 hgettmp0]] :=
    arm_cmd_large_subi_lsem (s := s) hbody hneq_tmp_rsp hgetrsp hsz.
  set vm1 := vm0.[vtmp <- ok (pword_of_word ts')]%vmap.
  set vm2 := vm1.[vrsp <- ok (pword_of_word ts')]%vmap.

  have hgetrsp1 :
    get_var vm1 vrsp = ok (Vword ts).
  * rewrite get_var_neq; last exact: hneq_tmp_rsp.
    rewrite (get_var_eq_except _ hvm0); first exact: hgetrsp.
    exact: (Sv_neq_not_in_singleton hneq_tmp_rsp).

  have hgettmp1 :
    get_var vm1 vtmp = ok (Vword ts').
  * by rewrite get_var_eq.

  eexists.
  split.

  (* R[tmp] := R[rsp] - off; *)
  - apply: (lsem_trans hsem).
    apply: lsem_step3; rewrite /lsem1 /step /=.

    (* R[tmp] := R[tmp] & alignment; *)
    + rewrite (find_instr_skip hbody) /=.
      rewrite onth_cat -/cmd_large_subi ltnn subnn /=.
      exact:
        (arm_op_align_eval_instr
           _
           (ls := {| lvm := vm0; |})
           _ _ _
           (y := vtmpi)
           _
           hgettmp0).

    (* M[R[rsp]] := R[tmp]; *)
    + rewrite /= -addnA.
      rewrite (find_instr_skip hbody) /=.
      rewrite onth_cat lt_nm_n sub_nmn /=.
      exact:
        (arm_op_str_off_eval_instr
           _
           (ls := {| lvm := vm1; |})
           _
           (y := vrspi)
           hgettmp1
           hgetrsp1
           hwrite).

    (* R[rsp] := R[tmp]; *)
    + rewrite /= -!addnA addn1.
      rewrite (find_instr_skip hbody) /=.
      rewrite onth_cat lt_nm_n sub_nmn /=.
      rewrite /of_estate /=.
      rewrite !size_cat /=.
      rewrite -(addn1 2) (addnS _ 2) (addnS (size P) _) -(addn1 (_ + _)).
      exact:
        (arm_op_mov_eval_instr
           _
           (ls := {| lvm := vm1; |})
           _ _ _
           (y := vtmpi)
           hgettmp1).

  - repeat apply: wf_vm_set.
    exact: (vmap_eq_except_wf_vm hwf_vm hvm0 hgettmp0).

  - move=> x.
    t_notin_add.
    t_vm_get.
    rewrite hvm0; first done.
    apply: Sv_neq_not_in_singleton.
    by apply/nesym.

  - by t_get_var.

  rewrite /= -/vm2.
  move=> x hx _.
  move: hx => /vflagsP hxtype.

  have ? : vrsp <> x.
  - apply/eqP. apply: vtype_diff. by rewrite hxtype.

  have ? : vtmp <> x.
  - apply/eqP. apply: vtype_diff. by rewrite hxtype.

  t_vm_get.
  rewrite hvm0 /=; first done.
  by apply: Sv_neq_not_in_singleton.
Qed.

Lemma store_mn_of_wsizeP ws ws' mn (w : word ws) (w' : word ws') :
  store_mn_of_wsize ws = Some mn
  -> truncate_word ws w' = ok w
  -> exec_sopn (Oarm (ARM_op mn default_opts)) [:: Vword w' ]
     = ok [:: Vword w ].
Proof.
  case: ws w => w // [?]; subst mn.
  all: rewrite /exec_sopn /=.
  all: move=> -> /=.
  all: by rewrite zero_extend_u.
Qed.

Lemma uload_mn_of_wsizeP ws ws' mn (w : word ws) (w' : word ws') :
  uload_mn_of_wsize ws = Some mn
  -> truncate_word ws w' = ok w
  -> exec_sopn (Oarm (ARM_op mn default_opts)) [:: Vword w' ]
     = ok [:: Vword (zero_extend reg_size w) ].
Proof.
  case: ws w => w // [?]; subst mn.
  all: rewrite /exec_sopn /=.
  all: by move=> -> /=.
Qed.

Lemma arm_hlip_lassign
  (s1 s2 : estate) pc ii x e ws li ws' (w : word ws) (w' : word ws') :
  lassign arm_liparams x ws e = Some li
  -> sem_rexpr (emem s1) (evm s1) e = ok (Vword w')
  -> truncate_word ws w' = ok w
  -> write_lexpr x (Vword w) s1 = ok s2
  -> eval_instr lp (MkLI ii li) (of_estate s1 fn pc)
     = ok (of_estate s2 fn pc.+1).
Proof.
  move=> hlassign hseme htrunc hwrite.

  move: hlassign.
  rewrite /lassign /= /arm_lassign.
  case: x hwrite => [ ? ? ? | x ] hwrite /=.
  {
    case hmn: store_mn_of_wsize => [mn|] // [?]; subst li.
    rewrite /eval_instr /= /sem_sopn /=.
    rewrite to_estate_of_estate.
    rewrite hseme {hseme} /=.
    rewrite (store_mn_of_wsizeP hmn htrunc) {hmn htrunc}.
    by move: hwrite; rewrite /= => ->.
  }

  case: ws w htrunc hwrite => //= w htrunc hwrite.
  case: e hseme => [ ??? | ]; last case => //; last case => // - [] // [] // z.
  2: move => e.
  all: move => /= hseme /Some_inj <-{li}.
  all: rewrite /eval_instr /= /sem_sopn /= to_estate_of_estate.
  - rewrite hseme {hseme} /=.
    rewrite /exec_sopn /=.
    rewrite htrunc {htrunc} /=.
    rewrite zero_extend_u.
    by rewrite hwrite {hwrite} /=.

  - rewrite hseme {hseme} /=.
    rewrite /exec_sopn /=.
    rewrite htrunc {htrunc} /=.
    by rewrite hwrite {hwrite} /=.

  case/ok_inj/Vword_inj: hseme => ?; subst => /= ?; subst.
  move: htrunc; rewrite truncate_word_u => /ok_inj ?; subst.
  by rewrite zero_extend_u {} hwrite.
Qed.

End LINEARIZATION.

Definition arm_hliparams :
  h_linearization_params (ap_lip arm_params) :=
  {|
    spec_lip_allocate_stack_frame := arm_spec_lip_allocate_stack_frame;
    spec_lip_free_stack_frame := arm_spec_lip_free_stack_frame;
    spec_lip_set_up_sp_register := arm_spec_lip_set_up_sp_register;
    spec_lip_set_up_sp_stack := arm_spec_lip_set_up_sp_stack;
    hlip_lassign := arm_hlip_lassign;
  |}.

Lemma arm_ok_lip_tmp :
  exists r : reg_t, of_string (lip_tmp (ap_lip arm_params)) = Some r.
Proof.
  exists R12.
  rewrite /=.
  change "r12"%string with (to_string R12).
  exact: to_stringK.
Qed.

(* ------------------------------------------------------------------------ *)
(* Lowering hypotheses. *)

Lemma arm_lower_callP
  (eft : eqType)
  (pT : progT eft)
  (sCP : semCallParams)
  (p : prog)
  (ev : extra_val_t)
  (is_regx : var -> bool)
  (options : lowering_options)
  (warning : instr_info -> warning_msg -> instr_info)
  (fv : fresh_vars)
  (is_var_in_memory : var_i -> bool)
  (_ : lop_fvars_correct arm_loparams fv (p_funcs p))
  (f : funname)
  scs mem scs' mem'
  (va vr : seq value) :
  psem.sem_call p ev scs mem f va scs' mem' vr
  -> let lprog :=
       lowering.lower_prog
         (lop_lower_i arm_loparams is_regx)
         options
         warning
         fv
         is_var_in_memory
         p
     in
     psem.sem_call lprog ev scs mem f va scs' mem' vr.
Proof.
  exact: lower_callP.
Qed.

Definition arm_hloparams : h_lowering_params (ap_lop arm_params) :=
  {|
    hlop_lower_callP := arm_lower_callP;
  |}.


(* ------------------------------------------------------------------------ *)
(* Assembly generation hypotheses. *)

Section ASM_GEN.

(* FIXME: the following line fixes type inference with Coq 8.16 *)
Local Instance the_asm : asm _ _ _ _ _ _ := _.

Lemma condt_of_rflagP rf r :
  eval_cond (get_rf rf) (condt_of_rflag r) = to_bool (of_rbool (rf r)).
Proof.
  rewrite -get_rf_to_bool_of_rbool. by case: r.
Qed.

Lemma condt_notP rf c b :
  eval_cond rf c = ok b
  -> eval_cond rf (condt_not c) = ok (negb b).
Proof.
  case: c => /=.

  (* Introduce booleans [b] and equalities [_ = b] and [rf _ = ok b].
     Rewrite all equalities, simplify and case all booleans. *)
  all: t_xrbindP=> *.
  all: subst=> /=.
  all:
    repeat
      match goal with
      | [ H : _ _ = ok _ |- _ ] => rewrite H {H} /=
      end.
  all:
    by repeat
      match goal with
      | [ b : bool |- _ ] => case: b
      end.
Qed.

Lemma condt_andP rf c0 c1 c b0 b1 :
  condt_and c0 c1 = Some c
  -> eval_cond rf c0 = ok b0
  -> eval_cond rf c1 = ok b1
  -> eval_cond rf c = ok (b0 && b1).
Proof.
  move: c0 c1 => [] [] //.
  all: move=> [?]; subst c.
  all: rewrite /eval_cond /=.

  (* Introduce booleans [b] and equalities [_ = b] and [rf _ = ok b].
     Rewrite all equalities, simplify and case all booleans. *)
  all: t_xrbindP=> *.
  all: subst=> /=.
  all:
    repeat
      match goal with
      | [ H : _ _ = ok _ |- _ ] => rewrite H {H} /=
      end.
  all:
    by repeat
      match goal with
      | [ b : bool |- _ ] => case: b
      end.
Qed.

Lemma condt_orP rf c0 c1 c b0 b1 :
  condt_or c0 c1 = Some c
  -> eval_cond rf c0 = ok b0
  -> eval_cond rf c1 = ok b1
  -> eval_cond rf c = ok (b0 || b1).
Proof.
  move: c0 c1 => [] [] //.
  all: move=> [?]; subst c.
  all: rewrite /eval_cond /=.

  (* Introduce booleans [b] and equalities [_ = b] and [rf _ = ok b].
     Rewrite all equalities, simplify and case all booleans. *)
  all: t_xrbindP=> *.
  all: subst=> /=.
  all:
    repeat
      match goal with
      | [ H : _ _ = ok _ |- _ ] => rewrite H {H} /=
      end.
  all:
    by repeat
      match goal with
      | [ b : bool |- _ ] => case: b
      end.
Qed.

Lemma eval_assemble_cond_Pvar ii m rf x r v :
  eqflags m rf
  -> of_var_e ii x = ok r
  -> get_var (evm m) x = ok v
  -> exists2 v',
       value_of_bool (eval_cond (get_rf rf) (condt_of_rflag r)) = ok v'
       & value_uincl v v'.
Proof.
  move=> eqf hr hv.
  have hincl := xgetflag_ex eqf hr hv.
  clear ii x m eqf hr hv.

  rewrite condt_of_rflagP.

  eexists; last exact: hincl.
  clear v hincl.
  exact: value_of_bool_to_bool_of_rbool.
Qed.

Lemma eval_assemble_cond_Onot rf c v v0 v1 :
  value_of_bool (eval_cond (get_rf rf) c) = ok v1
  -> value_uincl v0 v1
  -> sem_sop1 Onot v0 = ok v
  -> exists2 v',
       value_of_bool (eval_cond (get_rf rf) (condt_not c)) = ok v'
       & value_uincl v v'.
Proof.
  move=> hv1 hincl.
  move=> /sem_sop1I /= [b hb ?]; subst v.

  have hc := value_uincl_to_bool_value_of_bool hincl hb hv1.
  clear v0 v1 hincl hb hv1.

  change arm.eval_cond with eval_cond.
  rewrite (condt_notP hc) {hc}.
  by eexists.
Qed.

Lemma eval_assemble_cond_Obeq ii m rf v x0 x1 r0 r1 v0 v1 :
  is_rflags_GE r0 r1 = true
  -> eqflags m rf
  -> of_var_e ii x0 = ok r0
  -> get_var (evm m) x0 = ok v0
  -> of_var_e ii x1 = ok r1
  -> get_var (evm m) x1 = ok v1
  -> sem_sop2 Obeq v0 v1 = ok v
  -> exists2 v',
       value_of_bool (eval_cond (get_rf rf) GE_ct) = ok v' & value_uincl v v'.
Proof.
  move=> hGE eqf hr0 hv0 hr1 hv1.

  move=> /sem_sop2I /= [b0 [b1 [b [hb0 hb1 hb ?]]]]; subst v.
  move: hb.
  rewrite /mk_sem_sop2 /=.
  move=> [?]; subst b.

  have hincl0 := xgetflag_ex eqf hr0 hv0.
  have hincl1 := xgetflag_ex eqf hr1 hv1.
  clear ii m x0 x1 eqf hr0 hv0 hr1 hv1.

  have ? := to_boolI hb0; subst v0.
  have ? := to_boolI hb1; subst v1.
  clear hb0 hb1.

  move: r0 r1 hincl0 hincl1 hGE.
  move=> [] [] // hincl0 hincl1 _.
  all: rewrite 2!get_rf_to_bool_of_rbool.
  all: rewrite (value_uinclE hincl0) {hincl0} /=.
  all: rewrite (value_uinclE hincl1) {hincl1} /=.
  all: by eexists.
Qed.

Lemma eval_assemble_cond_Oand rf c c0 c1 v v0 v1 v0' v1' :
  condt_and c0 c1 = Some c
  -> value_of_bool (eval_cond (get_rf rf) c0) = ok v0'
  -> value_uincl v0 v0'
  -> value_of_bool (eval_cond (get_rf rf) c1) = ok v1'
  -> value_uincl v1 v1'
  -> sem_sop2 Oand v0 v1 = ok v
  -> exists2 v',
       value_of_bool (eval_cond (get_rf rf) c) = ok v' & value_uincl v v'.
Proof.
  move=> hand hv0' hincl0 hv1' hincl1.
  move=> /sem_sop2I /= [b0 [b1 [b [hb0 hb1 hb ?]]]]; subst v.

  move: hb.
  rewrite /mk_sem_sop2 /=.
  move=> [?]; subst b.

  have hc0 := value_uincl_to_bool_value_of_bool hincl0 hb0 hv0'.
  have hc1 := value_uincl_to_bool_value_of_bool hincl1 hb1 hv1'.
  clear hincl0 hb0 hv0' hincl1 hb1 hv1'.

  change arm.eval_cond with eval_cond.
  rewrite (condt_andP hand hc0 hc1) {hand hc0 hc1} /=.
  by eexists.
Qed.

Lemma eval_assemble_cond_Oor rf c c0 c1 v v0 v1 v0' v1' :
  condt_or c0 c1 = Some c
  -> value_of_bool (eval_cond (get_rf rf) c0) = ok v0'
  -> value_uincl v0 v0'
  -> value_of_bool (eval_cond (get_rf rf) c1) = ok v1'
  -> value_uincl v1 v1'
  -> sem_sop2 Oor v0 v1 = ok v
  -> exists2 v',
       value_of_bool (eval_cond (get_rf rf) c) = ok v' & value_uincl v v'.
Proof.
  move=> hor hv0' hincl0 hv1' hincl1.
  move=> /sem_sop2I /= [b0 [b1 [b [hb0 hb1 hb ?]]]]; subst v.

  move: hb.
  rewrite /mk_sem_sop2 /=.
  move=> [?]; subst b.

  have hc0 := value_uincl_to_bool_value_of_bool hincl0 hb0 hv0'.
  have hc1 := value_uincl_to_bool_value_of_bool hincl1 hb1 hv1'.
  clear hincl0 hb0 hv0' hincl1 hb1 hv1'.

  change arm.eval_cond with eval_cond.
  rewrite (condt_orP hor hc0 hc1) {hor hc0 hc1} /=.
  by eexists.
Qed.

Lemma arm_eval_assemble_cond ii m rf e c v :
  eqflags m rf
  -> agp_assemble_cond arm_agparams ii e = ok c
  -> sem_fexpr (evm m) e = ok v
  -> exists2 v',
       value_of_bool (eval_cond (get_rf rf) c) = ok v' & value_uincl v v'.
Proof.
  rewrite /=.
  elim: e c v => [| x | op1 e hind | op2 e0 hind0 e1 hind1 |] //= c v eqf.

  - t_xrbindP=> r hr hc; subst c.
    move=> hv.
    exact: (eval_assemble_cond_Pvar eqf hr hv).

  - case: op1 => //.
    t_xrbindP=> c' hc' hc; subst c.
    move=> v0 hv0 hsem.
    have [v1 hv1 hincl1] := hind _ _ eqf hc' hv0.
    clear ii m e eqf hc' hv0 hind.
    exact: (eval_assemble_cond_Onot hv1 hincl1 hsem).

  case: op2 => //.
  - case: e0 hind0 => // x0 _.
    case: e1 hind1 => // x1 _.
    t_xrbindP=> r0 hr0 r1 hr1 //=.
    case hGE: is_rflags_GE => // -[?]; subst c.
    move=> v0 hv0 v1 hv1 hsem.
    exact: (eval_assemble_cond_Obeq hGE eqf hr0 hv0 hr1 hv1 hsem).

  - t_xrbindP=> c0 hass0 c1 hass1.
    case hand: condt_and => [c'|] // [?]; subst c'.
    move=> v0 hsem0 v1 hsem1 hsem.
    have [v0' hv0' hincl0] := hind0 _ _ eqf hass0 hsem0.
    have [v1' hv1' hincl1] := hind1 _ _ eqf hass1 hsem1.
    clear eqf hass0 hsem0 hind0 hass0 hsem1 hind1.
    exact: (eval_assemble_cond_Oand hand hv0' hincl0 hv1' hincl1 hsem).

  t_xrbindP=> c0 hass0 c1 hass1.
  case hor: condt_or => [c'|] // [?]; subst c'.
  move=> v0 hsem0 v1 hsem1 hsem.
  have [v0' hv0' hincl0] := hind0 _ _ eqf hass0 hsem0.
  have [v1' hv1' hincl1] := hind1 _ _ eqf hass1 hsem1.
  clear eqf hass0 hsem0 hind0 hass0 hsem1 hind1.
  exact: (eval_assemble_cond_Oor hor hv0' hincl0 hv1' hincl1 hsem).
Qed.

(* TODO_ARM: Is there a way of avoiding importing here? *)
Import arch_sem.

Lemma arm_assemble_extra_op
  rip ii op lvs args op' lvs' args' op'' asm_args m xs ys m' s :
  sem_rexprs m args = ok xs
  -> exec_sopn (Oasm (ExtOp op)) xs = ok ys
  -> write_lexprs lvs ys m = ok m'
  -> to_asm ii op lvs args = ok (op', lvs', args')
  -> assemble_asm_op arm_agparams rip ii op' lvs' args'
     = ok (op'', asm_args)
  -> lom_eqv rip m s
  -> exists2 s', eval_op op'' asm_args s = ok s' & lom_eqv rip m' s'.
Proof. by case: op. Qed.

Definition arm_hagparams : h_asm_gen_params (ap_agp arm_params) :=
  {|
    hagp_eval_assemble_cond := arm_eval_assemble_cond;
    hagp_assemble_extra_op := arm_assemble_extra_op;
  |}.

End ASM_GEN.


(* ------------------------------------------------------------------------ *)
(* Shared hypotheses. *)

Definition arm_is_move_opP op vx v :
  ap_is_move_op arm_params op
  -> exec_sopn (Oasm op) [:: vx ] = ok v
  -> List.Forall2 value_uincl v [:: vx ].
Proof.
  case: op => //.
  move=> [[]] //.
  move=> [] //.
  move=> [] //.
  move=> [[] [] [?|]] _ //.
  rewrite /exec_sopn /=.
  t_xrbindP=> w w'' hvx.
  have [ws' [w' [-> /truncate_wordP [hws' ->]]]] := to_wordI hvx.
  rewrite /sopn_sem /=.
  rewrite /drop_semi_nzcv /=.
  move=> [<-] <-.
  apply: List.Forall2_cons; last done.
  exact: (word_uincl_zero_ext w' hws').
Qed.


(* ------------------------------------------------------------------------ *)

Definition arm_h_params : h_architecture_params arm_params :=
  {|
    hap_hpip := arm_hpiparams;
    hap_hsap := arm_hsaparams;
    hap_hlip := arm_hliparams;
    ok_lip_tmp := arm_ok_lip_tmp;
    hap_hlop := arm_hloparams;
    hap_hagp := arm_hagparams;
    hap_is_move_opP := arm_is_move_opP;
  |}.

End Section.
