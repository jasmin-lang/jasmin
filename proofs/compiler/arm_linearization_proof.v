From mathcomp Require Import all_ssreflect all_algebra.
Require Import
  arch_extra
  expr
  psem
  psem_facts
  sem_one_varmap
  linear
  linear_sem
  linearization_proof.
Require Import
  arm_decl
  arm_instr_decl
  arm_extra
  arm_linearization.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Definition opts :=
  {| args_size      := reg_size
  ;  set_flags      := false
  ;  is_conditional := false
  ;  has_shift      := None
  |}.

Lemma spec_arm_allocate_stack_frame :
  forall (lp : lprog) (s : estate) sp_rsp ii fn pc ts sz,
    let rsp := vid sp_rsp in
    let vm := evm s in
    let '(lvs, op, ps) := arm_allocate_stack_frame (VarI rsp xH) sz in
    let i := MkLI ii (Lopn lvs op ps) in
    let ts' := pword_of_word (ts + wrepr Uptr sz) in
    let s' := with_vm s (vm.[rsp <- ok ts'])%vmap in
    (vm.[rsp])%vmap = ok (pword_of_word ts)
    -> eval_instr lp i (of_estate s fn pc)
       = ok (of_estate s' fn pc.+1).
Proof.
  move=> lp s sp_rsp ii fn pc ts sz.
  move=> /= Hvm.
  rewrite /eval_instr /= /sem_sopn /=.
  rewrite /get_gvar /get_var /on_vu /=.
  rewrite Hvm /=.
  rewrite pword_of_wordE.
  by rewrite zero_extend_u.
Qed.

Lemma spec_arm_free_stack_frame :
  forall (lp: lprog) (s: estate) sp_rsp ii fn pc ts sz,
    let rsp := vid sp_rsp in
    let vm := evm s in
    let '(lvs, op, ps) := arm_free_stack_frame (VarI rsp xH) sz in
    let i := MkLI ii (Lopn lvs op ps) in
    let ts' := pword_of_word (ts - wrepr Uptr sz) in
    let s' := with_vm s (vm.[rsp <- ok ts'])%vmap in
    (vm.[rsp])%vmap = ok (pword_of_word ts)
    -> eval_instr lp i (of_estate s fn pc)
       = ok (of_estate s' fn pc.+1).
Proof.
  move=> lp s sp_rsp ii fn pc ts sz.
  move=> /= Hvm.
  rewrite /eval_instr /= /sem_sopn /=.
  rewrite /get_gvar /get_var /on_vu /=.
  rewrite Hvm /=.
  rewrite pword_of_wordE.
  rewrite zero_extend_u.
  by rewrite wrepr_opp.
Qed.

Definition spec_arm_ensure_rsp_alignment :
  forall (lp: lprog) (s1: estate) rsp_id ii fn pc ws ts',
    let vrsp := Var (sword Uptr) rsp_id in
    let vrspi := VarI vrsp xH in
    let rsp' := align_word ws ts' in
    get_var (evm s1) vrsp = ok (Vword ts')
    -> wf_vm (evm s1)
    -> let '(lvs, op, ps) := arm_ensure_rsp_alignment vrspi ws in
       let i := MkLI ii (Lopn lvs op ps) in
       let vm1' := (evm s1).[vrsp <- ok (pword_of_word rsp')]%vmap in
       exists vm',
         [/\ eval_instr lp i (of_estate s1 fn pc)
             = ok (of_estate (with_vm s1 vm') fn pc.+1)
         ,   vm' = vm1' [\sv_of_flags rflags]
         ,   forall x,
               Sv.In x (sv_of_flags rflags)
               -> ~ is_ok (vm'.[x]%vmap)
               -> (evm s1).[x]%vmap = vm'.[x]%vmap
         &   wf_vm vm'
         ].
Proof.
  move=> lp s1 rsp_id ii fn pc ws ts'.
  move=> vrsp vrspi al /= Hvrsp Hwm1.
  rewrite /eval_instr /= /sem_sopn /= /get_gvar /=.
  rewrite Hvrsp /=.
  rewrite zero_extend_u.
  rewrite pword_of_wordE.
  rewrite /with_vm /=.
  eexists.
  split.
  - reflexivity.
  - move=> x hin.
    rewrite !(@Fv.setP _ _ vrsp).
    case: (vrsp =P x).
    + move=> ?. by subst x.
    + done.
  - move=> x /sv_of_flagsP /mapP [f _ ->].
    by case f;
      repeat (rewrite Fv.setP_eq || rewrite Fv.setP_neq //).
  apply wf_vm_set.
  exact Hwm1.
Qed.

Lemma spec_arm_lassign :
  forall (lp : lprog) ii fn pc (s1 s2 : estate) x e ws ws'
         (w : word ws) (w' : word ws'),
    let '(lvs, op, ps) := arm_lassign x ws e in
    let i := MkLI ii (Lopn lvs op ps) in
    sem_pexpr [::] s1 e = ok (Vword w')
    -> truncate_word ws w' = ok w
    -> write_lval [::] x (Vword w) s1 = ok s2
    -> eval_instr lp i (of_estate s1 fn pc)
       = ok (of_estate s2 fn pc.+1).
Proof.
  move=> lp ii fn pc s1 s2 x e ws ws' w w' /=.
  move=> Hsem_pexpr Htruncate_word Hwrite_lval.
  rewrite /eval_instr /= /sem_sopn /=.
  rewrite to_estate_of_estate.
  rewrite Hsem_pexpr /=.
  rewrite /exec_sopn /=.
  rewrite Htruncate_word /=.
  case: ws w Htruncate_word Hwrite_lval =>
    /= ? _ Hwrite_lval;
    try by rewrite Hwrite_lval /=.
  - by apply TODO_ARM. (* x = (u64)e *)
  - by apply TODO_ARM. (* x = (u128)e *)
  - by apply TODO_ARM. (* x = (u256)e *)
Qed.

Definition h_arm_linearization_params :
  h_linearization_params arm_linearization_params.
  split.
  - exact: spec_arm_allocate_stack_frame.
  - exact: spec_arm_free_stack_frame.
  - exact: spec_arm_ensure_rsp_alignment.
  - exact: spec_arm_lassign.
Defined.
