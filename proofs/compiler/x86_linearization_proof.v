From mathcomp Require Import all_ssreflect all_algebra.
Require Import expr psem psem_facts sem_one_varmap linear linear_sem linearization_proof.
Require Import x86_decl x86_instr_decl x86_extra x86_linear_sem x86_linearization.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma spec_x86_mov_op :
  forall (lp : lprog) (s : estate) fn pc x lbl ptr ii,
  vtype x == sword Uptr ->
  label.encode_label (label_in_lprog lp) (fn, lbl) = Some ptr ->
  let i := LstoreLabel {| v_var := x; v_info := 1%positive |} lbl in
  let vm := evm s in
  let s' := with_vm s (vm.[x <- pof_val (vtype x) (Vword ptr)])%vmap in
  eval_instr lp x86_mov_eop {| li_ii := ii; li_i := i |} (of_estate s fn pc) =
  ok (of_estate s' fn pc.+1).
Proof.
  move=> lp s fn pc x lbl ptr ii /eqP hty hlabel.
  rewrite /= /eval_instr /= /sem_sopn /= /exec_sopn /= hlabel.
  rewrite /write_var /= /set_var /=.
  case: x hty => _ xn /= -> /=.
  by rewrite zero_extend_u wrepr_unsigned.
Qed.

Lemma spec_x86_allocate_stack_frame :
  forall (lp: lprog) (s: estate) sp_rsp ii fn pc ts sz,
    let rsp := vid sp_rsp in
    let vm := evm s in
    let i :=
      let args := x86_allocate_stack_frame (VarI rsp xH) sz in
      MkLI ii (Lopn args.1.1 args.1.2 args.2)
    in
    let ts' := pword_of_word (ts + wrepr Uptr sz) in
    let s' := with_vm s (vm.[rsp <- ok ts'])%vmap in
    (vm.[rsp])%vmap = ok (pword_of_word ts)
    -> eval_instr lp x86_mov_eop i (of_estate s fn pc)
       = ok (of_estate s' fn pc.+1).
Proof.
  move=> lp s sp_rsp ii fn pc ts sz.
  move=> /= Hvm.
  rewrite /eval_instr /= /sem_sopn /=.
  rewrite /get_gvar /get_var /on_vu /=.
  rewrite Hvm /=.
  rewrite pword_of_wordE.
  by rewrite 3!zero_extend_u.
Qed.

Lemma spec_x86_free_stack_frame :
  forall (lp: lprog) (s: estate) sp_rsp ii fn pc ts sz,
    let rsp := vid sp_rsp in
    let vm := evm s in
    let i :=
      let args := x86_free_stack_frame (VarI rsp xH) sz in
      MkLI ii (Lopn args.1.1 args.1.2 args.2)
    in
    let ts' := pword_of_word (ts - wrepr Uptr sz) in
    let s' := with_vm s (vm.[rsp <- ok ts'])%vmap in
    (vm.[rsp])%vmap = ok (pword_of_word ts)
    -> eval_instr lp x86_mov_eop i (of_estate s fn pc)
       = ok (of_estate s' fn pc.+1).
Proof.
  move=> lp s sp_rsp ii fn pc ts sz.
  move=> /= Hvm.
  rewrite /eval_instr /= /sem_sopn /=.
  rewrite /get_gvar /get_var /on_vu /=.
  rewrite Hvm /=.
  rewrite pword_of_wordE.
  by rewrite 3!zero_extend_u.
Qed.

Definition spec_x86_ensure_rsp_alignment :
  forall (lp: lprog) (s1: estate) rsp_id ws ts' ii fn pc,
    let vrsp := Var (sword Uptr) rsp_id in
    let vrspi := VarI vrsp xH in
    let rsp' := align_word ws ts' in
    get_var (evm s1) vrsp = ok (Vword ts')
    ->
    wf_vm (evm s1) ->
    let i :=
      let args := x86_ensure_rsp_alignment vrspi ws in
      MkLI ii (Lopn args.1.1 args.1.2 args.2)
    in
    exists vm', [/\
       eval_instr
         lp
         x86_mov_eop
         i
         (of_estate s1 fn pc)
       = ok (of_estate (with_vm s1 vm') fn pc.+1),
     vm' = (evm s1).[vrsp <- ok (pword_of_word rsp')]%vmap [\sv_of_flags rflags],
     forall x, Sv.In x (sv_of_flags rflags) -> ~ is_ok (vm'.[x]%vmap) -> (evm s1).[x]%vmap = vm'.[x]%vmap
   & wf_vm vm'].
Proof.
  move=> lp s1 rsp_id ws ts' sp_rsp ii fn.
  move=> vrsp vrspi al /= Hvrsp.
  rewrite /eval_instr /= /sem_sopn /= /get_gvar /=.
  rewrite Hvrsp /=.
  rewrite !zero_extend_u pword_of_wordE /=.
  rewrite /with_vm /=.
  eexists; split; first by reflexivity.
  + move=> x hin. rewrite !(@Fv.setP _ _ vrsp).
    case: (vrsp =P x).
    + by move=> ?; subst x.
    move=> _.
    have hneq: forall (f:rflag), to_var f != x.
    + move=> f.
      apply /eqP => heq.
      apply /hin /sv_of_flagsP /mapP.
      exists f => //.
      by apply /mapP; eexists; last by reflexivity.
    by rewrite !Fv.setP_neq.
  + move=> x /sv_of_flagsP /mapP [f _ ->].
    by case f;
      repeat (rewrite Fv.setP_eq || rewrite Fv.setP_neq //).
  by do! apply wf_vm_set.
Qed.

Lemma spec_x86_lassign :
  forall (lp: lprog) (s1 s2: estate) x e ws ws'
         (w: word ws) (w': word ws') ii fn pc,
    let i :=
      let args := x86_lassign x ws e in
      MkLI ii (Lopn args.1.1 args.1.2 args.2)
    in
    sem_pexpr [::] s1 e = ok (Vword w')
    -> truncate_word ws w' = ok w
    -> write_lval [::] x (Vword w) s1 = ok s2
    -> eval_instr
         lp
         x86_mov_eop
         i
         (of_estate s1 fn pc)
       = ok (of_estate s2 fn pc.+1).
Proof.
  move=> lp s1 s2 x e ws ws' w w' ii fn pc /=.
  move=> Hsem_pexpr Htruncate_word Hwrite_lval.
  rewrite /eval_instr /= /sem_sopn /=.
  rewrite to_estate_of_estate.
  rewrite Hsem_pexpr /=.
  rewrite /exec_sopn /=.
  case: ws w Htruncate_word Hwrite_lval
    => /= ? Htruncate_word Hwrite_lval;
    rewrite Htruncate_word /=;
    rewrite Hwrite_lval /=;
    done.
Qed.

Definition h_x86_linearization_params : h_linearization_params x86_mov_op x86_linearization_params.
Proof.
  split.
  - exact: spec_x86_mov_op.
  - exact: spec_x86_allocate_stack_frame.
  - exact: spec_x86_free_stack_frame.
  - exact: spec_x86_ensure_rsp_alignment.
  - exact: spec_x86_lassign.
Qed.
