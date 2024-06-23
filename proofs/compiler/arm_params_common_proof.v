From Coq Require Import Lia.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype ssralg.
From mathcomp Require Import word_ssrZ.

Require Import
  arch_params
  compiler_util
  expr
  fexpr
  fexpr_sem
  linear
  linear_sem
  linear_facts
  psem.
Require Import
  arch_decl
  arch_extra
  sem_params_of_arch_extra.
Require Import
  arm_decl
  arm_extra
  arm_instr_decl
  arm_params_core_proof.

Require Export arm_params_common.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Most ARM instructions with default options are executed as follows:
   1. Unfold instruction execution definitions, e.g. [eval_instr].
   2. Rewrite argument hypotheses, i.e. [sem_pexpr].
   3. Unfold casting definitions in result, e.g. [zero_extend] and
      [pword_of_word].
   4. Rewrite result hypotheses, i.e. [write_lval]. *)
Ltac t_arm_op :=
  rewrite /eval_instr /= /sem_sopn /= /exec_sopn /get_gvar /=;
  t_simpl_rewrites;
  rewrite /of_estate /= /with_vm /=;
  repeat rewrite truncate_word_u /=;
  rewrite ?zero_extend_u ?addn1;
  t_simpl_rewrites.

Module ARMFopnP.

Section WITH_PARAMS.

Context
  {atoI  : arch_toIdent}
  {syscall_state : Type}
  {sc_sem : syscall_sem syscall_state}
  {call_conv : calling_convention}.

#[local] Existing Instance withsubword.

Let mkv xname vi :=
  let: x := {| vname := xname; vtype := sword arm_reg_size; |} in
  let: xi := {| v_var := x; v_info := vi; |} in
  (xi, x).

Lemma sem_fopn_equiv o s :
  ARMFopn_coreP.sem_fopn_args o s = sem_fopn_args (ARMFopn.to_opn o) s.
Proof.
  case: o => -[xs o] es /=; case: sem_rexprs => //= >.
  by rewrite /exec_sopn /=; case: app_sopn.
Qed.

Lemma sem_fopns_equiv o s :
  ARMFopn_coreP.sem_fopns_args s o = sem_fopns_args s (map ARMFopn.to_opn o).
Proof. by elim: o s => //= o os ih s; rewrite sem_fopn_equiv; case: sem_fopn_args. Qed.

Section ARM_OP.

(* Linear state after executing a linear instruction [Lopn]. *)
Notation next_ls ls m vm := (lnext_pc (lset_mem_vm ls m vm)) (only parsing).
Notation next_vm_ls ls vm := (lnext_pc (lset_vm ls vm)) (only parsing).
Notation next_mem_ls ls m := (lnext_pc (lset_mem ls m)) (only parsing).

Lemma addi_sem_fopn_args {s xname vi y imm wy} :
  let: (xi, x) := mkv xname vi in
  get_var true (evm s) (v_var y) >>= to_word Uptr = ok wy
  -> let: wx' := Vword (wy + wrepr reg_size imm)in
     let: vm' := (evm s).[x <- wx'] in
     sem_fopn_args (ARMFopn.addi xi y imm) s = ok (with_vm s vm').
Proof. by move=> h; rewrite -sem_fopn_equiv; apply ARMFopn_coreP.addi_sem_fopn_args. Qed.

Lemma mov_sem_fopn_args {s xname vi y} {wy : word Uptr} :
  let: (xi, x) := mkv xname vi in
  get_var true (evm s) (v_var y) >>= to_word Uptr = ok wy ->
  let: vm' := (evm s).[x <- Vword wy] in
  sem_fopn_args (ARMFopn.mov xi y) s = ok (with_vm s vm').
Proof. by move=> h; rewrite -sem_fopn_equiv; apply ARMFopn_coreP.mov_sem_fopn_args. Qed.

Lemma align_sem_fopn_args xname vi y al s (wy : word Uptr) :
  let: (xi, x) := mkv xname vi in
  get_var true (evm s) (v_var y) >>= to_word Uptr = ok wy ->
  let: wx' := Vword (align_word al wy) in
  let: vm' := (evm s).[x <- wx'] in
  sem_fopn_args (ARMFopn.align xi y al) s = ok (with_vm s vm').
Proof.
 Opaque wsize_size.
 rewrite /=; t_xrbindP => *; t_arm_op.
 by rewrite /= wrepr_wnot ZlnotE Z.sub_1_r Z.add_1_r Z.succ_pred.
 Transparent wsize_size.
Qed.

(* FIXME try to remove the usage of this lemma, use sem_fopn_args version instead *)
Lemma align_eval_instr {lp ls ii xname vi y al} {wy : word Uptr} :
  let: (xi, x) := mkv xname vi in
  get_var true (lvm ls) (v_var y) = ok (Vword wy) ->
  let: li := li_of_fopn_args ii (ARMFopn.align xi y al) in
  let: wx' := Vword (align_word al wy) in
  let: vm' := (lvm ls).[x <- wx'] in
  eval_instr lp li ls = ok (next_vm_ls ls vm').
Proof.
  move=> h1; set vm := _.[ _ <- _].
  apply (sem_fopn_args_eval_instr (ls:= ls) (s' := with_vm (to_estate ls) vm)).
  by apply :  align_sem_fopn_args; rewrite h1 /= truncate_word_u.
Qed.

(* FIXME try to remove the usage of this lemma, use sem_fopn_args version instead *)
Lemma sub_eval_instr {lp ls ii xname vi y z} {wy wz : word Uptr} :
  let: (xi, x) := mkv xname vi in
  get_var true (lvm ls) (v_var y) = ok (Vword wy) -> 
  get_var true (lvm ls) (v_var z) = ok (Vword wz) ->
  let: li := li_of_fopn_args ii (ARMFopn.sub xi y z) in
  let: wx' := Vword (wy - wz)in
  let: vm' := (lvm ls).[x <- wx'] in
  eval_instr lp li ls = ok (next_vm_ls ls vm').
Proof.
  move=> hy hz.
  have /(_ xname vi):= ARMFopn_coreP.sub_sem_fopn_args (s:=to_estate _) (to_word_get_var hy) (to_word_get_var hz).
  by rewrite sem_fopn_equiv; apply: sem_fopn_args_eval_instr.
Qed.

(* FIXME try to remove the usage of this lemma, use sem_fopn_args version instead *)
Lemma subi_eval_instr {lp ls ii xname vi y imm wy} :
  let: (xi, x) := mkv xname vi in
  get_var true (lvm ls) (v_var y) = ok (Vword wy) ->
  let: li := li_of_fopn_args ii (ARMFopn.subi xi y imm) in 
  let: wx' := Vword (wy - wrepr reg_size imm)in
  let: vm' := (lvm ls).[x <- wx'] in
  eval_instr lp li ls = ok (next_vm_ls ls vm').
Proof.
  move=> h1; set vm := _.[ _ <- _].
  have /(_ xname vi imm):= ARMFopn_coreP.subi_sem_fopn_args (s:=to_estate _) (to_word_get_var h1).
  by rewrite sem_fopn_equiv; apply: sem_fopn_args_eval_instr.
Qed.

(* FIXME try to remove the usage of this lemma, use sem_fopn_args version instead *)
Lemma mov_eval_instr {lp ls ii xname vi y} {wy : word Uptr} :
  let: (xi, x) := mkv xname vi in
  get_var true (lvm ls) (v_var y) = ok (Vword wy) ->
  let: li := li_of_fopn_args ii (ARMFopn.mov xi y) in
  let: vm' := (lvm ls).[x <- Vword wy] in
  eval_instr lp li ls = ok (next_vm_ls ls vm').
Proof.
  move=> hy.
  have /(_ xname vi):= ARMFopn_coreP.mov_sem_fopn_args (s:=to_estate _) (to_word_get_var hy).
  by rewrite sem_fopn_equiv; apply: sem_fopn_args_eval_instr.
Qed.

(* FIXME try to remove the usage of this lemma, use sem_fopn_args version instead *)
Lemma movi_eval_instr {lp ls ii imm xname vi} :
  let: (xi, x) := mkv xname vi in
  (is_expandable imm \/ is_w16_encoding imm) ->
  let: li := li_of_fopn_args ii (ARMFopn.movi xi imm) in
  let: vm' := (lvm ls).[x <- Vword (wrepr U32 imm)] in
  eval_instr lp li ls = ok (next_vm_ls ls vm').
Proof.
  move=> h.
  have := [elaborate ARMFopn_coreP.movi_sem_fopn_args (xname := xname) (vi := vi) (s:=to_estate ls) h].
  by rewrite sem_fopn_equiv; apply: sem_fopn_args_eval_instr.
Qed.

Lemma li_eval_instr {lp ls ii imm xname vi} :
  let: (xi, x) := mkv xname vi in
  let: li := li_of_fopn_args ii (ARMFopn.li xi imm) in
  let: vm' := (lvm ls).[x <- Vword (wrepr U32 imm)] in
  eval_instr lp li ls = ok (next_vm_ls ls vm').
Proof. by t_arm_op. Qed.

Lemma str_eval_instr {lp ls m' ii xname vi y off wx} {wy : word reg_size} :
  let: (xi, x) := mkv xname vi in
  get_var true (lvm ls) x = ok (Vword wx)
  -> get_var true (lvm ls) (v_var y) = ok (Vword wy)
  -> write (lmem ls) Aligned (wx + wrepr Uptr off)%R wy = ok m'
  -> let: li := li_of_fopn_args ii (ARMFopn.str y xi off) in
     eval_instr lp li ls = ok (next_mem_ls ls m').
Proof. move=> ???. by t_arm_op. Qed.

End ARM_OP.

Opaque ARMFopn.add.
Opaque ARMFopn.addi.
Opaque ARMFopn.mov.
Opaque ARMFopn.movi.
Opaque ARMFopn.sub.
Opaque ARMFopn.subi.

Lemma li_lsem lp fn ls ii P Q xname vi imm :
  let: (xi, x) := mkv xname vi in
  let: lcmd := li_of_fopn_args ii (ARMFopn.li xi imm) in
  is_linear_of lp fn (P ++ lcmd :: Q)
  -> lpc ls = size P
  -> lfn ls = fn
  -> exists vm',
       let: ls' := setpc (lset_vm ls vm') (size P + 1) in
       [/\ lsem lp ls ls'
         , vm' =[\ Sv.singleton x ] lvm ls
         & get_var true vm' x = ok (Vword (wrepr reg_size imm))
       ].
Proof.
  move=> hlin hpc hfn.
  eexists; split.
  - rewrite addn1 -lnext_pc_setpc -hpc setpc_id.
    exact: (eval_lsem_step1 hlin _ _ li_eval_instr).
  - move=> x /Sv.singleton_spec /nesym /eqP hx. by rewrite Vm.setP_neq.
  by rewrite get_var_eq.
Qed.
Opaque ARMFopn.li.

Lemma smart_addi_sem_fopn_args xname vi y imm s (w : wreg) :
  let: (xi, x) := mkv xname vi in
  let: lc := ARMFopn.smart_addi xi y imm in
  is_arith_small imm \/ x <> v_var y ->
  get_var true (evm s) (v_var y) >>= to_word Uptr = ok w -> 
  exists vm',
    [/\ sem_fopns_args s lc = ok (with_vm s vm')
      , vm' =[\ Sv.singleton x ] evm s
      & get_var true vm' x = ok (Vword (w + wrepr reg_size imm)%R) ].
Proof.
  rewrite /=; set x := {| vname := _; |}; set xi := {| v_var := _; |}.
  move=> hor hget; rewrite -sem_fopns_equiv.
  have := [elaborate ARMFopn_coreP.gen_smart_opi_sem_fopn_args is_arith_small (neutral:= Some 0%Z)
             (@ARMFopn_coreP.add_sem_fopn_args _ _) (@ARMFopn_coreP.addi_sem_fopn_args _ _)].
  move=> /(_ _ xname vi xi y imm s w) [] //.
  + by move=> >; rewrite wrepr0 GRing.addr0.
  move=> vm' [hsem heq heqx] ; exists vm'; split => //=.
  apply: eq_exI heq; rewrite /xi /=; SvD.fsetdec.
Qed.

Lemma smart_subi_sem_fopn_args xname vi y imm s (w : wreg) :
  let: (xi, x) := mkv xname vi in
  let: lc := ARMFopn.smart_subi xi y imm in
  is_arith_small imm \/ x <> v_var y ->
  get_var true (evm s) (v_var y) >>= to_word Uptr = ok w ->
  exists vm',
    [/\ sem_fopns_args s lc = ok (with_vm s vm')
      , vm' =[\ Sv.singleton x ] evm s
      & get_var true vm' x = ok (Vword (w - wrepr reg_size imm))%R ].
Proof.
  rewrite /=; set x := {| vname := _; |}; set xi := {| v_var := _; |}.
  move=> hor hget; rewrite -sem_fopns_equiv.
  have := [elaborate ARMFopn_coreP.gen_smart_opi_sem_fopn_args is_arith_small (neutral:= Some 0%Z)
              (@ARMFopn_coreP.sub_sem_fopn_args _ _) (@ARMFopn_coreP.subi_sem_fopn_args _ _)].
  move=> /(_ _ xname vi xi y imm s w) [] //.
  + by move=> >; rewrite wrepr0 GRing.subr0.
  move=> vm' [hsem heq heqx] ; exists vm'; split => //=.
  apply: eq_exI heq; rewrite /xi /=; SvD.fsetdec.
Qed.

Lemma smart_addi_tmp_sem_fopn_args s (tmp : var_i) xname vi imm w :
  let: (xi, x) := mkv xname vi in
  let: lcmd := ARMFopn.smart_addi_tmp xi tmp imm in
  x <> v_var tmp -> 
  vtype tmp = sword U32 ->
  get_var true (evm s) x >>= to_word Uptr = ok w ->
  exists vm',
    [/\ sem_fopns_args s lcmd = ok (with_vm s vm')
      , evm s =[\ Sv.add x (Sv.singleton tmp) ] vm'
      & get_var true vm' x = ok (Vword (w + wrepr reg_size imm)%R) ].
Proof.
  rewrite /=; set x := {| vname := _; |}; set xi := {| v_var := _; |}.
  move=> hne hty hget; rewrite -sem_fopns_equiv.
  have := [elaborate ARMFopn_coreP.gen_smart_opi_sem_fopn_args is_arith_small (neutral:= Some 0%Z)
             (@ARMFopn_coreP.add_sem_fopn_args _ _) (@ARMFopn_coreP.addi_sem_fopn_args _ _)].
  move=> /(_ _ xname vi tmp xi imm s w) [] //.
  + by move=> >; rewrite wrepr0 GRing.addr0.
  + by right => h; rewrite h in hne.
  move=> vm' [hsem heq heqx] ; exists vm'; split => //=.
  by apply: eq_exS.
Qed.

Lemma smart_subi_tmp_sem_fopn_args s (tmp : var_i) xname vi imm w :
  let: (xi, x) := mkv xname vi in
  let: lcmd := ARMFopn.smart_subi_tmp xi tmp imm in
  x <> v_var tmp ->
  vtype tmp = sword Uptr ->
  get_var true (evm s) x >>= to_word Uptr = ok w ->
  exists vm',
    [/\ sem_fopns_args s lcmd = ok (with_vm s vm')
      , evm s =[\ Sv.add x (Sv.singleton tmp) ] vm'
      & get_var true vm' x = ok (Vword (w - wrepr reg_size imm)%R) ].
Proof.
  rewrite /=; set x := {| vname := _; |}; set xi := {| v_var := _; |}.
  move=> hne hty hget; rewrite -sem_fopns_equiv.
  have := [elaborate ARMFopn_coreP.gen_smart_opi_sem_fopn_args is_arith_small (neutral:= Some 0%Z)
              (@ARMFopn_coreP.sub_sem_fopn_args _ _) (@ARMFopn_coreP.subi_sem_fopn_args _ _)].
  move=> /(_ _ xname vi tmp xi imm s w) [] //.
  + by move=> >; rewrite wrepr0 GRing.subr0.
  + by right => h; rewrite h in hne.
  move=> vm' [hsem heq heqx] ; exists vm'; split => //=.
  by apply: eq_exS.
Qed.

End WITH_PARAMS.

End ARMFopnP.

Section WITH_PARAMS.

Context
  {atoI  : arch_toIdent}
  {syscall_state : Type}
  {sc_sem : syscall_sem syscall_state}
  {call_conv : calling_convention}
.

#[local] Existing Instance withsubword.

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

End WITH_PARAMS.
