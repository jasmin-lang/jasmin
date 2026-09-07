(* Correctness of the params-level ARMv8-A operation wrappers
   ([ARMv8AFopn_*] in armv8a_params.v), mirroring [arm_params_common_proof.v].

   These lemmas lift the core [sem_fopn_args] results of
   [armv8a_params_core_proof.v] through the [to_opn] wrapper (which tags the
   core op with [Oarmv8a]) to the generic linear-semantics [sem_fopn_args] and
   [eval_instr], for the single-instruction builders used by the compiler's
   stack handling: [mov], [addi], [subi] and [align], and for the
   [li]-based smart combinators [smart_addi], [smart_subi] and their
   in-place [_tmp] variants. *)

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
  armv8a_decl
  armv8a_extra
  armv8a_instr_decl
  armv8a_params_core
  armv8a_params_core_proof
  armv8a_params.

Ltac t_armv8a_op :=
  rewrite /eval_instr /= /sem_sopn /= /exec_sopn /get_gvar /=;
  t_simpl_rewrites;
  rewrite /of_estate /= /with_vm /=;
  repeat rewrite truncate_word_u /=;
  rewrite ?zero_extend_u ?addn1;
  t_simpl_rewrites.

Module ARMv8AFopnP.

Section WITH_PARAMS.

Context
  {atoI  : arch_toIdent}
  {syscall_state : Type}
  {sc_sem : syscall_sem syscall_state}
  {call_conv : calling_convention}.

#[local] Existing Instance withsubword.

Let mkv xname vi :=
  let: x := {| vname := xname; vtype := aword armv8a_reg_size; |} in
  let: xi := {| v_var := x; v_info := vi; |} in
  (xi, x).

Lemma sem_fopn_equiv o s :
  ARMv8AFopn_coreP.sem_fopn_args o s = sem_fopn_args (to_opn o) s.
Proof.
  case: o => -[xs o] es /=; case: sem_rexprs => //= >.
  rewrite /exec_sopn /= /sopn_sem /=; case: id_valid => //=.
  rewrite /sopn_sem_ /= /semi_to_atype.
  move: (computational_eq _) (computational_eq _) => e1 e2.
  rewrite <- e1, <- e2.
  by case: app_sopn.
Qed.

Lemma sem_fopns_equiv o s :
  ARMv8AFopn_coreP.sem_fopns_args s o = sem_fopns_args s (map to_opn o).
Proof. by elim: o s => //= o os ih s; rewrite sem_fopn_equiv; case: sem_fopn_args. Qed.

Section ARMV8A_OP.

Notation next_vm_ls ls vm := (lnext_pc (lset_vm ls vm)) (only parsing).

Lemma mov_sem_fopn_args {s} {xi:var_i} {y} {wy : word Uptr} :
  convertible xi.(vtype) (aword armv8a_reg_size) ->
  get_var true (evm s) (v_var y) >>= to_word Uptr = ok wy ->
  let: vm' := (evm s).[xi <- Vword wy] in
  sem_fopn_args (ARMv8AFopn_mov xi y) s = ok (with_vm s vm').
Proof. by move=> hc h; rewrite -sem_fopn_equiv; apply: ARMv8AFopn_coreP.mov_sem_fopn_args. Qed.

Lemma addi_sem_fopn_args {s} {xi:var_i} {y imm wy} :
  convertible xi.(vtype) (aword armv8a_reg_size) ->
  get_var true (evm s) (v_var y) >>= to_word Uptr = ok wy ->
  let: wx' := Vword (wy + wrepr reg_size imm)in
  let: vm' := (evm s).[xi <- wx'] in
  sem_fopn_args (ARMv8AFopn_addi xi y imm) s = ok (with_vm s vm').
Proof. by move=> hc h; rewrite -sem_fopn_equiv; apply: ARMv8AFopn_coreP.addi_sem_fopn_args. Qed.

Lemma subi_sem_fopn_args {s} {xi:var_i} {y imm wy} :
  convertible xi.(vtype) (aword armv8a_reg_size) ->
  get_var true (evm s) (v_var y) >>= to_word Uptr = ok wy ->
  let: wx' := Vword (wy - wrepr reg_size imm)in
  let: vm' := (evm s).[xi <- wx'] in
  sem_fopn_args (ARMv8AFopn_subi xi y imm) s = ok (with_vm s vm').
Proof. by move=> hc h; rewrite -sem_fopn_equiv; apply: ARMv8AFopn_coreP.subi_sem_fopn_args. Qed.

(* The alignment mask [Z_mod_lnot (wsize_size al - 1)] is the complement of
   [wsize_size al - 1], i.e. [-wsize_size al] modulo the register base, so the
   AND behind [align] computes exactly [align_word]. *)
Lemma armv8a_align_mask (ws : wsize) al :
  wrepr ws (Z_mod_lnot (wsize_size al - 1) ws) = wrepr ws (- wsize_size al).
Proof.
  rewrite /Z_mod_lnot wrepr_mod -wrepr_wnot wrepr_mod wrepr_wnot ZlnotE.
  by f_equal; ring.
Qed.

Lemma align_sem_fopn_args {s} {xi:var_i} {y al} {wy : word Uptr} :
  convertible xi.(vtype) (aword armv8a_reg_size) ->
  get_var true (evm s) (v_var y) >>= to_word Uptr = ok wy ->
  let: wx' := Vword (align_word al wy) in
  let: vm' := (evm s).[xi <- wx'] in
  sem_fopn_args (ARMv8AFopn_align xi y al) s = ok (with_vm s vm').
Proof.
  move=> hc h.
  rewrite -sem_fopn_equiv /ARMv8AFopn_core.align /align_word -armv8a_align_mask.
  exact: (ARMv8AFopn_coreP.andi_sem_fopn_args (imm := Z_mod_lnot (wsize_size al - 1) reg_size) hc h).
Qed.

Lemma mov_eval_instr {lp ls ii xname vi y} {wy : word Uptr} :
  let: (xi, x) := mkv xname vi in
  get_var true (lvm ls) (v_var y) = ok (Vword wy) ->
  let: li := li_of_fopn_args ii (ARMv8AFopn_mov xi y) in
  let: vm' := (lvm ls).[x <- Vword wy] in
  eval_instr lp li ls = ok (next_vm_ls ls vm').
Proof.
  move=> hy.
  have := mov_sem_fopn_args (s:=to_estate _) (xi:=(mkv xname vi).1) erefl (to_word_get_var hy).
  by apply: sem_fopn_args_eval_instr.
Qed.

Lemma addi_eval_instr {lp ls ii xname vi y imm wy} :
  let: (xi, x) := mkv xname vi in
  get_var true (lvm ls) (v_var y) = ok (Vword wy) ->
  let: li := li_of_fopn_args ii (ARMv8AFopn_addi xi y imm) in
  let: wx' := Vword (wy + wrepr reg_size imm)in
  let: vm' := (lvm ls).[x <- wx'] in
  eval_instr lp li ls = ok (next_vm_ls ls vm').
Proof.
  move=> h1.
  have := addi_sem_fopn_args (s:=to_estate _) (xi:=(mkv xname vi).1) (imm:=imm) erefl (to_word_get_var h1).
  by apply: sem_fopn_args_eval_instr.
Qed.

Lemma subi_eval_instr {lp ls ii xname vi y imm wy} :
  let: (xi, x) := mkv xname vi in
  get_var true (lvm ls) (v_var y) = ok (Vword wy) ->
  let: li := li_of_fopn_args ii (ARMv8AFopn_subi xi y imm) in
  let: wx' := Vword (wy - wrepr reg_size imm)in
  let: vm' := (lvm ls).[x <- wx'] in
  eval_instr lp li ls = ok (next_vm_ls ls vm').
Proof.
  move=> h1.
  have := subi_sem_fopn_args (s:=to_estate _) (xi:=(mkv xname vi).1) (imm:=imm) erefl (to_word_get_var h1).
  by apply: sem_fopn_args_eval_instr.
Qed.

Lemma align_eval_instr {lp ls ii xname vi y al} {wy : word Uptr} :
  let: (xi, x) := mkv xname vi in
  get_var true (lvm ls) (v_var y) = ok (Vword wy) ->
  let: li := li_of_fopn_args ii (ARMv8AFopn_align xi y al) in
  let: wx' := Vword (align_word al wy) in
  let: vm' := (lvm ls).[x <- wx'] in
  eval_instr lp li ls = ok (next_vm_ls ls vm').
Proof.
  move=> h1.
  have := align_sem_fopn_args (s:=to_estate _) (xi:=(mkv xname vi).1) (al:=al) erefl (to_word_get_var h1).
  by apply: sem_fopn_args_eval_instr.
Qed.

End ARMV8A_OP.

Lemma smart_addi_sem_fopn_args (xi:var_i) y imm s (w : word Uptr) :
  convertible xi.(vtype) (aword armv8a_reg_size) ->
  let: lc := ARMv8AFopn_smart_addi xi y imm in
  is_arith_small imm \/ xi <> v_var y :> var ->
  get_var true (evm s) (v_var y) >>= to_word Uptr = ok w ->
  exists vm',
    [/\ sem_fopns_args s lc = ok (with_vm s vm')
      , vm' =[\ Sv.singleton xi ] evm s
      & get_var true vm' xi = ok (Vword (w + wrepr reg_size imm)%R) ].
Proof.
  move=> hc hor hget; rewrite -sem_fopns_equiv.
  have := [elaborate
    ARMv8AFopn_coreP.gen_smart_opi_sem_fopn_args
      (is_small := is_arith_small) (neutral := Some 0%Z)
      (@ARMv8AFopn_coreP.add_sem_fopn_args _ _)
      (@ARMv8AFopn_coreP.addi_sem_fopn_args _ _)].
  move=> /(_ _ xi xi y imm s w) [] //.
  + by move=> >; rewrite wrepr0 GRing.addr0.
  move=> vm' [hsem heq heqx]; exists vm'; split => //=.
  by apply: eq_exI heq; clear; SvD.fsetdec.
Qed.

Lemma smart_subi_sem_fopn_args (xi:var_i) y imm s (w : word Uptr) :
  convertible xi.(vtype) (aword armv8a_reg_size) ->
  let: lc := ARMv8AFopn_smart_subi xi y imm in
  is_arith_small imm \/ xi <> v_var y :> var ->
  get_var true (evm s) (v_var y) >>= to_word Uptr = ok w ->
  exists vm',
    [/\ sem_fopns_args s lc = ok (with_vm s vm')
      , vm' =[\ Sv.singleton xi ] evm s
      & get_var true vm' xi = ok (Vword (w - wrepr reg_size imm)%R) ].
Proof.
  move=> hc hor hget; rewrite -sem_fopns_equiv.
  have := [elaborate
    ARMv8AFopn_coreP.gen_smart_opi_sem_fopn_args
      (is_small := is_arith_small) (neutral := Some 0%Z)
      (@ARMv8AFopn_coreP.sub_sem_fopn_args _ _)
      (@ARMv8AFopn_coreP.subi_sem_fopn_args _ _)].
  move=> /(_ _ xi xi y imm s w) [] //.
  + by move=> >; rewrite wrepr0 GRing.subr0.
  move=> vm' [hsem heq heqx]; exists vm'; split => //=.
  by apply: eq_exI heq; clear; SvD.fsetdec.
Qed.

Lemma smart_addi_tmp_sem_fopn_args s (tmp xi : var_i) imm (w : word Uptr) :
  convertible xi.(vtype) (aword armv8a_reg_size) ->
  let: lcmd := ARMv8AFopn_smart_addi_tmp xi tmp imm in
  v_var xi <> v_var tmp ->
  convertible (vtype tmp) (aword Uptr) ->
  get_var true (evm s) (v_var xi) >>= to_word Uptr = ok w ->
  exists vm',
    [/\ sem_fopns_args s lcmd = ok (with_vm s vm')
      , evm s =[\ Sv.add xi (Sv.singleton tmp) ] vm'
      & get_var true vm' xi = ok (Vword (w + wrepr reg_size imm)%R) ].
Proof.
  move=> hc hne hty hget; rewrite -sem_fopns_equiv.
  have := [elaborate
    ARMv8AFopn_coreP.gen_smart_opi_sem_fopn_args
      (is_small := is_arith_small) (neutral := Some 0%Z)
      (@ARMv8AFopn_coreP.add_sem_fopn_args _ _)
      (@ARMv8AFopn_coreP.addi_sem_fopn_args _ _)].
  move=> /(_ _ tmp xi xi imm s w) [] //.
  + by move=> >; rewrite wrepr0 GRing.addr0.
  + by right => h; rewrite h in hne.
  move=> vm' [hsem heq heqx]; exists vm'; split => //=.
  by apply: eq_exS.
Qed.

Lemma smart_subi_tmp_sem_fopn_args s (tmp xi : var_i) imm (w : word Uptr) :
  convertible xi.(vtype) (aword armv8a_reg_size) ->
  let: lcmd := ARMv8AFopn_smart_subi_tmp xi tmp imm in
  v_var xi <> v_var tmp ->
  convertible (vtype tmp) (aword Uptr) ->
  get_var true (evm s) (v_var xi) >>= to_word Uptr = ok w ->
  exists vm',
    [/\ sem_fopns_args s lcmd = ok (with_vm s vm')
      , evm s =[\ Sv.add xi (Sv.singleton tmp) ] vm'
      & get_var true vm' xi = ok (Vword (w - wrepr reg_size imm)%R) ].
Proof.
  move=> hc hne hty hget; rewrite -sem_fopns_equiv.
  have := [elaborate
    ARMv8AFopn_coreP.gen_smart_opi_sem_fopn_args
      (is_small := is_arith_small) (neutral := Some 0%Z)
      (@ARMv8AFopn_coreP.sub_sem_fopn_args _ _)
      (@ARMv8AFopn_coreP.subi_sem_fopn_args _ _)].
  move=> /(_ _ tmp xi xi imm s w) [] //.
  + by move=> >; rewrite wrepr0 GRing.subr0.
  + by right => h; rewrite h in hne.
  move=> vm' [hsem heq heqx]; exists vm'; split => //=.
  by apply: eq_exS.
Qed.

End WITH_PARAMS.

End ARMv8AFopnP.
