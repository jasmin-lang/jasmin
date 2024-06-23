From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype.

Require Import
  expr
  fexpr
  label
  linear
  stack_zero_strategy
  arch_decl
  arch_extra
  arm_decl
  arm_extra
  arm_instr_decl
  arm_params_common.
Require Import compiler_util.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section STACK_ZEROIZATION.

Context {atoI : arch_toIdent}.

Section RSP.

Context
  (vrsp : var_i)
  (lbl : label)
  (alignment ws : wsize)
  (stk_max : Z)
.

Let vsaved_sp := mk_var_i (to_var R02).
Let voff := mk_var_i (to_var R03).
Let vzero := mk_var_i (to_var R12).
Let vzf := mk_var_i (to_var ZF).
Let vflags := [seq mk_var_i (to_var f) | f <- rflags ].
Let leflags := [seq LLvar f | f <- vflags ].

(* For both strategies we need to initialize:
   - [saved_sp] to save [SP]
   - [off] to offset from [SP] to already zeroized region
   - [SP] to align and point to the end of the region to zeroize
   - [zero] to zero
   Since we can't align [SP] directly, we use [zero] as a scratch register.
   This is the implementation:
    saved_sp = sp
    off:lo = stk_max:lo
    off:hi = stk_max:hi
    zero = saved_sp & - (wsize_size alignment)
    sp = zero
    sp -= off
    zero = 0
*)
Definition sz_init : lcmd :=
  let args :=
    ARMFopn.mov vsaved_sp vrsp
    :: ARMFopn.li voff stk_max
    :: ARMFopn.align vzero vsaved_sp alignment
    :: ARMFopn.mov vrsp vzero
    :: ARMFopn.sub vrsp vrsp voff
    :: [:: ARMFopn.movi vzero 0 ]
  in
  map (li_of_fopn_args dummy_instr_info) args.

Definition store_zero (off : fexpr) : linstr_r :=
  if store_mn_of_wsize ws is Some mn
    then
      let current := Store Aligned ws vrsp off in
      let op := ARM_op mn default_opts in
      Lopn [:: current ] (Oarm op) [:: rvar vzero ]
    else Lalign. (* Absurd case. *)

(* Implementation:
l1:
    ?{zf}, off = #SUBS(off, wsize_size ws)
    (ws)[rsp + off] = zero
    IF (!zf) GOTO l1
*)
Definition sz_loop : lcmd :=
  let dec_off :=
    let opts :=
      {| set_flags := true; is_conditional := false; has_shift := None; |}
    in
    let op := ARM_op SUB opts in
    let dec := rconst U32 (wsize_size ws) in
    Lopn (leflags ++ [:: LLvar voff ]) (Oarm op) [:: rvar voff; dec ]
  in
  let irs :=
    [:: Llabel InternalLabel lbl
      ; dec_off
      ; store_zero (Fvar voff)
      ; Lcond (Fapp1 Onot (Fvar vzf)) lbl
    ]
  in
  map (MkLI dummy_instr_info) irs.

Definition restore_sp :=
  [:: li_of_fopn_args dummy_instr_info (ARMFopn.mov vrsp vsaved_sp) ].

Definition stack_zero_loop : lcmd := sz_init ++ sz_loop ++ restore_sp.

Definition stack_zero_loop_vars :=
  sv_of_list v_var [:: vsaved_sp, voff, vzero & vflags].


(* Implementation:
    (ws)[rsp + (stk_max / wsize_size ws - 1) * wsize_size ws] = zero
    ...
    (ws)[rsp + wsize_size ws] = zero
    (ws)[rsp + 0] = zero
*)
Definition sz_unrolled : lcmd :=
  let rn := rev (ziota 0 (stk_max / wsize_size ws)) in
  [seq MkLI dummy_instr_info (store_zero (fconst reg_size (off * wsize_size ws))) | off <- rn ].

Definition stack_zero_unrolled : lcmd := sz_init ++ sz_unrolled ++ restore_sp.

(* [voff] is used, because it is set by [sz_init], even though it is not used in
   the for loop. *)
Definition stack_zero_unrolled_vars :=
  sv_of_list v_var [:: vsaved_sp, voff, vzero & vflags].

End RSP.

Definition stack_zeroization_cmd
  (szs : stack_zero_strategy)
  (rspn : Ident.ident)
  (lbl : label)
  (ws_align ws : wsize)
  (stk_max : Z) :
  cexec (lcmd * Sv.t) :=
  let err msg :=
    {|
      pel_msg := compiler_util.pp_s msg;
      pel_fn := None;
      pel_fi := None;
      pel_ii := None;
      pel_vi := None;
      pel_pass := Some "stack zeroization"%string;
      pel_internal := false;
  |}
  in
  let err_size :=
    err "Stack zeroization size not supported in ARMv7"%string in
  Let _ := assert (ws <= U32)%CMP err_size in
  let rsp := vid rspn in
  match szs with
  | SZSloop =>
    ok (stack_zero_loop rsp lbl ws_align ws stk_max, stack_zero_loop_vars)
  | SZSloopSCT =>
    let err_sct := err "Strategy ""loop with SCT"" is not supported in ARMv7"%string in
    Error err_sct
  | SZSunrolled =>
    ok (stack_zero_unrolled rsp ws_align ws stk_max, stack_zero_unrolled_vars)
  end.

End STACK_ZEROIZATION.
