(* Stack zeroization for ARMv8-A (AArch64). *)

From mathcomp Require Import ssreflect.

Require Import
  expr
  fexpr
  label
  linear
  stack_zero_strategy
  arch_decl
  arch_extra
  armv8a_decl
  armv8a_extra
  armv8a_instr_decl
  armv8a_params_core.
Require Import compiler_util.

Section STACK_ZEROIZATION.

Context {atoI : arch_toIdent}.

(* Wrappers turning [ARMv8AFopn_core] argument triples into [fopn_args]. *)
Definition to_opn '(d, o, e) : fopn_args := (d, Oarmv8a o, e).

Definition fopn_mov x y := to_opn (ARMv8AFopn_core.mov x y).
Definition fopn_sub x y z := to_opn (ARMv8AFopn_core.sub x y z).
Definition fopn_movi x imm := to_opn (ARMv8AFopn_core.movi x imm).
Definition fopn_align x y al := to_opn (ARMv8AFopn_core.align x y al).

(* Load an immediate to a register (kept as a single pseudo-instruction,
   expanded to a MOVZ/MOVK sequence at assembly generation). *)
Definition fopn_li (x : var_i) (imm : Z) : fopn_args :=
  let op := Oasm (ExtOp (Oarmv8a_smart_li reg_size)) in
  ([:: LLvar x ], op, [:: rconst reg_size imm ]).

Section RSP.

Context
  (vrsp : var_i)
  (lbl : label)
  (alignment ws : wsize)
  (stk_max : Z)
.

Let vsaved_sp := mk_var_i (to_var R2).
Let voff := mk_var_i (to_var R3).
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
    off = stk_max
    zero = saved_sp & - (wsize_size alignment)
    sp = zero
    sp -= off
    zero = 0
*)
Definition sz_init : lcmd :=
  let args :=
    fopn_mov vsaved_sp vrsp
    :: fopn_li voff stk_max
    :: fopn_align vzero vsaved_sp alignment
    :: fopn_mov vrsp vzero
    :: fopn_sub vrsp vrsp voff
    :: [:: fopn_movi vzero 0 ]
  in
  map (li_of_fopn_args dummy_instr_info) args.

Definition store_zero (off : fexpr) : linstr_r :=
  if store_mn_of_wsize ws is Some mn
    then
      let current := Store Aligned ws (faddv Uptr vrsp off) in
      (* A 32-bit clear step needs the W form of STR; the narrow stores
         (STRB, STRH) store the low bits of the X register. *)
      let op := ARMv8A_op mn (opts_at (match ws with U32 => U32 | _ => U64 end)) in
      Lopn [:: current ] (Oarmv8a op) [:: rvar vzero ]
    else Lalign. (* Absurd case. *)

(* Implementation:
l1:
    ?{zf}, off = #SUBS(off, wsize_size ws)
    (ws)[rsp + off] = zero
    IF (!zf) GOTO l1
*)
Definition sz_loop : lcmd :=
  let dec_off :=
    let op := ARMv8A_op SUBS default_opts in
    let dec := rconst reg_size (wsize_size ws) in
    Lopn (leflags ++ [:: LLvar voff ]) (Oarmv8a op) [:: rvar voff; dec ]
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
  [:: li_of_fopn_args dummy_instr_info (fopn_mov vrsp vsaved_sp) ].

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
    err "Stack zeroization size not supported in ARMv8-A"%string in
  Let _ := assert (ws <= U64)%CMP err_size in
  let rsp := vid rspn in
  match szs with
  | SZSloop =>
    ok (stack_zero_loop rsp lbl ws_align ws stk_max, stack_zero_loop_vars)
  | SZSloopSCT =>
    let err_sct := err "Strategy ""loop with SCT"" is not supported in ARMv8-A"%string in
    Error err_sct
  | SZSunrolled =>
    ok (stack_zero_unrolled rsp ws_align ws stk_max, stack_zero_unrolled_vars)
  end.

End STACK_ZEROIZATION.
