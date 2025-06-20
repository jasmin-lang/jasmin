Require Import
compiler
psem
safety
wint_int
extra_vars_call
contracts_asserts
remove_init_preds.


Section SAFETY_ASSERTS.
Context `{asmop:asmOp} {pd: PointerData} {msfsz : MSFsize}.
Context (create_var : v_kind -> string -> stype -> var_info -> var).
Context (B : var -> var).
Context {fcp : FlagCombinationParams}.
Context (is_move_op : asm_op_t -> bool).


Definition create_safety_asserts (p: _uprog): _uprog :=
  let p := sc_prog p in
  let p := extra_vars_call_prog create_var p in
  let p := rm_var_init_prog create_var B p in
  let p := contracts_asserts_prog p in
  let p := rm_var_init_const_prop B p in
  rm_var_init_dc is_move_op p
.

End SAFETY_ASSERTS.