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


Definition create_safety_asserts (p: _uprog): result compiler_util.pp_error_loc _uprog :=
  (* First add the safety conditions *)
  Let p := sc_prog p in
  (* This make the arguments and destinations of function call uniq variable.
     Similar to make reference argument *)
  Let p := extra_vars_call_prog create_var p in
  (* Introduce the boolean variables that encode is_var_init and is_arr_init *)
  let p := rm_var_init_prog B p in
  (* Add the post after the call.
     Do we really want to keep it or to intergrate it into constant_prop ?
     One advantage is that static analysis can reuse the result more easyly ?
  *)
  let p := contracts_asserts_prog p in
  (* Performs constant propagation *)
  let p := rm_var_init_const_prop B p in
  (* Dead code *)
  ok (rm_var_init_dc is_move_op p)
.

End SAFETY_ASSERTS.
