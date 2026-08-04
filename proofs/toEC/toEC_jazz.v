Require Import compiler_util expr arch_decl arch_extra.
Require Import normalize_cond.
Require Import refresh_for.
Require Import for_to_while.
Require Import flatten_while.
Require Import remove_baseop_casts.
Require Import normalize_calls.
Require Import make_coercions_explicit.

Section TOEC.

Context
  {reg regx xreg rflag cond asm_op extra_op : Type}
  {asm_e : asm_extra reg regx xreg rflag cond asm_op extra_op}
  (fresh_var_ident : v_kind -> instr_info -> string -> atype -> Ident.ident)
.

Definition toEC_prog (normal : bool) (p : _uprog) : cexec _uprog :=
  Let p1 := refresh_for_prog fresh_var_ident false (normalize_cond_prog p) in
  Let p2 := if normal then for_to_while_prog fresh_var_ident p1 else ok p1 in
  let p3 := flatten_while_prog p2 in
  Let p4 := remove_baseop_casts_prog fresh_var_ident p3 in
  Let p5 := normalize_calls_prog fresh_var_ident p4 in
  mce_prog p5.

End TOEC.
