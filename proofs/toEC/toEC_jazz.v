Require Import compiler_util expr.
Require Import normalize_cond.
Require Import refresh_for.
Require Import for_to_while.
Require Import flatten_while.

Section TOEC.

Context
  {asm_op : Type}
  {asmop : asmOp asm_op}
  (fresh_var_ident : v_kind -> instr_info -> string -> atype -> Ident.ident)
.

Definition toEC_prog (normal : bool) (p : _uprog) : cexec _uprog :=
  Let p1 := refresh_for_prog fresh_var_ident false (normalize_cond_prog p) in
  Let p2 := if normal then for_to_while_prog fresh_var_ident p1 else ok p1 in
  ok (flatten_while_prog p2).

End TOEC.
