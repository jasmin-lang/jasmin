Require Import expr.
Require Import normalize_cond.
Require Import refresh_for.

Section TOEC.

Context
  {asm_op : Type}
  {asmop : asmOp asm_op}
  (fresh_var_ident : v_kind -> instr_info -> string -> atype -> Ident.ident)
.

Definition toEC_prog (p : _uprog) : _uprog :=
  refresh_for_prog fresh_var_ident false (normalize_cond_prog p).

End TOEC.
