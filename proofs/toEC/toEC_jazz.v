Require Import expr.
Require Import normalize_cond.

Section TOEC.

Context
  {asm_op : Type}
  {asmop : asmOp asm_op}
.

Definition toEC_prog (p : _uprog) : _uprog := normalize_cond_prog p.

End TOEC.
