Require Import toec_for toec_while.
Import compiler_util expr.

Section TOEC.
Context `{asmOp}.
Context (fresh_var_ident: v_kind -> instr_info -> string -> atype -> Ident.ident).

Definition toec_prog {pT : progT} (p : prog) : cexec prog :=
  let p := toec_while_prog p in
  toec_for_prog fresh_var_ident p.

Definition toec_uprog : _uprog -> cexec _uprog :=
  toec_prog : (@prog _ _ progUnit -> _).

End TOEC.
