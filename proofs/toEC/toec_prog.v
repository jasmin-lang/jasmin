Require Import toec_for toec_while for_to_while.
Import compiler_util expr.

#[local] Instance toec_LoopCounter : LoopCounter :=
  {| loop_counter := 100; loop_counterP := eq_refl; |}.

Section TOEC.
Context `{asmOp}.
Context (fresh_var_ident: v_kind -> instr_info -> string -> atype -> Ident.ident).

(* The loops are put in the form that EasyCrypt expects: the [for] loops
   become [while] loops. *)
Definition toec_prog {pT : progT} (p : prog) : cexec prog :=
  let p := toec_while_prog p in
  Let p := toec_for_prog fresh_var_ident p in
  for_to_while_prog fresh_var_ident p.

Definition toec_uprog : _uprog -> cexec _uprog :=
  toec_prog : (@prog _ _ progUnit -> _).

End TOEC.
