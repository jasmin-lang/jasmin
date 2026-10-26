Require Import toec_for toec_while for_to_while normalize_calls contracts_to_asserts safety explicit_init.
Import compiler_util expr.

#[local] Instance toec_LoopCounter : LoopCounter :=
  {| loop_counter := 100; loop_counterP := eq_refl; |}.

Section TOEC.
Context `{asmOp} {pd : PointerData} {msfsz : MSFsize}.
Context (fresh_var_ident: v_kind -> instr_info -> string -> atype -> Ident.ident).

(* The loops are put in the form that EasyCrypt expects: the [for] loops
   become [while] loops. *)
Definition toec_prog {pT : progT} (p : prog) : cexec prog :=
  let p := toec_while_prog p in
  Let p := toec_for_prog fresh_var_ident p in
  Let p := normalize_calls_prog fresh_var_ident p in
  for_to_while_prog fresh_var_ident p.

Definition toec_uprog : _uprog -> cexec _uprog :=
  toec_prog : (@prog _ _ progUnit -> _).

(* The extraction for safety. The contracts become assertions once the
   destinations of the calls are normalised: the results of a call are then in
   distinct variables, which the postcondition of the callee reads. The safety
   conditions are added next, so that they describe the instructions that are
   extracted, those of the contracts included, and before [toec_while], which
   moves the condition part of a loop, where they go, out of it;
   [explicit_init] checks the form [normalize_calls] produces. In the result,
   the contracts are not checks but specifications: the semantics of the
   extracted program evaluates its assertions, not its contracts. *)
Definition toec_uprog_safety (mask : var -> var) (p : _uprog) : cexec _uprog :=
  Let p := normalize_calls_prog (pT := progUnit) fresh_var_ident p in
  Let p := contracts_to_asserts_prog fresh_var_ident p in
  Let p := sc_prog p in
  let p := toec_while_prog (pT := progUnit) p in
  Let p := toec_for_prog (pT := progUnit) fresh_var_ident p in
  explicit_init_prog mask p.

End TOEC.
