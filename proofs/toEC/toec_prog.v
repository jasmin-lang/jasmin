Require Import toec_for toec_while for_to_while normalize_calls contracts_to_asserts safety explicit_init
  simplify_asserts assert_facts dead_args drop_asserts drop_removable.
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

(* The passes common to the extraction for safety and to the plain extraction
   through it. The contracts become assertions once the destinations of the
   calls are normalised: the results of a call are then in distinct
   variables, which the postcondition of the callee reads. The safety
   conditions are added next, so that they describe the instructions that are
   extracted, those of the contracts included, and before [toec_while], which
   moves the condition part of a loop, where they go, out of it;
   [explicit_init] checks the form [normalize_calls] produces. In the result,
   the contracts are not checks but specifications: the semantics of the
   extracted program evaluates its assertions, not its contracts. The
   variables that [contracts_to_asserts] introduces are named by
   [fresh_removable_ident], the masks of [explicit_init] are given by [mask],
   so that the caller can tell them from the variables of the plain
   extraction. *)
Context (fresh_removable_ident : v_kind -> instr_info -> string -> atype -> Ident.ident).

Definition toec_uprog_assert (mask : var -> var) (p : _uprog) : cexec _uprog :=
  Let p := normalize_calls_prog (pT := progUnit) fresh_var_ident p in
  Let p := contracts_to_asserts_prog fresh_removable_ident p in
  Let p := sc_prog p in
  let p := toec_while_prog (pT := progUnit) p in
  Let p := toec_for_prog (pT := progUnit) fresh_var_ident p in
  explicit_init_prog mask p.

(* The extraction for safety: [toec_uprog_assert], then the assertions are
   simplified with what holds where they are ([simplify_asserts]): the
   constants, among them the masks of the scalars, and the masks of the arrays
   known to be full; then the conjuncts that an earlier assertion establishes
   are removed ([assert_facts]). Then the code that computes nothing used is
   removed, with the parameters and the results of the functions that nothing
   uses ([dead_args]): among them the masks that no assertion reads.
   [protect] tells the parameters and results that are kept, [dead_info
   protect] those that are dead. *)
Definition toec_uprog_safety (mask : var -> var) (protect : funname -> var -> bool)
    (dead_info : (funname -> var -> bool) -> _uprog ->
                 funname -> option (seq bool) * option (seq bool))
    (p : _uprog) : cexec _uprog :=
  Let p := toec_uprog_assert mask p in
  let p := assert_facts_prog (simplify_asserts_prog p) in
  dead_args_prog protect (dead_info protect) p.

(* The plain extraction through the passes of the extraction for safety:
   [toec_uprog_assert], then the assertions are removed, and with them the
   only readers of the variables these passes introduce, which
   [drop_removable] removes: [removable] holds for them, and only for them.
   The rest of the program is that of the plain extraction ([toec_uprog]). *)
Definition toec_uprog_via_safety (mask : var -> var) (removable : var -> bool)
    (p : _uprog) : cexec _uprog :=
  Let p := toec_uprog_assert mask p in
  drop_removable_prog removable (drop_asserts_prog (pT := progUnit) p).

End TOEC.
