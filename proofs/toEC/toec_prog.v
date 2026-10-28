Require Import wint_int toec_for toec_while normalize_calls contracts_to_asserts safety
  explicit_init simplify_asserts assert_facts typing_check dead_args drop_asserts.
Import compiler_util expr.

#[local] Instance toec_LoopCounter : LoopCounter :=
  {| loop_counter := 100; loop_counterP := eq_refl; |}.

Section TOEC.
Context `{asmOp} {pd : PointerData} {msfsz : MSFsize}.
Context (fresh_var_ident: v_kind -> instr_info -> string -> atype -> Ident.ident).

(* [wi2i_prog] turns the machine words annotated [wint] into integers;
   [get_info] tells the integer variable of each such word variable. *)
Context (get_info : _uprog -> Sv.t * (var -> option (signedness * var))).

(* The passes common to both extractions: the words annotated [wint] become
   integers when [wi2i] holds (on a program without [wint], [wi2i_prog] is the
   identity); then the destinations of the calls are normalised, so that the
   results of a call are in distinct variables, and the loops are put in the
   form that EasyCrypt expects. *)
Definition toec_uprog_common (wi2i : bool) (p : _uprog) : cexec _uprog :=
  Let p := if wi2i then wi2i_prog get_info p else ok p in
  Let p := normalize_calls_prog (pT := progUnit) fresh_var_ident p in
  let p := toec_while_prog (pT := progUnit) p in
  toec_for_prog (pT := progUnit) fresh_var_ident p.

(* The plain extraction: the common passes, then the assertions of the source
   are removed. *)
Definition toec_uprog (wi2i : bool) (p : _uprog) : cexec _uprog :=
  Let p := toec_uprog_common wi2i p in
  ok (drop_asserts_prog (pT := progUnit) p).

(* The extraction for safety. After the common passes, the contracts become
   assertions: the postcondition of a callee reads the results of the call,
   which are in distinct variables. The safety conditions are added next, so
   that they describe the instructions that are extracted, those of the
   contracts included. [sc_prog] puts the conditions of a loop
   [while {c1} e {c2}] in [c1], which EasyCrypt does not have: [toec_while]
   moves it out again. Then the initialisation state of the variables is made
   explicit ([explicit_init], with the masks given by [mask]); the assertions
   are simplified with what holds where they are ([simplify_asserts]): the
   constants, among them the masks of the scalars, and the masks of the arrays
   known to be full; then the conjuncts that an earlier assertion establishes
   are removed ([assert_facts]). The result is type checked ([check_prog]):
   [dead_args] is correct on a well typed program. Last, the code that
   computes nothing used is removed, with the parameters and the results of
   the functions that nothing uses ([dead_args]): among them the masks that
   no assertion reads and the copies that [contracts_to_asserts] introduces,
   named by [fresh_copy_ident].
   [protect] tells the parameters and results that are kept, [dead_info
   protect] those that are dead. In the result, the contracts are not checks
   but specifications: the semantics of the extracted program evaluates its
   assertions, not its contracts. *)
Context (fresh_copy_ident : v_kind -> instr_info -> string -> atype -> Ident.ident).

Definition toec_uprog_safety (wi2i : bool) (mask : var -> var)
    (protect : funname -> var -> bool)
    (dead_info : (funname -> var -> bool) -> _uprog ->
                 funname -> option (seq bool) * option (seq bool))
    (p : _uprog) : cexec _uprog :=
  Let p := toec_uprog_common wi2i p in
  Let p := contracts_to_asserts_prog fresh_copy_ident p in
  Let p := sc_prog p in
  let p := toec_while_prog (pT := progUnit) p in
  Let p := explicit_init_prog mask p in
  let p := assert_facts_prog (simplify_asserts_prog p) in
  Let _ := check_prog p in
  dead_args_prog protect (dead_info protect) p.

End TOEC.
