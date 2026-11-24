From Coq Require Import Uint63.
Require Import toec_for toec_while normalize_calls for_to_while.
Import compiler_util expr.

#[local] Instance toec_LoopCounter : LoopCounter :=
  {| loop_counter := 100; loop_counterP := eq_refl; |}.

Section TOEC.
Context `{asmOp} {pd : PointerData} {msfsz : MSFsize}.
Context (fresh_var_ident: v_kind -> instr_info -> int -> string -> atype -> Ident.ident).
Context (arrays_by_size : bool).

(* The loops are put in the form that EasyCrypt expects: the [for] loops
   become [while] loops. *)
Definition toec_prog {pT : progT} (p : prog) : cexec prog :=
  let fresh_var_ident0 k ii := fresh_var_ident k ii 0%uint63 in
  let p := toec_while_prog p in
  Let p := toec_for_prog fresh_var_ident0 p in
  Let p := normalize_calls_prog fresh_var_ident arrays_by_size p in
  for_to_while_prog fresh_var_ident0 p.

Definition toec_uprog : _uprog -> cexec _uprog :=
  toec_prog : (@prog _ _ progUnit -> _).

End TOEC.
