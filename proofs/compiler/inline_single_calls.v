From Coq Require Import ZArith.
From mathcomp Require Import
  all_ssreflect
  all_algebra.

Require Import
  compiler_util
  expr
  utils.
Require
  dead_calls
  inline.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section WITH_PARAMS.

Context
  {wsw : WithSubWord}
  {asm_op : Type}
  {asmop : asmOp asm_op}.

Definition isc_prog
  (single_calls : seq funname)
  (rename_fd : instr_info -> funname -> ufundef -> ufundef)
  (to_keep : seq funname)
  (p : uprog) :
  cexec uprog :=
  if nilp single_calls
  then ok p
  else
    let is_inline ii fn := if fn \in single_calls then Some ii else None in
    Let p := inline.inline_prog_err is_inline rename_fd p in
    dead_calls.dead_calls_err_seq to_keep p.

End WITH_PARAMS.
