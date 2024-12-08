From mathcomp Require Import ssreflect.
Require Import expr compiler_util.

Import Utf8.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Import E.

  Definition pass : string := "loop unrolling".

  Definition for_loop_remains :=
    {| pel_msg := pp_s "for loops remain"
    ; pel_fn := None
    ; pel_fi := None
    ; pel_ii := None
    ; pel_vi := None
    ; pel_pass := Some pass
    ; pel_internal := false |}.

End E.

Section ASM_OP.

Context `{asmop: asmOp}.

Section CHECK_NO_FOR_LOOP_CMD.
  Context (check_no_for_loop_instr: instr → cexec unit).

  Definition check_no_for_loop_cmd c := allM check_no_for_loop_instr c.

End CHECK_NO_FOR_LOOP_CMD.

Fixpoint check_no_for_loop_instr_r i : cexec unit :=
  match i with
  | (Cassgn _ _ _ _ | Copn _ _ _ _ | Csyscall _ _ _ | Ccall _ _ _)
    => ok tt
  | (Cif _ c c' | Cwhile _ c _ c') =>
      check_no_for_loop_cmd check_no_for_loop_instr c >> check_no_for_loop_cmd check_no_for_loop_instr c'
  | Cfor _ _ _ => Error E.for_loop_remains
  end
with check_no_for_loop_instr i : cexec unit :=
  let: MkI ii i := i in
  add_iinfo ii (check_no_for_loop_instr_r i).

Definition check_no_for_loop_fd (f : funname * ufundef) :=
  let: (fn, fd) := f in
  add_funname fn (add_finfo (f_info fd) (check_no_for_loop_cmd check_no_for_loop_instr (f_body fd))).

Definition check_no_for_loop (p: uprog) :=
  allM check_no_for_loop_fd (p_funcs p).

End ASM_OP.
