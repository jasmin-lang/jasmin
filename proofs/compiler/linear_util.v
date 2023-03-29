From mathcomp Require Import
  all_ssreflect
  all_algebra.
Require Import expr linear.
Require Import compiler_util.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Notation map_lprog_name := (map_cfprog_name_gen lfd_info).

Section ASM_OP.

Context
  {asm_op : Type}
  {asmop : asmOp asm_op}.

Definition map_lfundef_body
  (f : lcmd -> lcmd)
  (lfd : lfundef) :
  lfundef :=
  {|
    lfd_info := lfd_info lfd;
    lfd_align := lfd_align lfd;
    lfd_tyin := lfd_tyin lfd;
    lfd_arg := lfd_arg lfd;
    lfd_body := f (lfd_body lfd);
    lfd_tyout := lfd_tyout lfd;
    lfd_res := lfd_res lfd;
    lfd_export := lfd_export lfd;
    lfd_callee_saved := lfd_callee_saved lfd;
    lfd_total_stack := lfd_total_stack lfd;
  |}.

End ASM_OP.

Notation with_lfd_body lfd lcmd :=
  (map_lfundef_body (fun _ => lcmd) lfd) (only parsing).
