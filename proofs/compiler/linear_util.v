From mathcomp Require Import all_ssreflect all_algebra.
Require Import expr label linear.
Require Import compiler_util.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* [map_cfprog_gen] specialized to functions of type [lfundef] *)
Notation map_lprog_name := (map_cfprog_name_gen lfd_info).
Notation map_lprog := (map_cfprog_gen lfd_info).

Section ASM_OP.

Context {asm_op} {asmop : asmOp asm_op}.

Definition map_lfundef (f : lcmd -> lcmd) (lfd : lfundef) : lfundef :=
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
    lfd_used_stack := lfd_used_stack lfd;
  |}.

Fixpoint max_map
  {A B : Type} `{Cmp B} (f : A -> option B) xs acc : option B :=
  match xs with
  | [::] => acc
  | x :: xs' =>
      let acc' :=
        if f x is Some y
        then Some (if acc is Some z then max y z else y)
        else acc
      in
      max_map f xs' acc'
  end.

Definition max_lcmd_lbl (c : lcmd) : option label :=
  let f '(MkLI _ i) :=
    if i is Llabel lbl
    then Some lbl
    else None
  in
  max_map f c None.

Definition max_lfd_lbl (lfd : lfundef) : option label :=
  max_lcmd_lbl (lfd_body lfd).

(* FIXME: maybe useless? *)
Definition max_lprog_lbl (p : lprog) : option label :=
  max_map (fun '(_, fd) => max_lfd_lbl fd) (lp_funcs p) None.

Definition next_lbl lbl := (lbl + 1)%positive.

Definition next_lfd_lbl (lfd : lfundef) : label :=
  if max_lfd_lbl lfd is Some lbl
  then next_lbl lbl
  else xH.

Definition next_lprog_lbl (p : lprog) : label :=
  if max_lprog_lbl p is Some lbl
  then next_lbl lbl
  else xH.

End ASM_OP.
