Require Import compiler_util expr.

Section LOWERING.

Definition fresh_vars : Type := string -> stype -> Ident.ident.

Context
  {asm_op lowering_options : Type}
  {asmop : asmOp asm_op}
  (lower_i0 :
    lowering_options
    -> (instr_info -> warning_msg -> instr_info)
    -> fresh_vars
    -> instr
    -> cmd)
  (options : lowering_options)
  (warning : instr_info -> warning_msg -> instr_info)
  (fv : fresh_vars)
  {pT : progT}
  (all_fresh_vars : seq Ident.ident)
  (fvars : Sv.t).

Definition disj_fvars (x : Sv.t) : bool := disjoint x fvars.

Definition fvars_correct (fds : fun_decls) : bool :=
  disj_fvars (vars_p fds) && uniq all_fresh_vars.

Definition is_lval_in_memory (x : lval) : bool :=
  match x with
  | Lnone _ _ => false
  | Lvar v => is_var_in_memory v
  | Laset _ _ _ v _ => is_var_in_memory v
  | Lasub _ _ _ v _ => is_var_in_memory v
  | Lmem _ _ _ _ => true
  end.

Notation lower_i :=
  (lower_i0 options warning fv).

Definition lower_cmd  (c : cmd) : cmd :=
  conc_map lower_i c.

Definition lower_fd (fd : fundef) : fundef :=
  {|
    f_info := f_info fd;
    f_tyin := f_tyin fd;
    f_params := f_params fd;
    f_body := lower_cmd (f_body fd);
    f_tyout := f_tyout fd;
    f_res := f_res fd;
    f_extra := f_extra fd;
  |}.

Definition lower_prog (p : prog) :=
  map_prog lower_fd p.

End LOWERING.
