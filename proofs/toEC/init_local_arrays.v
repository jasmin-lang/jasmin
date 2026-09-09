Require Import expr.

Section INIT_LOCAL_ARRAYS.

Context
  {asm_op : Type}
  {asmop : asmOp asm_op}
.

Definition is_local_array_var (x : var) : bool :=
  match vtype x with
  | aarr _ _ => true
  | _ => false
  end.

(* Local array variables of [fd]: variables of array type occurring in
   the body or the results, minus the parameters. [Sv.elements] gives a
   deterministic (though otherwise arbitrary) order; that is all that is
   required, so no name-sort tiebreaker is needed. *)
Definition local_arrays (fd : _fundef unit) : seq var :=
  [seq x <- Sv.elements
              (Sv.diff
                 (Sv.union (vars_c fd.(f_body)) (vars_l fd.(f_res)))
                 (vars_l fd.(f_params)))
  | is_local_array_var x].

Definition init_local_array_instr (ii : instr_info) (x : var) : instr :=
  let xi := {| v_var := x; v_info := dummy_var_info; |} in
  MkI ii (Cassgn (Lvar xi) AT_none (vtype x)
    (match vtype x with
     | aarr ws n => Parr_init ws n
     | _ => Parr_init U8 0
     end)).

Definition init_local_arrays_body (fd : _fundef unit) : cmd :=
  let ii := entry_info_of_fun_info fd.(f_info) in
  map (init_local_array_instr ii) (local_arrays fd) ++ fd.(f_body).

Definition init_local_arrays_fd (fd : _fundef unit) : _fundef unit :=
  {|
    f_info := f_info fd;
    f_contract := f_contract fd;
    f_tyin := f_tyin fd;
    f_params := f_params fd;
    f_body := init_local_arrays_body fd;
    f_tyout := f_tyout fd;
    f_res := f_res fd;
    f_extra := f_extra fd;
  |}.

Definition init_local_arrays_fun_decl
  (fd : funname * _fundef unit) : funname * _fundef unit :=
  let '(fn, fd) := fd in (fn, init_local_arrays_fd fd).

Definition init_local_arrays_prog (p : _uprog) : _uprog :=
  {|
    p_funcs := map init_local_arrays_fun_decl (p_funcs p);
    p_globs := p_globs p;
    p_extra := p_extra p;
  |}.

End INIT_LOCAL_ARRAYS.
