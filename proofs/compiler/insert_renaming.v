From mathcomp Require Import ssreflect eqtype ssrbool.
Require Import expr compiler_util.
Import Utf8.

Section WITH_PARAMS.

  Context {asm_op : Type} {asmop : asmOp asm_op} {pT: progT}.

  Definition rename_var_r (x: var_i) : instr_r :=
    Cassgn (Lvar x) AT_none (vtype x) (Pvar (mk_lvar x)).

  Definition rename_var ii (x: var_i) : instr :=
    MkI ii (rename_var_r x).

  Definition rename_vars ii : seq var_i → cmd :=
    map (rename_var ii).

  Definition insert_renaming_body (fd: fundef) : cmd :=
    rename_vars (entry_info_of_fun_info fd.(f_info)) fd.(f_params) ++
    fd.(f_body) ++
    rename_vars (ret_info_of_fun_info fd.(f_info)) fd.(f_res).

  Context (insert_renaming_p: fun_info → bool).

  Definition should_insert_renaming (fd: fundef) : bool :=
    let well_typed xs tys := tys == [seq vtype (v_var x) | x <- xs ] in
    [&& insert_renaming_p fd.(f_info),
      well_typed fd.(f_params) fd.(f_tyin) &
      well_typed fd.(f_res) fd.(f_tyout) ].

  Definition insert_renaming_fd (fd: fundef) : fundef :=
    if should_insert_renaming fd then
      with_body fd (insert_renaming_body fd)
    else fd.

  Definition insert_renaming_prog (p: prog) : prog :=
    map_prog insert_renaming_fd p.

End WITH_PARAMS.
