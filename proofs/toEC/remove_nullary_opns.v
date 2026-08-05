Require Import expr.

Section REMOVE_NULLARY_OPNS.

Context
  {asm_op : Type}
  {asmop : asmOp asm_op}
.

#[local] Existing Instance progUnit.

Section CMD.

Context (remove_nullary_opns_i : instr -> cmd).

Fixpoint remove_nullary_opns_c (c : cmd) : cmd :=
  match c with
  | [::] => [::]
  | i :: c => remove_nullary_opns_i i ++ remove_nullary_opns_c c
  end.

End CMD.

Fixpoint remove_nullary_opns_i (i : instr) : cmd :=
  let 'MkI ii ir := i in
  match ir with
  | Cassgn _ _ _ _ | Csyscall _ _ _ | Cassert _ | Ccall _ _ _ => [:: i]
  | Copn xs t o es => match xs with [::] => [::] | _ => [:: i] end
  | Cif e c1 c2 =>
      [:: MkI ii (Cif e (remove_nullary_opns_c remove_nullary_opns_i c1)
                    (remove_nullary_opns_c remove_nullary_opns_i c2))]
  | Cfor x r c =>
      [:: MkI ii (Cfor x r (remove_nullary_opns_c remove_nullary_opns_i c))]
  | Cwhile al c1 e info c2 =>
      [:: MkI ii
            (Cwhile al (remove_nullary_opns_c remove_nullary_opns_i c1) e info
               (remove_nullary_opns_c remove_nullary_opns_i c2))]
  end.

Definition remove_nullary_opns_fd (fd : _fundef unit) : _fundef unit :=
  {|
    f_info := f_info fd;
    f_contract := f_contract fd;
    f_tyin := f_tyin fd;
    f_params := f_params fd;
    f_body := remove_nullary_opns_c remove_nullary_opns_i fd.(f_body);
    f_tyout := f_tyout fd;
    f_res := f_res fd;
    f_extra := f_extra fd;
  |}.

Definition remove_nullary_opns_fun_decl
  (fd : funname * _fundef unit) : funname * _fundef unit :=
  let '(fn, fd) := fd in (fn, remove_nullary_opns_fd fd).

Definition remove_nullary_opns_prog (p : _uprog) : _uprog :=
  {|
    p_funcs := map remove_nullary_opns_fun_decl (p_funcs p);
    p_globs := p_globs p;
    p_extra := p_extra p;
  |}.

End REMOVE_NULLARY_OPNS.
