Require Import expr.

Section FLATTEN_WHILE.

Context
  {asm_op : Type}
  {asmop : asmOp asm_op}
.

#[local] Existing Instance progUnit.

Section CMD.

Context (flatten_while_i : instr -> cmd).

Fixpoint flatten_while_c (c : cmd) : cmd :=
  match c with
  | [::] => [::]
  | i :: c => flatten_while_i i ++ flatten_while_c c
  end.

End CMD.

Fixpoint flatten_while_i (i : instr) : cmd :=
  let 'MkI ii ir := i in
  match ir with
  | Cassgn _ _ _ _ | Copn _ _ _ _ | Csyscall _ _ _ | Cassert _ | Ccall _ _ _ =>
      [:: i]
  | Cif e c1 c2 =>
      [:: MkI ii (Cif e (flatten_while_c flatten_while_i c1)
                    (flatten_while_c flatten_while_i c2))]
  | Cfor x r c =>
      [:: MkI ii (Cfor x r (flatten_while_c flatten_while_i c))]
  | Cwhile al c1 e info c2 =>
      let c2' := flatten_while_c flatten_while_i c2 in
      match c1 with
      | [::] => [:: MkI ii (Cwhile al [::] e info c2')]
      | _ =>
          let c1' := flatten_while_c flatten_while_i c1 in
          c1' ++ [:: MkI ii (Cwhile al [::] e info (c2' ++ c1'))]
      end
  end.

Definition flatten_while_fd (fd : _fundef unit) : _fundef unit :=
  {|
    f_info := f_info fd;
    f_contract := f_contract fd;
    f_tyin := f_tyin fd;
    f_params := f_params fd;
    f_body := flatten_while_c flatten_while_i fd.(f_body);
    f_tyout := f_tyout fd;
    f_res := f_res fd;
    f_extra := f_extra fd;
  |}.

Definition flatten_while_fun_decl
  (fd : funname * _fundef unit) : funname * _fundef unit :=
  let '(fn, fd) := fd in (fn, flatten_while_fd fd).

Definition flatten_while_prog (p : _uprog) : _uprog :=
  {|
    p_funcs := map flatten_while_fun_decl (p_funcs p);
    p_globs := p_globs p;
    p_extra := p_extra p;
  |}.

End FLATTEN_WHILE.
