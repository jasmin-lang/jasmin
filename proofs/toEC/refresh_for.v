From mathcomp Require Import ssrbool eqtype.
Require Import expr.

Section REFRESH_FOR.

Context
  {asm_op : Type}
  {asmop : asmOp asm_op}
  (fresh_var_ident : v_kind -> instr_info -> string -> atype -> Ident.ident)
  (always : bool)
.

Definition refresh_for_clone (ii : instr_info) (x : var) : var :=
  let n := x.(vname) in
  let n' := fresh_var_ident (Ident.id_kind n) ii (Ident.id_name n) x.(vtype) in
  {| vtype := x.(vtype); vname := n'; |}.

Let refresh_for_ii_aux rf (i : instr) : instr :=
  let 'MkI ii ir := i in MkI ii (rf ii ir).

Let refresh_for_c_aux rf (c : cmd) : cmd := map (refresh_for_ii_aux rf) c.

Fixpoint refresh_for_i (ii : instr_info) (i : instr_r) : instr_r :=
  let rec := refresh_for_c_aux refresh_for_i in
  match i with
  | Cassgn _ _ _ _ | Copn _ _ _ _ | Csyscall _ _ _ | Cassert _ | Ccall _ _ _ =>
    i
  | Cif e c1 c2 => Cif e (rec c1) (rec c2)
  | Cwhile al c1 e info c2 => Cwhile al (rec c1) e info (rec c2)
  | Cfor x r c =>
      if always || Sv.mem x (write_c c) then
        let x' := refresh_for_clone ii x.(v_var) in
        let xi' := {| v_var := x'; v_info := x.(v_info); |} in
        let cpy :=
          MkI ii (Cassgn (Lvar x) AT_inline x.(v_var).(vtype) (Plvar xi'))
        in
        Cfor xi' r (cpy :: rec c)
      else Cfor x r (rec c)
  end.

Definition refresh_for_ii := refresh_for_ii_aux refresh_for_i.
Definition refresh_for_c := refresh_for_c_aux refresh_for_i.

Definition refresh_for_fd (fd : _fundef unit) : _fundef unit :=
  {|
    f_info := f_info fd;
    f_contract := f_contract fd;
    f_tyin := f_tyin fd;
    f_params := f_params fd;
    f_body := refresh_for_c fd.(f_body);
    f_tyout := f_tyout fd;
    f_res := f_res fd;
    f_extra := f_extra fd;
  |}.

Definition refresh_for_fun_decl
  (fd : funname * _fundef unit) : funname * _fundef unit :=
  let '(fn, fd) := fd in (fn, refresh_for_fd fd).

Definition refresh_for_prog (p : _uprog) : _uprog :=
  {|
    p_funcs := map refresh_for_fun_decl (p_funcs p);
    p_globs := p_globs p;
    p_extra := p_extra p;
  |}.

End REFRESH_FOR.
