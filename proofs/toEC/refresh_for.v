From mathcomp Require Import ssrbool eqtype.
Require Import compiler_util expr.

Module Import E.

  Definition pass : string := "refresh for".

  Definition fresh_error (ii : instr_info) :=
    pp_internal_error_s_at pass ii "fresh for-counter is not fresh".

End E.

Section REFRESH_FOR.

Context
  {asm_op : Type}
  {asmop : asmOp asm_op}
  (fresh_var_ident : v_kind -> instr_info -> string -> atype -> Ident.ident)
  (always : bool)
.

#[local] Existing Instance progUnit.

Definition refresh_for_clone (ii : instr_info) (x : var) : var :=
  let n := x.(vname) in
  let n' := fresh_var_ident (Ident.id_kind n) ii (Ident.id_name n) x.(vtype) in
  {| vtype := x.(vtype); vname := n'; |}.

Let refresh_for_ii_aux rf (i : instr) : cexec instr :=
  let 'MkI ii ir := i in
  Let ir' := rf ii ir in
  ok (MkI ii ir').

Let refresh_for_c_aux rf (c : cmd) : cexec cmd :=
  mapM (refresh_for_ii_aux rf) c.

Fixpoint refresh_for_i
  (V : Sv.t) (ii : instr_info) (i : instr_r) : cexec instr_r :=
  let rec := refresh_for_c_aux (refresh_for_i V) in
  match i with
  | Cassgn _ _ _ _ | Copn _ _ _ _ | Csyscall _ _ _ | Cassert _ | Ccall _ _ _ =>
    ok i
  | Cif e c1 c2 =>
    Let c1 := rec c1 in
    Let c2 := rec c2 in
    ok (Cif e c1 c2)
  | Cwhile al c1 e info c2 =>
    Let c1 := rec c1 in
    Let c2 := rec c2 in
    ok (Cwhile al c1 e info c2)
  | Cfor x r c =>
      if always || Sv.mem x (write_c c) then
        let x' := refresh_for_clone ii x.(v_var) in
        Let _ := assert (~~ Sv.mem x' V) (E.fresh_error ii) in
        let xi' := {| v_var := x'; v_info := x.(v_info); |} in
        let cpy :=
          MkI ii (Cassgn (Lvar x) AT_inline x.(v_var).(vtype) (Plvar xi'))
        in
        Let c := rec c in
        ok (Cfor xi' r (cpy :: c))
      else
        Let c := rec c in
        ok (Cfor x r c)
  end.

Definition refresh_for_ii (V : Sv.t) := refresh_for_ii_aux (refresh_for_i V).
Definition refresh_for_c (V : Sv.t) := refresh_for_c_aux (refresh_for_i V).

Definition refresh_for_fd
  (V : Sv.t) (fd : _fundef unit) : cexec (_fundef unit) :=
  Let c := refresh_for_c V fd.(f_body) in
  ok {|
    f_info := f_info fd;
    f_contract := f_contract fd;
    f_tyin := f_tyin fd;
    f_params := f_params fd;
    f_body := c;
    f_tyout := f_tyout fd;
    f_res := f_res fd;
    f_extra := f_extra fd;
  |}.

Definition refresh_for_prog (p : _uprog) : cexec _uprog :=
  let V := vars_p (p_funcs p) in
  Let funcs := map_cfprog (refresh_for_fd V) (p_funcs p) in
  ok {|
    p_funcs := funcs;
    p_globs := p_globs p;
    p_extra := p_extra p;
  |}.

End REFRESH_FOR.
