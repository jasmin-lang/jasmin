From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.
Require Import compiler_util expr.

Module Import E.

  Definition pass : string := "for to while".

  Definition fresh_error (ii : instr_info) :=
    pp_internal_error_s_at pass ii "fresh for-loop variable is not fresh".

End E.

Section FOR_TO_WHILE.

Context
  {asm_op : Type}
  {asmop : asmOp asm_op}
  (fresh_var_ident : v_kind -> instr_info -> string -> atype -> Ident.ident)
.

#[local] Existing Instance progUnit.

Definition for_to_while_clone (ii : instr_info) (x : var) : var :=
  let n := x.(vname) in
  let n' :=
    fresh_var_ident
      (Ident.id_kind n) ii (Ident.id_name n ++ "_ftw")%string aint
  in
  {| vtype := aint; vname := n'; |}.

Definition for_to_while_bound_var (ii : instr_info) : var :=
  {| vtype := aint;
     vname := fresh_var_ident (Reg (Normal, Direct)) ii "for_bound" aint;
  |}.

Definition for_to_while_bound
  (acc : Sv.t) (X : Sv.t) (ii : instr_info) (e : pexpr)
  : cexec (Sv.t * pexpr * cmd) :=
  if e is Pconst _ then ok (acc, e, [::])
  else
    let bi := {| v_var := for_to_while_bound_var ii; v_info := dummy_var_info; |} in
    Let _ := assert (~~ Sv.mem bi.(v_var) (Sv.union X acc)) (E.fresh_error ii) in
    ok (Sv.add bi.(v_var) acc, Plvar bi,
        [:: MkI ii (Cassgn (Lvar bi) AT_none aint e)]).

Section CMD.

Context (for_to_while_i : Sv.t -> Sv.t -> instr -> cexec (Sv.t * cmd)).

Fixpoint for_to_while_c
  (acc : Sv.t) (X : Sv.t) (c : cmd) : cexec (Sv.t * cmd) :=
  match c with
  | [::] => ok (acc, [::])
  | i :: c =>
    Let ai := for_to_while_i acc X i in
    Let ac := for_to_while_c ai.1 X c in
    ok (ac.1, ai.2 ++ ac.2)
  end.

End CMD.

Fixpoint for_to_while_i
  (acc : Sv.t) (X : Sv.t) (i : instr) : cexec (Sv.t * cmd) :=
  let 'MkI ii ir := i in
  match ir with
  | Cassgn _ _ _ _ | Copn _ _ _ _ | Csyscall _ _ _ | Cassert _ | Ccall _ _ _ =>
    ok (acc, [:: i])
  | Cif e c1 c2 =>
    Let ac1 := for_to_while_c for_to_while_i acc X c1 in
    Let ac2 := for_to_while_c for_to_while_i ac1.1 X c2 in
    ok (ac2.1, [:: MkI ii (Cif e ac1.2 ac2.2)])
  | Cwhile al c1 e info c2 =>
    Let ac1 := for_to_while_c for_to_while_i acc X c1 in
    Let ac2 := for_to_while_c for_to_while_i ac1.1 X c2 in
    ok (ac2.1, [:: MkI ii (Cwhile al ac1.2 e info ac2.2)])
  | Cfor x (dir, e1, e2) c =>
    Let ac := for_to_while_c for_to_while_i acc X c in
    let i' := for_to_while_clone ii x.(v_var) in
    Let _ := assert (~~ Sv.mem i' (Sv.union X ac.1)) (E.fresh_error ii) in
    let acc1 := Sv.add i' ac.1 in
    let xi' := {| v_var := i'; v_info := x.(v_info); |} in
    let reinstall :=
      MkI ii (Cassgn (Lvar x) AT_inline aint (Plvar xi'))
    in
    match dir with
    | UpTo =>
      Let bnd := for_to_while_bound acc1 X ii e2 in
      let '(acc2, b, bcmd) := bnd in
      let init := MkI ii (Cassgn (Lvar xi') AT_none aint e1) in
      let cond := Papp2 (Olt Cmp_int) (Plvar xi') b in
      let incr :=
        MkI ii (Cassgn (Lvar xi') AT_none aint
                  (Papp2 (Oadd Op_int) (Plvar xi') (Pconst 1)))
      in
      let body := reinstall :: ac.2 ++ [:: incr] in
      ok (acc2, init :: bcmd ++ [:: MkI ii (Cwhile NoAlign [::] cond ii body)])
    | DownTo =>
      Let bnd := for_to_while_bound acc1 X ii e1 in
      let '(acc2, b, bcmd) := bnd in
      let init := MkI ii (Cassgn (Lvar xi') AT_none aint e2) in
      let cond := Papp2 (Olt Cmp_int) b (Plvar xi') in
      let decr :=
        MkI ii (Cassgn (Lvar xi') AT_none aint
                  (Papp2 (Osub Op_int) (Plvar xi') (Pconst 1)))
      in
      let body := reinstall :: ac.2 ++ [:: decr] in
      ok (acc2, bcmd ++ init :: [:: MkI ii (Cwhile NoAlign [::] cond ii body)])
    end
  end.

Definition for_to_while_fd (fd : _fundef unit) : cexec (_fundef unit) :=
  let X := vars_fd fd in
  Let ac := for_to_while_c for_to_while_i Sv.empty X fd.(f_body) in
  ok {|
    f_info := f_info fd;
    f_contract := f_contract fd;
    f_tyin := f_tyin fd;
    f_params := f_params fd;
    f_body := ac.2;
    f_tyout := f_tyout fd;
    f_res := f_res fd;
    f_extra := f_extra fd;
  |}.

Definition for_to_while_prog (p : _uprog) : cexec _uprog :=
  Let funcs := map_cfprog for_to_while_fd (p_funcs p) in
  ok {|
    p_funcs := funcs;
    p_globs := p_globs p;
    p_extra := p_extra p;
  |}.

End FOR_TO_WHILE.
