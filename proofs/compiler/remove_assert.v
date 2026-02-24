(* ** Imports and settings *)
From mathcomp Require Import all_ssreflect.
Require Import expr compiler_util ZArith.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Import E.

  Definition pass : string := "remove assert".

  Definition error := pp_internal_error_s pass "bigop remains".

End E.

Section ASM_OP.

Section Section.

Context `{asmop : asmOp}.

Definition check_opN (op : opN) :=
  match op with
  | Opack _ _ | Oarray _ | Ocombine_flags _ => true
  | Ois_arr_init _ | Ois_barr_init _ => false
  end.

Fixpoint check_e (e : pexpr) :=
  match e with
  | Pconst _ | Pbool _ | Parr_init _ _ | Pvar _ => true
  | Pget _ _ _ _ e
  | Psub _ _ _ _ e
  | Pload _ _ e
  | Papp1 _ e => check_e e
  | Papp2 o e1 e2 => check_e e1 && check_e e2
  | PappN op es => check_opN op && all check_e es
  | Pif ty e1 e2 e3 => all check_e [::e1; e2; e3]
  | Pbig _ _ _ _ _ _ | Pis_var_init _ | Pis_mem_init _ _ => false
  end.

Definition check_es := all check_e.

Definition check_lval (lv:lval) :=
  match lv with
  | Lnone _ _ | Lvar _ => true
  | Lmem _ _ _ e | Laset _ _ _ _ e | Lasub _ _ _ _ e => check_e e
  end.

Definition check_lvals := all check_lval.

Definition remove_assert_c (remove_assert_i: instr -> cexec cmd) c :  cexec cmd :=
  foldr (fun i r =>
    Let r := r in
    Let i := remove_assert_i i in
    ok ( i ++ r)) (ok [::]) c.

Fixpoint remove_assert_i (i:instr) : cexec cmd :=
  let (ii, ir) := i in
  add_iinfo ii
  match ir with
  | Cassert _ => ok ([::])
  | Cassgn x _ _ e =>
    Let _ := assert (check_lval x && check_e e) E.error in
    ok [:: i]
  | Copn xs _ _ es | Csyscall xs _ es | Ccall xs _ es =>
    Let _ := assert (check_lvals xs && check_es es) E.error in
    ok [:: i]
  | Cif e c1 c2 =>
    Let _ := assert (check_e e) E.error in
    Let c1 := remove_assert_c remove_assert_i c1 in
    Let c2 := remove_assert_c remove_assert_i c2 in
    ok [:: MkI ii (Cif e c1 c2)]
  | Cwhile al c1 e ii' c2 =>
    Let _ := assert (check_e e) E.error in
    Let c1 := remove_assert_c remove_assert_i c1 in
    Let c2 := remove_assert_c remove_assert_i c2 in
    ok [:: MkI ii (Cwhile al c1 e ii' c2)]
  | Cfor x (d, e1, e2) c =>
    Let _ := assert (check_e e1 && check_e e2) E.error in
    Let c := remove_assert_c remove_assert_i c in
    ok [:: MkI ii (Cfor x (d, e1, e2) c)]
  end.

Context {pT:progT}.

Definition remove_assert_fd (fd:fundef) :=
  Let c := remove_assert_c remove_assert_i fd.(f_body) in
  ok {| f_info   := fd.(f_info);
     f_contra := None;
     f_tyin   := fd.(f_tyin);
     f_params := fd.(f_params);
     f_body   := c;
     f_tyout  := fd.(f_tyout);
     f_res    := fd.(f_res);
     f_extra  := fd.(f_extra);
  |}.

Definition remove_assert_prog (p: prog) : cexec prog :=
  Let funcs := map_cfprog remove_assert_fd (p_funcs p) in
  ok {| p_extra := p_extra p; p_globs := p_globs p; p_funcs := funcs |}.

End Section.

End ASM_OP.
