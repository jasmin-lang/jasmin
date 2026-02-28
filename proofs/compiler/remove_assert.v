From Coq Require Import ssreflect.
Require Import expr compiler_util ZArith.

Section ASM_OP.

Context `{asmop : asmOp}.

Definition remove_assert_c (remove_assert_i: instr -> cmd) c :  cmd :=
  foldr (fun i r =>
    let i := remove_assert_i i in
     i ++ r) [::] c.

Fixpoint remove_assert_i (i: instr) : cmd :=
  let 'MkI ii ir := i in
  match ir with
  | Cassert _ => [::]
  | Cassgn _ _ _ _
  | Copn _ _ _ _ | Csyscall _ _ _ | Ccall _ _ _ =>
    [:: i]
  | Cif e c1 c2 =>
    let c1 := remove_assert_c remove_assert_i c1 in
    let c2 := remove_assert_c remove_assert_i c2 in
    [:: MkI ii (Cif e c1 c2)]
  | Cwhile al c1 e ii' c2 =>
    let c1 := remove_assert_c remove_assert_i c1 in
    let c2 := remove_assert_c remove_assert_i c2 in
    [:: MkI ii (Cwhile al c1 e ii' c2)]
  | Cfor x (d, e1, e2) c =>
    let c := remove_assert_c remove_assert_i c in
    [:: MkI ii (Cfor x (d, e1, e2) c)]
  end.

Context {pT:progT}.

Definition remove_assert_fd (fd: fundef) :=
  let c := remove_assert_c remove_assert_i fd.(f_body) in
  {| f_info   := fd.(f_info);
     f_contra := None;
     f_tyin   := fd.(f_tyin);
     f_params := fd.(f_params);
     f_body   := c;
     f_tyout  := fd.(f_tyout);
     f_res    := fd.(f_res);
     f_extra  := fd.(f_extra);
  |}.

Definition remove_assert_prog (p: prog) : prog :=
  map_prog remove_assert_fd p.

End ASM_OP.
