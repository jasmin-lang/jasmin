(* ** Imports and settings *)
From mathcomp Require Import all_ssreflect.
Require Import expr compiler_util ZArith.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope vmap.
Local Open Scope seq_scope.

Section ASM_OP.

Context `{asmop : asmOp}.

Definition remove_assert_c (remove_assert_i: instr -> cmd)
                       c :  cmd :=
  foldr (fun i r =>
    let i := remove_assert_i i in
    i++r) [::] c.

Fixpoint remove_assert_i (i:instr) {struct i} : cmd :=
  let (ii,ir) := i in
  match ir with
  | Cassert e => [::]

  | Cassgn _ _ _ _ 
  | Copn _ _ _ _ 
  | Csyscall _ _ _  
  | Ccall _ _ _ _ => [:: i]

  | Cif b c1 c2 =>
    let c1 := remove_assert_c remove_assert_i c1 in
    let c2 := remove_assert_c remove_assert_i c2 in
    [:: MkI ii (Cif b c1 c2)]

  | Cfor x (dir, e1, e2) c =>
    let c := remove_assert_c remove_assert_i c in 
    [:: MkI ii (Cfor x (dir,e1,e2) c) ]

  | Cwhile a c1 e c2 =>
    let c1 := remove_assert_c remove_assert_i c1 in 
    let c2 := remove_assert_c remove_assert_i c2 in 
    [:: MkI ii (Cwhile a c1 e c2) ]
  end.

Section Section.

Context {T} {pT:progT T}.

Definition remove_assert_fd {eft} (fd: _fundef eft) : _fundef eft :=
  let 'MkFun ii tyi params c tyo res ef := fd in
  let c := remove_assert_c remove_assert_i c in
  MkFun ii tyi params c tyo res ef.

Definition remove_assert_prog (p: prog) : prog :=
  map_prog remove_assert_fd p.

End Section.

End ASM_OP.
