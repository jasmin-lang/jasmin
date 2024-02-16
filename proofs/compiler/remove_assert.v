(* ** Imports and settings *)
From mathcomp Require Import all_ssreflect.
Require Import expr compiler_util ZArith.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section ASM_OP.

Section Section.

Context `{asmop : asmOp}.

Fixpoint remove_assert_i (i:instr) {struct i} : cmd :=
  let (ii,ir) := i in
  match ir with
  | Cassert t p e => [::]

  | Cassgn _ _ _ _
  | Copn _ _ _ _
  | Csyscall _ _ _
  | Ccall _ _ _ => [:: i]

  | Cif b c1 c2 =>
      let c1 := foldr (fun i c => remove_assert_i i ++ c) [::] c1 in
      let c2 := foldr (fun i c => remove_assert_i i ++ c) [::] c2 in
      [:: MkI ii (Cif b c1 c2)]

  | Cfor x (dir, e1, e2) c =>
      let c := foldr (fun i c => remove_assert_i i ++ c) [::] c in
      [:: MkI ii (Cfor x (dir,e1,e2) c) ]

  | Cwhile a c1 e c2 =>
      let c1 := foldr (fun i c => remove_assert_i i ++ c) [::] c1 in
      let c2 := foldr (fun i c => remove_assert_i i ++ c) [::] c2 in
    [:: MkI ii (Cwhile a c1 e c2) ]
  end.


Definition remove_assert_c  c :  cmd :=
  foldr (fun i r => remove_assert_i i ++r ) [::] c.


Context {pT:progT}.

Definition remove_assert_fd (fd:fundef) :=
  {| f_info   := fd.(f_info);
     f_contra := fd.(f_contra);
     f_tyin   := fd.(f_tyin);
     f_params := fd.(f_params);
     f_body   := remove_assert_c fd.(f_body);
     f_tyout  := fd.(f_tyout);
     f_res    := fd.(f_res);
     f_extra  := fd.(f_extra);
  |}.

Definition remove_assert_prog (p: prog) : prog :=
  map_prog remove_assert_fd p.

End Section.

End ASM_OP.
