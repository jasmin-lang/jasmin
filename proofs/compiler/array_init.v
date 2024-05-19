(* ** Imports and settings *)
Require Import ZArith.
From mathcomp Require Import ssreflect ssrfun ssrbool.
Require Import expr compiler_util.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope seq_scope.

Section ASM_OP.

Context `{asmop:asmOp}.

(* ----------------------------------------------------------------------- *)
(* Remove array initialisation                                             *)

Section Section.

Context (is_reg_array : var -> bool).

Fixpoint remove_init_i i :=
  match i with
  | MkI ii ir =>
    match ir with
    | Cassgn x _ _ e => 
      if is_array_init e then 
        let t := 
          match x with
          | Lvar x => is_reg_array x
          | Lasub _ _ _ x _ => is_reg_array x
          | _ => true 
          end in
        if t then [::] else [::i]
      else [::i]
    | Copn _ _ _ _   => [::i]
    | Csyscall _ _ _ => [::i]
    | Cif e c1 c2  =>
      let c1 := foldr (fun i c => remove_init_i i ++ c) [::] c1 in
      let c2 := foldr (fun i c => remove_init_i i ++ c) [::] c2 in
      [:: MkI ii (Cif e c1 c2) ]
    | Cfor x r c   =>
      let c := foldr (fun i c => remove_init_i i ++ c) [::] c in
      [:: MkI ii (Cfor x r c) ]
    | Cwhile a c e c' =>
      let c := foldr (fun i c => remove_init_i i ++ c) [::] c in
      let c' := foldr (fun i c => remove_init_i i ++ c) [::] c' in
      [:: MkI ii (Cwhile a c e c') ]
    | Ccall _ _ _  => [::i]
    end
  end.

Definition remove_init_c c :=  foldr (fun i c => remove_init_i i ++ c) [::] c.

Context {pT: progT}.

Definition remove_init_fd (fd:fundef) :=
  {| f_info   := fd.(f_info);
     f_tyin   := fd.(f_tyin);
     f_params := fd.(f_params);
     f_body   := remove_init_c fd.(f_body);
     f_tyout  := fd.(f_tyout);
     f_res    := fd.(f_res);
     f_extra  := fd.(f_extra);
  |}.

Definition remove_init_prog (p:prog) := map_prog remove_init_fd p.

End Section.

(* ----------------------------------------------------------------------- *)
(* Insert array initialisation                                             *)

Section Section.

  Context (add_init_i : Sv.t -> instr -> cmd * Sv.t).

  Fixpoint add_init_c I (c:cmd) := 
    match c with
    | [::] => ([::], I) 
    | i::c => 
      let (i,I) := add_init_i I i in
      let (c,I) := add_init_c I c in
      (i ++ c, I)
    end.

End Section.

Definition add_init_aux ii x c :=
  match x.(vtype) with
  | sarr n =>
    if ~~ is_ptr x then
      let x := VarI x (var_info_of_ii ii) in
      MkI ii (Cassgn (Lvar x) AT_none (sarr n) (Parr_init n)) :: c
    else c
  | _ => c
  end.

Definition add_init ii I extra i := 
  Sv.fold (add_init_aux ii) (Sv.diff extra I) [::i].

Fixpoint add_init_i I (i:instr) := 
  let (ii,ir) := i in
  match ir with
  | Cif e c1 c2 =>
    let (c1, I1) := add_init_c add_init_i I c1 in
    let (c2, I2) := add_init_c add_init_i I c2 in
    let extra := Sv.union (read_e e) (Sv.union (Sv.diff I1 I2) (Sv.diff I2 I1)) in
    let i := MkI ii (Cif e c1 c2) in
    (add_init ii I extra i, (Sv.union I1 I2))
  | _ =>
    let Wi := write_i ir in
    let Ri := read_i ir in
    let extra := Sv.union Wi Ri in
    (add_init (ii_with_location ii) I extra i, Sv.union I Wi)
  end.

Context {pT: progT}.

Definition add_init_fd (fd:fundef) :=
  let I := vrvs [seq (Lvar i) | i <- f_params fd] in
  let f_body  := (add_init_c add_init_i I fd.(f_body)).1 in
  {| f_info   := fd.(f_info);
     f_tyin   := fd.(f_tyin);
     f_params := fd.(f_params);
     f_body   := f_body;
     f_tyout  := fd.(f_tyout);
     f_res    := fd.(f_res);
     f_extra  := fd.(f_extra);
  |}.

Definition add_init_prog (p:prog) := map_prog add_init_fd p.

End ASM_OP.
