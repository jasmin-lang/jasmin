(* ** License
 * -----------------------------------------------------------------------
 * Copyright 2016--2017 IMDEA Software Institute
 * Copyright 2016--2017 Inria
 *
 * Permission is hereby granted, free of charge, to any person obtaining
 * a copy of this software and associated documentation files (the
 * "Software"), to deal in the Software without restriction, including
 * without limitation the rights to use, copy, modify, merge, publish,
 * distribute, sublicense, and/or sell copies of the Software, and to
 * permit persons to whom the Software is furnished to do so, subject to
 * the following conditions:
 *
 * The above copyright notice and this permission notice shall be
 * included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
 * EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.
 * IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY
 * CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT,
 * TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE
 * SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 * ----------------------------------------------------------------------- *)

(* * Prove properties about semantics of dmasm input language *)

(* ** Imports and settings *)
Require Import ZArith.
From mathcomp Require Import all_ssreflect.
Require Import expr compiler_util.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope vmap.
Local Open Scope seq_scope.

(* ----------------------------------------------------------------------- *)
(* Remove array initialisation                                             *)

Section Section.

Context (is_reg_array : var -> bool).

Definition is_array_init e :=
  match e with
  | Parr_init _ => true
  | _           => false
  end.

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
    | Ccall _ _ _ _  => [::i]
    | Ccopy x e =>
      if is_array_init e then 
        let t := 
          match x with
          | Lvar x => is_reg_array x
          | Lasub _ _ _ x _ => is_reg_array x
          | _ => true 
          end in
        if t then [::] else [::i]
      else [::i]
    end
  end.

Definition remove_init_c c :=  foldr (fun i c => remove_init_i i ++ c) [::] c.

Context {T} {pT:progT T}.

Definition remove_init_fd (fd:fundef) :=
  {| f_iinfo  := fd.(f_iinfo);
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


Section Section.

Context (is_ptr : var -> bool).

(* TODO: move *)
Definition dummy_info := xH.

Definition add_init_aux ii x c := 
  match x.(vtype) with
  | sarr n =>
    if ~~ is_ptr x then
      let x := VarI x dummy_info in
      MkI ii (Cassgn (Lvar x) AT_inline (sarr n) (Parr_init n)) :: c
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
    (add_init ii I extra i, Sv.union I Wi)
  end.

Context {T} {pT:progT T}.

Definition add_init_fd (fd:fundef) :=
  let I := vrvs [seq (Lvar i) | i <- f_params fd] in
  let f_body  := (add_init_c add_init_i I fd.(f_body)).1 in
  {| f_iinfo  := fd.(f_iinfo);
     f_tyin   := fd.(f_tyin);
     f_params := fd.(f_params);
     f_body   := f_body;
     f_tyout  := fd.(f_tyout);
     f_res    := fd.(f_res);
     f_extra  := fd.(f_extra);
  |}.

Definition add_init_prog (p:prog) := map_prog add_init_fd p.

End Section.

