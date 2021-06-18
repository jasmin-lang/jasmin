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

(* ** Imports and settings *)

From mathcomp Require Import all_ssreflect all_algebra.
From CoqWord Require Import ssrZ.
Require Import expr.
Require Import compiler_util ZArith.
Import Utf8.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope vmap.

Local Open Scope seq_scope.

Module CmpIndex.

  Definition t := [eqType of Z].

  Definition cmp : t -> t -> comparison := Z.compare.

  Lemma cmpO : Cmp cmp.
  Proof. apply ZO. Qed.

End CmpIndex.

Record varr_info := {
  vi_v : var;
  vi_s : wsize;
  vi_n : list Ident.ident;
}.

Record expand_info := {
  vars : list var;
  arrs : list varr_info;
}.

Module Mi := gen_map.Mmake CmpIndex.

Record array_info := {
   ai_ty    : wsize;
   ai_elems : Mi.t var;
}.

Record t := {
  svars : Sv.t;
  sarrs : Mvar.t array_info;
}.

Definition of_list (l: list var) := 
  foldl (fun s x => Sv.add x s) Sv.empty l.

Definition init_elems ty id (svmi : Sv.t * Mi.t var * Z) := 
  let '(sv,mi,i) := svmi in
  let xi := {| vtype := ty; vname := id |} in
  Let _ := assert (~~ Sv.mem xi sv) (Cerr_linear "array_expansion 2. Please report") in
  ok (Sv.add xi sv, Mi.set mi i xi, (i + 1)%Z).

Definition init_array_info (x : varr_info) (svm:Sv.t * Mvar.t array_info) :=
  let (sv,m) := svm in
  let ty := sword x.(vi_s) in
  Let _ :=  assert (~~ Sv.mem x.(vi_v) sv) (Cerr_linear "array_expansion 1. Please report") in
  Let svelems := foldM (init_elems ty) (sv,Mi.empty _,0%Z) x.(vi_n) in
  let '(sv, mi, _) := svelems in
  ok (sv, Mvar.set m x.(vi_v) {| ai_ty := x.(vi_s); ai_elems := mi |}).
        
Definition init_map (fi : expand_info) := 
  let svars := of_list fi.(vars) in
  Let sarrs := foldM init_array_info (svars, Mvar.empty _) fi.(arrs) in
  ok {| svars := svars; sarrs := sarrs.2 |}.

Definition check_gvar (m : t) (x: gvar) := 
  ~~ is_lvar x || Sv.mem (gv x) m.(svars).

(* FIXME: improve error messages *)
Fixpoint expand_e (m : t) (e : pexpr) : cexec pexpr := 
  match e with
  | Pconst _ | Pbool _ | Parr_init _ => ok e

  | Pvar x =>
    Let _ := assert (check_gvar m x) (Cerr_linear "array_expansion : error 1") in 
    ok e

  | Pget aa ws x e1 => 
    if check_gvar m x then 
      Let e1 := expand_e m e1 in
      ok (Pget aa ws x e1)
    else 
      let x := gv x in
      match Mvar.get m.(sarrs) x, is_const e1 with
      | Some ai, Some i =>
        Let _ := assert (ai.(ai_ty) == ws) (Cerr_linear "array_expansion : error 2") in
        Let _ := assert (aa == AAscale) (Cerr_linear "array_expansion : error 2 scale ") in
        match Mi.get ai.(ai_elems) i with
        | Some v => ok (Pvar (mk_lvar {| v_var := v; v_info := v_info x |}))
        | _ => Error (Cerr_linear "array_expansion : error 3") 
        end 
      | _, _ => Error (Cerr_linear "array_expansion : error 4") 
      end
  
  | Psub aa ws len x e1 => 
    Let _ := assert (check_gvar m x) (Cerr_linear "array_expansion : error 5") in
    Let e1 := expand_e m e1 in
    ok (Psub aa ws len x e1)

  | Pload ws x e1 =>
    Let _ := assert (Sv.mem x m.(svars)) (Cerr_linear "array_expansion : error 6") in
    Let e1 := expand_e m e1 in
    ok (Pload ws x e1)

  | Papp1 o e1 => 
    Let e1 := expand_e m e1 in
    ok (Papp1 o e1)

  | Papp2 o e1 e2 =>
    Let e1 := expand_e m e1 in
    Let e2 := expand_e m e2 in
    ok (Papp2 o e1 e2) 

  | PappN o es => 
    Let es := mapM (expand_e m) es in
    ok (PappN o es)   
           
  | Pif ty e1 e2 e3 =>
    Let e1 := expand_e m e1 in
    Let e2 := expand_e m e2 in
    Let e3 := expand_e m e3 in
    ok (Pif ty e1 e2 e3) 

  end.

Definition expand_lv (m : t) (x : lval)  :=
  match x with
  | Lnone _ _ => ok x

  | Lvar x => 
    Let _ := assert (Sv.mem x m.(svars)) (Cerr_linear "array_expansion : error 7") in
    ok (Lvar x)

  | Lmem ws x e => 
    Let _ := assert (Sv.mem x m.(svars)) (Cerr_linear "array_expansion : error 8") in
    Let e := expand_e m e in
    ok (Lmem ws x e)

  | Laset aa ws x e =>
    if Sv.mem x m.(svars) then 
      Let e := expand_e m e in
      ok (Laset aa ws x e)
    else 
      match Mvar.get m.(sarrs) x, is_const e with
      | Some ai, Some i =>
        Let _ := assert (ai.(ai_ty) == ws) (Cerr_linear "array_expansion : error 9") in
        Let _ := assert (aa == AAscale) (Cerr_linear "array_expansion : error 9 scale ") in
        match Mi.get ai.(ai_elems) i with
        | Some v => ok (Lvar {| v_var := v; v_info := v_info x |})
        | _ => Error (Cerr_linear "array_expansion : error 10") 
        end 
      | _, _ => Error (Cerr_linear "array_expansion : error 11") 
      end
  
  | Lasub aa ws len x e =>
    Let _ := assert (Sv.mem x m.(svars)) (Cerr_linear "array_expansion : error 12") in
    Let e := expand_e m e in
    ok (Lasub aa ws len x e)

  end.

Definition expand_es m := mapM (expand_e m).

Definition expand_lvs m := mapM (expand_lv m).

Fixpoint expand_i (m : t) (i : instr) : ciexec instr :=
  let (ii,ir) := i in
  match ir with
  | Cassgn x tag ty e =>
    Let x := add_iinfo ii (expand_lv m x) in
    Let e := add_iinfo ii (expand_e m e) in
    ok (MkI ii (Cassgn x tag ty e))

  | Copn xs tag o es =>
    Let xs := add_iinfo ii (expand_lvs m xs) in
    Let es := add_iinfo ii (expand_es m es) in
    ok (MkI ii (Copn xs tag o es))

  | Cif b c1 c2 =>
    Let b  := add_iinfo ii (expand_e m b) in
    Let c1 := mapM (expand_i m) c1 in 
    Let c2 := mapM (expand_i m) c2 in 
    ok (MkI ii (Cif b c1 c2))

  | Cfor x (dir, e1, e2) c =>
    Let _  := add_iinfo ii (assert (Sv.mem x m.(svars)) (Cerr_linear "array_expansion : error 13")) in
    Let e1 := add_iinfo ii (expand_e m e1) in
    Let e2 := add_iinfo ii (expand_e m e2) in
    Let c  := mapM (expand_i m) c in 
    ok (MkI ii (Cfor x (dir, e1, e2) c))

  | Cwhile a c e c' =>
    Let e  := add_iinfo ii (expand_e m e) in
    Let c  := mapM (expand_i m) c in 
    Let c' := mapM (expand_i m) c' in 
    ok (MkI ii (Cwhile a c e c'))
  
  | Ccall ini xs fn es =>
    Let xs := add_iinfo ii (expand_lvs m xs) in
    Let es := add_iinfo ii (expand_es m es) in
    ok (MkI ii (Ccall ini xs fn es))
  end.

Definition expand_fd (fi : funname -> ufundef -> expand_info) (ffd : funname * ufundef) :=
  let (f, fd) := ffd in
  Let m := add_err_fun f (init_map (fi f fd)) in
  match fd with
  | MkFun ii tyin params c tyout res ef =>
    Let _ := 
      add_err_fun f (assert (all (fun x => Sv.mem (v_var x) m.(svars)) params)
                            (Cerr_linear "expand_fd : params")) in
    Let _ := 
      add_err_fun f (assert (all (fun x => Sv.mem (v_var x) m.(svars)) res)
                            (Cerr_linear "expand_fd : res")) in

    Let c := add_finfo f f (mapM (expand_i m) c) in
    ok (f, MkFun ii tyin params c tyout res ef)
  end.

Definition expand_prog (fi : funname -> ufundef -> expand_info) (p: uprog) : cfexec uprog :=
  Let funcs := mapM (expand_fd fi) (p_funcs p) in
  ok {| p_extra := p_extra p; p_globs := p_globs p; p_funcs := funcs |}.

