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
Require Import expr compiler_util allocation.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope vmap.
Local Open Scope seq_scope.

(* ** inlining
 * -------------------------------------------------------------------- *)

Definition assgn_tuple iinfo (xs:lvals) flags (es:pexprs) :=
  let assgn xe := MkI iinfo (Cassgn xe.1 flags xe.2) in
  map assgn (zip xs es).

Definition inline_c (inline_i: instr -> Sv.t -> ciexec (Sv.t * cmd)) c s := 
  foldr (fun i r =>
    Let r := r in
    Let ri := inline_i i r.1 in
    ciok (ri.1, ri.2 ++ r.2)) (ciok (s,[::])) c.

Definition sparams fd := 
  vrvs_rec Sv.empty (map Lvar fd.(f_params)).

Definition locals_p fd := 
  let s := read_es (map Pvar fd.(f_res)) in
  let w := write_c_rec s fd.(f_body) in
  let r := read_c_rec w fd.(f_body) in
  vrvs_rec r (map Lvar fd.(f_params)).

Definition locals fd := 
  Sv.diff (locals_p fd) (sparams fd).

Definition check_rename iinfo f fd1 fd2 (s:Sv.t) := 
  Let _ := add_infun iinfo (CheckAllocReg.check_fundef (f,fd1) (f,fd2) tt) in
  let s2 := locals_p fd2 in
  if disjoint s s2 then ciok tt 
  else cierror iinfo (Cerr_inline s s2).

Definition get_fun (p:prog) iinfo (f:funname) :=
  match get_fundef p f with
  | Some fd => ciok fd 
  | None    => cierror iinfo (Cerr_unknown_fun f "inlining")
  end.

Section INLINE.

Variable rename_fd : funname -> fundef -> fundef.

Definition dummy_info := xH.

Definition mkdV x := {| v_var := x; v_info := dummy_info |}.

Definition arr_init p := Papp1 Oarr_init (Pconst (Zpos p)).

Definition array_init iinfo (X: Sv.t) := 
  let assgn x c := 
    match x.(vtype) with
    | sarr p => 
      MkI iinfo (Cassgn (Lvar (mkdV x)) AT_rename_arg (arr_init p)) :: c
    | _      => c
    end in
  Sv.fold assgn X [::].
    
Fixpoint inline_i (p:prog) (i:instr) (X:Sv.t) : ciexec (Sv.t * cmd) := 
  match i with
  | MkI iinfo ir =>
    match ir with 
    | Cassgn x t e => ciok (Sv.union (read_i ir) X, [::i])
    | Copn xs o es => ciok (Sv.union (read_i ir) X, [::i])
    | Cif e c1 c2  =>
      Let c1 := inline_c (inline_i p) c1 X in
      Let c2 := inline_c (inline_i p) c2 X in
      ciok (read_e_rec (Sv.union c1.1 c2.1) e, [::MkI iinfo (Cif e c1.2 c2.2)])
    | Cfor x (d,lo,hi) c =>
      let X := Sv.union (read_i ir) X in
      Let c := inline_c (inline_i p) c X in
      ciok (X, [::MkI iinfo (Cfor x (d, lo, hi) c.2)])
    | Cwhile c e c' =>
      let X := Sv.union (read_i ir) X in
      Let c := inline_c (inline_i p) c X in
      Let c' := inline_c (inline_i p) c' X in
      ciok (X, [::MkI iinfo (Cwhile c.2 e c'.2)])
    | Ccall inline xs f es =>
      let X := Sv.union (read_i ir) X in
      if inline is InlineFun then
        Let fd := get_fun p iinfo f in 
        let fd' := rename_fd f fd in
        (* FIXME : locals is computed 2 times (one in check_rename) *)
        Let _ := check_rename iinfo f fd fd' (Sv.union (vrvs xs) X) in
        let init_array := array_init iinfo (locals fd') in                
        ciok (X,  assgn_tuple iinfo (map Lvar fd'.(f_params)) AT_rename_arg es ++
                  init_array ++ 
                  (fd'.(f_body) ++ 
                  assgn_tuple iinfo xs AT_rename_res (map Pvar fd'.(f_res))))
      else ciok (X, [::i])        
    end
  end.

Definition inline_fd (p:prog) (fd:fundef) :=
  match fd with 
  | MkFun ii params c res =>
    let s := read_es (map Pvar res) in
    Let c := inline_c (inline_i p) c s in
    ok (MkFun ii params c.2 res)
  end.

Definition inline_fd_cons (ffd:funname * fundef) (p:cfexec prog) :=
  Let p := p in 
  let f := ffd.1 in
  Let fd := add_finfo f f (inline_fd p ffd.2) in
  cfok ((f,fd)::p).

Definition inline_prog (p:prog) := 
  foldr inline_fd_cons (cfok [::]) p.

Definition inline_prog_err (p:prog) := 
  if uniq [seq x.1 | x <- p] then inline_prog (p:prog)
  else cferror Ferr_uniqfun.

Definition is_array_init e := 
  match e with
  | Papp1 Oarr_init _ => true
  | _                 => false
  end.

Fixpoint remove_init_i i := 
  match i with
  | MkI ii ir =>
    match ir with
    | Cassgn x t e => if is_array_init e then [::] else [::i]
    | Copn _ _ _   => [::i]
    | Cif e c1 c2  => 
      let c1 := foldr (fun i c => remove_init_i i ++ c) [::] c1 in
      let c2 := foldr (fun i c => remove_init_i i ++ c) [::] c2 in
      [:: MkI ii (Cif e c1 c2) ]
    | Cfor x r c   => 
      let c := foldr (fun i c => remove_init_i i ++ c) [::] c in
      [:: MkI ii (Cfor x r c) ]
    | Cwhile c e c' =>
      let c := foldr (fun i c => remove_init_i i ++ c) [::] c in
      let c' := foldr (fun i c => remove_init_i i ++ c) [::] c' in
      [:: MkI ii (Cwhile c e c') ]
    | Ccall _ _ _ _  => [::i]
    end
  end.

Definition remove_init_c c :=  foldr (fun i c => remove_init_i i ++ c) [::] c.

Definition remove_init_fd fd := 
  {| f_iinfo  := fd.(f_iinfo);
     f_params := fd.(f_params);  
     f_body   := remove_init_c fd.(f_body);
     f_res    := fd.(f_res); |}.

Definition remove_init_prog (p:prog) := map_prog remove_init_fd p.

End INLINE.
