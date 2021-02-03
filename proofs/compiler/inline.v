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

Section INLINE.

Context (inline_var: var -> bool).

Definition get_flag (x:lval) flag :=
  match x with
  | Lvar x => if inline_var x then AT_inline else flag
  | _      => flag
  end.

Definition assgn_tuple iinfo (xs:lvals) flag (tys:seq stype) (es:pexprs) :=
  let assgn xe := MkI iinfo (Cassgn xe.1 (get_flag xe.1 flag) xe.2.1 xe.2.2) in
  map assgn (zip xs (zip tys es)).

Definition inline_c (inline_i: instr -> Sv.t -> ciexec (Sv.t * cmd)) c s :=
  foldr (fun i r =>
    Let r := r in
    Let ri := inline_i i r.1 in
    ciok (ri.1, ri.2 ++ r.2)) (ciok (s,[::])) c.

Definition sparams (fd:ufundef) :=
  vrvs_rec Sv.empty (map Lvar fd.(f_params)).

Definition locals_p (fd:ufundef) :=
  let s := read_es (map Plvar fd.(f_res)) in
  let w := write_c_rec s fd.(f_body) in
  let r := read_c_rec w fd.(f_body) in
  vrvs_rec r (map Lvar fd.(f_params)).

Definition locals fd :=
  Sv.diff (locals_p fd) (sparams fd).

Definition check_rename iinfo f (fd1 fd2:ufundef) (s:Sv.t) :=
  Let _ := add_infun iinfo (CheckAllocRegU.check_fundef tt tt (f,fd1) (f,fd2) tt) in
  let s2 := locals_p fd2 in
  if disjoint s s2 then ciok tt
  else cierror iinfo (Cerr_inline s s2).

Definition get_fun (p:ufun_decls) iinfo (f:funname) :=
  match get_fundef p f with
  | Some fd => ciok fd
  | None    => cierror iinfo (Cerr_unknown_fun f "inlining")
  end.

Variable rename_fd : instr_info -> funname -> ufundef -> ufundef.

Fixpoint inline_i (p:ufun_decls) (i:instr) (X:Sv.t) : ciexec (Sv.t * cmd) :=
  match i with
  | MkI iinfo ir =>
    match ir with
    | Cassgn x _ _ e => ciok (Sv.union (read_i ir) X, [::i])
    | Copn xs _ o es => ciok (Sv.union (read_i ir) X, [::i])
    | Cif e c1 c2  =>
      Let c1 := inline_c (inline_i p) c1 X in
      Let c2 := inline_c (inline_i p) c2 X in
      ciok (read_e_rec (Sv.union c1.1 c2.1) e, [::MkI iinfo (Cif e c1.2 c2.2)])
    | Cfor x (d,lo,hi) c =>
      let X := Sv.union (read_i ir) X in
      Let c := inline_c (inline_i p) c X in
      ciok (X, [::MkI iinfo (Cfor x (d, lo, hi) c.2)])
    | Cwhile a c e c' =>
      let X := Sv.union (read_i ir) X in
      Let c := inline_c (inline_i p) c X in
      Let c' := inline_c (inline_i p) c' X in
      ciok (X, [::MkI iinfo (Cwhile a c.2 e c'.2)])
    | Ccall inline xs f es =>
      let X := Sv.union (read_i ir) X in
      if inline is InlineFun then
        Let fd := get_fun p iinfo f in
        let fd' := rename_fd iinfo f fd in
        Let _ := check_rename iinfo f fd fd' (Sv.union (vrvs xs) X) in
        ciok (X,  assgn_tuple iinfo (map Lvar fd'.(f_params)) AT_rename fd'.(f_tyin) es ++
                  (fd'.(f_body) ++
                  assgn_tuple iinfo xs AT_rename fd'.(f_tyout) (map Plvar fd'.(f_res))))
      else ciok (X, [::i])
    end
  end.

Definition inline_fd (p:ufun_decls) (fd:ufundef) :=
  match fd with
  | MkFun ii tyin params c tyout res ef =>
    let s := read_es (map Plvar res) in
    Let c := inline_c (inline_i p) c s in
    ok (MkFun ii tyin params c.2 tyout res ef)
  end.

Definition inline_fd_cons (ffd:funname * ufundef) (p:cfexec ufun_decls) :=
  Let p := p in
  let f := ffd.1 in
  Let fd := add_finfo f f (inline_fd p ffd.2) in
  cfok ((f,fd):: p).

Definition inline_prog (p:ufun_decls) :=
  foldr inline_fd_cons (cfok [::]) p.

Definition inline_prog_err (p:uprog) :=
  if uniq [seq x.1 | x <- p_funcs p] then
    Let fds := inline_prog (p_funcs p) in
    ok {| p_extra := p_extra p; p_globs := p_globs p; p_funcs := fds |}
  else cferror Ferr_uniqfun.

End INLINE.
