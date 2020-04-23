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
From mathcomp Require Import all_ssreflect.
Require Import gen_map expr compiler_util ZArith.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope vmap.
Local Open Scope seq_scope.

Section Section.

Context (is_reg_ptr : var -> bool) (fresh_id : glob_decls -> var -> Ident.ident).
Context {T} {pT:progT T}.
Context (p : prog).

Definition with_var xi x := 
  let x' := {| vtype := vtype x; vname := fresh_id (p_globs p) x |} in
  {| v_var := x'; v_info := xi.(v_info) |}.

Definition is_reg_ptr_expr x e := 
  match e with
  | Pvar x' => 
    if is_reg_ptr x && (is_glob x' || ~~is_reg_ptr x'.(gv)) then 
      Some (with_var x'.(gv) x) 
    else None
  | Psub _ _ _ x' _ =>  Some (with_var x'.(gv) x)
  | _      => None 
  end.

Definition is_reg_ptr_lval x r := 
  match r with
  | Lvar x' => if is_reg_ptr x && ~~is_reg_ptr x' then Some (with_var x' x) else None
  | Lasub _ _ _ x' _ => Some (with_var x' x)
  | _      => None 
  end.

Definition fmap2 {aT bT cT} (f : aT -> bT -> cT -> aT * cT) : 
   aT -> seq bT -> seq cT -> aT * seq cT :=
  fix map a lb lc :=
    match lb, lc with
    | [:: b & bs], [:: c & cs] =>
      let y := f a b c in
      let ys := map y.1 bs cs in
      (ys.1, y.2 :: ys.2)
    | _, _ => (a, lc)
    end.

Definition do_prologue ii acc x e :=
  match is_reg_ptr_expr x e with
  | Some x => 
    (MkI ii (Cassgn (Lvar x) AT_rename (vtype x) e) :: acc, Plvar x)
  | None => (acc, e)
  end.

Definition make_prologue ii xs es := 
  fmap2 (do_prologue ii) [::] xs es.

Definition do_epilogue ii acc x r :=
  match is_reg_ptr_lval x r with
  | Some x => 
    (MkI ii (Cassgn r AT_rename (vtype x) (Plvar x)) :: acc, Lvar x)
  | None => (acc, r)
  end.

Definition make_epilogue ii xs rs := 
  fmap2 (do_epilogue ii) [::] xs rs.

Section SIG.

Context (get_sig : funname -> seq var * seq var) (X: Sv.t).

Definition update_c (update_i : instr -> cexec cmd) (c:cmd) := 
  Let ls := mapM update_i c in
  ok (flatten ls).

Fixpoint update_i (i:instr) : cexec cmd := 
  let (ii,ir) := i in
  match ir with
  | Cassgn _ _ _ _ |  Copn _ _ _ _ => 
    ok [::i]
  | Cif b c1 c2 =>
    Let c1 := update_c update_i c1 in
    Let c2 := update_c update_i c2 in
    ok [::MkI ii (Cif b c1 c2)]
  | Cfor x r c =>
    Let c := update_c update_i c in
    ok [::MkI ii (Cfor x r c)]
  | Cwhile a c e c' =>
    Let c  := update_c update_i c in
    Let c' := update_c update_i c' in
    ok [::MkI ii (Cwhile a c e c')]
  | Ccall ini xs fn es =>
    let: (params, returns) := get_sig fn in
    let: (prologue, es) := make_prologue ii params es in
    let: (epilogue, xs) := make_epilogue ii returns xs in
    prologue ++ MkI ii (Ccall ini xs fn es) :: epilogue
  end.

Definition update_fd (ffd: fun_decl) := 
  let (f,fd)  := ffd in
  let body    := fd.(f_body) in
  let write   := write_c body in
  let read    := read_c  body in
  let returns := read_es (map Plvar fd.(f_res)) in
  Let _ := 
    assert (Sv.is_empty (Sv.inter (Sv.union returns (Sv.union write read)) X))
           (Ferr_fun f (Cerr_stk_alloc "makeRerenceArguments (not disjoint) : please report")) in
  let body := update_c update_i body in
  ok (f, with_body fd body).

End SIG.

Definition Sv_of_list := foldl (fun s x => Sv.add x s) Sv.empty.

Definition error_msg := (Ferr_msg (Cerr_stk_alloc "makeRerenceArguments: please report")).

Definition make_sig (gd:glob_decls) (ffd:fun_decl) (Xms: Sv.t * Mp.t (seq var * seq var)) := 
  let (X,ms) := Xms in
  let (f,fd) := ffd in
  let dox (x:var_i) := {| vtype := vtype x; vname := fresh_id gd x |} in
  let xs := map dox fd.(f_params) in
  let rs := map dox fd.(f_res) in
  Let _ := assert (uniq xs && uniq rs) error_msg in
  let X := Sv.union (Sv_of_list xs) (Sv.union (Sv_of_list rs) X) in
  ok (X, Mp.set ms f (xs,rs)).

Definition makereference_prog (p:prog) : cfexec prog := 
  Let Xms := foldrM (make_sig (p_globs p)) (Sv.empty, Mp.empty _) p.(p_funcs) in 
  let: (X,ms) := Xms in 
  let get_sig (f:funname) := odflt ([::], [::]) (Mp.get ms f) in
  Let funcs := mapM (update_fd get_sig X) p.(p_funcs) in
  ok {| p_extra := p_extra p; p_globs := p_globs p; p_funcs := funcs |}.

End Section.

