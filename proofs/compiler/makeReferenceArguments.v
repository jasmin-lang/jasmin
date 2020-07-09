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

Fixpoint make_prologue ii (X:Sv.t) xs tys es := 
  match xs, tys, es with
  | [::], [::], [::] => ok ([::], [::])
  | x::xs, ty::tys, e::es =>
    let x := x.(v_var) in
    match is_reg_ptr_expr x e with
    | Some y => 
      Let _ := assert ([&& ty == vtype y, ~~is_sbool ty & ~~Sv.mem y X ])
                      (ii, Cerr_stk_alloc "makeReferenceArguments: bad fresh id") in
      Let pes := make_prologue ii (Sv.add y X) xs tys es in
      let: (p,es') := pes in 
      ok (MkI ii (Cassgn (Lvar y) AT_rename ty e) :: p, Plvar y :: es')
    | None =>
      Let pes := make_prologue ii X xs tys es in
      let: (p,es') := pes in
      ok (p, e::es')
    end
  | _, _, _ => Error (ii, Cerr_stk_alloc "prologue : assert false")
  end.

Fixpoint make_epilogue ii (X:Sv.t) xs tys rs := 
  match xs, tys, rs with
  | [::], [::], [::] => ok ([::], [::])
  | x::xs, ty::tys, r::rs =>
    let x := x.(v_var) in
     match is_reg_ptr_lval x r with
     | Some y => 
       Let _ := assert ([&& ty == vtype y, ~~is_sbool ty & ~~Sv.mem y X ])
                        (ii, Cerr_stk_alloc "makeReferenceArguments: bad fresh id") in
       Let prs := make_epilogue ii (Sv.add y X) xs tys rs in
       let: (p,rs') := prs in 
       ok (MkI ii (Cassgn r AT_rename ty (Plvar y)) :: p, Lvar y::rs')
     | None =>
       Let prs :=  make_epilogue ii X xs tys rs in
       let: (p,rs') := prs in
       ok (p, r::rs')
     end
   | _, _, _ => Error (ii, Cerr_stk_alloc "epilogue: assert false")
   end.
  
Definition update_c (update_i : instr -> ciexec cmd) (c:cmd) :=
  Let ls := mapM update_i c in
  ok (flatten ls).

Fixpoint update_i (get_sig : funname -> seq var_i * seq stype * seq var_i * seq stype) 
                  (X:Sv.t) (i:instr) : ciexec cmd :=
  let (ii,ir) := i in
  match ir with
  | Cassgn _ _ _ _ |  Copn _ _ _ _ => 
    ok [::i]
  | Cif b c1 c2 =>
    Let c1 := update_c (update_i get_sig X) c1 in
    Let c2 := update_c (update_i get_sig X) c2 in
    ok [::MkI ii (Cif b c1 c2)]
  | Cfor x r c =>
    Let c := update_c (update_i get_sig X) c in
    ok [::MkI ii (Cfor x r c)]
  | Cwhile a c e c' =>
    Let c  := update_c (update_i get_sig X) c in
    Let c' := update_c (update_i get_sig X) c' in
    ok [::MkI ii (Cwhile a c e c')]
  | Ccall ini xs fn es =>
    let: (params,tparams,returns,treturns) := get_sig fn in
    Let pres := make_prologue ii X params tparams es in
    let: (prologue, es) := pres in
    Let epxs := make_epilogue ii X returns treturns xs in
    let: (epilogue, xs) := epxs in 
    Let _ := assert (disjoint (vrvs xs) (write_c epilogue))
                    (ii, Cerr_stk_alloc "please report: makeReferenceArguments/epilogue") in
    ok (prologue ++ MkI ii (Ccall ini xs fn es) :: epilogue)
  end.

Definition update_fd (get_sig : funname -> seq var_i * seq stype * seq var_i * seq stype) (fd: fundef) :=
  let body    := fd.(f_body) in
  let write   := write_c body in
  let read    := read_c  body in
  let returns := read_es (map Plvar fd.(f_res)) in
  let X := Sv.union returns (Sv.union write read) in
  Let body := update_c (update_i get_sig X) body in
  ok (with_body fd body).

Definition get_sig (p:prog) n :=
  if get_fundef p.(p_funcs) n is Some fd then
        (fd.(f_params), fd.(f_tyin), fd.(f_res), fd.(f_tyout))
  else ([::], [::], [::], [::]).

Definition makereference_prog : cfexec prog :=
  Let funcs := map_cfprog (update_fd (get_sig p)) p.(p_funcs) in
  ok {| p_extra := p_extra p; p_globs := p_globs p; p_funcs := funcs |}.

End Section.

