From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp Require Import word_ssrZ.
Require Import psem_defs.

(*---------------- Check on subtyping -------------------------------*)
(* returns true in case t is subtype of te *)
Definition check_type (e : pexpr) (te t : stype) : exec stype := 
if subtype t te then ok te else type_error.

(* returns true if the type of e is tint *)
Definition check_int (e : pexpr) (te : stype) := check_type e te sint.

(* return true if the type of e is tbool *)
Definition check_bool (e : pexpr) (te : stype) := check_type e te sbool.

(* return true if the type of e is pointer and the pointer size pd is less/equal
   to the pointer size of e *)
Definition check_ptr (e : pexpr) (pd : wsize) (te : stype) := check_type e te (sword pd).

(* returns true if the expression is of array type *)
Definition check_array (e : pexpr) (te : stype) := 
match te with 
| sarr _ => ok te 
| _ => type_error
end.

Section TypeE.

Variable ty_pexpr : wsize -> pexpr -> exec stype.

(* Pget aa ws x e: Checks x is of type array and e(index) is of type int 
   Returns word of size ws *)
Definition ty_get_set (pd : wsize) (ws : wsize) (x : gvar) (e : pexpr) : exec stype := 
let tx := x.(gv).(v_var).(vtype) in 
Let te := ty_pexpr pd e in
Let ta := check_array (Pvar x) tx in 
Let ti := check_int e te in
ok (sword ws).

(* Psub aa ws len x e: Checks x is of type array and e(index) is of type int
   Returns array type of length len *) 
Definition ty_get_set_sub (pd : wsize) (ws : wsize) (len : positive) (x : gvar) (e : pexpr) : exec stype := 
let tx := x.(gv).(v_var).(vtype) in 
Let te := ty_pexpr pd e in 
Let ta := check_array (Pvar x) tx in 
Let ti := check_int e te in 
ok (sarr (Z.to_pos (wsize_size ws) * len)).

Definition ty_load_store (pd : wsize) (ws : wsize) (x : var_i) (e : pexpr) : exec stype :=
let tx := x.(v_var).(vtype) in 
Let te := ty_pexpr pd e in 
Let tp := check_ptr (Pvar {| gv := x; gs := Slocal |}) pd tx in 
Let tp' := check_ptr e pd te in 
ok (sword ws).

Definition check_expr (pd : wsize) (e : pexpr) (ty : stype) : exec stype :=
Let te := ty_pexpr pd e in 
check_type e te ty.

Definition check_pexprs (pd : wsize) (es : pexprs) (tys : seq stype) : exec (seq stype) := 
mapM2 ErrType (check_expr pd) es tys. 

End TypeE.

(*------------- Typing rules for expressions ---------------*) 
Fixpoint ty_pexpr (pd : wsize) (e : pexpr) : exec stype := 
match e with 
| Pconst _ => ok sint
| Pbool _ => ok sbool
| Parr_init len => ok (sarr len)
| Pvar x => ok (x.(gv).(v_var).(vtype))
| Pget aa ws x e => ty_get_set ty_pexpr pd ws x e
| Psub aa ws len x e => ty_get_set_sub ty_pexpr pd ws len x e
| Pload ws x e => ty_load_store ty_pexpr pd ws x e 
| Papp1 op e => let (tin, tout) := type_of_op1 op in 
                Let ce := check_expr ty_pexpr pd e tin in 
                ok tout
| Papp2 op e1 e2 => let top := type_of_op2 op in 
                    Let ce1 := check_expr ty_pexpr pd e1 top.1.1 in
                    Let ce2 := check_expr ty_pexpr pd e2 top.1.2 in 
                    ok top.2
| PappN op es => let top := type_of_opN op in 
                 Let ces := check_pexprs ty_pexpr pd es top.1 in 
                 ok top.2
| Pif ty b et ef => Let cb := check_expr ty_pexpr pd b sbool in
                    Let ct := check_expr ty_pexpr pd et ty in 
                    Let cf := check_expr ty_pexpr pd ef ty in 
                    ok ty
end.

Section TypeLval.

Variable ty_lval : wsize -> lval -> exec stype.

Definition check_lval (pd : wsize) (l : lval) (ty : stype) : exec stype := 
Let tx := ty_lval pd l in 
if (subtype tx ty) then ok tx else type_error. 

Definition check_lvals (pd : wsize) (ls : lvals) (tys : seq stype) : exec (seq stype) :=
if (size tys == size ls) 
then mapM2 ErrType (check_lval pd) ls tys 
else type_error.

End TypeLval.

(*--------------- Typing rules for lvals -------------------*)
Definition ty_lval (pd : wsize) (l : lval) : exec stype :=
match l with 
| Lnone _ ty => ok ty
| Lvar x => ok x.(v_var).(vtype)
| Lmem ws x e => ty_load_store ty_pexpr pd ws x e
| Laset aa ws x e => ty_get_set ty_pexpr pd ws {| gv := x; gs := Slocal |} e
| Lasub aa ws len x e => ty_get_set_sub ty_pexpr pd ws len {| gv := x; gs := Slocal |} e
end.

(*-------------- Typing rules for instr --------------------*)
