(* * Type checker of unit programs

   [check_prog p] checks that every expression, destination, assertion and
   contract of [p] is well typed, that each operator is valid (its semantics
   fails otherwise, in every mode), that the arguments of each operator, system
   call and function call have the types of the parameters, that each
   destination accepts the type of the value written into it, and that the
   global declarations have the types of their variables. A word of size [ws]
   is accepted where a smaller word is expected ([subatype]). *)

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.
From Coq Require Import ZArith.
Require Import expr psem_defs compiler_util.

Local Open Scope seq_scope.

Module Import E.

  Definition pass : string := "type checking".

  Definition typing_error (pp : pp_error) := {|
    pel_msg := pp;
    pel_fn := None;
    pel_fi := None;
    pel_ii := None;
    pel_vi := None;
    pel_pass := Some pass;
    pel_internal := false
  |}.

  Definition array_expected := typing_error (pp_s "array expected").
  Definition arity_mismatch := typing_error (pp_s "arity mismatch").
  Definition unknown_function := typing_error (pp_s "unknown function").
  Definition unknown_global := typing_error (pp_s "unknown global variable").
  Definition invalid_operator := typing_error (pp_s "invalid operator").
  Definition global_mismatch :=
    typing_error (pp_s "global variable type value mismatch").

End E.

Section TYPING.

Context `{asmop : asmOp}.
Context {pd : PointerData}.
Context {msfsz : MSFsize}.

Definition ty_var (x : var_i) : atype := x.(v_var).(vtype).

Definition check_array (te : atype) : cexec unit :=
  if te is aarr _ _ then ok tt else Error E.array_expected.

Definition pp_atype (t : atype) : pp_error :=
  match t with
  | abool => pp_s "bool"
  | aint => pp_s "int"
  | aword ws => pp_s ("u" ++ string_of_wsize ws)%string
  | aarr ws len =>
      pp_nobox [:: pp_s ("u" ++ string_of_wsize ws)%string;
                   pp_s "["; pp_z len; pp_s "]"]
  end.

(* A value of the actual type [te] is accepted where [ty] is expected. *)
Definition check_type (te ty : atype) : cexec unit :=
  if subatype ty te then ok tt
  else
    Error (typing_error (pp_vbox
      [:: pp_s "check type failed:";
          pp_hov [:: pp_s "expected type ="; pp_atype ty];
          pp_hov [:: pp_s "actual type   ="; pp_atype te]])).

Definition check_int (te : atype) : cexec unit := check_type te aint.

Definition check_ptr (te : atype) : cexec unit := check_type te (aword Uptr).

Section GLOBS.

(* The global declarations of the program. *)
Variable gd : glob_decls.

(* A global variable is declared. *)
Definition ty_gvar (x : gvar) : cexec atype :=
  let tx := ty_var x.(gv) in
  if is_lvar x then ok tx
  else if get_global_value gd x.(gv) is Some _ then ok tx
  else Error unknown_global.

Definition check_expr (ty_expr : pexpr -> cexec atype) (e : pexpr) (ty : atype)
  : cexec unit :=
  Let te := ty_expr e in
  check_type te ty.

Definition check_exprs
  (ty_expr : pexpr -> cexec atype) (es : seq pexpr) (tys : seq atype)
  : cexec unit :=
  fold2 E.arity_mismatch (fun e ty _ => check_expr ty_expr e ty) es tys tt.

Definition ty_get_set
  (ty_expr : pexpr -> cexec atype) (ws : wsize) (x : gvar) (e : pexpr)
  : cexec atype :=
  Let tx := ty_gvar x in
  Let te := ty_expr e in
  Let _ := check_array tx in
  Let _ := check_int te in
  ok (aword ws).

Definition ty_get_set_sub
  (ty_expr : pexpr -> cexec atype) (ws : wsize) (len : Z) (x : gvar) (e : pexpr)
  : cexec atype :=
  Let tx := ty_gvar x in
  Let te := ty_expr e in
  Let _ := check_array tx in
  Let _ := check_int te in
  ok (aarr ws len).

Definition ty_load_store (ty_expr : pexpr -> cexec atype) (ws : wsize) (e : pexpr)
  : cexec atype :=
  Let te := ty_expr e in
  Let _ := check_ptr te in
  ok (aword ws).

Fixpoint ty_expr (e : pexpr) : cexec atype :=
  match e with
  | Pconst _ => ok aint
  | Pbool _ => ok abool
  | Parr_init ws len => ok (aarr ws len)
  | Pvar x => ty_gvar x
  | Pget _ _ ws x e => ty_get_set ty_expr ws x e
  | Psub _ ws len x e => ty_get_set_sub ty_expr ws len x e
  | Pload _ ws e => ty_load_store ty_expr ws e
  | Papp1 op e =>
    let (tin, tout) := type_of_op1 op in
    Let _ := check_expr ty_expr e tin in
    ok tout
  | Papp2 op e1 e2 =>
    let '(tin1, tin2, tout) := type_of_op2 op in
    Let _ := check_expr ty_expr e1 tin1 in
    Let _ := check_expr ty_expr e2 tin2 in
    ok tout
  | PappN op es =>
    let (tins, tout) := type_of_opN op in
    Let _ := check_exprs ty_expr es tins in
    ok tout
  | Pif ty b e1 e2 =>
    Let _ := check_expr ty_expr b abool in
    Let _ := check_expr ty_expr e1 ty in
    Let _ := check_expr ty_expr e2 ty in
    ok ty
  end.

Definition ty_lval (x : lval) : cexec atype :=
  match x with
  | Lnone _ ty => ok ty
  | Lvar x => ok (ty_var x)
  | Lmem _ ws _ e => ty_load_store ty_expr ws e
  | Laset _ _ ws x e => ty_get_set ty_expr ws (mk_lvar x) e
  | Lasub _ ws len x e => ty_get_set_sub ty_expr ws len (mk_lvar x) e
  end.

(* The destination [x] accepts a value of type [ty]. *)
Definition check_lval (x : lval) (ty : atype) : cexec unit :=
  Let tx := ty_lval x in
  check_type ty tx.

Definition check_lvals (xs : lvals) (tys : seq atype) : cexec unit :=
  fold2 E.arity_mismatch (fun x ty _ => check_lval x ty) xs tys tt.

Fixpoint check_eassert (a : eassert) : cexec unit :=
  match a with
  | Pexpr e => check_expr ty_expr e abool
  | PappN_safety op es => check_exprs ty_expr es (type_of_opN_safety op).1
  | Pis_var_init _ => ok tt
  | Pis_mem_init e1 e2 =>
    Let _ := check_expr ty_expr e1 (aword Uptr) in
    check_expr ty_expr e2 aint
  | Pand a1 a2 =>
    Let _ := check_eassert a1 in
    check_eassert a2
  end.

Definition get_fun (p : ufun_decls) (f : funname) : cexec ufundef :=
  o2r unknown_function (get_fundef p f).

Fixpoint check_instr (p : ufun_decls) (i : instr) : cexec unit :=
  let check_cmd := allM (check_instr p) in
  let 'MkI _ ir := i in
  match ir with
  | Cassgn x _ ty e =>
    Let _ := check_expr ty_expr e ty in
    check_lval x ty
  | Copn xs _ o es =>
    Let _ := assert (i_valid (get_instr_desc o)) E.invalid_operator in
    Let _ := check_exprs ty_expr es (sopn_tin o) in
    check_lvals xs (sopn_tout o)
  | Csyscall xs o es =>
    let s := syscall_sig_u o in
    Let _ := check_exprs ty_expr es (scs_tin s) in
    check_lvals xs (scs_tout s)
  | Cassert a => check_eassert a.2
  | Cif e c1 c2 =>
    Let _ := check_expr ty_expr e abool in
    Let _ := check_cmd c1 in
    check_cmd c2
  | Cfor i (_, e1, e2) c =>
    Let _ := check_int (ty_var i) in
    Let _ := check_expr ty_expr e1 aint in
    Let _ := check_expr ty_expr e2 aint in
    check_cmd c
  | Cwhile _ c1 e _ c2 =>
    Let _ := check_expr ty_expr e abool in
    Let _ := check_cmd c1 in
    check_cmd c2
  | Ccall xs fn es =>
    Let fd := get_fun p fn in
    Let _ := check_exprs ty_expr es fd.(f_tyin) in
    check_lvals xs fd.(f_tyout)
  end.

Definition check_assertions (l : assertions) : cexec unit :=
  allM (fun a => check_eassert a.2) l.

Definition check_contract (tyin tyout : seq atype) (fc : fun_contract)
  : cexec unit :=
  Let _ := check_lvals (map Lvar (f_iparams fc)) tyin in
  Let _ := check_lvals (map Lvar (f_ires fc)) tyout in
  Let _ := check_assertions fc.(f_pre) in
  check_assertions fc.(f_post).

Definition check_fun (p : ufun_decls) (f : ufun_decl) : cexec unit :=
  let fd := f.2 in
  Let _ := check_lvals (map Lvar fd.(f_params)) fd.(f_tyin) in
  Let _ := check_exprs ty_expr (map Plvar fd.(f_res)) fd.(f_tyout) in
  Let _ := allM (check_instr p) fd.(f_body) in
  oapp (check_contract fd.(f_tyin) fd.(f_tyout)) (ok tt) fd.(f_contract).

End GLOBS.

(* The value of a global has the type of its variable. *)
Definition check_global_decl (gdecl : glob_decl) : cexec unit :=
  let '(g, d) := gdecl in
  let ok_ty :=
    match d, g.(vtype) with
    | Gword ws _, aword ws' => ws == ws'
    | Garr len _, aarr ws len' => (len =? arr_size ws len')%Z
    | _, _ => false
    end in
  if ok_ty then ok tt else Error global_mismatch.

(* The functions are checked in the order of the source, the reverse of that
   of [p_funcs]. *)
Definition check_prog (p : uprog) : cexec unit :=
  Let _ := allM check_global_decl p.(p_globs) in
  allM (check_fun p.(p_globs) p.(p_funcs)) (rev p.(p_funcs)).

End TYPING.
