(* ** Imports and settings *)
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq eqtype ssralg.
From mathcomp Require Import word_ssrZ.
From Coq Require Import ZArith Uint63.
Require Import global values sopn pseudo_operator expr psem compiler_util.

Local Open Scope seq_scope.

Module Import E.

  Definition pass : string := "type checking".

  Definition ii_loop_iterator := ii_loop_iterator pass.

  Definition typing_error (pp : pp_error) := {|
    pel_msg := pp;
    pel_fn := None;
    pel_fi := None;
    pel_ii := None;
    pel_vi := None;
    pel_pass := Some pass;
    pel_internal := false
  |}.

  Definition pp_atype (t : atype) : pp_error :=
  match t with
  | abool => pp_s "bool"
  | aint => pp_s "int"
  | aword ws => pp_s ("u" ++ string_of_wsize ws)%string
  | aarr ws len =>
      pp_nobox [:: pp_s ("u" ++ string_of_wsize ws)%string;
                   pp_s "["; pp_z len; pp_s "]"]
  end.

  (* "<pp> has type <te> while <ty> is expected" *)
  Definition type_mismatch (pp : pp_error) (te ty : atype) :=
    typing_error (pp_box [:: pp; pp_s "has type"; pp_atype te;
                             pp_s "while"; pp_atype ty; pp_s "is expected"]).

  Definition expr_type_mismatch (e : pexpr) (te ty : atype) :=
    type_mismatch (pp_box [:: pp_s "the expression"; pp_e e]) te ty.

  Definition lval_type_mismatch (x : lval) (tx ty : atype) :=
    type_mismatch (pp_box [:: pp_s "the left value"; pp_lv x]) tx ty.

  Definition array_expected (e : pexpr) (te : atype) := (* caught by pretyping *)
    typing_error (pp_box [:: pp_s "the expression"; pp_e e; pp_s "has type";
                             pp_atype te; pp_s "while an array is expected"]).

  Definition arity_mismatch (msg : string) (n : nat) := (* caught by pretyping *)
    typing_error (pp_box [:: pp_s "invalid number of"; pp_s msg;
                             pp_z (Z.of_nat n); pp_s "expected"]).

  Definition unknown_function (fn : funname) := (* caught by pretyping *)
    typing_error (pp_box [:: pp_s "Unknown function"; pp_fn fn]).

  Definition undefined_global (x : var) :=
    typing_error (pp_box [:: pp_s "global variable"; pp_var x; pp_s "is not defined"]).

  Definition global_mismatch (x : var) (ty vty : atype) :=
    typing_error (pp_box [:: pp_s "global variable"; pp_var x; pp_s "has type";
                             pp_atype ty; pp_s "but its value has type"; pp_atype vty]).

  Definition invalid_intrinsics := typing_error (pp_s "invalid operator, please report").

End E.

Section TYPING.

Context `{asmop : asmOp}.
Context {pd : PointerData}.
Context {msfsz : MSFsize}.

Definition ty_var (x : var_i) : atype := x.(v_var).(vtype).
Definition ty_gvar (x : gvar) : atype := ty_var x.(gv).

Definition check_array (x : gvar) (te : atype) : cexec unit :=
  if te is aarr _ _ then ok tt else Error (E.array_expected (Pvar x) te).

(* [err] is the error to report, built by the caller (it knows the expression) *)
Definition check_type (err : pp_error_loc) (te : atype (*actual type*)) (ty : atype (*expected type*)) (*expected wsize <= actual wsize*): cexec unit :=
  let b := subatype ty te in
  if negb b then Error err
  else ok tt.

Section GLOBALS.

Context (gd : glob_decls).

Definition check_var (x: gvar) : cexec unit := 
  if (is_lvar x) then ok tt else
                              if get_global_value gd (x.(gv)) is Some ga 
                              then ok tt else Error (E.undefined_global x.(gv).(v_var)).

Definition check_int (e : pexpr) (te : atype) : cexec unit :=
  check_type (E.expr_type_mismatch e te aint) te aint.

Definition check_ptr (e : pexpr) (te : atype) : cexec unit :=
  check_type (E.expr_type_mismatch e te (aword Uptr)) te (aword Uptr).

Definition check_expr_ (ty_expr : pexpr -> cexec atype) (e : pexpr) (ty : atype) : cexec unit := 
  Let te := ty_expr e in
  check_type (E.expr_type_mismatch e te ty) te ty.

Definition check_exprs_ (ty_expr : pexpr -> cexec atype) (es : seq pexpr) (tys : seq atype) : cexec unit := 
  fold2 (E.arity_mismatch "expressions" (size tys)) (fun e ty _ => check_expr_ ty_expr e ty) es tys tt.

Definition ty_get_set_ (ty_expr : pexpr -> cexec atype) (ws : wsize) (x : gvar) (e' : pexpr) : cexec atype :=
  Let _ := check_var x in
  let tx := ty_gvar x in
  Let te := ty_expr e' in
  Let _ := check_array x tx in
  Let _ := check_int e' te in
  ok (aword ws).

Definition ty_get_set_sub_ (ty_expr : pexpr -> cexec atype) (ws : wsize) (len : Z) (x : gvar) (e' : pexpr) : cexec atype := 
  Let _ := check_var x in
  let tx := ty_gvar x in
  Let te := ty_expr e' in
  Let _ := check_array x tx in
  Let _ := check_int e' te in
  ok (aarr ws len).

Definition ty_load_store_ (ty_expr : pexpr -> cexec atype) (ws : wsize) (e' : pexpr) : cexec atype :=
  Let te := ty_expr e' in
  Let _ := check_ptr e' te in
  ok (aword ws). (*pd <= te*)

Fixpoint ty_expr (e : pexpr) : cexec atype :=
    match e with
    | Pconst _ => ok aint
    | Pbool _ => ok abool
    | Parr_init ws len => ok (aarr ws len)
    | Pvar x => Let _ := check_var x in
                ok (ty_gvar x)
    | Pget _ _ ws x e => ty_get_set_ ty_expr ws x e
    | Psub _ ws len x e => ty_get_set_sub_ ty_expr ws len x e
    | Pload _ ws e =>     ty_load_store_ ty_expr ws e
    | Papp1 op e =>       let (tin, tout) := type_of_op1 op in
                          Let _ := check_expr_ ty_expr e tin in
                          ok tout
    | Papp2 op e1 e2 =>   let '(tin1, tin2, tout) := type_of_op2 op in
                          Let _ := check_expr_ ty_expr e1 tin1 in
                          Let _ := check_expr_ ty_expr e2 tin2 in
                          ok tout
    | PappN op es =>      let (tins, tout) := type_of_opN op in
                          Let _ := check_exprs_ ty_expr es tins in
                          ok tout
    | Pif ty b e1 e2 =>   Let _ := check_expr_ ty_expr b abool in
                          Let _ := check_expr_ ty_expr e1 ty in
                          Let _ := check_expr_ ty_expr e2 ty in
                          ok ty
    end.

Definition check_expr      := check_expr_      ty_expr.
Definition check_exprs     := check_exprs_     ty_expr.
Definition ty_get_set      := ty_get_set_      ty_expr.
Definition ty_get_set_sub  := ty_get_set_sub_  ty_expr.
Definition ty_load_store   := ty_load_store_   ty_expr.

Definition ty_lval (x : lval): cexec atype :=
  match x with
    | Lnone _ ty => ok ty
    | Lvar x' => ok (ty_var x')
    | Lmem _ ws _ e => ty_load_store ws e 
    | Laset _ _ ws x' e => ty_get_set ws (mk_lvar x') e 
    | Lasub _ ws len x' e => ty_get_set_sub ws len (mk_lvar x') e
  end.

Definition check_lval (x : lval) (ty : atype) : cexec unit :=
  Let tx := ty_lval x in
  check_type (E.lval_type_mismatch x tx ty) ty tx.

Definition check_lvals xs tys : cexec unit :=
  fold2 (E.arity_mismatch "left values" (size tys)) (fun x ty _ => check_lval x ty) xs tys tt.

Fixpoint check_eassert (a : eassert) : cexec unit :=
  match a with
    | Pexpr e => check_expr e abool
    | PappN_safety op es => 
      let (tins , _) := type_of_opN_safety op in 
      check_exprs es tins
    | Pis_var_init _ => ok tt
    | Pis_mem_init e1 e2 => Let _ := check_expr e1 (aword Uptr) in
                            check_expr e2 aint
    | Pand a1 a2 => Let _ := check_eassert a1 in
                    check_eassert a2
  end.

Definition check_cmd (check_instr : ufun_decls -> instr -> cexec unit) p (c : list instr) : cexec unit :=
  allM (check_instr p) c. 

Definition get_fun (p:ufun_decls) (f : funname) :=
  o2r (unknown_function f) (get_fundef p f). (* unreachable, undefined function call error thrown in pretyping:94 *)

Fixpoint check_instr (p : ufun_decls) (i : instr) : cexec unit :=
  let 'MkI ii ir := i in
  match ir with
    | Cassgn x _ ty e => Let _ := add_iinfo ii (check_expr e ty) in
                          add_iinfo ii (check_lval x ty)
    | Copn xs _ sop es => let (tins , tout) :=
                            (sopn_tin sop , sopn_tout sop) in
                          Let _ := add_iinfo ii (check_exprs es tins) in
                          Let _ := add_iinfo ii (check_lvals xs tout) in
                          if (sopn_i_valid sop) then ok tt else Error (pp_at_ii ii E.invalid_intrinsics)
    | Csyscall xs o es => let s := syscall_sig_u o in
                          let tins := scs_tin s in
                          let tout := scs_tout s in
                          Let _ := add_iinfo ii (check_exprs es tins) in
                          add_iinfo ii (check_lvals xs tout)
    | Cassert a => add_iinfo ii (check_eassert (snd a))
    | Cif e c1 c2 => Let _ := add_iinfo ii (check_expr e abool) in
                      Let _ := check_cmd check_instr p c1 in
                      check_cmd check_instr p c2
    | Cfor i (_ ,e1 ,e2) c => Let _ := add_iinfo ii (check_expr (Pvar (mk_lvar i)) aint) in
                              Let _ := add_iinfo ii (check_expr e1 aint) in
                              Let _ := add_iinfo ii (check_expr e2 aint) in
                              check_cmd check_instr p c
    | Cwhile _ c1 e _ c2 => Let _ := add_iinfo ii (check_expr e abool) in
                            Let _ := check_cmd check_instr p c1 in
                            check_cmd check_instr p c2
    | Ccall xs fn es =>  Let fd := add_iinfo ii (get_fun p fn) in
                          Let _  := add_iinfo ii (check_exprs es fd.(f_tyin)) in
                          add_iinfo ii (check_lvals xs fd.(f_tyout))
  end.

Definition check_global_decl (gd : glob_decl) : cexec unit :=
  let '(g, d) := gd in
  let ty := g.(vtype) in 
  match d with 
    | Gword ws _ => let c := match ty with
                              | aword ws' => ws != ws'
                              | _ => true 
                            end
                    in if c then Error (global_mismatch g ty (aword ws)) else ok tt
    | Garr len _ => let c := match ty with
                              | aarr ws len' => len != arr_size ws len'
                              | _ => true
                            end
                    in if c then Error (global_mismatch g ty (aarr U8 len)) else ok tt
  end.

Definition check_contract (tyins tyouts : list atype) (fc : fun_contract) : cexec unit :=
  Let _ := check_lvals (map Lvar fc.(f_iparams)) tyins in
  Let _ := check_lvals (map Lvar fc.(f_ires)) tyouts in
  Let _ := allM (fun '(_, a) => check_eassert a) fc.(f_pre) in
  allM (fun '(_, a) => check_eassert a) fc.(f_post).

Definition check_fun (p : ufun_decls) (func : ufun_decl) : cexec unit := 
  let fd := snd func in
  let res := map (Pvar \o mk_lvar) fd.(f_res) in
  add_finfo fd.(f_info) (
  Let _ := check_lvals (map Lvar fd.(f_params)) fd.(f_tyin) in
  Let _ := check_exprs res fd.(f_tyout) in
  Let _ := check_cmd check_instr p fd.(f_body) in
  Let _ := oapp (check_contract fd.(f_tyin) fd.(f_tyout)) (ok tt) fd.(f_contract) in
  ok tt).

End GLOBALS.

Definition check_prog (p : uprog): cexec unit :=
  let gds := p.(p_globs) in
  let funcs := p.(p_funcs) in
  Let _ := allM check_global_decl gds in
  Let _ := allM (check_fun gds funcs) (rev funcs) in
  ok tt.



  
End TYPING.










