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

  Definition array_expected := typing_error (pp_s "array expected").
  Definition check_type_failed := typing_error (pp_s "check type failed").
  Definition arity_mismatch := typing_error (pp_s "arity mismatch").
  Definition unknown_function := typing_error (pp_s "Unknown function").
  Definition global_mismatch := typing_error (pp_s "global variable type value mismatch").

End E.

Section WITH_PARAMS.

Context `{asmop : asmOp}.
Context {pd : wsize}.
Context {msfsz : wsize}.

Notation vp := (Mvar.t var).

(* Definition type_of_expr (e : pexpr) : atype :=
    match e with
    | Pconst _ => aint
    | Pbool _ => abool
    | Parr_init ws len => aarr ws len
    | Pvar x => x.(gv).(v_var).(vtype)
    | Pget _ _ ws _ _ => aword ws
    | Psub _ ws len _ _ => aarr ws len
    | Pload _ ws _ => aword ws
    | Papp1 o _ => snd (type_of_op1 o)
    | Papp2 o _ _ => let '(_, _, tout) := type_of_op2 o in
                    tout
    | PappN o _ => snd (type_of_opN o)
    | Pif ty _ _ _ => ty
end. *)

Definition ty_var (x : var_i) : atype := x.(v_var).(vtype).
Definition ty_gvar (x : gvar) : atype := ty_var x.(gv).

Definition check_array (te : atype) : cexec unit :=
  match te with
  | aarr _ _ => ok tt
  | _ => Error E.array_expected
  end.

(* Debug rendering of a type for error messages *)
Definition pp_atype (t : atype) : pp_error :=
  match t with
  | abool => pp_s "bool"
  | aint => pp_s "int"
  | aword ws => pp_s ("u" ++ string_of_wsize ws)%string
  | aarr ws len =>
      pp_nobox [:: pp_s ("u" ++ string_of_wsize ws)%string;
                   pp_s "["; pp_z len; pp_s "]"]
  end.

Definition check_type (te : atype (*actual type*)) (ty : atype (*expected type*)) (*expected type <= actual type*): cexec unit :=
  let b := subatype ty te in
  if negb b then
    Error (typing_error (pp_vbox
      [:: pp_s "check type failed:";
          pp_hov [:: pp_s "expected type (ty) ="; pp_atype ty];
          pp_hov [:: pp_s "actual type   (te) ="; pp_atype te];
          pp_hov [:: pp_s "subatype ty te ="; pp_s (if b then "true" else "false")%string]]))
  else ok tt.

Definition check_int (te : atype) : cexec unit := check_type te (aint).

Definition check_ptr (te : atype) : cexec unit := check_type te (aword pd).

Definition check_expr (ty_expr : pexpr -> cexec atype) (e' : pexpr) (ty : atype) : cexec unit := 
  Let te := ty_expr e' in
  check_type te ty.

Definition check_exprs (ty_expr : pexpr -> cexec atype) (es : seq pexpr) (tys : seq atype) : cexec unit := 
  fold2 E.arity_mismatch (fun e ty _ => check_expr ty_expr e ty) es tys tt.

Definition ty_get_set (ty_expr : pexpr -> cexec atype) (ws : wsize) (x : gvar) (e' : pexpr) : cexec atype :=
  let tx := ty_gvar x in
  Let te := ty_expr e' in
  Let _ := check_array tx in
  Let _ := check_int te in 
  ok (aword ws).

Definition ty_get_set_sub (ty_expr : pexpr -> cexec atype) (ws : wsize) (len : Z) (x : gvar) (e' : pexpr) : cexec atype := 
  let tx := ty_gvar x in
  Let te := ty_expr e' in
  Let _ := check_array tx in
  Let _ := check_int te in
  ok (aarr ws len). (* TODO : how about checking that subarr fits within arr*) 

Definition ty_load_store (ty_expr : pexpr -> cexec atype) (ws : wsize) (e' : pexpr) : cexec atype :=
  Let te := ty_expr e' in
  Let _ := check_ptr te in
  ok (aword ws). (*pd <= te*)

Fixpoint ty_expr (e : pexpr) : cexec atype :=
    match e with
    | Pconst _ => ok aint
    | Pbool _ => ok abool
    | Parr_init ws len => ok (aarr ws len)
    | Pvar x => ok (ty_gvar x)
    | Pget _ _ ws x e => ty_get_set ty_expr ws x e
    | Psub _ ws len x e => ty_get_set_sub ty_expr ws len x e
    | Pload _ ws e =>     ty_load_store ty_expr ws e
    | Papp1 op e =>       let (tin, tout) := type_of_op1 op in
                          Let _ := check_expr ty_expr e tin in
                          ok tout
    | Papp2 op e1 e2 =>   let '(tin1, tin2, tout) := type_of_op2 op in
                          Let _ := check_expr ty_expr e1 tin1 in
                          Let _ := check_expr ty_expr e2 tin2 in
                          ok tout
    | PappN op es =>      let (tins, tout) := type_of_opN op in
                          Let _ := check_exprs ty_expr es tins in
                          ok tout
    | Pif ty b e1 e2 =>   Let _ := check_expr ty_expr b abool in
                          Let _ := check_expr ty_expr e1 ty in
                          Let _ := check_expr ty_expr e2 ty in
                          ok ty
    end.

Definition ty_lval (x : lval): cexec atype :=
  match x with
    | Lnone _ ty => ok ty
    | Lvar x' => ok (ty_var x')
    | Lmem _ ws _ e => ty_load_store ty_expr ws e 
    | Laset _ _ ws x' e => ty_get_set ty_expr ws (mk_gvar x') e 
    | Lasub _ ws len x' e => ty_get_set_sub ty_expr ws len (mk_gvar x') e
  end.

Definition check_lval (x : lval) (ty : atype) : cexec unit :=
  Let tx := ty_lval x in
  check_type ty tx.

Definition check_lvals xs tys : cexec unit :=
  fold2 E.arity_mismatch (fun x ty _ => check_lval x ty) xs tys tt.

Fixpoint check_eassert (a : eassert) : cexec unit :=
  match a with
    | Pexpr e => check_expr ty_expr e abool
    | PappN_safety op es => let (tins , _) := type_of_opN_safety op in 
                            check_exprs ty_expr es tins
    | Pis_var_init _ => ok tt
    | Pis_mem_init e1 e2 => Let _ := check_expr ty_expr e1 (aword pd) in 
                            check_expr ty_expr e2 aint
    | Pand a1 a2 => Let _ := check_eassert a1 in
                    check_eassert a2
  end.

Definition check_cmd (check_instr : ufun_decls -> instr -> cexec unit) p (c : list instr) : cexec unit :=
  allM (check_instr p) c. 

Definition get_fun (p:ufun_decls) (f : funname) :=
  match get_fundef p f with
    | Some fd => ok fd
    | None => Error unknown_function (* unreachable, undefined function call error thrown in pretyping:94 *)
  end.

Fixpoint check_instr (p : ufun_decls) (i : instr) : cexec unit :=
  let 'MkI ii ir := i in
  match ir with
    | Cassgn x _ ty e => Let _ := check_expr ty_expr e ty in
                          check_lval x ty
    | Copn xs _ sop es => let (tins , tout) :=
                            (sopn_tin (pd := {| Uptr := pd |}) (msfsz := {| msf_size := msfsz |}) sop ,
                             sopn_tout (pd := {| Uptr := pd |}) (msfsz := {| msf_size := msfsz |}) sop) in
                          Let _ := check_exprs ty_expr es tins in
                          check_lvals xs tout
    | Csyscall xs o es => let s := syscall_sig_u o in
                          let tins := scs_tin s in
                          let tout := scs_tout s in
                          Let _ := check_exprs ty_expr es tins in
                          check_lvals xs tout
    | Cassert a => check_eassert (snd a)
    | Cif e c1 c2 => Let _ := check_expr ty_expr e abool in
                      Let _ := check_cmd check_instr p c1 in
                      check_cmd check_instr p c2
    | Cfor i (_ ,e1 ,e2) c => Let _ := check_expr ty_expr (Pvar (mk_gvar i)) aint in
                              Let _ := check_expr ty_expr e1 aint in
                              Let _ := check_expr ty_expr e2 aint in
                              check_cmd check_instr p c
    | Cwhile _ c1 e _ c2 => Let _ := check_expr ty_expr e abool in
                            Let _ := check_cmd check_instr p c1 in
                            check_cmd check_instr p c1
    | Ccall xs fn es =>  Let fd := get_fun p fn in
                          Let _  := check_exprs ty_expr es fd.(f_tyin) in
                          check_lvals xs fd.(f_tyout)
  end.

Definition check_global_decl (gd : glob_decl) : cexec unit :=
  let '(g, d) := gd in
  let ty := g.(vtype) in 
  match d with 
    | Gword ws _ => let c := match ty with
                              | aword ws' => ws != ws'
                              (* | aword ws' => negb (ws <= ws')%CMP *)
                              | _ => true 
                            end
                    in if c then Error global_mismatch else ok tt
    | Garr len _ => let c := match ty with
                              | aarr ws len' => len != arr_size ws len'
                              | _ => true
                            end
                    in if c then Error global_mismatch else ok tt
  end.

Definition check_contract (tyin tyout : list atype) (fc : fun_contract) : cexec unit := (* I don't know what a contract is*)
  let args := map (Pvar \o mk_gvar) fc.(f_iparams) in
  let res := map (Pvar \o mk_gvar) fc.(f_ires) in
  Let _ := check_exprs ty_expr args tyin in
  Let _ := check_exprs ty_expr res tyout in
  Let _ := allM (fun '(_, a) => check_eassert a) fc.(f_pre) in
  allM (fun '(_, a) => check_eassert a) fc.(f_post).

Definition check_fun (p : ufun_decls) (func : ufun_decl) : cexec unit := 
  let fd := snd func in
  let args := map (Pvar \o mk_gvar) fd.(f_params) in
  let res := map (Pvar \o mk_gvar) fd.(f_res) in
  Let _ := check_exprs ty_expr args fd.(f_tyin) in
  Let _ := check_exprs ty_expr res fd.(f_tyout) in
  Let _ := check_cmd check_instr p fd.(f_body) in
  Let _ := oapp (check_contract fd.(f_tyin) fd.(f_tyout)) (ok tt) fd.(f_contract) in
  ok tt.

Definition check_prog (p : uprog): cexec unit :=
  let gds := p.(p_globs) in
  let funcs := p.(p_funcs) in
  Let _ := allM check_global_decl gds in
  Let _ := allM (check_fun funcs) (rev funcs) in
  ok tt.



  
End WITH_PARAMS.










