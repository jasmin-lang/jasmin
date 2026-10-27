(* ** Imports and settings *)
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq eqtype.
Require Import expr compiler_util normalize_calls.

Local Open Scope seq_scope.

(* ** The contracts of the functions as assertions

   The semantics evaluates the precondition of a function at each call, in a
   state where only the parameters of the contract are bound, to the
   arguments of the call; and its postcondition on return, in a state where the
   parameters of the contract are bound to the arguments of the call and its
   results to the results of the function. The pass makes these checks
   assertions of the program, in two places.

   In the body of a function with a contract:

     iparams := params;  assert pre;  body;  ires := res;  assert post

   The parameters hold the arguments of the call, truncated to the types of the
   parameters, as the contract sees them. The variables of the contract are
   not variables of the function ([check_contract]): the body does not change
   them, and the postcondition reads the arguments of the call.

   Around a call [xs = f(es)] to a function [f] with a contract, in the caller:

     ip := es;  assert pre[iparams := ip];  xs = f(ip);  assert post[iparams := ip, ires := xs]

   The arguments are copied into fresh variables [ip]: the call may write a
   variable they read, and the postcondition reads the arguments. The call
   takes these copies as arguments, which hold the values of [es] truncated to
   the types of the parameters, as the callee receives them. The results are
   not copied: the destinations of the call are pairwise distinct variables of
   the types of the results, as [normalize_calls] produces them, so after the
   call each of them holds its result; a destination [_] becomes a fresh
   variable. The variables of the contract are renamed in its assertions, which
   read no other local variable.

   Both places check what the semantics of the contracts checks, on the same
   values: a program whose contracts are not evaluated, but whose assertions
   are, behaves as the source whose contracts are. The contracts are kept: the
   extraction prints them as the specifications of the functions. *)

Module Import E.

  Definition pass : string := "contracts to asserts".

  Definition contract_error :=
    pp_internal_error_s pass
      "a contract does not match the signature of its function, reads a variable it does not bind, or binds a variable of the function, or the parameters of the function are not distinct variables of the types of its arguments".

  Definition fresh_error (ii : instr_info) :=
    pp_internal_error_s_at pass ii "fresh auxiliary variable is not fresh".

  Definition call_error (ii : instr_info) :=
    pp_internal_error_s_at pass ii
      "the arguments or the destinations of a call to a function with a contract do not match its signature".

  Definition unknown_fun_error (ii : instr_info) :=
    pp_internal_error_s_at pass ii "call to an unknown function".

End E.

(* Renaming of the local variables of an assertion. *)
Section RENAME.

Context (r : Mvar.t var).

Fixpoint rename_eassert (a : eassert) : eassert :=
  match a with
  | Pexpr e => Pexpr (rename_e r e)
  | PappN_safety o es => PappN_safety o (map (rename_e r) es)
  | Pis_var_init x => Pis_var_init (rename_var r x)
  | Pis_mem_init e1 e2 => Pis_mem_init (rename_e r e1) (rename_e r e2)
  | Pand a1 a2 => Pand (rename_eassert a1) (rename_eassert a2)
  end.

Definition rename_assertion (a : assertion) : assertion := (a.1, rename_eassert a.2).

End RENAME.

(* [xs_k] renamed into [ys_k]; when [xs] binds a variable twice, the last
   binding wins, as in [write_vars]. *)
Definition rename_map (xs ys : seq var_i) : Mvar.t var :=
  foldl (fun m xy => Mvar.set m (v_var xy.1) (v_var xy.2)) (Mvar.empty var) (zip xs ys).

Section ASM_OP.

Context `{asmop : asmOp}.
Context (fresh_var_ident : v_kind -> instr_info -> string -> atype -> Ident.ident).

(* [xs_k := es_k], at the type [tys_k]. *)
Definition copy_es ii (xs : seq var_i) (tys : seq atype) (es : pexprs) : cmd :=
  map2 (fun x ty_e => MkI ii (Cassgn (Lvar x) AT_none ty_e.1 ty_e.2)) xs (zip tys es).

Definition assert_all ii (asrts : assertions) : cmd :=
  map (fun a => MkI ii (Cassert a)) asrts.

(* A fresh variable of the type of [x], named after it. The tally is the number
   of auxiliary variables already generated in the function: two copies of the
   same instruction receive distinct names from the memoising oracle. *)
Definition fresh_cvar ii (X acc : Sv.t) (x : var_i) : cexec (Sv.t * var_i) :=
  let ty := vtype x in
  let y :=
    {| vtype := ty;
       vname := fresh_var_ident (Reg (Normal, Direct)) ii
                  (Ident.id_name (vname x) ++ pos_tally (Sv.cardinal acc)) ty;
    |}
  in
  Let _ := assert (~~ Sv.mem y (Sv.union X acc)) (E.fresh_error ii) in
  ok (Sv.add y acc, {| v_var := y; v_info := var_info_of_ii ii |}).

Fixpoint fresh_cvars ii (X acc : Sv.t) (xs : seq var_i) : cexec (Sv.t * seq var_i) :=
  match xs with
  | [::] => ok (acc, [::])
  | x :: xs =>
    Let r := fresh_cvar ii X acc x in
    Let rs := fresh_cvars ii X r.1 xs in
    ok (rs.1, r.2 :: rs.2)
  end.

(* The variable that holds each result after the call: the destination, a
   variable of the type of the result, or a fresh variable for [_]. *)
Fixpoint call_dests ii (X acc : Sv.t) (lvs : lvals) (ires : seq var_i) :
  cexec (Sv.t * seq var_i) :=
  match lvs, ires with
  | [::], [::] => ok (acc, [::])
  | lv :: lvs, y :: ires =>
    Let r :=
      match lv with
      | Lvar x =>
        Let _ := assert (vtype x == vtype y) (E.call_error ii) in
        ok (acc, x)
      | Lnone _ ty =>
        Let _ := assert (ty == vtype y) (E.call_error ii) in
        fresh_cvar ii X acc y
      | _ => Error (E.call_error ii)
      end
    in
    Let rs := call_dests ii X r.1 lvs ires in
    ok (rs.1, r.2 :: rs.2)
  | _, _ => Error (E.call_error ii)
  end.

Definition call_with_contract ii (X acc : Sv.t) (lvs : lvals) (f : funname)
  (es : pexprs) (tyin : seq atype) (ci : fun_contract) : cexec (Sv.t * cmd) :=
  Let _ := assert (size es == size ci.(f_iparams)) (E.call_error ii) in
  Let rp := fresh_cvars ii X acc ci.(f_iparams) in
  Let rd := call_dests ii X rp.1 lvs ci.(f_ires) in
  Let _ := assert (uniq [seq v_var x | x <- rd.2]) (E.call_error ii) in
  let mpre := rename_map ci.(f_iparams) rp.2 in
  let mpost := rename_map (ci.(f_iparams) ++ ci.(f_ires)) (rp.2 ++ rd.2) in
  ok (rd.1,
      copy_es ii rp.2 tyin es
      ++ assert_all ii (map (rename_assertion mpre) ci.(f_pre))
      ++ MkI ii (Ccall [seq Lvar x | x <- rd.2] f [seq Plvar x | x <- rp.2])
      :: assert_all ii (map (rename_assertion mpost) ci.(f_post))).

Context (p : _uprog).

Section CMD.

Context (c2a_i : Sv.t -> instr -> cexec (Sv.t * cmd)).

Fixpoint c2a_c (acc : Sv.t) (c : cmd) : cexec (Sv.t * cmd) :=
  match c with
  | [::] => ok (acc, [::])
  | i :: c =>
    Let ai := c2a_i acc i in
    Let ac := c2a_c ai.1 c in
    ok (ac.1, ai.2 ++ ac.2)
  end.

End CMD.

Fixpoint c2a_i (X acc : Sv.t) (i : instr) : cexec (Sv.t * cmd) :=
  let 'MkI ii ir := i in
  match ir with
  | Cassgn _ _ _ _ | Copn _ _ _ _ | Csyscall _ _ _ | Cassert _ => ok (acc, [:: i])
  | Ccall lvs f es =>
    if get_fundef (p_funcs p) f is Some fd then
      if fd.(f_contract) is Some ci then
        call_with_contract ii X acc lvs f es fd.(f_tyin) ci
      else ok (acc, [:: i])
    else Error (E.unknown_fun_error ii)
  | Cif e c1 c2 =>
    Let ac1 := c2a_c (c2a_i X) acc c1 in
    Let ac2 := c2a_c (c2a_i X) ac1.1 c2 in
    ok (ac2.1, [:: MkI ii (Cif e ac1.2 ac2.2)])
  | Cfor x r c =>
    Let ac := c2a_c (c2a_i X) acc c in
    ok (ac.1, [:: MkI ii (Cfor x r ac.2)])
  | Cwhile al c1 e info c2 =>
    Let ac1 := c2a_c (c2a_i X) acc c1 in
    Let ac2 := c2a_c (c2a_i X) ac1.1 c2 in
    ok (ac2.1, [:: MkI ii (Cwhile al ac1.2 e info ac2.2)])
  end.

Definition contract_vars (ci : fun_contract) : Sv.t :=
  Sv.union (vars_l ci.(f_iparams)) (vars_l ci.(f_ires)).

(* The checks of the contract of the function, then its own assertions around
   the body whose calls check the contracts of their callees. *)
Definition contracts_to_asserts_fd (fd : ufundef) : cexec ufundef :=
  let X := Sv.union (vars_fd fd) (oapp contract_vars Sv.empty fd.(f_contract)) in
  Let ac := c2a_c (c2a_i X) Sv.empty fd.(f_body) in
  let body := ac.2 in
  if fd.(f_contract) is Some ci then
    let ii := if body is MkI ii _ :: _ then ii else dummy_instr_info in
    ok (with_body fd
          (copy_es ii ci.(f_iparams) fd.(f_tyin) (map Plvar fd.(f_params))
           ++ assert_all ii ci.(f_pre)
           ++ body
           ++ copy_es ii ci.(f_ires) fd.(f_tyout) (map Plvar fd.(f_res))
           ++ assert_all ii ci.(f_post)))
  else ok (with_body fd body).

(* The contract binds one variable per parameter and per result, of its type;
   its precondition reads only its parameters, its postcondition only its
   parameters and results; its variables are not variables of the
   function. The parameters of the function are pairwise distinct and of the
   types of its arguments: after the initialisation of the function, each of
   them holds its argument, which the copies give to the contract. *)
Definition check_contract (fd : ufundef) : cexec unit :=
  if fd.(f_contract) is Some ci then
    let iparams := vars_l ci.(f_iparams) in
    assert
      [&& all2 (fun (x : var_i) ty => vtype x == ty) ci.(f_iparams) fd.(f_tyin),
          all2 (fun (x : var_i) ty => vtype x == ty) ci.(f_ires) fd.(f_tyout),
          all2 (fun (x : var_i) ty => vtype x == ty) fd.(f_params) fd.(f_tyin),
          uniq [seq v_var x | x <- fd.(f_params)],
          size ci.(f_iparams) == size fd.(f_params),
          size ci.(f_ires) == size fd.(f_res),
          Sv.subset (read_easserts [seq a.2 | a <- ci.(f_pre)]) iparams,
          Sv.subset (read_easserts [seq a.2 | a <- ci.(f_post)]) (contract_vars ci)
        & disjoint (contract_vars ci) (vars_fd fd)]
      E.contract_error
  else ok tt.

Definition contracts_to_asserts_prog : cexec _uprog :=
  Let _ := allM (fun f => add_funname f.1 (add_finfo f.2.(f_info) (check_contract f.2)))
                p.(p_funcs) in
  Let funcs := map_cfprog contracts_to_asserts_fd (p_funcs p) in
  ok {| p_funcs := funcs; p_globs := p_globs p; p_extra := p_extra p |}.

End ASM_OP.
