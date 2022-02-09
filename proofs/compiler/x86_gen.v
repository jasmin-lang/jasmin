From Coq Require Import Utf8 Relation_Operators.
From mathcomp Require Import all_ssreflect all_algebra.
Require Import compiler_util expr values linear asm_gen arch_extra.
Require Import x86_decl x86_instr_decl x86_extra x86_sem.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import compiler_util.

(* TODO: half of this file is not x86-dependent and could become architecture-generic *)

(* -------------------------------------------------------------------- *)

Definition not_condt (c:condt) := 
  match c with
  | O_ct  => NO_ct
  | NO_ct => O_ct
  | B_ct  => NB_ct 
  | NB_ct => B_ct
  | E_ct  => NE_ct 
  | NE_ct => E_ct 
  | BE_ct => NBE_ct 
  | NBE_ct => BE_ct 
  | S_ct   => NS_ct 
  | NS_ct  => S_ct 
  | P_ct   => NP_ct 
  | NP_ct  => P_ct 
  | L_ct   => NL_ct 
  | NL_ct  => L_ct 
  | LE_ct  => NLE_ct 
  | NLE_ct => LE_ct
  end.

Definition or_condt ii e c1 c2 : cexec condt := 
  match c1, c2 with
  | L_ct, E_ct | E_ct, L_ct => ok LE_ct
  | B_ct, E_ct | E_ct, B_ct => ok BE_ct 
  | _, _ => Error (E.berror ii e "Invalid condition (OR)")
  end.

Definition and_condt ii e c1 c2 := 
  match c1, c2 with
  | NB_ct, NE_ct | NE_ct, NB_ct => ok NBE_ct
  | NE_ct, NL_ct | NL_ct, NE_ct => ok NLE_ct 
  | _, _ => Error (E.berror ii e "Invalid condition (AND)")
  end.

Fixpoint assemble_cond_r ii (e: pexpr) : cexec condt :=
  match e with
  | Pvar v =>
    Let r := of_var_e ii v.(gv) in
    match r with
    | OF => ok O_ct
    | CF => ok B_ct
    | ZF => ok E_ct
    | SF => ok S_ct
    | PF => ok P_ct
    | DF => Error (E.berror ii e "Cannot branch on DF")
    end
  | Papp1 Onot e => 
    Let c := assemble_cond_r ii e in
    ok (not_condt c)

  | Papp2 Oor e1 e2 =>
    Let c1 := assemble_cond_r ii e1 in
    Let c2 := assemble_cond_r ii e2 in
    or_condt ii e c1 c2
  
  | Papp2 Oand e1 e2 =>
    Let c1 := assemble_cond_r ii e1 in
    Let c2 := assemble_cond_r ii e2 in
    and_condt ii e c1 c2
    
  | Papp2 Obeq (Pvar x1) (Pvar x2) =>
    Let r1 := of_var_e ii x1.(gv) in
    Let r2 := of_var_e ii x2.(gv) in
    if (r1 == SF) && (r2 == OF) || (r1 == OF) && (r2 == SF) then ok NL_ct
    else Error (E.berror ii e "Invalid condition (NL)")
  
  (* We keep this by compatibility but it will be nice to remove it *)
  | Pif _ (Pvar v1) (Papp1 Onot (Pvar vn2)) (Pvar v2) =>
    Let r1 := of_var_e ii v1.(gv) in
    Let rn2 := of_var_e ii vn2.(gv) in
    Let r2 := of_var_e ii v2.(gv) in
    if [&& r1 == SF, rn2 == OF & r2 == OF] ||
       [&& r1 == OF, rn2 == SF & r2 == SF] then
      ok L_ct
    else Error (E.berror ii e "Invalid condition (L)")

  | Pif _ (Pvar v1) (Pvar v2) (Papp1 Onot (Pvar vn2)) =>
    Let r1 := of_var_e ii v1.(gv) in
    Let r2 := of_var_e ii v2.(gv) in
    Let rn2 := of_var_e ii vn2.(gv) in
    if [&& r1 == SF, rn2 == OF & r2 == OF] ||
       [&& r1 == OF, rn2 == SF & r2 == SF] then
      ok NL_ct
    else  Error (E.berror ii e "Invalid condition (NL)")
  
  | _ => Error (E.berror ii e "don't known how to compile the condition")

  end.

Definition assemble_cond ii (e: pexpr) : cexec condt :=
  assemble_cond_r ii e.

(* -------------------------------------------------------------------- *)

Definition assemble_prog (p : lprog) : cexec asm_prog :=
  let rip := mk_ptr (lp_rip p) in
  let rsp := mk_ptr (lp_rsp p) in
  Let _ :=
    assert
      (to_reg rip == None)
      (E.gen_error true None None (pp_s "Invalid RIP"))
  in
  Let _ :=
      assert
        (of_string (lp_rsp p) == Some RSP)
        (E.gen_error true None None (pp_s "Invalid RSP"))
  in
  Let fds :=
    map_cfprog_linear (assemble_fd assemble_cond rip rsp) (lp_funcs p)
  in
  ok {| asm_globs := lp_globs p; asm_funcs := fds; |}.
