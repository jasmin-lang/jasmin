From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype ssralg.
From mathcomp Require Import word_ssrZ.
From Coq Require Import ZArith.
Require Import expr sem_op_typed compiler_util.
Require Export safety_common.
Import Utf8.
Import oseq.
Require Import flag_combination.
Import pseudo_operator.

Local Open Scope seq_scope.
Local Open Scope Z_scope.

Set Printing Implicit.

(* Converts for loops into ones where the index variable is not modified in the body. *)

Section TOEC_FOR.

Context `{asmop:asmOp} {pd: PointerData} {msfsz : MSFsize}.

Context (fresh_var_ident: v_kind -> instr_info -> string -> atype -> Ident.ident).

Definition fresh_loop_counter (x : var) ii : var_i :=
  let name := fresh_var_ident (Ident.id_kind x.(vname)) ii (Ident.id_name x.(vname)) (vtype x) in
  {| v_var := Var (vtype x) name ; v_info := var_info_of_ii ii |}.

Fixpoint toec_for_i (V : Sv.t) (i : instr) : cexec instr :=
  let ec_for_c := mapM (toec_for_i V) in
  let 'MkI ii ir := i in
  Let ir' :=
    match ir with
    | Cassgn _ _ _ _ | Copn _ _ _ _ | Csyscall _ _ _
    | Cassert _      | Ccall _ _ _ => ok ir
    | Cif e c1 c2 =>
        Let c1 := ec_for_c c1 in
        Let c2 := ec_for_c c2 in
        ok (Cif e c1 c2)
    | Cwhile a c1 e ii c2 =>
        Let c1 := ec_for_c c1 in
        Let c2 := ec_for_c c2 in
        ok (Cwhile a c1 e ii c2)
    | Cfor x r c =>
        if ~~ Sv.mem (v_var x) (write_c c) then
          Let c := ec_for_c c in
          ok (Cfor x r c)
        else
          let x' := fresh_loop_counter x ii in
          Let c := ec_for_c c in
          let assgn := Cassgn (Lvar x) AT_inline (vtype x') (Plvar x') in
          let err := (pp_internal_error_s_at "ec_loop" ii "fresh variable not fresh") in
          assert (~~ Sv.mem (v_var x') V) err
            >> ok (Cfor x' r (MkI ii assgn :: c))
    end
  in ok (MkI ii ir').

Definition toec_for_c (V : Sv.t) : cmd -> cexec cmd :=
  mapM (toec_for_i V).

Section PROGT.
Context {pT : progT}.

Definition toec_for_fun (f : fundef) : cexec fundef :=
  Let b := toec_for_c (vars_fd f) (f_body f) in
  ok (with_body f b).

Definition toec_for_prog (p : prog) : cexec prog :=
  Let fds := map_cfprog toec_for_fun (p_funcs p) in
  ok {| p_funcs := fds; p_globs := p_globs p; p_extra := p_extra p |}.

End PROGT.


Definition toec_for_uprog (p : _uprog) : cexec _uprog :=
  toec_for_prog (p : @prog _ _ progUnit).

End TOEC_FOR.

