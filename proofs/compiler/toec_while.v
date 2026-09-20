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

(* Convert Jasmin's complex while loops into simple ones. *)

Section TOEC_WHILE.

Context `{asmop:asmOp} {pd: PointerData} {msfsz : MSFsize}.

Section PROGT.

Context {pT : progT}.

Definition toec_while_c (ec_while_i : instr -> cmd) (c : cmd) : cmd :=
  flatten (map ec_while_i c).

Fixpoint toec_while_i (i : instr) : cmd :=
  let 'MkI ii ir := i in
  match ir with
  | Cassgn _ _ _ _ | Copn _ _ _ _ | Csyscall _ _ _
  | Cassert _      | Ccall _ _ _ => [:: i]
  | Cif e c1 c2 =>
      let c1 := toec_while_c toec_while_i c1 in
      let c2 := toec_while_c toec_while_i c2 in
      [:: MkI ii (Cif e c1 c2)]
  | Cfor x r c =>
      let c := toec_while_c toec_while_i c in
      [:: MkI ii (Cfor x r c)]
  | Cwhile a c1 e ii c2 =>
      let c1 := toec_while_c toec_while_i c1 in
      let c2 := toec_while_c toec_while_i c2 in
      let tl := Cwhile a [::] e ii (c2 ++ c1) in
      c1 ++ [:: MkI ii tl]
  end.

Definition toec_while_fun (f : fundef) : fundef :=
  with_body f (toec_while_c toec_while_i (f_body f)).

Definition toec_while_prog : prog -> prog :=
  map_prog toec_while_fun.

End PROGT.

Definition toec_while_uprog (p : _uprog) : _uprog :=
  toec_while_prog (p : @prog _ _ progUnit).

End TOEC_WHILE.

