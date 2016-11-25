Require Import ZArith Setoid Morphisms.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat ssrint ssralg tuple.
From mathcomp Require Import choice fintype eqtype div seq zmodp.
Require Import strings word dmasm_utils dmasm_type dmasm_var dmasm_expr.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* ** Compiler error 
 * -------------------------------------------------------------------------- *)

Inductive compiler_error_msg :=
  | Cerr_Alloc    : var_i -> compiler_error_msg
  | Cerr_Loop     : compiler_error_msg
  | Cerr_fold2    : string -> compiler_error_msg
  | Cerr_neqop    : sopn -> sopn -> string -> compiler_error_msg
  | Cerr_neqfun   : funname -> funname -> string -> compiler_error_msg
  | Cerr_neqinstr : instr_r -> instr_r -> string -> compiler_error_msg.

Definition compiler_error := (instr_info * compiler_error_msg)%type.

Definition cexec A := result compiler_error_msg A.
Definition ciexec A := result compiler_error A.

Definition cok {A} (a:A) : cexec A := @Ok compiler_error_msg A a.
Definition ciok {A} (a:A) : ciexec A := @Ok compiler_error A a.

Definition cerror  (c:compiler_error_msg) {A} : cexec A := @Error _ A c.
Definition cierror (c:compiler_error) {A} : ciexec A := @Error _ A c.

Module Type LoopCounter.
  Parameter nb:nat.
End LoopCounter.

Module Loop : LoopCounter.
  Definition nb := 100.
End Loop.

Definition add_iinfo {A} ii (r:cexec A) : ciexec A := 
  match r with
  | Ok a => @Ok _ A a
  | Error e  => Error (ii,e)
  end.


