Require Import ZArith Setoid Morphisms.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat ssrint ssralg tuple.
From mathcomp Require Import choice fintype eqtype div seq zmodp.
Require Import strings word dmasm_utils dmasm_type dmasm_var dmasm_expr.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* ** Compiler error 
 * -------------------------------------------------------------------------- *)

Inductive error_msg :=
  | Cerr_varalloc : var_i -> var_i -> string -> error_msg
  | Cerr_inline   : Sv.t -> Sv.t -> error_msg
  | Cerr_Loop     : string -> error_msg
  | Cerr_fold2    : string -> error_msg
  | Cerr_neqop2   : sop2 -> sop2 -> string -> error_msg
  | Cerr_neqop    : sopn -> sopn -> string -> error_msg
  | Cerr_neqdir   : string -> error_msg
  | Cerr_neqexpr  : pexpr -> pexpr -> string -> error_msg
  | Cerr_neqrval  : rval -> rval -> string -> error_msg
  | Cerr_neqfun   : funname -> funname -> string -> error_msg
  | Cerr_neqinstr : instr_r -> instr_r -> string -> error_msg
  | Cerr_unknown_fun : funname -> string -> error_msg
  | Cerr_in_fun   : fun_error -> error_msg
  | Cerr_arr_exp  : pexpr -> pexpr -> error_msg 
  | Cerr_arr_exp_v: rval -> rval -> error_msg 
  | Cerr_stk_alloc: string -> error_msg

with fun_error   := 
  | Ferr_in_body  : funname -> funname -> (instr_info * error_msg) -> fun_error
  | Ferr_neqfun   : funname -> funname -> fun_error
  | Ferr_neqprog  : fun_error
  | Ferr_loop     : fun_error.


Notation instr_error := (instr_info * error_msg)%type.

Definition cexec A := result error_msg A.
Definition ciexec A := result instr_error A.
Definition cfexec A := result fun_error A.

Definition cok {A} (a:A) : cexec A := @Ok error_msg A a.
Definition ciok {A} (a:A) : ciexec A := @Ok instr_error A a.
Definition cfok {A} (a:A) : cfexec A := @Ok fun_error A a.

Definition cerror  (c:error_msg) {A} : cexec A := @Error _ A c.
Definition cierror (ii:instr_info) (c:error_msg) {A} : ciexec A := @Error _ A (ii,c).
Definition cferror  (c:fun_error) {A} : cfexec A := @Error _ A c.

Definition add_iinfo {A} ii (r:cexec A) : ciexec A := 
  match r with
  | Ok a => @Ok _ A a
  | Error e  => Error (ii,e)
  end.

Definition add_finfo {A} f1 f2 (r:ciexec A) : cfexec A := 
  match r with
  | Ok a => @Ok _ A a
  | Error e  => Error (Ferr_in_body f1 f2 e)
  end.

Definition add_infun {A} (ii:instr_info) (r:cfexec A) : ciexec A :=
  match r with
  | Ok a => @Ok _ A a
  | Error e => Error (ii, Cerr_in_fun e)
  end.

Lemma add_iinfoP A (a:A) (e:cexec A) ii (P:Prop):  
  (e = ok a -> P) -> 
  add_iinfo ii e = ok a -> P.
Proof. by case: e=> //= a' H [] Heq;apply H;rewrite Heq. Qed.

Lemma add_finfoP A (a:A) e f1 f2 (P:Prop):  
  (e = ok a -> P) -> 
  add_finfo f1 f2 e = ok a -> P.
Proof. by case: e=> //= a' H [] Heq;apply H;rewrite Heq. Qed.

Lemma add_infunP A a ii (e:cfexec A) (P:Prop):  
  (e = ok a -> P) -> 
  add_infun ii e = ok a -> P.
Proof. by case: e=> //= a' H [] Heq;apply H;rewrite Heq. Qed.
 
Module Type LoopCounter.
  Parameter nb  : nat.
  Parameter nbP : nb = (nb.-1).+1.
End LoopCounter.

Module Loop : LoopCounter.
  Definition nb := 100.
  Lemma nbP : nb = (nb.-1).+1.
  Proof. done. Qed.
End Loop.



