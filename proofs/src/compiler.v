Require Import ZArith.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat ssrint ssralg.
From mathcomp Require Import choice fintype eqtype div seq zmodp finset.
Require Import Coq.Logic.Eqdep_dec.
Require Import finmap strings word dmasm_utils dmasm_type dmasm_var dmasm_expr dmasm_sem.
Require Import allocation inlining unrolling constant_prop dead_code.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.

Local Open Scope ring_scope.
Local Open Scope fun_scope.
Local Open Scope vmap.
Local Open Scope seq_scope.


Definition unroll1 ta tr (fd:fundef ta tr) := 
  let fd := unroll_call fd in
  let fd := const_prop_call fd in
  dead_code_call fd.

Fixpoint unroll (n:nat) ta tr (fd:fundef ta tr) :=
  match n with
  | O   => Ok unit fd  (* Should we raise an error ? *)
  | S n => 
    unroll1 fd >>= (fun fd' =>
      if eqb_fundef fd fd' then Ok unit fd 
      else unroll n fd')
  end.
                
Definition compile_fd ta tr (fd fdrn:fundef ta tr) :=
  if check_alloc_fd fd fdrn then
    check_inline_fd fdrn >>= (fun _ =>
    unroll nb_loop (inline_fd fdrn))
  else Error tt.

Lemma unroll1P ta tr (fd fd':fundef ta tr) mem va mem' vr:
  unroll1 fd = Ok unit fd' ->
  sem_call mem fd  va mem' vr ->
  sem_call mem fd' va mem' vr.
Proof.
  rewrite /unroll1=> Heq Hsem.
  have := dead_code_callP (const_prop_call (unroll_call fd)) mem mem' va vr.
  rewrite Heq=> H;apply H=> {H}.
  by apply const_prop_callP;apply unroll_callP.
Qed.

Lemma unrollP ta tr (fd fd':fundef ta tr) mem va mem' vr:
  unroll nb_loop fd = Ok unit fd' ->
  sem_call mem fd  va mem' vr ->
  sem_call mem fd' va mem' vr.
Proof.
  elim: nb_loop fd => /= [fd [] ->//|n Hn fd].
  case Heq: unroll1=> [fd1|] //=.
  case:ifP => [_ [] -> | _ Hu Hs] //.
  by apply (Hn fd1) => //;apply: unroll1P Hs.
Qed.

Opaque nb_loop.

Lemma compile_fdP ta tr (fd fdrn fd':fundef ta tr) mem va mem' vr:
  compile_fd fd fdrn = Ok unit fd' ->
  sem_call mem fd  va mem' vr ->
  sem_call mem fd' va mem' vr.
Proof.
  rewrite /compile_fd.
  case Hrn: check_alloc_fd => //=.
  case Hinl : check_inline_fd => [s|] //= Hunr Hsem.
  apply (unrollP Hunr).
  apply: inlineP Hinl.
  by apply: check_alloc_fdP Hsem.
Qed.
    
   


