Require Import ZArith.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat ssrint ssralg.
From mathcomp Require Import choice fintype eqtype div seq zmodp finset.
Require Import Coq.Logic.Eqdep_dec.
Require Import strings word dmasm_utils dmasm_type dmasm_var dmasm_expr memory dmasm_sem.
Require Import compiler_util allocation inlining unrolling constant_prop dead_code.
Require Import array_expansion.

(*Require Import stack_alloc linear. *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition unroll1 (p:prog) := 
  let p := unroll_prog p in
  let p := const_prop_prog p in
  dead_code_prog p.

Fixpoint unroll (n:nat) (p:prog) :=
  match n with
  | O   => cferror Ferr_loop
  | S n => 
    Let p' := unroll1 p in
    if p == p' then cfok p 
    else unroll n p'
  end.

Definition unroll_loop (p:prog) := unroll Loop.nb p.

Section COMPILER.

(*Variable expand: forall ta tr, fundef ta tr -> fundef ta tr.
Variable ralloc: forall ta tr, fundef ta tr -> fundef ta tr.
Variable stk_alloc : forall ta tr, fundef ta tr -> seq.seq (var * Z) * S.fundef ta tr. *)

Variable rename_fd : fundef -> fundef.
Variable expand_fd : fundef -> fundef.
Variable alloc_fd  : fundef -> fundef.

Definition expand_prog (p:prog) := 
  map (fun f => (f.1, expand_fd f.2)) p.

Definition alloc_prog (p:prog) := 
    map (fun f => (f.1, alloc_fd f.2)) p.

Definition compile_prog (p:prog) := 
  Let p := inline_prog rename_fd p in
  Let p := unroll Loop.nb p in
  let pe := expand_prog p in
  Let _ := CheckExpansion.check_prog p pe in
  let pa := alloc_prog pe in
  Let _ := CheckAllocReg.check_prog pe pa in
  cfok pa.

(*
    
Definition compile_fd (ffd:funname * fundef ta tr) :=
  let fdrn := rename fd in
  if CheckAllocReg.check_fd fd fdrn then
    check_inline_fd fdrn >>= (fun _ =>
    unroll nb_loop (inline_fd fdrn) >>= (fun fd =>
    let fdea := expand fd in                                           
    if CheckExpansion.check_fd fd fdea then
      let fda := ralloc fdea in
       if CheckAllocReg.check_fd fdea fda then
         let (l, fds) := stk_alloc fda in
         if stack_alloc.check_fd l fda fds then 
           linear_fd fds >>= (fun lfd =>
             if lfd.(lfd_stk_size) == S.fd_stk_size fds then Ok unit lfd 
             else Error tt)
         else Error tt
       else Error tt
    else Error tt))
  else Error tt.

Section PROOF.

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

Lemma compile_fdP ta tr (fd:fundef ta tr) (fd':lfundef ta tr)mem va mem' vr:
  compile_fd fd = Ok unit fd' ->
  sem_call mem fd va mem' vr ->
  (exists p, alloc_stack mem (lfd_stk_size fd') = ok p) ->
  lsem_fd fd' va mem mem' vr.
Proof.
  rewrite /compile_fd.
  case Hrn:  CheckAllocReg.check_fd => //=.
  case Hinl: check_inline_fd => [s|] //=.
  case Hunr: unroll => [fdu|] //=.
  case Hea:  CheckExpansion.check_fd => //=.
  case Hra:  CheckAllocReg.check_fd => //=.
  case stk_alloc => [l fds] //=.
  case Hsa: stack_alloc.check_fd => //=.
  case Hlfd:linear_fd => [lfd|] //=. 
  case:eqP => [ Heq| //] [] <- Hsem;rewrite Heq=> Hex.
  apply: (linear_fdP Hlfd).
  apply: (stack_alloc.check_fdP Hsa) Hex.
  apply: (CheckAllocReg.check_fdP Hra).
  apply: (CheckExpansion.check_fdP Hea). 
  apply: (unrollP Hunr).
  apply: inlineP Hinl.
  by apply: CheckAllocReg.check_fdP Hsem.
Qed.

End PROOF.
*)

End COMPILER.

    
