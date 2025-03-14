
From Jasmin Require Import oseq.
(* problematic *)
From Jasmin Require Import expr.
From Jasmin Require Import it_jasmin_lib.

(* FIXME clean this *)
From Coq Require Import
     Arith.PeanoNat
     Lists.List
     Strings.String
     Morphisms
     Setoid
     RelationClasses
     EquivDec
     Equality
     Program.Tactics.

From ExtLib Require Import
     Data.String
     Structures.Monad
     Structures.Traversable
     Data.List
     Core.RelDec
     Structures.Maps
     Data.Map.FMapAList.

From ITree Require Import
     ITree
     ITreeFacts
     Monad
     Basics.HeterogeneousRelations
     Events.Map
     Events.State
     Events.StateFacts
     Events.Reader
     Events.Exception
     Events.FailFacts.

Require Import Paco.paco.
Require Import Psatz.
Require Import ProofIrrelevance.
Require Import FunctionalExtensionality.

From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq eqtype fintype.

From ITree Require Import
     Basics.Category
     Basics.Basics
     Basics.Function
     Core.ITreeDefinition
     Core.KTree
     Eq.Eqit
     Eq.UpToTaus
     Eq.Paco2
     Indexed.Sum
     Indexed.Function
     Indexed.Relation
     Interp.Handler
     Interp.Interp
     Interp.InterpFacts
     Interp.Recursion.

From ITree Require Import Rutt RuttFacts.

From ITree Require Import EqAxiom.

From Jasmin Require Import expr psem_defs psem oseq.
From Jasmin Require Import it_gen_lib it_jasmin_lib it_exec.
From Jasmin Require Import compiler_util.
(* problematic *)

(* End FIXME *)
Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.
Local Open Scope option_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Set Universe Polymorphism. *)

(* This files contains semantic models distinguished by use of either
mutual or double recursion, and by either modular, error-aware or flat
structure. There are fives models (MM: mutual modular; ME: mutual
error; MF: mutual flat; DE: double error; DF double flat) *)

(**** ERROR SEMANTICS *******************************************)
Section Errors.

(* type of errors (this might becom richer) *)
  (* Variant ErrType : Type := Err : ErrType. *)
(* error events *)


Definition ErrEvent : Type -> Type := exceptE error_data.

(*
sem_I : prog -> estate -> instr -> itree syscall_Event (state_error + estate)
sem_i : prog -> estate -> instr_r -> itree syscall_Event (state_error + estate)
sem_c : prog -> estate -> cmd -> itree syscall_Event (state_error + estate)
sem_fun : prog -> mem -> syscall -> funname -> values -> itree syscall_Event (state_error + (mem * syscall * values))
*)

(* failT (itree E) R = itree E (option R) *)
Definition handle_Err {E} : ErrEvent ~> execT (itree E) :=
  fun _ e =>
    match e with
    | Throw e' => Ret (ESerror _ e')
    end.

(* Err handler *)
Definition ext_handle_Err {E: Type -> Type} :
  ErrEvent +' E ~> execT (itree E) :=
  fun _ e =>
  match e with
  | inl1 e' => handle_Err e'
  | inr1 e' => Vis e' (pure (fun x => ESok x)) end.

(* ErrEvent interpreter *)
Definition interp_Err {E: Type -> Type} {A}
  (t: itree (ErrEvent +' E) A) : execT (itree E) A :=
  interp_exec ext_handle_Err t.

(*** auxiliary error functions *)

Definition ioget {E: Type -> Type} `{ErrEvent -< E} {V} (err: error_data) (o: option V) : itree E V :=
  match o with
  | Some v => Ret v
  | None => throw err
  end.

Definition err_result {E: Type -> Type} `{ErrEvent -< E} (Err : error -> error_data) :
  result error ~> itree E :=
  fun _ t => match t with
             | Ok v => Ret v
             | Error e => throw (Err e) end.

End Errors.

Section WSW.
Context
  {asm_op: Type}
  {asmop: asmOp asm_op}
  {wsw: WithSubWord}
  {dc: DirectCall}
  {syscall_state : Type}
  {ep : EstateParams syscall_state}
  {spp : SemPexprParams}
  {sip : SemInstrParams asm_op syscall_state}
  {pT : progT}
  {scP : semCallParams}
  (pr : prog)
  (ev : extra_val_t).

Definition mk_error_data (s:estate) (e:error)  := (e, tt).

Definition mk_errtype := fun s => mk_error_data s ErrType.

Definition iget_fundef {E} `{ErrEvent -< E}
  (fn: funname) (s:estate) : itree E fundef :=
  ioget (mk_errtype s) (get_fundef (p_funcs pr) fn).

Definition iresult  {E} `{ErrEvent -< E} {T} (s:estate) (F : exec T)  : itree E T :=
  err_result (mk_error_data s) F.

Definition iwrite_var {E} `{ErrEvent -< E}
   (wdb : bool) (x : var_i) (v : value) (s : estate) : itree E estate :=
  iresult s (write_var wdb x v s).

Definition iwrite_lval {E} `{ErrEvent -< E}
   (wdb : bool) (gd : glob_decls) (x : lval) (v : value) (s : estate) : itree E estate :=
  iresult s (write_lval wdb gd x v s).

Definition iwrite_lvals {E} `{ErrEvent -< E}
   (wdb : bool) (gd : glob_decls) (s : estate) (xs : lvals) (vs : values) : itree E estate :=
  iresult s (write_lvals wdb gd s xs vs).

Definition isem_pexpr {E} `{ErrEvent -< E}
   (wdb : bool) (gd : glob_decls) (s : estate) (e: pexpr) : itree E value :=
  iresult s (sem_pexpr wdb gd s e).

Definition isem_pexprs {E} `{ErrEvent -< E}
   (wdb : bool) (gd : glob_decls) (s : estate) (es: pexprs) : itree E values :=
  iresult s (sem_pexprs wdb gd s es).

Definition eval_assgn
  (x: lval) (tg: assgn_tag) (ty: stype) (e: pexpr)
  (st1: estate) : exec estate :=
   (Let v := sem_pexpr true (p_globs pr) st1 e in
    Let v' := truncate_val ty v in
    write_lval true (p_globs pr) x v' st1).

Definition eval_syscall
   (xs: lvals) (o: syscall_t)
   (es: pexprs) (s: estate) : exec estate :=
  Let ves := sem_pexprs true (p_globs pr) s es in
  Let: (scs, m, vs) := exec_syscall s.(escs) s.(emem) o ves in
  write_lvals true (p_globs pr)
     (with_scs (with_mem s m) scs) xs vs.

(** Auxiliary functions for recursion on list (seq) *)

Fixpoint isem_map {E} (sem_i: instr -> estate -> itree E estate)
   (c: cmd) (st: estate) : itree E estate :=
  match c with
  | nil => Ret st
  | i :: c' => st' <- sem_i i st ;; isem_map sem_i c' st'
  end.

Fixpoint isem_for_body {E} `{ErrEvent -< E}
   (sem_i : instr -> estate -> itree E estate)
   (i: var_i) (c: cmd)
   (ls: list Z) (s: estate) : itree E estate :=
  match ls with
  | nil => ret s
  | (w :: ws) =>
    s <- iwrite_var true i (Vint w) s;;
    s <- isem_map sem_i c s;;
    isem_for_body sem_i i c ws s
  end.

(* Make global definition *)
Local Notation continue_loop st := (ret (inl st)).
Local Notation exit_loop st := (ret (inr st)).

Local Notation gd := (p_globs pr).

Definition isem_cond {E} `{ErrEvent -< E} (e:pexpr) (s: estate) : itree E bool :=
  iresult s (sem_pexpr true gd s e >>r= to_bool).

Definition isem_bound {E} `{ErrEvent -< E} (e:pexpr) (s: estate) :
   itree E Z :=
  iresult s (sem_pexpr true gd s e >>r= to_int).

Definition isem_while_body {E} `{ErrEvent -< E}
   (sem_i : instr -> estate -> itree E estate)
   (c1 : cmd) (e:pexpr) (c2: cmd) (s1 : estate) : itree E (estate + estate) :=
   s2 <- isem_map sem_i c1 s1 ;;
   b <- isem_cond e s2 ;;
   if b then s3 <- isem_map sem_i c2 s2 ;; continue_loop s3
   else exit_loop s2.

Definition isem_while {E} `{ErrEvent -< E}
   (sem_i : instr -> estate -> itree E estate)
   (c1 : cmd) (e:pexpr) (c2: cmd) (s1 : estate) : itree E estate :=
  ITree.iter (isem_while_body sem_i c1 e c2) s1.

Record fstate := { fscs : syscall_state_t; fmem : mem; fvals : values }.

Fixpoint isem_i_body {E} `{ErrEvent -< E}
   (sem_call : funname -> fstate -> itree E fstate)
   (i: instr) (s1: estate) : itree E estate :=
  let sem_i := isem_i_body sem_call in
  let sem_cmd := isem_map sem_i in
  let: (MkI _ i) := i in
  match i with
  | Cassgn x tg ty e => iresult s1 (eval_assgn x tg ty e s1)
  | Copn xs tg o es => iresult s1 (sem_sopn gd o s1 xs es)
  | Csyscall xs o es => iresult s1 (eval_syscall xs o es s1)

  | Cif e c1 c2 =>
    b <- isem_cond e s1;;
    sem_cmd (if b then c1 else c2) s1

  | Cwhile a c1 e c2 =>
    isem_while sem_i c1 e c2 s1

  | Cfor i (d, lo, hi) c =>
    vlo <- isem_bound lo s1 ;;
    vhi <- isem_bound hi s1 ;;
    isem_for_body sem_i i c (wrange d vlo vhi) s1

  | Ccall xs fn args =>
    vargs <- isem_pexprs  (~~direct_call) gd s1 args;;
    r <- sem_call fn {| fscs := escs s1; fmem:= emem s1; fvals := vargs |} ;;
    iwrite_lvals (~~direct_call) gd (with_scs (with_mem s1 r.(fmem)) r.(fscs)) xs r.(fvals)
  end.

(**********************************************************************)
(** error-aware interpreter with mutual recursion *)

Definition estate0 (fs : fstate) :=
  Estate fs.(fscs) fs.(fmem) Vm.init.

Definition initialize_call (fd:fundef) (fs:fstate) : exec estate :=
  let sinit := estate0 fs in
  Let vargs' := mapM2 ErrType dc_truncate_val fd.(f_tyin) fs.(fvals) in
  Let s0 := init_state fd.(f_extra) (p_extra pr) ev sinit in
  write_vars (~~direct_call) fd.(f_params) vargs' s0.

Definition finalize_call (fd : fundef) (s:estate) :=
  Let vres := get_var_is (~~ direct_call) s.(evm) fd.(f_res) in
  Let vres' := mapM2 ErrType dc_truncate_val fd.(f_tyout) vres in
  let scs := s.(escs) in
  let m := finalize fd.(f_extra) s.(emem) in
  ok {| fscs := scs; fmem := m; fvals := vres' |}.

Definition isem_call_body {E} `{ErrEvent -< E}
   (rec_call : funname -> fstate -> itree E fstate)
   (fn : funname) (fs:fstate) : itree E fstate :=
  (* FIXME: this is durty : sinit*)
  let sinit := estate0 fs in
  fd <- iget_fundef fn sinit;;
  s1 <- iresult sinit (initialize_call fd fs);;
  s2 <- isem_map (isem_i_body rec_call) fd.(f_body) s1;;
  iresult s2 (finalize_call fd s2).

Notation it_rec_call := (trigger_inl1). 

Notation CALL := (callE (funname * fstate) fstate).

Definition isem_fcallY {E}
    (fn: funname) (fc: fstate) : itree (CALL +' E) fstate :=
  trigger (Call (fn, fc)).

Definition isem_call_bodyY {E} `{ErrEvent -< E}                        
   (fn : funname) (fs:fstate) : itree (CALL +' E) fstate :=
  (* FIXME: this is durty : sinit*)
  let sinit := estate0 fs in
  fd <- iget_fundef fn sinit;;
  s1 <- iresult sinit (initialize_call fd fs);;
  s2 <- isem_map (isem_i_body isem_fcallY) fd.(f_body) s1;;
  iresult s2 (finalize_call fd s2).

Definition isem_callY {E} `{ErrEvent -< E}
  (fn : funname) (fs : fstate) :
  itree E fstate :=
  rec (fun x => isem_call_bodyY (fst x) (snd x)) (fn, fs).

Definition isem_i {E} `{ErrEvent -< E} (i : instr) (s : estate) :
  itree E estate :=
  isem_i_body isem_callY i s.

Definition isem_cmd {E} `{ErrEvent -< E} (c : cmd) (s : estate) :
  itree E estate :=
  isem_map isem_i c s.

Definition sem_call (fn : funname) (fs : fstate) :
  execT (itree void1) (fstate) :=
  interp_Err (isem_callY fn fs).


Lemma interp_isem_cmd {E} `{ErrEvent -< E} c s :
  eutt (E:=E) eq (interp (mrecursive it_rec_call) (isem_map (isem_i_body isem_fcallY) c s))
    (isem_map (isem_i_body isem_callY) c s).

  
(********************************************************************************************)
  
(* callE (funname * fstate) fstate : Type -> Type :=
   | Call : (funname * fstate) -> callE (funname * fstate) fstate fstate.
*)
Variant recCall : Type -> Type :=
 | RecCall (f:funname) (fs:fstate) : recCall fstate.

(* Make global definition *)

Definition rec_call {E} (f:funname) (fs:fstate) : itree (recCall +' E) fstate :=
 trigger_inl1 (RecCall f fs).

Definition isem_i_rec {E} `{ErrEvent -< E} (i : instr) (s1: estate) : itree (recCall +' E) estate :=
  isem_i_body rec_call i s1.

Definition isem_call_rec {E} `{ErrEvent -< E}
   (fn : funname) (fs:fstate) : itree (recCall +' E) fstate :=
  isem_call_body rec_call fn fs.

Definition interp_recCall {E} `{ErrEvent -< E} : recCall ~> itree (recCall +' E) :=
 fun T (rc : recCall T) =>
   match rc with
   | RecCall fn fs => isem_call_rec fn fs
   end.

Definition isem_call {E} `{ErrEvent -< E} (fn : funname) (fs : fstate) : itree E fstate :=
  mrec interp_recCall (RecCall fn fs).

Definition isem_i {E} `{ErrEvent -< E} (i : instr) (s : estate) : itree E estate :=
  isem_i_body isem_call i s.

Definition isem_cmd {E} `{ErrEvent -< E} (c : cmd) (s : estate) : itree E estate :=
  isem_map isem_i c s.

Definition sem_call (fn : funname) (fs : fstate) : execT (itree void1) (fstate) :=
  interp_Err (isem_call fn fs).

(* Core lemmas about the definition *)

Lemma interp_ioget {E : Type -> Type} `{ErrEvent -< E} Err T (o : option T) :
  eutt (E:=E) eq (interp (mrecursive interp_recCall) (ioget Err o)) (ioget Err o).
Proof.
  case o => /=.
  + move=> ?; rewrite interp_ret; reflexivity.
  rewrite interp_vis bind_trigger.
  by apply eqit_Vis => -[].
Qed.

Lemma interp_iresult {E : Type -> Type} `{ErrEvent -< E} s T (r : exec T) :
  eutt (E:=E) eq (interp (mrecursive interp_recCall) (iresult s r)) (iresult s r).
Proof.
  case r => /=.
  + move=> ?; rewrite interp_ret; reflexivity.
  move=> e; rewrite interp_vis bind_trigger.
  by apply eqit_Vis => -[].
Qed.

Lemma interp_isem_cmd {E} `{ErrEvent -< E} c s :
  eutt (E:=E) eq (interp (mrecursive interp_recCall) (isem_map (isem_i_body rec_call) c s))
    (isem_map (isem_i_body isem_call) c s).
Proof.
  apply: (cmd_rect
    (Pr := fun ir => forall ii s,
       eutt (E:=E) eq (interp (mrecursive interp_recCall) (isem_i_rec (MkI ii ir) s))
                      (isem_i (MkI ii ir) s))
    (Pi := fun i => forall s,
       eutt (E:=E) eq (interp (mrecursive interp_recCall) (isem_i_rec i s))
                      (isem_i i s))
    (Pc := fun c => forall s,
       eutt (E:=E) eq (interp (mrecursive interp_recCall) (isem_map isem_i_rec c s))
                      (isem_cmd c s))) c s => //=.
  + move=> s; rewrite interp_ret; reflexivity.
  + move=> i c hi hc s; rewrite interp_bind;apply eqit_bind; first by apply hi.
    by move=> s'; apply hc.
  + by move=> >; apply interp_iresult.
  + by move=> >; apply interp_iresult.
  + by move=> >; apply interp_iresult.
  + move=> e c1 c2 hc1 hc2 ii s; rewrite /isem_i /isem_i_rec /=.
    rewrite interp_bind; apply eqit_bind.
    + by apply interp_iresult.
    by move=> []; [apply hc1 | apply hc2].
  + move=> v dir lo hi c hc ii s; rewrite /isem_i /isem_i_rec /=.
    rewrite interp_bind; apply eqit_bind; first by apply interp_iresult.
    move=> vlo.
    rewrite interp_bind; apply eqit_bind; first by apply interp_iresult.
    move=> vhi; elim: wrange s => {vlo vhi ii} //=.
    + move=> >; rewrite interp_ret; reflexivity.
    move=> j js hrec s.
    rewrite interp_bind; apply eqit_bind; first by apply interp_iresult.
    move=> s'; rewrite interp_bind.
    rewrite hc; setoid_rewrite hrec; reflexivity.
  + move=> al c1 e c2 hc1 hc2 ii s; rewrite /isem_i /isem_i_rec /= /isem_while.
    rewrite interp_iter; apply eutt_iter => {}s.
    rewrite /isem_while_body.
    rewrite interp_bind; apply eqit_bind; first by apply hc1.
    move=> s1; rewrite interp_bind; apply eqit_bind; first by apply interp_iresult.
    move=> [].
    + rewrite interp_bind; apply eqit_bind; first by apply hc2.
      move=> s2; rewrite interp_ret; reflexivity.
    rewrite interp_ret; reflexivity.
  move=> xs f es ii s; rewrite /isem_i /isem_i_rec /=.
  rewrite interp_bind; apply eqit_bind; first by apply interp_iresult.
  move=> vs.
  rewrite interp_bind; apply eqit_bind; last by move=> >; apply interp_iresult.
  rewrite interp_mrecursive; reflexivity.
Qed.

Lemma isem_call_unfold {E} `{ErrEvent -< E} (fn : funname) (fs : fstate) :
  isem_call (E:=E) fn fs ≈ isem_call_body isem_call fn fs.
Proof.
  rewrite {1}/isem_call.
  rewrite mrec_as_interp.
  rewrite {2}/interp_recCall /isem_call_rec /isem_call_body.
  rewrite interp_bind; apply eqit_bind.
  + by apply interp_ioget.
  move=> fd; rewrite interp_bind; apply eqit_bind.
  + by apply interp_iresult.
  move=> s1; rewrite interp_bind; apply eqit_bind.
  + apply interp_isem_cmd.
  move=> s2; apply interp_iresult.
Qed.

End WSW.


