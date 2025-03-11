
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
(* FIXME: change this name *)
Definition ioget {E: Type -> Type} `{ErrEvent -< E} {V} (err: error_data) (o: option V) : itree E V :=
  match o with
  | Some v => Ret v
  | None => throw err
  end.

(*
Definition err_put {E: Type -> Type} `{ErrEvent -< E} {S}
  (f: S -> option S) : stateT S (itree E) unit :=
  fun st => match (f st) with
            | Some st' => Ret (st', tt)
            | None => throw Err end.

Definition err_write {E: Type -> Type} `{ErrEvent -< E} {S}
  (ms: option S) : stateT S (itree E) unit :=
  fun st => match ms with
            | Some st' => Ret (st', tt)
            | None => throw Err end.
*)
(*
Definition err_opt {E: Type -> Type} `{ErrEvent -< E} :
  option ~> itree E :=
  fun _ t => match t with
             | Some v => Ret v
             | None => throw Err end.

Definition err_st_opt {E: Type -> Type} `{ErrEvent -< E} {S} :
  option ~> stateT S (itree E) :=
  fun _ t st => match t with
                | Some v => Ret (st, v)
                | None => throw Err end.
*)
Definition err_result {E: Type -> Type} `{ErrEvent -< E} (Err : error -> error_data) :
  result error ~> itree E :=
  fun _ t => match t with
             | Ok v => Ret v
             | Error e => throw (Err e) end.

End Errors.


(*********************************************************************)
(*** LANGUAGE DEFINITIONS *********************************************)
(* we are exploring more alternatives *)
Section Lang.
Context (asm_op: Type) (asmop: asmOp asm_op).


(**********************************************************************)
(********** EVENT SEMANTICS ******************************************)

Section WSW.
Context {wsw: WithSubWord}.
Context
  (dc: DirectCall)
  (syscall_state : Type)
  (ep : EstateParams syscall_state)
  (spp : SemPexprParams)
  (sip : SemInstrParams asm_op syscall_state)
  (pT : progT)
  (scP : semCallParams)
  (ev : extra_val_t).

Section OneProg.
Context (pr : prog).


(***** FUN-READER SEMANTICS ******************************************)
(* Section ModularSem. *)

(*
Definition get_FunCode (fn: funname) : option cmd :=
  opt_lift (@f_body asm_op asmop extra_fun_t) (get_FunDef fn).

Definition get_FunDests (fn: funname) : option lvals :=
  get_FunDef fn >>o= fun f => Some (map Lvar (f.(f_res))).
*)

(***** INSTR AUX FUNCTIONS *******************************************)

(** Ccall *)
(*
Definition ret_get_FunDef {E: Type -> Type}
  (fn: funname) : execT (itree E) FunDef :=
  Ret (o2r ErrType (get_FunDef fn)).
*)

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






(*Definition ret_get_FunCode {E: Type -> Type}
  (fn: funname) : execT (itree E) cmd :=
  f <- ret_get_FunDef fn ;;
  Ret (ok (funCode f)).

Definition err_get_FunCode {E} `{ErrEvent -< E}
  (fn: funname) : itree E cmd :=
  f <- err_get_FunDef fn ;;
  Ret (funCode f).
*)
(*
Definition pure_eval_Args (args: pexprs) (st: estate) :
  exec (seq value) :=
  sem_pexprs (~~direct_call) (p_globs pr) st args.

Definition truncate_Args (f: FunDef) (vargs: seq value) :
  exec (seq value) :=
  mapM2 ErrType dc_truncate_val f.(f_tyin) vargs.
*)

(*
Definition err_eval_Args {E} `{ErrEvent -< E}
  (fn: funname) (args: pexprs) (st0: estate) : itree E (seq value) :=
  f <- err_get_FunDef fn ;;
  vargs' <- err_result (pure_eval_Args args st0) ;;
  err_result (truncate_Args f vargs').

Definition err_init_state {E} `{ErrEvent -< E}
   (fn: funname) (vargs: seq value) (st0: estate) : itree E estate :=
  let scs1 := st0.(escs) in
  let m1 := st0.(emem) in
  f <- err_get_FunDef fn ;;
  st1 <- err_result
       (init_state f.(f_extra) (p_extra pr) ev (Estate scs1 m1 Vm.init)) ;;
  err_result
      (write_vars (~~direct_call) (f_params f) vargs st1).

Definition err_return_val {E} `{ErrEvent -< E}
  (fn: funname) (st0: estate) : itree E (seq value) :=
  f <- err_get_FunDef fn ;;
  vres <- err_result
      (get_var_is (~~ direct_call) st0.(evm) f.(f_res)) ;;
  err_result
      (mapM2 ErrType dc_truncate_val f.(f_tyout) vres).

Definition err_reinstate_caller {E} `{ErrEvent -< E}
  (fn: funname) (xs: lvals) (vres: seq value)
  (st_ee st_er: estate) : itree E estate :=
  f <- err_get_FunDef fn ;;
  let scs2 := st_ee.(escs) in
  let m2 := finalize f.(f_extra) st_ee.(emem) in
  err_result
         (write_lvals (~~direct_call) (p_globs pr)
                      (with_scs (with_mem st_er m2) scs2) xs vres).
*)
(*
Definition ret_eval_Args {E: Type -> Type}
  (fn: funname) (args: pexprs) (st0: estate) : execT (itree E) (seq value) :=
  f <- ret_get_FunDef fn ;;
  Ret (Let vargs' := pure_eval_Args args st0 in truncate_Args f vargs').

Definition ret_init_state {E: Type -> Type}
   (fn: funname) (vargs: seq value) (st0: estate) : execT (itree E) estate :=
  let scs1 := st0.(escs) in
  let m1 := st0.(emem) in
  f <- ret_get_FunDef fn ;;
  Ret
  (Let st1 := init_state f.(f_extra) (p_extra pr) ev (Estate scs1 m1 Vm.init) in
   write_vars (~~direct_call) (f_params f) vargs st1).

Definition ret_return_val {E: Type -> Type}
  (fn: funname) (st0: estate) : execT (itree E) (seq value) :=
  f <- ret_get_FunDef fn ;;
  Ret
  (Let vres := get_var_is (~~ direct_call) st0.(evm) f.(f_res) in
   mapM2 ErrType dc_truncate_val f.(f_tyout) vres).

Definition ret_reinstate_caller {E: Type -> Type}
  (fn: funname) (xs: lvals) (vres: seq value)
  (st_ee st_er: estate) : execT (itree E) estate :=
  f <- ret_get_FunDef fn ;;
  let scs2 := st_ee.(escs) in
  let m2 := finalize f.(f_extra) st_ee.(emem) in
  Ret (write_lvals (~~direct_call) (p_globs pr)
                      (with_scs (with_mem st_er m2) scs2) xs vres).
*)
(** WriteIndex *)
(*
Definition ret_mk_WriteIndex {E}
  (x: var_i) (z: Z) (st1: estate) : execT (itree E) estate :=
    Ret (write_var true x (Vint z) st1).
*)
(*
Definition err_mk_WriteIndex {E} `{ErrEvent -< E}
  (x: var_i) (z: Z) (st1: estate) : itree E estate :=
    err_result (write_var true x (Vint z) st1).

(** EvalCond *)
Definition ret_mk_EvalCond {E}
  (e: pexpr) (st1: estate) : execT (itree E) bool :=
   let vv := sem_pexpr true (p_globs pr) st1 e in
   match vv with
   | Ok (Vbool bb) => ret (ok bb)
   | _ => ret (Error ErrType) end.

Definition err_mk_EvalCond {E} `{ErrEvent -< E}
  (e: pexpr) (st1: estate) : itree E bool :=
   let vv := sem_pexpr true (p_globs pr) st1 e in
   match vv with
   | Ok (Vbool bb) => ret bb
   | _ => throw ErrType end.


(** EvalBound *)
Definition ret_mk_EvalBound {E}
  (e: pexpr) (st1: estate) : execT (itree E) Z :=
   let vv := sem_pexpr true (p_globs pr) st1 e in
   match vv with
   | Ok (Vint zz) => ret (ok zz)
   | _ => ret (Error ErrType) end.

Definition err_mk_EvalBound {E} `{ErrEvent -< E}
  (e: pexpr) (st1: estate) : itree E Z :=
   let vv := sem_pexpr true (p_globs pr) st1 e in
   match vv with
   | Ok (Vint zz) => ret zz
   | _ => throw ErrType end.

*)

(** AssgnE *)
(* terminating *)

Definition eval_assgn
  (x: lval) (tg: assgn_tag) (ty: stype) (e: pexpr)
  (st1: estate) : exec estate :=
   (Let v := sem_pexpr true (p_globs pr) st1 e in
    Let v' := truncate_val ty v in
    write_lval true (p_globs pr) x v' st1).
(*
Definition ieval_assgn {E} `{ErrEvent -< E}
 (x: lval) (tg: assgn_tag) (ty: stype) (e: pexpr)
  (s: estate) : itree E estate :=
  iresult s (eval_assgn x tg ty e s).
*)
(*
Definition err_mk_AssgnE {E: Type -> Type} `{ErrEvent -< E}
  (x: lval) (tg: assgn_tag) (ty: stype) (e: pexpr)
  (st1: estate) : itree E estate :=
    v <- err_result (sem_pexpr true (p_globs pr) st1 e) ;;
    v' <- err_result (truncate_val ty v) ;;
    err_result (write_lval true (p_globs pr) x v' st1).


(** OpnE *)
(* terminating *)
Definition ret_mk_OpnE {E: Type -> Type}
  (xs: lvals) (tg: assgn_tag) (o: sopn)
  (es : pexprs) (st1: estate) : execT (itree E) estate := Ret
    (sem_sopn (p_globs pr) o st1 xs es).

Definition err_mk_OpnE {E: Type -> Type} `{ErrEvent -< E}
  (xs: lvals) (tg: assgn_tag) (o: sopn)
   (es : pexprs) (st1: estate) : itree E estate :=
    err_result (sem_sopn (p_globs pr) o st1 xs es).


(** SyscallE *)
(* terminating *)
*)

Definition eval_syscall
   (xs: lvals) (o: syscall_t)
   (es: pexprs) (s: estate) : exec estate :=
  Let ves := sem_pexprs true (p_globs pr) s es in
  Let: (scs, m, vs) := exec_syscall s.(escs) s.(emem) o ves in
  write_lvals true (p_globs pr)
     (with_scs (with_mem s m) scs) xs vs.

(*
Definition ieval_syscall {E} `{ErrEvent -< E}
   (xs: lvals) (o: syscall_t)
   (es: pexprs) (s: estate) : exec estate
  iresult (eval_syscall
*)
(*
Definition err_mk_SyscallE {E: Type -> Type} `{ErrEvent -< E}
  (xs: lvals) (o: syscall_t) (es: pexprs) (st1: estate) :
  itree E estate :=
    ves <- err_result (sem_pexprs true (p_globs pr) st1 es ) ;;
    r3 <- err_result (exec_syscall st1.(escs) st1.(emem) o ves) ;;
    match r3 with
    | (scs, m, vs) =>
        err_result (write_lvals true (p_globs pr)
                       (with_scs (with_mem st1 m) scs) xs vs) end.
*)

(*** INTERPRETERS WITH ERROR (quasi-flat) ******************************)
Section ErrorAwareSem.

(** Auxiliary functions for recursion on list (seq) *)

Fixpoint sem_cmd_ {E} (sem_i: instr_r -> estate -> itree E estate)
   (c: cmd) (st: estate) : itree E estate :=
  match c with
  | nil => Ret st
  | (MkI _ i) :: c' => st' <- sem_i i st ;; sem_cmd_ sem_i c' st'
  end.

Fixpoint sem_for {E} `{ErrEvent -< E}
   (sem_cmd : cmd -> estate -> itree E estate)
   (i: var_i) (c: cmd)
   (ls: list Z) (s: estate) : itree E estate :=
  match ls with
  | nil => ret s
  | (w :: ws) =>
    s <- iwrite_var true i (Vint w) s;;
    s <- sem_cmd c s;;
    sem_for sem_cmd i c ws s
  end.

(**********************************************************************)
(** error-aware interpreter with mutual recursion *)
Section With_MREC_error.

(* mutual recursion events *)
(* FIXME : should we find a better name ? *)
Variant FCState : Type -> Type :=
 | FLCode (c: cmd) (st: estate) : FCState estate
 | FFCall (scs : syscall_state_t) (m:mem)
          (f: funname) (vs:values) : FCState (syscall_state_t * mem * values).

Local Notation continue_loop st := (ret (inl st)).
Local Notation exit_loop st := (ret (inr st)).
Local Notation rec_call := (trigger_inl1).

Local Notation gd := (p_globs pr).

Definition sem_cond {E} `{ErrEvent -< E} (e:pexpr) (s: estate) :
   itree E bool :=
  iresult s (sem_pexpr true gd s e >>r= to_bool).

Definition sem_bound {E} `{ErrEvent -< E} (e:pexpr) (s: estate) :
   itree E Z :=
  iresult s (sem_pexpr true gd s e >>r= to_int).

Definition msem_i {E} `{ErrEvent -< E} (i : instr_r) (s1: estate) : itree (FCState +' E) estate :=
(*  let R := st_cmd_map_r meval_instr in *)
  let R := (fun c s => rec_call (FLCode c s)) in
  match i with
  | Cassgn x tg ty e => iresult s1 (eval_assgn x tg ty e s1)
  | Copn xs tg o es => iresult s1 (sem_sopn gd o s1 xs es)
  | Csyscall xs o es => iresult s1 (eval_syscall xs o es s1)
  | Cif e c1 c2 =>
      b <- sem_cond e s1;;
      if b then R c1 s1 else R c2 s1
  | Cwhile a c1 e c2 =>
      ITree.iter (fun s1 =>
           s2 <- R c1 s1 ;;
           b <- sem_cond e s2 ;;
           if b then s3 <- R c2 s2 ;; continue_loop s3
           else exit_loop s2) s1
  | Cfor i (d, lo, hi) c =>
     vlo <- sem_bound lo s1 ;;
     vhi <- sem_bound hi s1 ;;
     sem_for R i c (wrange d vlo vhi) s1

  | Ccall xs fn args =>
      vargs <- isem_pexprs  (~~direct_call) gd s1 args;;
      res <- rec_call (FFCall (escs s1) (emem s1) fn vargs);;
      let: (scs2, m2, vs) := res in
      iwrite_lvals (~~direct_call) gd (with_scs (with_mem s1 m2) scs2) xs vs
end.

Definition msem_I {E} `{ErrEvent -< E} (i : instr) (s1: estate) : itree (FCState +' E) estate :=
  let: MkI ii i := i in msem_i i s1.

Definition msem_call {E} `{ErrEvent -< E}
   (scs1 : syscall_state_t) (m1 : mem)
   (fn : funname) (vargs' : values) : itree (FCState +' E) (syscall_state_t * mem * values) :=
  let sinit := (Estate scs1 m1 Vm.init) in
  f <- iget_fundef fn sinit;;
  vargs <- iresult sinit (mapM2 ErrType dc_truncate_val f.(f_tyin) vargs');;
  s0 <- iresult sinit (init_state f.(f_extra) (p_extra pr) ev sinit);;
  s1 <- iresult s0 (write_vars (~~direct_call) f.(f_params) vargs s0);;
  s2 <- rec_call (FLCode f.(f_body) s1);;
  vres <- iresult s2 (get_var_is (~~ direct_call) s2.(evm) f.(f_res));;
  vres' <- iresult s2 (mapM2 ErrType dc_truncate_val f.(f_tyout) vres);;
  let scs2 := s2.(escs) in
  let m2 := finalize f.(f_extra) s2.(emem) in
  Ret (scs2, m2, vres).

Definition msem_fcstate {E} `{ErrEvent -< E} : FCState ~> itree (FCState +' E) :=
 fun _ fs =>
   match fs with
   | FLCode c st => sem_cmd_ msem_i c st
   | FFCall scs m fn vs => msem_call scs m fn vs
   end.

Definition msem_cmd {E} `{ErrEvent -< E} (c: cmd) (st: estate) :
  itree E estate :=
  mrec msem_fcstate (FLCode c st).

(*
Definition meval_cmd {E} (c: cmd) (st: estate) : itree E (option estate) :=
  @interp_Err E estate (mevalE_cmd c st).

Definition mevalE_fun {E} `{ErrEvent -< E} :
  (funname * (values * estate)) ->
  itree E (values * estate) :=
  fun fvst =>
    let '(fn, (va, st)) := fvst in
    st1 <- err_init_state fn va st ;;
    c <- err_get_FunCode fn ;;
    st2 <- mevalE_cmd c st1 ;;
    vs <- err_return_val fn st2 ;;
    ret (vs, st2).

Definition meval_fun_ {E} `{ErrEvent -< E}
  (fn: funname) (va: values) (st0: estate) :
  itree (FCState +' E) (values * estate) :=
  st1 <- err_init_state fn va st0 ;;
  c <- err_get_FunCode fn ;;
  st2 <- rec_call (FLCode c st1) ;;
  vs <- err_return_val fn st2 ;;
  ret (vs, st2).
*)

End With_MREC_error.

End ErrorAwareSem.

End OneProg.

End WSW.

End Lang.

