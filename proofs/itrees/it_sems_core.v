
From Jasmin Require Import oseq.
(* problematic *)
From Jasmin Require Import expr.
From Jasmin Require Import it_jasmin_lib.

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
From Jasmin Require Import it_gen_lib it_jasmin_lib.
From Jasmin Require Import compiler_util.
(* problematic *)
From Jasmin Require Import it_exec_mono.

Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.
Local Open Scope option_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Set Universe Polymorphism. *)

Obligation Tactic := done || idtac.

(* This files contains semantic models distinguished by use of either
mutual or double recursion, and by either modular, error-aware or flat
structure. There are fives models (MM: mutual modular; ME: mutual
error; MF: mutual flat; DE: double error; DF double flat) *)

(**** ERROR SEMANTICS *******************************************)
Section Errors.
  
(* type of errors (this might becom richer) *)
  (* Variant ErrType : Type := Err : ErrType. *)
Notation ErrType1 := (error).
Notation ErrType2 := (option pp_error_loc).
Notation Err := (ErrType).

(* error events *)
Definition ErrState : Type -> Type := exceptE ErrType1.
Definition CErrState : Type -> Type := exceptE ErrType2.

(* failT (itree E) R = itree E (option R) *)
Definition handle_Err {E} : ErrState ~> failT (itree E) :=
  fun _ _ => Ret (None).

(* Err handler *)
Definition ext_handle_Err {E: Type -> Type} :
  ErrState +' E ~> failT (itree E) :=
  fun _ e =>
  match e with
  | inl1 e' => handle_Err e'
  | inr1 e' => Vis e' (pure (fun x => Some x)) end.                        

(* ErrState interpreter *)
Definition interp_Err {E: Type -> Type} {A}  
  (t: itree (ErrState +' E) A) : failT (itree E) A :=
  interp_fail ext_handle_Err t.


(*** auxiliary error functions *)

Definition err_get {E: Type -> Type} `{ErrState -< E} {S} {V}
  (f: S -> option V) : stateT S (itree E) V :=
  fun st => match (f st) with
            | Some v => Ret (st, v)
            | None => throw Err end.                

Definition err_put {E: Type -> Type} `{ErrState -< E} {S}
  (f: S -> option S) : stateT S (itree E) unit :=
  fun st => match (f st) with
            | Some st' => Ret (st', tt)
            | None => throw Err end.                

Definition err_write {E: Type -> Type} `{ErrState -< E} {S}
  (ms: option S) : stateT S (itree E) unit :=
  fun st => match ms with
            | Some st' => Ret (st', tt)
            | None => throw Err end.                

Definition err_opt {E: Type -> Type} `{ErrState -< E} :
  option ~> itree E :=
  fun _ t => match t with
             | Some v => Ret v
             | None => throw Err end.                

Definition err_st_opt {E: Type -> Type} `{ErrState -< E} {S} :
  option ~> stateT S (itree E) :=
  fun _ t st => match t with
                | Some v => Ret (st, v)
                | None => throw Err end.                

Definition err_result {E: Type -> Type} `{ErrState -< E} T :
  result T ~> itree E :=
  fun _ t => match t with
             | Ok v => Ret v
             | Error _ => throw Err end.                

End Errors.


(*********************************************************************)
(*** LANGUAGE DEFINITIONS *********************************************)
(* we are exploring more alternatives *)
Section Lang.
Context (asm_op: Type) (asmop: asmOp asm_op).

(* reader events *)
Variant FunE : Type -> Type :=
  | FunCode (fn : funname) : FunE cmd.                               


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

Definition FunDef : Type := _fundef extra_fun_t.

Definition get_FunDef (fn: funname) : option FunDef :=
  get_fundef (p_funcs pr) fn.

Definition funCode (f: FunDef) : cmd := 
  @f_body asm_op asmop extra_fun_t f.

Definition get_FunCode (fn: funname) : option cmd := 
  opt_lift (@f_body asm_op asmop extra_fun_t) (get_FunDef fn).

Definition get_FunDests (fn: funname) : option lvals :=
  get_FunDef fn >>o= fun f => Some (map Lvar (f.(f_res))). 

Definition handle_FunE {E: Type -> Type}
  `{ErrState -< E} : FunE ~> itree E :=
  fun _ e =>
    match e with
    | FunCode fn => err_opt (get_FunCode fn) end.   

Definition ext_handle_FunE {E: Type -> Type} `{ErrState -< E} :
  FunE +' E ~> itree E :=
  case_ handle_FunE (id_ E).

(* FunE interpreter *)
Definition interp_FunE {E: Type -> Type} {X: ErrState -< E}
  {A: Type}
  (t : itree (FunE +' E) A) : itree E A :=
  interp ext_handle_FunE t.


(***** INSTR AUX FUNCTIONS *******************************************)

(** Ccall *)

Definition ret_get_FunDef {E: Type -> Type} 
  (fn: funname) : execT (itree E) FunDef :=
  Ret (o2r ErrType (get_FunDef fn)).           

Definition err_get_FunDef {E} `{ErrState -< E}
  (fn: funname) : itree E FunDef :=
  err_opt (get_FunDef fn).           


Definition ret_get_FunCode {E: Type -> Type}
  (fn: funname) : execT (itree E) cmd :=
  f <- ret_get_FunDef fn ;;
  Ret (ok (funCode f)).

Definition err_get_FunCode {E} `{ErrState -< E}
  (fn: funname) : itree E cmd :=
  f <- err_get_FunDef fn ;;
  Ret (funCode f).

Definition pure_eval_Args (args: pexprs) (st: estate) :
  exec (seq value) := 
  sem_pexprs (~~direct_call) (p_globs pr) st args.

Definition truncate_Args (f: FunDef) (vargs: seq value) :
  exec (seq value) :=
  mapM2 ErrType dc_truncate_val f.(f_tyin) vargs.

Definition err_eval_Args {E} `{ErrState -< E}
  (fn: funname) (args: pexprs) (st0: estate) : itree E (seq value) :=
  f <- err_get_FunDef fn ;;
  vargs' <- err_result (pure_eval_Args args st0) ;;
  err_result (truncate_Args f vargs').
  
Definition err_init_state {E} `{ErrState -< E}
   (fn: funname) (vargs: seq value) (st0: estate) : itree E estate :=   
  let scs1 := st0.(escs) in
  let m1 := st0.(emem) in
  f <- err_get_FunDef fn ;;
  st1 <- err_result 
       (init_state f.(f_extra) (p_extra pr) ev (Estate scs1 m1 Vm.init)) ;;
  err_result 
      (write_vars (~~direct_call) (f_params f) vargs st1).

Definition err_return_val {E} `{ErrState -< E}
  (fn: funname) (st0: estate) : itree E (seq value) :=
  f <- err_get_FunDef fn ;;
  vres <- err_result 
      (get_var_is (~~ direct_call) st0.(evm) f.(f_res)) ;;
  err_result 
      (mapM2 ErrType dc_truncate_val f.(f_tyout) vres).

Definition err_reinstate_caller {E} `{ErrState -< E}
  (fn: funname) (xs: lvals) (vres: seq value)
  (st_ee st_er: estate) : itree E estate :=
  f <- err_get_FunDef fn ;;
  let scs2 := st_ee.(escs) in
  let m2 := finalize f.(f_extra) st_ee.(emem) in      
  err_result 
         (write_lvals (~~direct_call) (p_globs pr)
                      (with_scs (with_mem st_er m2) scs2) xs vres).

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

(** WriteIndex *)
Definition ret_mk_WriteIndex {E} 
  (x: var_i) (z: Z) (st1: estate) : execT (itree E) estate :=  
    Ret (write_var true x (Vint z) st1).                             

Definition err_mk_WriteIndex {E} `{ErrState -< E}
  (x: var_i) (z: Z) (st1: estate) : itree E estate :=  
    err_result (write_var true x (Vint z) st1).                             

(** EvalCond *)
Definition ret_mk_EvalCond {E} 
  (e: pexpr) (st1: estate) : execT (itree E) bool :=
   let vv := sem_pexpr true (p_globs pr) st1 e in                               
   match vv with
   | Ok (Vbool bb) => ret (ok bb)
   | _ => ret (Error ErrType) end.                       

Definition err_mk_EvalCond {E} `{ErrState -< E}
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

Definition err_mk_EvalBound {E} `{ErrState -< E}
  (e: pexpr) (st1: estate) : itree E Z :=
   let vv := sem_pexpr true (p_globs pr) st1 e in                               
   match vv with
   | Ok (Vint zz) => ret zz
   | _ => throw ErrType end.                       


(** AssgnE *)
(* terminating *)
Definition ret_mk_AssgnE {E: Type -> Type} 
  (x: lval) (tg: assgn_tag) (ty: stype) (e: pexpr) 
  (st1: estate) : execT (itree E) estate := Ret
   (Let v := sem_pexpr true (p_globs pr) st1 e in 
    Let v' := truncate_val ty v in
    write_lval true (p_globs pr) x v' st1).

Definition err_mk_AssgnE {E: Type -> Type} `{ErrState -< E}
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

Definition err_mk_OpnE {E: Type -> Type} `{ErrState -< E}
  (xs: lvals) (tg: assgn_tag) (o: sopn)
   (es : pexprs) (st1: estate) : itree E estate :=
    err_result (sem_sopn (p_globs pr) o st1 xs es).


(** SyscallE *)
(* terminating *)
Definition ret_mk_SyscallE {E: Type -> Type}
  (xs: lvals) (o: syscall_t)
  (es: pexprs) (st1: estate) : execT (itree E) estate := Ret 
   (Let ves := sem_pexprs true (p_globs pr) st1 es in 
    Let r3 := exec_syscall st1.(escs) st1.(emem) o ves in 
    match r3 with
    | (scs, m, vs) =>
        write_lvals true (p_globs pr)
                    (with_scs (with_mem st1 m) scs) xs vs end).

Definition err_mk_SyscallE {E: Type -> Type} `{ErrState -< E}
  (xs: lvals) (o: syscall_t) (es: pexprs) (st1: estate) :
  itree E estate :=
    ves <- err_result (sem_pexprs true (p_globs pr) st1 es ) ;;
    r3 <- err_result (exec_syscall st1.(escs) st1.(emem) o ves) ;;
    match r3 with
    | (scs, m, vs) =>
        err_result (write_lvals true (p_globs pr)
                       (with_scs (with_mem st1 m) scs) xs vs) end.


(*** INTERPRETERS WITH ERROR (quasi-flat) ******************************)
Section ErrorAwareSem.

(** Auxiliary functions for recursion on list (seq) *)

Fixpoint st_cmd_map_r {E} (R: instr_r -> estate -> itree E estate)
  (c: cmd) (st: estate) : itree E estate := 
  match c with 
  | nil => Ret st 
  | (MkI _ i) :: c' => st' <- R i st ;; st_cmd_map_r R c' st'
  end.

Fixpoint eval_for {E} `{ErrState -< E}
  (R: cmd -> estate -> itree E estate)                
  (i: var_i) (c: cmd)
  (ls: list Z) (st: estate) : itree E estate :=
    match ls with
    | nil => fun st' => ret st'
    | (w :: ws) => fun st' =>
                     st1 <- err_mk_WriteIndex i w st' ;;
                     st2 <- R c st1 ;;
                     eval_for R i c ws st2
    end st.


(**********************************************************************)
(** error-aware interpreter with mutual recursion *)
Section With_MREC_error.

(* mutual recursion events *)
Variant FCState : Type -> Type :=
 | FLCode (c: cmd) (st: estate) : FCState estate
 | FFCall (xs: lvals) (f: funname) (es: pexprs) (st: estate) : FCState estate.
  
Local Notation continue_loop st := (ret (inl st)).
Local Notation exit_loop st := (ret (inr st)).
Local Notation rec_call := (trigger_inl1). 

Fixpoint meval_instr {E} `{ErrState -< E} (i : instr_r) (st: estate) :
  itree (FCState +' E) estate := 
  let R := st_cmd_map_r meval_instr in
  match i with
  | Cassgn x tg ty e => err_mk_AssgnE x tg ty e st
  | Copn xs tg o es => err_mk_OpnE xs tg o es st
  | Csyscall xs o es => err_mk_SyscallE xs o es st                          
                                        
  | Cif e c1 c2 =>
      b <- err_mk_EvalCond e st ;;
      if b then R c1 st else R c2 st 
                            
  | Cfor i (d, lo, hi) c => 
          vlo <- err_mk_EvalBound lo st ;;
          vhi <- err_mk_EvalBound hi st ;;
          eval_for R i c (wrange d vlo vhi) st

  | Cwhile a c1 e c2 => 
      ITree.iter (fun st0 =>
           st1 <- R c1 st0 ;;          
           b <- err_mk_EvalCond e st1 ;;
           if b then st2 <- R c2 st1 ;; continue_loop st2
           else exit_loop st1) st
  
  | Ccall xs fn es => rec_call (FFCall xs fn es st)      
  end.

Definition meval_fcall {E} `{ErrState -< E}
  (xs: lvals) (fn: funname) (es: pexprs) (st0: estate) :
  itree (FCState +' E) estate :=
  va <- err_eval_Args fn es st0 ;;
  st1 <- err_init_state fn va st0 ;;
  c <- err_get_FunCode fn ;;
  st2 <- rec_call (FLCode c st1) ;;
  vs <- err_return_val fn st2 ;;
  err_reinstate_caller fn xs vs st2 st0.

Definition meval_cstate {E} `{ErrState -< E} :
  FCState ~> itree (FCState +' E) :=           
  fun _ fs => match fs with
              | FLCode c st => st_cmd_map_r meval_instr c st
              | FFCall xs fn es st => meval_fcall xs fn es st      
              end.      

Definition mevalE_cmd {E} `{ErrState -< E} (c: cmd) (st: estate) :
  itree E estate :=
  mrec meval_cstate (FLCode c st).

Definition meval_cmd {E} (c: cmd) (st: estate) : itree E (option estate) := 
  @interp_Err E estate (mevalE_cmd c st).

Definition mevalE_fun {E} `{ErrState -< E} :
  (funname * (values * estate)) -> 
  itree E (values * estate) :=
  fun fvst =>
    let '(fn, (va, st)) := fvst in
    st1 <- err_init_state fn va st ;;
    c <- err_get_FunCode fn ;;
    st2 <- mevalE_cmd c st1 ;;
    vs <- err_return_val fn st2 ;;
    ret (vs, st2).

Definition meval_fun_ {E} `{ErrState -< E}
  (fn: funname) (va: values) (st0: estate) :
  itree (FCState +' E) (values * estate) :=
  st1 <- err_init_state fn va st0 ;;
  c <- err_get_FunCode fn ;;
  st2 <- rec_call (FLCode c st1) ;;
  vs <- err_return_val fn st2 ;;
  ret (vs, st2).

End With_MREC_error.

End ErrorAwareSem.

End OneProg.

End WSW.

End Lang.

