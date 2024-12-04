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
(*     Basics.Tacs *)
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

From Jasmin Require Import expr it_lib psem_defs psem oseq.

Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.
Local Open Scope option_scope.

Obligation Tactic := done || idtac.

Section ExecT.

  Context {m : Type -> Type} {Fm: Functor.Functor m} {Mm : Monad m}
    {MIm : MonadIter m}.

  Definition execT (m : Type -> Type) (a : Type) : Type :=
    m (exec a)%type.

  Global Instance execT_fun : Functor.Functor (execT m) :=
    {| Functor.fmap :=
        fun X Y (f: X -> Y) => 
          Functor.fmap (fun x =>
                          match x with
                          | Error e => Error e
                          | Ok x => @Ok error Y (f x) end) |}.

  Global Instance execT_monad : Monad (execT m) :=
    {| ret := fun _ x => ret (ok x);
       bind := fun _ _ c k =>
                 bind (m := m) c 
                   (fun x => match x with
                             | Error e => ret (Error e)
                             | Ok x => k x end)
    |}.

  Global Instance execT_iter  : MonadIter (execT m) :=
    fun A I body i => Basics.iter (M := m) (I := I) (R := exec A) 
      (fun i => bind (m := m)
               (body i)
               (fun x => match x with
                         | Error e       => ret (inr (Error e))
                         | Ok (inl j) => ret (inl j)
                         | Ok (inr a) => ret (inr (ok a))
                         end)) i.

End ExecT.


(**** ERROR SEMANTICS *******************************************)
Section Errors.
  
(* type of errors (this might becom richer) *)
  (* Variant ErrType : Type := Err : ErrType. *)
Notation ErrType1 := (error).
Notation Err := (ErrType).

(* error events *)
Definition ErrState : Type -> Type := exceptE ErrType1.

(* failT (itree E) R = itree E (option R) *)
Definition handle_Err {E} : ErrState ~> failT (itree E) :=
  fun _ _ => Ret (None).

(* Err handler *)
Definition ext_handle_Err {E: Type -> Type} :
  ErrState +' E ~> failT (itree E) :=
  fun _ e =>
  match e with
  | inl1 e' => handle_Err _ e'
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

(** Hgh-level events *)

(* reader events *)
Variant FunE : Type -> Type :=
  | FunCode (fn : funname) : FunE cmd.                               

(* state events *)
Variant InstrE : Type -> Type :=
  | AssgnE : lval -> assgn_tag -> stype -> pexpr -> InstrE unit
  | OpnE : lvals -> assgn_tag -> sopn -> pexprs -> InstrE unit
  | SyscallE : lvals -> syscall_t -> pexprs -> InstrE unit
(* for Cif and Cwhile *)    
  | EvalCond (e: pexpr) : InstrE bool
(* for Cfor *)                                 
  | EvalBound (e: pexpr) : InstrE Z
  | WriteIndex (x: var_i) (z: Z) : InstrE unit                             
(* evaluates the expressions es and copy the values to a newly
initialized callee state *)
  | InitState (fn: funname) (es: pexprs) : InstrE unit
(* discards the callee state after copying the results to the caller
state *)  
  | SetDests (fn: funname) (xs: lvals) : InstrE unit.  
  
(* mutual recursion events *)
Variant CState : Type -> Type :=
 | LCode (c: cmd) : CState unit
 | FCall (xs: lvals) (f: funname) (es: pexprs) : CState unit.


(** Auxiliary functions for recursion on list (seq) *)

Fixpoint cmd_map {E} (R: instr -> itree E unit)
  (c: cmd) : itree E unit := 
  match c with 
  | nil => Ret tt 
  | i :: c' => R i ;; cmd_map R c'
  end.

Fixpoint cmd_map_r {E} (R: instr_r -> itree E unit)
  (c: cmd) : itree E unit := 
  match c with 
  | nil => Ret tt 
  | (MkI _ i) :: c' => R i ;; cmd_map_r R c'
  end.

Fixpoint denote_for {E} `{InstrE -< E}
  (R: cmd -> itree E unit) (i: var_i) (c: cmd) (ls: list Z) :
  itree E unit :=
    match ls with
    | nil => ret tt
    | (w :: ws) => trigger (WriteIndex i w) ;; R c ;; denote_for R i c ws
    end.


(**********************************************************************)
(**********************************************************************)
(** denotational interpreter with mutual recursion *)
Section With_MREC_mod.
Context (Eff : Type -> Type)
        (HasFunE : FunE -< Eff) 
        (HasInstrE : InstrE -< Eff).   

Local Notation continue_loop := (ret (inl tt)).
Local Notation exit_loop := (ret (inr tt)).
Local Notation rec_call := (trigger_inl1).

Fixpoint denote_instr (i : instr_r) : itree (CState +' Eff) unit := 
  let R := cmd_map_r denote_instr in
  match i with
  | Cassgn x tg ty e => trigger (AssgnE x tg ty e)
  | Copn xs tg o es => trigger (OpnE xs tg o es)
  | Csyscall xs o es => trigger (SyscallE xs o es)                          
                                
  | Cif e c1 c2 =>
      b <- trigger (EvalCond e) ;;
      if b then R c1 else R c2 

  | Cfor i (d, lo, hi) c => 
          vlo <- trigger (EvalBound lo) ;;
          vhi <- trigger (EvalBound hi) ;;
          denote_for R i c (wrange d vlo vhi)
        
  | Cwhile a c1 e c2 => 
      ITree.iter (fun _ =>
           R c1 ;;          
           b <- trigger (EvalCond e) ;;
           if b then (R c2) ;; continue_loop 
           else exit_loop) tt 
  
  | Ccall xs fn es => rec_call (FCall xs fn es)      
  end.

Definition denote_fcall (fn: funname) (xs: lvals) (es: pexprs) :
  itree (CState +' Eff) unit :=
  trigger (InitState fn es) ;; 
  c <- trigger (FunCode fn) ;;   
  rec_call (LCode c) ;; 
  trigger (SetDests fn xs).

Definition denote_cstate : CState ~> itree (CState +' Eff) :=           
  fun _ fs => match fs with
              | LCode c => cmd_map_r denote_instr c
              | FCall xs fn es => denote_fcall fn xs es       
              end.      

(* MAIN: denotational interpreter *)
Definition denote_cmd (c: cmd) : itree Eff unit :=
  mrec denote_cstate (LCode c).

(* for single instructions *)
Definition denote_cmd1 (i: instr) : itree Eff unit :=
  denote_cmd (i :: nil).

Definition denote_fun (fn: funname) (xs: lvals) (es: pexprs) :
  itree Eff unit :=
  trigger (InitState fn es) ;; 
  c <- trigger (FunCode fn) ;;   
  denote_cmd c ;;
  trigger (SetDests fn xs).

(***************************************************************)

(** denotational compositionality of commands wrt instructions *)
Lemma seq_eqtree_gen_lemma (c: cmd) (i: instr) :
  eq_itree eq (denote_cmd (i :: c))
    (denote_cmd (i :: nil) ;; denote_cmd c).
  unfold denote_cmd.
  unfold mrec.
  setoid_rewrite <- interp_mrec_bind.
  simpl.
  destruct i; simpl.
  setoid_rewrite bind_bind.
  setoid_rewrite bind_ret_l.
  reflexivity.
Qed.

End With_MREC_mod.


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
Section EventSem.

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
    | FunCode fn => err_opt _ (get_FunCode fn) end.   

Definition ext_handle_FunE {E: Type -> Type} `{ErrState -< E} :
  FunE +' E ~> itree E :=
  case_ handle_FunE (id_ E).

(* FunE interpreter *)
Definition interp_FunE {E: Type -> Type} {X: ErrState -< E}
  {A: Type}
  (t : itree (FunE +' E) A) : itree E A :=
  interp ext_handle_FunE t.


(***** LOW-LEVEL EVENTS ***********************************************)

Variant StackE : Type -> Type :=
  (* returns the head without popping *)
  | GetTopState : StackE estate
  (* updates the head state *)                       
  | UpdateTopState (st: estate) : StackE unit
  (* pops the head and returns it *)                                    
  | PopState : StackE estate
  (* pushes a new head state *)                    
  | PushState (st: estate) : StackE unit. 


(***** INSTR AUX FUNCTIONS *******************************************)

(** Ccall *)

Definition ret_get_FunDef {E: Type -> Type} 
  (fn: funname) : execT (itree E) FunDef :=
  Ret (o2r ErrType (get_FunDef fn)).           

Definition err_get_FunDef {E} `{ErrState -< E}
  (fn: funname) : itree E FunDef :=
  err_opt _ (get_FunDef fn).           

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
  vargs' <- err_result _ _ (pure_eval_Args args st0) ;;
  err_result _ _ (truncate_Args f vargs').
  
Definition err_init_state {E} `{ErrState -< E}
   (fn: funname) (vargs: seq value) (st0: estate) : itree E estate :=   
  let scs1 := st0.(escs) in
  let m1 := st0.(emem) in
  f <- err_get_FunDef fn ;;
  st1 <- err_result _ _
       (init_state f.(f_extra) (p_extra pr) ev (Estate scs1 m1 Vm.init)) ;;
  err_result _ _
      (write_vars (~~direct_call) (f_params f) vargs st1).
      
Definition mk_InitState {E} `{StackE -< E} `{ErrState -< E}
  (fn: funname) (args: pexprs) : itree E unit :=
  st0 <- trigger GetTopState ;;
  vargs <- err_eval_Args fn args st0 ;;
  st1 <- err_init_state fn vargs st0 ;;                                  
  trigger (PushState st1).

Definition err_return_val {E} `{ErrState -< E}
  (fn: funname) (st0: estate) : itree E (seq value) :=
  f <- err_get_FunDef fn ;;
  vres <- err_result _ _
      (get_var_is (~~ direct_call) st0.(evm) f.(f_res)) ;;
  err_result _ _
      (mapM2 ErrType dc_truncate_val f.(f_tyout) vres).

Definition err_reinstate_caller {E} `{ErrState -< E}
  (fn: funname) (xs: lvals) (vres: seq value)
  (st_ee st_er: estate) : itree E estate :=
  f <- err_get_FunDef fn ;;
  let scs2 := st_ee.(escs) in
  let m2 := finalize f.(f_extra) st_ee.(emem) in      
  err_result _ _
         (write_lvals (~~direct_call) (p_globs pr)
                      (with_scs (with_mem st_er m2) scs2) xs vres).
  
Definition mk_SetDests {E} `{StackE -< E} `{ErrState -< E}
  (fn: funname) (xs: lvals) : itree E unit :=
  st0 <- trigger PopState ;;
  vres <- err_return_val fn st0 ;;
  st1 <- trigger GetTopState ;;
  st2 <- err_reinstate_caller fn xs vres st0 st1 ;;
  trigger (UpdateTopState st2).

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
    err_result _ _ (write_var true x (Vint z) st1).                             

Definition mk_WriteIndex {E} `{StackE -< E} `{ErrState -< E}
  (x: var_i) (z: Z) : itree E unit :=
  st1 <- trigger GetTopState ;;
  st2 <- err_mk_WriteIndex x z st1 ;;
  trigger (UpdateTopState st2).
  

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

Definition mk_EvalCond {E} `{StackE -< E} `{ErrState -< E}
  (e: pexpr) : itree E bool :=
   st1 <- trigger GetTopState ;;
   err_mk_EvalCond e st1.
                                      

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

Definition mk_EvalBound {E} `{StackE -< E} `{ErrState -< E}
  (e: pexpr) : itree E Z :=
   st1 <- trigger GetTopState ;;
   err_mk_EvalBound e st1.


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
    v <- err_result _ _ (sem_pexpr true (p_globs pr) st1 e) ;;
    v' <- err_result _ _ (truncate_val ty v) ;;
    err_result _ _ (write_lval true (p_globs pr) x v' st1).

Definition mk_AssgnE {E: Type -> Type} `{StackE -< E}
  `{ErrState -< E} (x: lval) (tg: assgn_tag) (ty: stype) (e: pexpr) :
   itree E unit :=
    st1 <- trigger GetTopState ;;
    st2 <- err_mk_AssgnE x tg ty e st1 ;;
    trigger (UpdateTopState st2).


(** OpnE *)

(* terminating *)
Definition ret_mk_OpnE {E: Type -> Type} 
  (xs: lvals) (tg: assgn_tag) (o: sopn)
  (es : pexprs) (st1: estate) : execT (itree E) estate := Ret
    (sem_sopn (p_globs pr) o st1 xs es).

Definition err_mk_OpnE {E: Type -> Type} `{ErrState -< E}
  (xs: lvals) (tg: assgn_tag) (o: sopn)
   (es : pexprs) (st1: estate) : itree E estate :=
    err_result _ _ (sem_sopn (p_globs pr) o st1 xs es).

Definition mk_OpnE {E: Type -> Type} `{StackE -< E}
  `{ErrState -< E} (xs: lvals) (tg: assgn_tag) (o: sopn)
  (es : pexprs) : itree E unit :=
   st1 <- trigger GetTopState ;;
   st2 <- err_mk_OpnE xs tg o es st1 ;;
   trigger (UpdateTopState st2).
  

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
    ves <- err_result _ _ (sem_pexprs true (p_globs pr) st1 es ) ;;
    r3 <- err_result _ _ (exec_syscall st1.(escs) st1.(emem) o ves) ;;
    match r3 with
    | (scs, m, vs) =>
        err_result _ _ (write_lvals true (p_globs pr)
                       (with_scs (with_mem st1 m) scs) xs vs) end.
 
Definition mk_SyscallE {E: Type -> Type} `{StackE -< E}
  `{ErrState -< E} (xs: lvals) (o: syscall_t) (es: pexprs) :
  itree E unit :=
    st1 <- trigger GetTopState ;;
    st2 <- err_mk_SyscallE xs o es st1 ;;
    trigger (UpdateTopState st2).


(***** INSTR EVENT SEMANTICS *******************************************)

(** InstrE handler *)
Definition handle_InstrE {E: Type -> Type} `{StackE -< E}
  `{ErrState -< E} : InstrE ~> itree E :=
  fun _ e =>
    match e with
    | AssgnE xs tg ty es => mk_AssgnE xs tg ty es
    | OpnE xs tg o es => mk_OpnE xs tg o es
    | SyscallE xs o es => mk_SyscallE xs o es                              
    | EvalCond e => mk_EvalCond e
    | EvalBound e => mk_EvalBound e
    | WriteIndex x z => mk_WriteIndex x z                               
    | InitState fn es => mk_InitState fn es
    | SetDests fn xs => mk_SetDests fn xs
    end.                                            
        
Definition ext_handle_InstrE {E: Type -> Type} `{StackE -< E}
  `{ErrState -< E} : InstrE +' E ~> itree E :=
  case_ handle_InstrE (id_ E).

(* InstrE interpreter *)
Definition interp_InstrE {E: Type -> Type} `{StackE -< E}
  `{ErrState -< E} {A: Type}
  (t : itree (InstrE +' E) A) : itree E A :=
  interp ext_handle_InstrE t.


(***** STACK EVENT SEMANTICS **************************************)

Definition estack := list estate.

 Definition tl_error {A} (l: list A) : option (seq A) :=
    match l with
      | nil => None 
      | a :: m => Some m
    end.

Definition handle_StackE {E} `{ErrState -< E} :
  StackE ~> stateT estack (itree E) :=
    fun _ e ss =>
      match e with
      | GetTopState => st <- err_opt _ (hd_error ss) ;; Ret (ss, st)
      | UpdateTopState st =>
          ss' <- err_opt _ (tl_error ss) ;; Ret (st :: ss', tt)
      | PopState =>
          ss' <- err_opt _ (tl_error ss) ;;
          st <- err_opt _ (hd_error ss) ;; Ret (ss', st)                        
      | PushState st => Ret (st :: ss, tt)   
      end.

Definition ext_handle_StackE {E: Type -> Type} `{ErrState -< E} :
  StackE +' E ~> stateT estack (itree E) :=
  case_ handle_StackE pure_state.

Definition interp_StackE {E: Type -> Type} `{ErrState -< E} {A: Type} 
  (t : itree (StackE +' E) A) : stateT estack (itree E) A :=
   interp_state ext_handle_StackE t.


(********* MODULAR INTERPRETERS *************************************)

(* evaluation abstracting from stack and errors *)
Definition evalSE_cmd {E} `{ErrState -< E}
  (c: cmd) : itree (FunE +' StackE +' E) unit :=
  interp_InstrE (denote_cmd _ _ _ c).

(* evaluation abstracting from errors, return value paired with unit
*)
Definition evalEU_cmd {E} `{ErrState -< E}
  (c: cmd) : stateT estack (itree E) unit :=
  interp_StackE (interp_FunE (evalSE_cmd c)).

(* evaluation abstracting from errors, returning a state *)
Definition evalE1_cmd {E} {X: ErrState -< E} 
  (c: cmd) (ss: estack) : itree E estate := 
  ss <- evalEU_cmd c ss ;;
  match ss with
  | (st :: nil, _) => ret st
  | _ => throw ErrType end.              

(* MAIN: full evaluation returning an optional state *)
Definition eval_cmd {E} (c: cmd) (ss: estack) : itree E (option estate) := 
  @interp_Err E estate (evalE1_cmd c ss).

Definition eval121_cmd {E} (c: cmd) (st: estate) : itree E (option estate) := 
  eval_cmd c (st::nil).

Definition eval0_cmd {E} (c: cmd) : itree E (option estate) := 
  eval_cmd c nil.

End EventSem.


(**********************************************************************)
(*********************************************************************)
(*** INTERPRETERS WITH ERROR (quasi-flat) ******************************)

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
(** error-aware interpreter with double recursion *)
Section With_REC_error.

Local Notation continue_loop st := (ret (inl st)).
Local Notation exit_loop st := (ret (inr st)).
Local Notation rec_call x := (trigger_inl1 (Call x)). 

(* introduce events *)
Fixpoint eval_instr_call {E} `{ErrState -< E} (i : instr_r) (st: estate) :
  itree (callE (funname * (values * estate)) (values * estate) +' E) estate := 
  let R := st_cmd_map_r eval_instr_call in 
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
                                         
  | Ccall xs fn es =>
      va <- err_eval_Args fn es st ;;
      vst <- rec_call (fn, (va, st)) ;;
      (* PROBLEM: we still need the calle state, so the function needs
      to return it *)
      err_reinstate_caller fn xs (fst vst) (snd vst) st 
  end.

Definition eval_fcall_body {E} `{ErrState -< E} :
  (funname * (values * estate)) -> 
  itree (callE (funname * (values * estate)) (values * estate) +' E)
        (values * estate) :=
  fun fvst =>
    let '(fn, (va, st)) := fvst in
    st1 <- err_init_state fn va st ;; 
    c <- err_get_FunCode fn ;; 
    st2 <- st_cmd_map_r eval_instr_call c st1 ;; 
    vs <- err_return_val fn st2 ;;
    ret (vs, st2).

Fixpoint eval_instr {E} `{ErrState -< E} (i : instr_r) (st: estate) :
    itree E estate := 
  let R := st_cmd_map_r eval_instr in 
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
                                         
  | Ccall xs fn es =>
      va <- err_eval_Args fn es st ;;
      vst <- rec eval_fcall_body (fn, (va, st)) ;;  
      err_reinstate_caller fn xs (fst vst) (snd vst) st 
  end.

(* denotational interpreter *)
Definition evalE_err_cmd {E} `{ErrState -< E} (c: cmd) (st: estate) :
  itree E estate := st_cmd_map_r eval_instr c st. 

(* MAIN: full evaluation returning an optional state *)
Definition eval_err_cmd {E} (c: cmd) (st: estate) : itree E (option estate) := 
  @interp_Err E estate (evalE_err_cmd c st).

Definition evalE_fun {E} `{ErrState -< E} :
  (funname * (values * estate)) -> 
  itree E (values * estate) :=
  fun fvst =>
    let '(fn, (va, st)) := fvst in
    st1 <- err_init_state fn va st ;;
    c <- err_get_FunCode fn ;;
    st2 <- evalE_err_cmd c st1 ;;
    vs <- err_return_val fn st2 ;;
    ret (vs, st2).

End With_REC_error.


(**********************************************************************)
(** error-aware interpreter with mutual recursion *)

(* mutual recursion events *)
Variant FCState : Type -> Type :=
 | FLCode (c: cmd) (st: estate) : FCState estate
 | FFCall (xs: lvals) (f: funname) (es: pexprs) (st: estate) : FCState estate.

(** E-interpreter with mutual recursion *)
Section With_MREC_error.

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


(**********************************************************************)
(*********************************************************************)
(*** FLAT INTERPRETERS ************************************************)

Fixpoint lpst_cmd_map_r {E}
  (R: instr_r -> option estate -> itree E (option estate))
  (c: cmd) (pst: option estate) : itree E (option estate) := 
  match c with 
  | nil => Ret pst 
  | (MkI _ i) :: c' => pst' <- R i pst ;; lpst_cmd_map_r R c' pst'
  end.

(* mutual recursion events *)
Variant PCState : Type -> Type :=
 | PLCode (c: cmd) (st: estate) : PCState (exec estate)
 | PFCall (xs: lvals) (f: funname) (es: pexprs) (st: estate) :
    PCState (exec estate).

Fixpoint optst_cmd_map_r {E}
  (R: instr_r -> estate -> failT (itree E) estate)
  (c: cmd) (st: estate) : failT (itree E) estate := 
  match c with 
  | nil => Ret (Some st) 
  | (MkI _ i) :: c' => st' <- R i st ;;
                       optst_cmd_map_r R c' st'
  end.

Fixpoint pst_cmd_map_r {E}
  (R: instr_r -> estate -> execT (itree E) estate)
  (c: cmd) (st: estate) : execT (itree E) estate := 
  match c with 
  | nil => Ret (ok st) 
  | (MkI _ i) :: c' => st' <- R i st ;;
                       pst_cmd_map_r R c' st'
  end.

Fixpoint pmeval_for {E} 
  (R: cmd -> estate -> execT (itree E) estate)                
  (i: var_i) (c: cmd)
  (ls: list Z) (st: estate) : execT (itree E) estate :=
    match ls with
    | nil => fun st' => ret st'
    | (w :: ws) => fun st' =>
                     st1 <- ret_mk_WriteIndex i w st' ;;
                     st2 <- R c st1 ;;
                     pmeval_for R i c ws st2
    end st.


(**********************************************************************)
(** flat interpreter with mutual recursion *)
Section With_MREC_flat.

Local Notation continue_loop st := (ret (inl st)).
Local Notation exit_loop st := (ret (inr st)).
Local Notation rec_call := (trigger_inl1). 

Fixpoint pmeval_instr {E} (i : instr_r) (st: estate) :
  execT (itree (PCState +' E)) estate := 
  let R := pst_cmd_map_r pmeval_instr in
  match i with
  | Cassgn x tg ty e => ret_mk_AssgnE x tg ty e st
  | Copn xs tg o es => ret_mk_OpnE xs tg o es st
  | Csyscall xs o es => ret_mk_SyscallE xs o es st                          
                                                 
  | Cif e c1 c2 =>
      b <- ret_mk_EvalCond e st ;;
      if b then R c1 st else R c2 st 

  | Cfor i (d, lo, hi) c => 
          vlo <- ret_mk_EvalBound lo st ;;
          vhi <- ret_mk_EvalBound hi st ;;
          pmeval_for R i c (wrange d vlo vhi) st

  | Cwhile a c1 e c2 => 
      execT_iter _ _ (fun st0 =>
           st1 <- R c1 st0 ;;          
           b <- ret_mk_EvalCond e st1 ;;
           if b then st2 <- R c2 st1 ;; continue_loop st2 
           else exit_loop st1) st

  | Ccall xs fn es => rec_call (PFCall xs fn es st) end.

Definition pmeval_fcall {E}  
  (xs: lvals) (fn: funname) (es: pexprs) (st0: estate) :
  execT (itree (PCState +' E)) estate :=
  f <- ret_get_FunDef fn ;;
  va <- ret_eval_Args fn es st0 ;;
  st1 <- ret_init_state fn va st0 ;;
  c <- ret_get_FunCode fn ;;
  rec_call (PLCode c st1) ;;
  vs <- ret_return_val fn st1 ;;
  ret_reinstate_caller fn xs vs st1 st0.

Definition pmeval_cstate {E} : PCState ~> itree (PCState +' E) :=           
  fun _ fs => match fs with
              | PLCode c st => pst_cmd_map_r pmeval_instr c st
              | PFCall xs fn es st => pmeval_fcall xs fn es st      
              end.      

Definition pmeval_cmd {E} (c: cmd) (st: estate) :
  execT (itree E) estate :=
  mrec pmeval_cstate (PLCode c st).

Definition pmeval_cmd1 {E} (i: instr) (st: estate) :
  execT (itree E) estate :=
  pmeval_cmd (i :: nil) st.

Definition pmeval_fun {E} (fn: funname) (va: values) (st: estate) :
  execT (itree E) (values * estate) :=
  st1 <- ret_init_state fn va st ;;
  c <- ret_get_FunCode fn ;;
  st2 <- pmeval_cmd c st1 ;;
  vs <- ret_return_val fn st2 ;;
  ret (vs, st2).

End With_MREC_flat.


(**********************************************************************)
(** flat interpreter with double recursion *)
Section With_REC_flat.

Local Notation continue_loop st := (ret (inl st)).
Local Notation exit_loop st := (ret (inr st)).
Local Notation rec_call x := (trigger_inl1 (Call x)). 

(* introduce events *)
Fixpoint peval_instr_call {E} (i : instr_r) (st: estate) :
  execT (itree (callE (funname * (values * estate)) (exec (values * estate))
                +' E))
    estate := 
  let R := pst_cmd_map_r peval_instr_call in 
  match i with 
  | Cassgn x tg ty e => ret_mk_AssgnE x tg ty e st
  | Copn xs tg o es => ret_mk_OpnE xs tg o es st
  | Csyscall xs o es => ret_mk_SyscallE xs o es st                          

  | Cif e c1 c2 =>
      b <- ret_mk_EvalCond e st ;;
      if b then R c1 st else R c2 st 

  | Cfor i (d, lo, hi) c => 
          vlo <- ret_mk_EvalBound lo st ;;
          vhi <- ret_mk_EvalBound hi st ;;
          pmeval_for R i c (wrange d vlo vhi) st

  | Cwhile a c1 e c2 => 
      execT_iter _ _ (fun st0 =>
           st1 <- R c1 st0 ;;          
           b <- ret_mk_EvalCond e st1 ;;
           if b then st2 <- R c2 st1 ;; continue_loop st2 
           else exit_loop st1) st

  | Ccall xs fn es =>
      va <- ret_eval_Args fn es st ;;      
      vst <- rec_call (fn, (va, st)) ;; 
      (* PROBLEM: we still need the calle state, so the function needs
      to return it *)
      ret_reinstate_caller fn xs (fst vst) (snd vst) st   
  end.

Definition peval_fcall_body' {E} :
  (funname * (values * estate)) -> 
  execT (itree (callE (funname * (values * estate)) (exec (values * estate))
         +' E)) (values * estate) :=
  fun fvst =>
    let '(fn, (va, st)) := fvst in
    st1 <- ret_init_state fn va st ;; 
    c <- ret_get_FunCode fn ;; 
    st2 <- pst_cmd_map_r peval_instr_call c st1 ;; 
    vs <- ret_return_val fn st2 ;;
    ret (vs, st2).

Definition peval_fcall_body {E} :
  (funname * (values * estate)) -> 
  execT (itree E) (values * estate) :=
  fun fvst => rec peval_fcall_body' fvst.

Fixpoint peval_instr {E} (i : instr_r) (st: estate) :
  execT (itree E) estate := 
  let R := pst_cmd_map_r peval_instr in 
  match i with 
  | Cassgn x tg ty e => ret_mk_AssgnE x tg ty e st
  | Copn xs tg o es => ret_mk_OpnE xs tg o es st
  | Csyscall xs o es => ret_mk_SyscallE xs o es st                          

  | Cif e c1 c2 =>
      b <- ret_mk_EvalCond e st ;;
      if b then R c1 st else R c2 st 

  | Cfor i (d, lo, hi) c => 
          vlo <- ret_mk_EvalBound lo st ;;
          vhi <- ret_mk_EvalBound hi st ;;
          pmeval_for R i c (wrange d vlo vhi) st

  | Cwhile a c1 e c2 => 
      execT_iter _ _ (fun st0 =>
           st1 <- R c1 st0 ;;          
           b <- ret_mk_EvalCond e st1 ;;
           if b then st2 <- R c2 st1 ;; continue_loop st2 
           else exit_loop st1) st

  | Ccall xs fn es => 
      va <- ret_eval_Args fn es st ;;      
(*      vst <- rec peval_fcall_body' (f, (va, st)) ;; *)
      vst <- peval_fcall_body (fn, (va, st)) ;; 
      ret_reinstate_caller fn xs (fst vst) (snd vst) st   
  end.

(* MAIN: denotational interpreter *)
Definition peval_flat_cmd {E} (c: cmd) (st: estate) :
  execT (itree E) estate := pst_cmd_map_r peval_instr c st. 

Definition peval_fun {E} :
  (funname * (values * estate)) -> 
  execT (itree E) (values * estate) :=
  fun fvst =>
    let '(fn, (va, st)) := fvst in
    st1 <- ret_init_state fn va st ;; 
    c <- ret_get_FunCode fn ;; 
    st2 <- peval_flat_cmd c st1 ;; 
    vs <- ret_return_val fn st2 ;;
    ret (vs, st2).

End With_REC_flat.

End OneProg.


(***************************************************************************)
(*** APPLICATION ***********************************************************)
(** we define a language translation and try to prove equivalence of
function application and commands across the translation under the
appropriate hypothesis. First we customize induction on Jasmin
commands and specify the translation. *)


(*** INDUCTION PRINCIPLE ****************************************************)
(** induction on Jasmin commands *)
Section CMD_IND.

Context (Pr: instr_r -> Prop) (Pi: instr -> Prop) (Pc: cmd -> Prop).
Context (Hnil : Pc [::])
        (Hcons : forall i c, Pi i -> Pc c -> Pc (i::c))

        (Hinstr : forall ii ir, Pr ir -> Pi (MkI ii ir))
        
        (Hassgn : forall x tg ty e, Pr (Cassgn x tg ty e))
        (Hopn : forall x tg o e, Pr (Copn x tg o e))
        (Hsyscall : forall x sc e, Pr (Csyscall x sc e))
        (Hif   : forall e c1 c2, Pc c1 -> Pc c2 -> Pr (Cif e c1 c2))
        (Hfor  : forall i rn c, Pc c -> Pr (Cfor i rn c))
        (Hwhile : forall a c1 e c2, Pc c1 -> Pc c2 -> Pr (Cwhile a c1 e c2))
        (Hcall  : forall xs fn es, Pr (Ccall xs fn es)).

Fixpoint cmd_IndF (Hi : forall i, Pi i) (c : cmd) : Pc c := 
  match c with
  | [::] => Hnil
  | i :: c => Hcons i c (Hi i) (cmd_IndF Hi c)
  end.

Definition instr_Ind (Hr : forall i, Pr i) (i : instr) : Pi i :=
  match i with MkI ii ir => Hinstr ii ir (Hr ir) end.

Fixpoint instr_r_Ind (ir: instr_r) : Pr ir :=
  let R := cmd_IndF (instr_Ind instr_r_Ind) in 
  match ir return Pr ir with
  | Cassgn x tg ty e => Hassgn x tg ty e 
  | Copn x tg o e => Hopn x tg o e
  | Csyscall x sc e => Hsyscall x sc e                        
  | Cif e c1 c2 => Hif e c1 c2 (R c1) (R c2)
  | Cfor i rn c => Hfor i rn c (R c)                     
  | Cwhile a c1 e c2 => Hwhile a c1 e c2 (R c1) (R c2)
  | Ccall xs fn es => Hcall xs fn es
  end.

Definition cmd_Ind := cmd_IndF (instr_Ind instr_r_Ind).

End CMD_IND.


(*** TRANSLATION SPEC *******************************************)
Section TRANSF.
Context (tr_lval : lval -> lval)
        (tr_expr : pexpr -> pexpr)
        (tr_opn : sopn -> sopn)
        (tr_sysc : syscall_t -> syscall_t).

Local Notation tr_lvals ls := (map tr_lval ls).
Local Notation tr_exprs es := (map tr_expr es).

Definition Tr_i (Th: instr_r -> instr_r) (i: instr) : instr :=
  match i with MkI ii ir => MkI ii (Th ir) end.  

Fixpoint Tr_ir (i : instr_r) : instr_r :=
  let R := Tr_i Tr_ir in
  match i with
  | Cassgn x tg ty e => Cassgn (tr_lval x) tg ty (tr_expr e)
  | Copn xs tg o es =>
      Copn (tr_lvals xs) tg (tr_opn o) (tr_exprs es)
  | Csyscall xs sc es =>
      Csyscall (tr_lvals xs) (tr_sysc sc) (tr_exprs es)
  | Cif e c1 c2 => Cif (tr_expr e) (map R c1) (map R c2)
  | Cfor i rg c => Cfor i rg (map R c)                     
  | Cwhile a c1 e c2 => Cwhile a (map R c1) (tr_expr e) (map R c2)
  | Ccall xs fn es => Ccall (tr_lvals xs) fn (tr_exprs es)
  end.
Local Notation Tr_instr := (Tr_i Tr_ir).
Local Notation Tr_cmd c := (map Tr_instr c).

Definition Tr_FunDef (f: FunDef) : FunDef :=
  match f with
  | MkFun i tyin p_xs c tyout r_xs xtr =>
    MkFun i tyin p_xs (Tr_cmd c) tyout r_xs xtr end.
    

(*********************************************************************)
(*** PROOFS **********************************************************)

Section TR_tests.

Context (pr1 pr2 : prog)
        (PR : forall T, T -> T -> Prop).
Context (TR_E : forall (E: Type -> Type) T1 T2,
            E T1 -> E T2 -> Prop)
        (VR_E : forall (E: Type -> Type) T1 T2,
            E T1 -> T1 -> E T2 -> T2 -> Prop).

Local Notation RS := (PR estate).
Local Notation RV := (PR values).
Local Notation RV1 := (PR value).
Local Notation RSMV := (PR (syscall_state * mem * seq value)).


(*********************************************************************)
Section Err_test.

Context (E: Type -> Type)
        (HasErr: ErrState -< E)     
        (HasStackE : StackE -< E)     
        (HasFunE : FunE -< E).     
     (*   (HasInstrE : InstrE -< E).     *)

Definition REv_sk (A B: Type) (e1: ErrState A) (e2: InstrE B) : Prop := True.

Definition RAns_sk (A B: Type) (e1: ErrState A) (v1: A) (e2: InstrE B) (v2: B) : Prop := True.

(*  | WriteIndex (x: var_i) (z: Z) : InstrE unit *)                            

Lemma ErrState_rutt_test1 (x: var_i) (z: Z) (k: unit -> itree InstrE unit) :
      @rutt ErrState InstrE unit unit REv_sk RAns_sk eq
                (throw ErrType) (Vis (WriteIndex x z) k).
  eapply rutt_Vis.
  unfold REv_sk; auto.
  intros.
  inv t1.
Qed.  

End Err_test.


(*********************************************************************)
(** proofs with the modular semantics *)
Section TR_MM_L1.

Context (E: Type -> Type)
        (HasErr: ErrState -< E)    
        (HasFunE : FunE -< E)
        (HasInstrE : InstrE -< E).     

(* toy assumptions, with eutt. this is too strong. notice that eq is
ok, because the event return type is unit. however, when interpreters
apply these to unrelated states, equivalence might be lost. So we
cannot realy express the constraint at this level. *)
Context
  (hinit: forall fn es1 es2, es2 = map tr_expr es1 ->
    @eutt E unit unit eq
      (trigger (InitState fn es1)) (trigger (InitState fn es2)))
  (hdests: forall fn xs1 xs2, xs2 = map tr_lval xs1 ->
    @eutt E unit unit eq 
      (trigger (SetDests fn xs1)) (trigger (SetDests fn xs2))).

(* should be shorter *)
Lemma adhoc_hinit {F} : forall fn es1 es2,
  es2 = map tr_expr es1 ->
  @eutt (F +' E) _ _ eq
    (trigger (InitState fn es1)) (trigger (InitState fn es2)).
  intros.
  have := (hinit fn es1 es2 H); intro I.
  inv H.
  unfold trigger in I.
  eapply eqit_inv_Vis_weak in I; eauto.
  dependent destruction I.
  unfold eqeq in H.
  dependent destruction x.
  destruct H as [H H0].
  unfold subevent in H.
  unfold resum in H.
  simpl in *.
  
  unfold trigger.
  have @A : (@eq Type unit unit) by reflexivity. 
  eapply eqit_Vis_gen with (p:= A); eauto; simpl.
  unfold subevent.
  unfold resum.
  unfold ReSum_inr.
  unfold CategoryOps.cat.
  unfold Cat_IFun.
  unfold inr_.
  unfold Inr_sum1.
  unfold resum.
  rewrite H.
  auto.
  intros.
  reflexivity.
Qed.  

(* should be shorter *)
Lemma adhoc_hdests {F} : forall fn xs1 xs2,
  xs2 = map tr_lval xs1 ->
  @eutt (F +' E) _ _ eq
    (trigger (SetDests fn xs1)) (trigger (SetDests fn xs2)).
  intros.
  have := (hdests fn xs1 xs2 H); intro I.
  inv H.
  unfold trigger in I.
  eapply eqit_inv_Vis_weak in I; eauto.
  dependent destruction I.
  unfold eqeq in H.
  dependent destruction x.
  destruct H as [H H0].
  unfold subevent in H.
  unfold resum in H.
  simpl in *.
  
  unfold trigger.
  have @A : (@eq Type unit unit) by reflexivity. 
  eapply eqit_Vis_gen with (p:= A); eauto; simpl.
  unfold subevent.
  unfold resum.
  unfold ReSum_inr.
  unfold CategoryOps.cat.
  unfold Cat_IFun.
  unfold inr_.
  unfold Inr_sum1.
  unfold resum.
  rewrite H.
  auto.
  intros.
  reflexivity.
Qed.  

(** denotational equivalence across the translation; the proof is nice
 and short, but relies on the toy eutt assumptions; notice that the
 FunCode event actually hides the fact that the functions on the two
 sides are actually different, se we don't need induction on commands
 *)
Lemma comp_gen_ok_MM1 (fn: funname)
  (xs1 xs2: lvals) (es1 es2: pexprs) 
  (hxs: xs2 = map tr_lval xs1)
  (hes: es2 = map tr_expr es1) :  
  eutt eq  
    (denote_fcall E _ _ fn xs1 es1) (denote_fcall E _ _ fn xs2 es2).
  intros.
  unfold denote_fcall; simpl.
  
  eapply eutt_clo_bind with (UU:= eq); eauto.
  rewrite hes.

  eapply adhoc_hinit; eauto.  
  
  intros.
  eapply eutt_clo_bind with (UU := eq); eauto.
  reflexivity.

  intros.
  inv H0.
  eapply eutt_clo_bind with (UU := eq); eauto.
  reflexivity.
  intros.
  
  eapply adhoc_hdests; eauto.
Qed.  

(** here there is no CState issue in the type, the proof is even
simpler (still relying on the toy assumptions) *)
Lemma comp_gen_ok_MM2 (fn: funname)
  (xs1 xs2: lvals) (es1 es2: pexprs) 
  (hxs: xs2 = map tr_lval xs1)
  (hes: es2 = map tr_expr es1) :  
  eutt eq  
    (denote_fun E _ _ fn xs1 es1) (denote_fun E _ _ fn xs2 es2).
  intros.
  unfold denote_fun; simpl.

  eapply eutt_clo_bind with (UU:= eq); eauto.
  intros.
  
  eapply eutt_clo_bind with (UU:= eq); eauto.
  reflexivity.
  intros.
  inv H0.

  eapply eutt_clo_bind with (UU:= eq); eauto.
  reflexivity.
Qed.  

End TR_MM_L1.


Section TR_MM_toy.

Context (E1: Type -> Type)
        (HasErr1: ErrState -< E1)     
        (HasStackE1 : StackE -< E1)     
        (HasFunE1 : FunE -< E1).     

Lemma Assgn_test :
    forall l a s p, @eutt E1 unit unit eq
      (interp_InstrE pr1 (trigger (AssgnE l a s p)))
      (interp_InstrE pr2 (trigger (AssgnE (tr_lval l) a s (tr_expr p)))).
  intros.
  unfold interp_InstrE.
  repeat setoid_rewrite interp_trigger.
  unfold ext_handle_InstrE.
  unfold case_.
  simpl.
  unfold mk_AssgnE.
  eapply eutt_clo_bind with (UU := RS).
  admit. (* need to go deeper *)
  intros.
  eapply eutt_clo_bind with (UU := RS).
  unfold err_mk_AssgnE.
  eapply eutt_clo_bind with (UU := RV1).
  admit.
  intros.
  eapply eutt_clo_bind with (UU := RV1).
  admit.
  intros.
  admit.
  intros. (* deeper *)
  admit.  
Abort.

Context (E2: Type -> Type)
        (HasErr2: ErrState -< E2)     
        (HasFunE2 : FunE -< E2).     

Context (RSS : estack * estate -> estack * estate -> Prop).
    
(* would-be proof of a toy assumption; in fact, requires rutt *)
Lemma Assgn_test : forall l a s p ss,
   @eutt E2 (estack * unit) _ eq
      (interp_StackE (interp_InstrE pr1 (trigger (AssgnE l a s p))) ss)
      (interp_StackE (interp_InstrE pr2
                        (trigger (AssgnE (tr_lval l) a s (tr_expr p)))) ss).
  intros.
  unfold interp_InstrE.
  unfold interp_StackE.
  repeat setoid_rewrite interp_trigger.
  unfold ext_handle_InstrE.
  unfold ext_handle_StackE.
  unfold case_.
  unfold Case_sum1.
  unfold Case_sum1_Handler.
  simpl.  
  unfold mk_AssgnE.
  setoid_rewrite interp_state_bind.
  eapply eutt_clo_bind with (UU := eq).  (* should be (UU:= RSS) *) 
  setoid_rewrite interp_state_trigger.
  simpl.
  reflexivity.

  intros.
  inv H.
  destruct u2 as [ss1 st1].
  simpl.
  setoid_rewrite interp_state_bind.

  eapply eutt_clo_bind with (UU := eq).  (* should be (UU:= RSS) *) 
  unfold err_mk_AssgnE.

  setoid_rewrite interp_state_bind.  
  eapply eutt_clo_bind with (UU := eq).  (* should be (UU := RSSV) *)
  admit. (* need generic relation *)

  intros.
  inv H.

  setoid_rewrite interp_state_bind.  
  eapply eutt_clo_bind with (UU := eq).  (* should be (UU := RSSV) *)
  destruct u2 as [ss2 st2].
  simpl.
  
  unfold truncate_val.
  unfold err_result.
  destruct (Let x := of_val s st2 in ok (to_val (t:=s) x)).
  setoid_rewrite interp_state_ret.
  reflexivity.
  setoid_rewrite interp_state_vis.
  eapply eutt_clo_bind with (UU := eq). (* same *) 

  simpl.
  unfold pure_state.
  eapply eqit_Vis_gen with (p:= erefl (void: Type)).
  unfold eqeq.
  reflexivity.
  unfold pweqeq.
  intros.
  reflexivity.

  intros.
  destruct u2; simpl.
  inv e1.

  intros.
  inv H.
  destruct u0; simpl.
  unfold err_result; simpl.
  admit. (* need generic relation (rutt) *)

  intros.
  inv H.
  destruct u2; simpl.
  setoid_rewrite interp_state_trigger.
  simpl.
  eapply eutt_clo_bind with (UU := eq). (* same *) 
  reflexivity.
  intros.
  inv H.
  reflexivity.
Admitted. 
  
(*
Lemma Assgn_test : forall l a s p
  (F: itree (StackE +' E2) ~> stateT estack (itree E2)),
   @eutt E2 _ _ eq
      (F (interp_InstrE pr1 (trigger (AssgnE l a s p))))
      (F (interp_InstrE pr2 (trigger (AssgnE (tr_lval l) a s (tr_expr p))))).
  
Context 
  (assgn_h2 :
    forall l a s p, @eutt E1 _ _ eq
      (interp_InstrE pr1 (trigger (AssgnE l a s p)))
      (interp_InstrE pr2 (trigger (AssgnE (tr_lval l) a s (tr_expr p))))).
*)       
End TR_MM_toy.


Section TR_MM_toy2.

Context (E: Type -> Type)
        (HasErr: ErrState -< E)     
        (HasStackE : StackE -< E)     
        (HasFunE : FunE -< E)     
        (HasInstrE : InstrE -< E).     

(* two alternative version of a toy hyp *)
Context (assgn_h :
          forall l a s p, AssgnE l a s p =
                            AssgnE (tr_lval l) a s (tr_expr p)).
Context 
  (assgn_h1 :
          forall l a s p, @eutt E _ _ eq (trigger (AssgnE l a s p))
                            (trigger (AssgnE (tr_lval l) a s (tr_expr p)))).

(* proving toy eutt across the translation for all commands (here we
need induction) *)
Lemma eutt_cmd_tr_L1 (cc: cmd) :  
  eutt eq  
    (denote_cmd E _ _ cc) (denote_cmd E _ _ (Tr_cmd cc)).
  set (Pr := fun (i: instr_r) => forall ii,
                 eutt eq (denote_cmd E _ _ ((MkI ii i) :: nil))
                       (denote_cmd _ _ _ ((Tr_instr (MkI ii i)) :: nil))).
  set (Pi := fun i => eutt eq (denote_cmd E _ _ (i::nil))
                       (denote_cmd _ _ _ (Tr_instr i :: nil))).
  set (Pc := fun c => eutt eq (denote_cmd E _ _ c)
                        (denote_cmd _ _ _ (Tr_cmd c))).
  revert cc.
  apply (cmd_Ind Pr Pi Pc); rewrite /Pr /Pi /Pc.
  - reflexivity.
  - intros; simpl.
    setoid_rewrite seq_eqtree_gen_lemma.
    rewrite H.
    setoid_rewrite H0.
    reflexivity.
  - intros; eauto.
  - simpl; intros.
    unfold denote_cmd.
    unfold mrec; simpl.
    setoid_rewrite <- assgn_h.
    reflexivity.
  - simpl; intros.
    unfold denote_cmd.
    unfold mrec.
    simpl.
    (* Opn hyp missing, simply to be added *)
    admit.
  - intros.
    unfold denote_cmd.
    unfold mrec; simpl.
    (* Csyscall hyp missing, as before *)
    admit.
  - intros; simpl.
    unfold denote_cmd.
    unfold mrec; simpl.
    unfold denote_cmd in H.
    setoid_rewrite interp_mrec_bind.
    eapply eutt_clo_bind with (UU := eq); try (intros; reflexivity).
    setoid_rewrite interp_mrec_bind.
    eapply eutt_clo_bind with (UU := eq).
    (* EvalCond hyp missing, as before *)
    admit.
    intros.
    inv H1.
    destruct u2.
    eapply H.
    eapply H0.
  - intros; simpl.
    unfold denote_cmd.
    unfold mrec; simpl.
    setoid_rewrite interp_mrec_bind.
    eapply eutt_clo_bind with (UU := eq); try (intros; reflexivity).
    destruct rn; simpl.
    destruct p; simpl.
    setoid_rewrite interp_mrec_bind.
    eapply eutt_clo_bind with (UU := eq).
    (* EvalBound hyp missing, as before *)
    admit.
    intros.
    inv H0.
    setoid_rewrite interp_mrec_bind.
    eapply eutt_clo_bind with (UU := eq).
    (* EvalBound hyp missing, as before *)
    admit.
    intros.
    inv H0.
    unfold denote_cmd in H.
    unfold mrec in H.
    unfold denote_for.

    induction (wrange d u2 u0).
    reflexivity.
    setoid_rewrite interp_mrec_bind.
    eapply eutt_clo_bind with (UU := eq).
    (* WriteIndex hyp missing, as before *)
    admit.

    intros.
    inv H0.
    destruct u3.
    setoid_rewrite interp_mrec_bind.
    eapply eutt_clo_bind with (UU := eq).
    eapply H.

    intros.
    inv H0.
    destruct u3.
    eapply IHl.

  - intros; simpl.
    unfold denote_cmd.
    unfold mrec; simpl.
    
    setoid_rewrite interp_mrec_bind.
    eapply eutt_clo_bind with (UU := eq); try (intros; reflexivity).

    setoid_rewrite interp_mrec_as_interp.
    setoid_rewrite interp_iter.
    unfold CategoryOps.iter.
    unfold Iter_Kleisli.
    unfold Basics.iter.
    unfold MonadIter_itree.
    
    eapply eutt_iter' with (RI := eq); eauto.
    intros.
    inv H1.
    destruct j2.
    setoid_rewrite interp_bind.
    eapply eutt_clo_bind with (UU := eq).
    setoid_rewrite interp_mrec_as_interp in H.
    eapply H.
    intros.
    inv H1.
    destruct u2.
    setoid_rewrite interp_bind.
    eapply eutt_clo_bind with (UU := eq).
    (* EvalCond hyp missing, as before *)
    admit.

    intros.
    inv H1.
    
    destruct u2.
    setoid_rewrite interp_bind.
    eapply eutt_clo_bind with (UU := eq).    
    setoid_rewrite interp_mrec_as_interp in H0.
    eapply H0.

    intros.
    reflexivity.
    reflexivity.

  - simpl; intros.
    unfold denote_cmd.
    unfold mrec; simpl.
    setoid_rewrite interp_mrec_bind.
    eapply eutt_clo_bind with (UU := eq); try (intros; reflexivity).
    unfold trigger_inl1.
    setoid_rewrite interp_mrec_trigger.
    unfold mrecursive.
    unfold mrec.
    simpl.
    unfold denote_fcall.
    simpl.
    
    setoid_rewrite interp_mrec_bind.
    eapply eutt_clo_bind with (UU := eq).
    setoid_rewrite interp_mrec_trigger.
    simpl.

    (* InitState hyp missing, as before *)
    admit.

    intros.
    inv H.
    destruct u2.
    setoid_rewrite interp_mrec_bind.
    eapply eutt_clo_bind with (UU := eq); try reflexivity.

    intros.
    inv H.
    setoid_rewrite interp_mrec_bind.
    eapply eutt_clo_bind with (UU := eq); try reflexivity.
    
    intros.
    inv H.
    destruct u0.
    setoid_rewrite interp_mrec_trigger.
    simpl.
        
    (* SetDests hyp missing, as before *)
    admit.
Admitted.     
    
End TR_MM_toy2.


Section TR_MM_toy3.

Context (E: Type -> Type)
        (HasErr: ErrState -< E)     
        (HasStackE : StackE -< E)     
        (HasFunE : FunE -< E).     

(* here should be rutt *)
Lemma tr_eutt_tun_ok (fn: funname)
  (xs1 xs2: lvals) (es1 es2: pexprs) 
  (hxs: xs2 = map tr_lval xs1)
  (hes: es2 = map tr_expr es1) :  
  eutt eq  
    (@interp_InstrE pr1 E _ _ _ (denote_fun _ _ _ fn xs1 es1))
    (interp_InstrE pr2 (denote_fun _ _ _ fn xs2 es2)).
  unfold interp_InstrE.
  setoid_rewrite comp_gen_ok_MM2 at 1; eauto.
  eapply eutt_interp; eauto.
  2: { reflexivity. }

  unfold eq2.
  unfold Eq2_Handler.
  unfold eutt_Handler.
  unfold i_pointwise.
  intros.
  
  unfold ext_handle_InstrE.
  unfold handle_InstrE.
  destruct a; eauto; simpl.
  2: { reflexivity. }

  unfold case_.
  unfold Case_sum1_Handler.
  unfold Handler.case_.
  destruct i.

  unfold mk_AssgnE.

  setoid_rewrite bind_trigger.
  eapply eqit_Vis_gen; eauto.
  instantiate (1 := erefl).
  unfold eqeq; simpl; auto.
  unfold pweqeq.
  intros.
  unfold err_mk_AssgnE.

  eapply eutt_clo_bind with (UU := RS); eauto.
  
  eapply eutt_clo_bind with (UU := RV1); eauto.
  (* missing hyp on semp_pexpr, but OK *)
  admit.

  intros.
  eapply eutt_clo_bind with (UU := RV1); eauto.
  (* missing hyp on truncate_val, but OK *)
  admit.

  intros.
  (* missing hyp on write_lval, but OK *)
  admit.

  intros.
  (* missing hyp on UpdateTopState, TOO STRONG *)
  admit.

  unfold mk_OpnE.

  eapply eutt_clo_bind with (UU := RS); eauto.
  (* missing hyp on GetTopState, but OK *)
  admit.

  intros.
  
  eapply eutt_clo_bind with (UU := RS); eauto.
  
  unfold err_mk_OpnE; simpl.
  (* missing hyp on sem_opn, but OK *)
  admit.

  intros.
  (* missing hyp on UpdateTopState, TOO STRONG *)
  admit.

  unfold mk_SyscallE; simpl.
  
  eapply eutt_clo_bind with (UU := RS); eauto.
  (* missing hyp on GetTopState, but OK *)
  admit.

  intros.
  eapply eutt_clo_bind with (UU := RS); eauto.
  unfold err_mk_SyscallE.
  
  eapply eutt_clo_bind with (UU := RV); eauto.
  (* missing hyp on sem_pexprs, but OK *)
  admit.

  intros.
  eapply eutt_clo_bind with (UU := RSMV); eauto.
  (* missing hyp on syscall_state_t, but OK *)
  admit.

  intros.
  (* missing hyp on write_lvals, but OK *)
  admit.

  intros.
  (* missing hyp on UpdateTopState, TOO STRONG *)
  admit.

  unfold mk_EvalCond.

  intros.
  eapply eutt_clo_bind with (UU := RS); eauto.
  (* missing hyp on GetTopState, but OK *)
  admit.

  intros.
  unfold err_mk_EvalCond.
  (* missing hyp on Boolen evaluation, but OK *)
  admit.

  unfold mk_EvalBound.
  
  intros.
  eapply eutt_clo_bind with (UU := RS); eauto.
  (* missing hyp on GetTopState, but OK *)
  admit.

  intros.
  (* missing hyp on bound evaluation, but OK *)
  admit.

  unfold mk_WriteIndex.
  
  intros.
  eapply eutt_clo_bind with (UU := RS); eauto.
  (* missing hyp on GetTopState, but OK *)
  admit.

  intros.
  eapply eutt_clo_bind with (UU := RS); eauto.
  (* missing hyp on index update, but OK *)
  admit.

  intros.
  (* missing hyp on UpdateTopState, TOO STRONG *)
  admit.

  unfold mk_InitState.

  eapply eutt_clo_bind with (UU := RS); eauto.
  (* missing hyp on GetTopState, but OK *)
  admit.

  intros.
  eapply eutt_clo_bind with (UU := RV); eauto.
  (* missing hyp on args eval, but OK *)
  admit.

  intros.
  eapply eutt_clo_bind with (UU := RS); eauto.
  (* missing hyp on init state, but OK *)
  admit.

  intros.
  (* missing hyp on PushState, TOO STRONG *)
  admit.

  unfold mk_SetDests.
  
  eapply eutt_clo_bind with (UU := RS); eauto.
  (* missing hyp on PopState, but OK *)
  admit.

  intros.
  
  eapply eutt_clo_bind with (UU := RV); eauto.
  (* missing hyp on ret val, but OK *)
  admit.
  
  intros.
  
  eapply eutt_clo_bind with (UU := RS); eauto.
  (* missing hyp on GetTopState, but OK *)
  admit.

  intros.
  
  eapply eutt_clo_bind with (UU := RS); eauto.
  (* missing hyp on reinstate, but OK *)
  admit.

  intros.
  (* missing hyp on UpdateTopState, TOO STRONG *)
  admit.

  intros.  
  rewrite H.
  (* missing hyp on init state, TOO STRONG *)
  admit.

  intros.
  rewrite H.
  (* missing hyp on set dests, TOO STRONG *)
  admit.
Admitted. 
   
End TR_MM_toy3.


Section TR_MM_toy4.

Context (E: Type -> Type)
        (HasErr: ErrState -< E).

(* here we need rutt *)
Lemma comp_gen_okMM_L3 (fn: funname)
  (xs1 xs2: lvals) (es1 es2: pexprs) 
  (hxs: xs2 = map tr_lval xs1)
  (hes: es2 = map tr_expr es1) (ss: estack) :  
  eutt eq  
    (@interp_StackE E _ _
       (@interp_FunE pr1 _ _ _ (interp_InstrE pr1 (denote_fun _ _ _ fn xs1 es1))) ss) 
    (interp_StackE (interp_FunE pr2 (interp_InstrE pr2 (denote_fun _ _ _ fn xs2 es2))) ss).
  unfold interp_StackE.
(*  
  eapply eutt_interp_state.
  setoid_rewrite comp_gen_okMM_L2.
*)
Admitted. 

End TR_MM_toy4.


Section GEN_ErrAndFlat.

Context (E: Type -> Type).   

Local Notation RV := (PR values).
Local Notation VS := (values * estate)%type.
Local Notation FVS := (funname * VS)%type.

Notation RVS := (fun (vs_st1 vs_st2 : VS) => 
  (RV vs_st1.1 vs_st2.1 /\ RS vs_st1.2 vs_st2.2)).
Notation RFVS := (fun (fvs1 fvs2 : FVS) => 
  (fvs1.1 = fvs2.1 /\ RVS fvs1.2 fvs2.2)).
Notation RC := (fun c1 c2: cmd => c2 = Tr_cmd c1).
Notation RFunDef := (fun f1 f2: FunDef => f2 = Tr_FunDef f1).

Context (rvs_def : PR VS = RVS)
        (rfvs_def : PR FVS = RFVS)
        (rc_def : PR cmd = RC)
        (rfundef_def : PR FunDef = RFunDef).


Section GEN_Err.

Context (HasErr: ErrState -< E).   

(* DE: relation between call events, i.e. over inputs of type 
# (funname * (values * estate)) *)
Definition TR_D_DE {T1 T2} (d1 : callE FVS VS T1)
                           (d2 : callE FVS VS T2) : Prop :=
  match (d1, d2) with
  | (Call f1, Call f2) => RFVS f1 f2 end.               

(* DE: relation between call outputs, i.e. (values * estate) *)
Program Definition VR_D_DE {T1 T2} (d1 : callE FVS VS T1) (t1: T1)
                                 (d2 : callE FVS VS T2) (t2: T2) : Prop.
  dependent destruction d1.
  dependent destruction d2.
  exact (RVS t1 t2).
Defined.

Lemma comp_gen_ok_DE (fn: funname) (vs1 vs2: values) (st1 st2: estate) :
  RV vs1 vs2 ->
  RS st1 st2 ->
  @rutt (callE FVS VS +' E) (callE FVS VS +' E) VS VS 
    (TR_E (callE FVS VS +' E))
    (VR_E (callE FVS VS +' E))
    (fun a1 a2 => @VR_D_DE _ _ (Call (fn, (vs1, st1))) a1
                               (Call (fn, (vs2, st2))) a2)  
    (evalE_fun pr1 (fn, (vs1, st1))) (evalE_fun pr2 (fn, (vs2, st2))).
  intros.
  unfold evalE_fun; simpl.
Admitted. 
  
(* ME: relation between FCState events *)
Definition TR_D_ME {T1 T2} (d1 : FCState T1)
                           (d2 : FCState T2) : Prop :=
  match (d1, d2) with
  | (FLCode c1 st1, FLCode c2 st2) => RC c1 c2 /\ RS st1 st2
  | (FFCall xs1 fn1 es1 st1, FFCall xs2 fn2 es2 st2) =>
      xs2 = map tr_lval xs1 /\ fn1 = fn2 /\ es2 = map tr_expr es1 /\ RS st1 st2
  | _ => False   
  end.               

(* ME: relation between FCState event outputs, i.e. over estate *)
Program Definition VR_D_ME {T1 T2}
  (d1 : FCState T1) (t1: T1) (d2 : FCState T2) (t2: T2) : Prop.
  remember d1 as D1.
  remember d2 as D2.
  dependent destruction d1.
  - dependent destruction d2.
    + exact (RS t1 t2).
    + exact (False).
  - dependent destruction d2.
    + exact (False).
    + exact (RS t1 t2).
Defined.      

Program Definition TR_DE_ME : prerel (FCState +' E) (FCState +' E) :=
  sum_prerel (@TR_D_ME) (TR_E E).

Program Definition VR_DE_ME : postrel (FCState +' E) (FCState +' E) :=
  sum_postrel (@VR_D_ME) (VR_E E).

Context (fcstate_t_def : TR_E (FCState +' E) = TR_DE_ME).
Context (fcstate_v_def : VR_E (FCState +' E) = VR_DE_ME).

Lemma comp_gen_ok_ME (fn: funname)
  (xs1 xs2: lvals) (es1 es2: pexprs) (st1 st2: estate) :
  xs2 = map tr_lval xs1 ->
  es2 = map tr_expr es1 -> 
  RS st1 st2 ->
  @rutt (FCState +' E) _ _ _ (TR_E _) (VR_E _)
    (fun a1 a2 => @VR_D_ME _ _ (FFCall xs1 fn es1 st1) a1
                             (FFCall xs2 fn es2 st2) a2)  
    (meval_fcall pr1 xs1 fn es1 st1) (meval_fcall pr2 xs2 fn es2 st2).
  intros.
  unfold meval_fcall; simpl.
  
  eapply rutt_bind with (RR := RV).
  unfold err_eval_Args.
  (* OK *)
  admit.

  intros.
  eapply rutt_bind with (RR := RS).
  unfold err_init_state.
  (* OK *)
  admit.

  intros.
  eapply rutt_bind with (RR := RC).
  unfold err_get_FunCode.
  (* OK *)
  admit.

  intros.
  inv H4.
  eapply rutt_bind with (RR := RS).
  eapply rutt_trigger; simpl.
  rewrite fcstate_t_def.
  unfold TR_DE_ME.
  econstructor.
  unfold TR_D_ME.
  split; auto.

  intros.
  (* OK *)
  admit.

  intros.
  eapply rutt_bind with (RR := RV).
  unfold err_return_val.
  (* OK *)
  admit.

  intros.
  unfold err_reinstate_caller.
  (* OK *)
  admit.
Admitted. 



(* Inductive lemma *)
Lemma rutt_cmd_tr_ME_step (cc: cmd) (st1 st2: estate) : 
  RS st1 st2 ->
  @rutt (FCState +' E) _ _ _
    (sum_prerel (@TR_D_ME) (TR_E E))
    (sum_postrel (@VR_D_ME) (VR_E E))
    RS (st_cmd_map_r (meval_instr pr1) cc st1)
    (st_cmd_map_r (meval_instr pr2) (Tr_cmd cc) st2).
  simpl; intros.

  set (Pr := fun (i: instr_r) => forall ii st1 st2, RS st1 st2 -> 
     @rutt (FCState +' E) _ _ _
    (sum_prerel (@TR_D_ME) (TR_E E))
    (sum_postrel (@VR_D_ME) (VR_E E))
    RS 
    (st_cmd_map_r (meval_instr pr1) ((MkI ii i) :: nil) st1)
    (st_cmd_map_r (meval_instr pr2) ((Tr_instr (MkI ii i)) :: nil) st2)).

  set (Pi := fun (i: instr) => forall st1 st2, RS st1 st2 -> 
     @rutt (FCState +' E) _ _ _
    (sum_prerel (@TR_D_ME) (TR_E E))
    (sum_postrel (@VR_D_ME) (VR_E E))
    RS 
    (st_cmd_map_r (meval_instr pr1) (i :: nil) st1)
    (st_cmd_map_r (meval_instr pr2) ((Tr_instr i) :: nil) st2)).

  set (Pc := fun (c: cmd) => forall st1 st2, RS st1 st2 -> 
     @rutt (FCState +' E) _ _ _
    (sum_prerel (@TR_D_ME) (TR_E E))
    (sum_postrel (@VR_D_ME) (VR_E E))
    RS 
    (st_cmd_map_r (meval_instr pr1) c st1)
    (st_cmd_map_r (meval_instr pr2) (Tr_cmd c) st2)).

  revert H.
  revert st1 st2.
  revert cc.
  apply (cmd_Ind Pr Pi Pc); rewrite /Pr /Pi /Pc; simpl; eauto.

  intros.
  { eapply rutt_Ret; eauto. }
  { intros.
    destruct i; simpl.
    eapply rutt_bind with (RR := RS); simpl in *.

    specialize (H st1 st2 H1).
    (* PROBLEM: we need to invert H. probably need a coinductive proof *)
    admit.

    intros.
    auto.
  }
Admitted.     

  
(* Here we apply the inductive lemma and comp_gen_ok *)
Lemma rutt_cmd_tr_ME (cc: cmd) (st1 st2: estate) : 
  RS st1 st2 ->
  @rutt E _ _ _ 
    (TR_E _) (VR_E _) RS
    (mevalE_cmd pr1 cc st1) (mevalE_cmd pr2 (Tr_cmd cc) st2).
  intros.
  unfold mevalE_cmd; simpl.
  eapply interp_mrec_rutt.
  intros.
  instantiate (3 := @TR_D_ME).
  instantiate (1 := @VR_D_ME).
  unfold meval_cstate.
  destruct d1.
  unfold TR_D_ME in H0.
  destruct d2; try intuition.
  inv H1; simpl.
  eapply rutt_cmd_tr_ME_step; eauto. 
   
  unfold TR_D_ME in H0.
  destruct d2; simpl in *; try intuition.
  inv H0.  
  set CC := (comp_gen_ok_ME f0 xs _ es _ _ _ erefl erefl H4).
  setoid_rewrite fcstate_t_def in CC.
  setoid_rewrite fcstate_v_def in CC.
  exact CC.
    
  simpl.
  eapply rutt_cmd_tr_ME_step; eauto. 
Qed.   

End GEN_Err.


Section GEN_Flat.
  
(* DE: relation between call events, i.e. over inputs of type #
(funname * (values * estate)) ### (similar to TR_D_DE, only difference
is in the call type) *)
Definition TR_D_DE_ex {T1 T2} (d1 : callE FVS (exec VS) T1)
                              (d2 : callE FVS (exec VS) T2) : Prop :=
  match (d1, d2) with
  | (Call f1, Call f2) => RFVS f1 f2 end.               


Section Asym_test.

(* DF: asymmetric relation between call event outputs, i.e. over #
(exec (values * estate)) *)
Definition exec_RVS (pp1 pp2 : exec VS) : Prop :=
  match (pp1, pp2) with
  | (Ok vt1, Ok vt2) => RVS vt1 vt2
  | (Error _, _) => True
  | _ => False end.
Context (exec_rvs_def : PR (exec VS) = exec_RVS).  

(* DF: asymmetric relation between call outputs, i.e. over ##########
(exec (values * estate)) *)
Program Definition VR_D_DE_ex {T1 T2}
  (d1 : callE FVS (exec VS) T1) (t1: T1)
  (d2 : callE FVS (exec VS) T2) (t2: T2) : Prop.
  dependent destruction d1.
  dependent destruction d2.
  exact (exec_RVS t1 t2).
Defined.

Definition exec_RS (p1 p2: exec estate) : Prop :=
  match (p1, p2) with
  | (Ok st1, Ok st2) => RS st1 st2
  | (Error _, _) => True                           
  | _ => False end.                         

Definition exec_RV (p1 p2: exec values) : Prop :=
  match (p1, p2) with
  | (Ok vv1, Ok vv2) => RV vv1 vv2
  | (Error _, _) => True                           
  | _ => False end.                         

Definition exec_RC (pc1 pc2: exec cmd) : Prop :=
  match (pc1, pc2) with
  | (Ok c1, Ok c2) => RC c1 c2
  | (Error _, _) => True                           
  | _ => False end.                         

Definition exec_RFunDef (pf1 pf2: exec FunDef) : Prop :=
  match (pf1, pf2) with
  | (Ok f1, Ok f2) => RFunDef f1 f2
  | (Error _, _) => True                           
  | _ => False end.                         

Lemma comp_gen_ok_DF_asym (fn: funname) (vs1 vs2: values) (st1 st2: estate) :
  RV vs1 vs2 ->
  RS st1 st2 ->
  @rutt E E
    (exec VS) (exec VS)
    (TR_E E) (VR_E E)  
    (fun (a1 a2: exec VS) => @VR_D_DE_ex _ _ (Call (fn, (vs1, st1))) a1
                             (Call (fn, (vs2, st2))) a2)  
    (peval_fcall_body pr1 (fn, (vs1, st1)))
    (peval_fcall_body pr2 (fn, (vs2, st2))).
  intros.
  unfold peval_fcall_body.
  unfold rec.

  eapply mrec_rutt.
  
  instantiate (1:= @TR_D_DE_ex).

  2: { unfold TR_D_DE_ex; simpl.
       split; eauto.
  }

  intros; simpl.
  
  destruct d1 as [f1].
  destruct d2 as [f2].
  simpl in *. 
  destruct f1 as [fn1 [v1 stt1]].
  destruct f2 as [fn2 [v2 stt2]].
  unfold TR_D_DE_ex in H1.
  destruct H1 as [H1 [H2 H3]].
  simpl in *.
  inv H1; simpl.
  
  eapply rutt_bind with (RR := exec_RS).
  - unfold ret_init_state.
    unfold exec_RS; simpl.
    eapply rutt_bind with (RR := exec_RFunDef).
    unfold ret_get_FunDef.
    eapply rutt_Ret.
    (* OK missing hyp about get_FunDef *)
    admit.

    unfold exec_RFunDef; simpl ; intros.
    destruct r1; simpl.
    { destruct r2; simpl.
      inv H1.
      eapply rutt_Ret.
      (* OK missing hyp about init_state *)
      admit.
      intuition.
    }
    { destruct r2; simpl.
      eapply rutt_Ret; eauto. 
      eapply rutt_Ret; eauto.
    }  
  
  - intros.
    unfold exec_RS in H1; simpl in *.
    destruct r1; try congruence.
    { destruct r2; try congruence.

      { eapply rutt_bind with (RR := exec_RC).

        { unfold exec_RS in H1.
          unfold ret_get_FunCode.
          unfold ret_get_FunDef.
          unfold get_FunDef.
          simpl.
          (* OK missing hyp about funCode *)
          admit.
        }  
        
        { intros.
          destruct r1.
          { destruct r2.
            
            { unfold exec_RC in H4; simpl in *.
              inv H4.
              eapply rutt_bind with (RR := exec_RS);
                unfold exec_RVS.

              { (* RR OK recursive lemma needed *)
                admit.
              }
              { simpl; intros.
                unfold exec_RS in H4.

                destruct r1.

                { destruct r2.

                  { eapply rutt_bind with (RR := exec_RV);
                    unfold exec_RVS.  

                    { (* OK return val lemma needed *)
                      admit.
                    }  

                    { intros.
                      unfold exec_RV in H5.

                      destruct r1.
                      { destruct r2.
                        eapply rutt_Ret; eauto.
                        intuition.
                      }

                      { destruct r2.
                        { eapply rutt_Ret; eauto.
                        }
                        { eapply rutt_Ret; eauto.
                        }
                      }
                    }
                  }

                  { intuition. }
                }

                destruct r2.
                { 
                  unfold ret_return_val.
                  simpl.
                  setoid_rewrite bind_bind.
                  simpl.
                  unfold ret_get_FunDef.
                  setoid_rewrite bind_ret_l.

                  destruct (o2r ErrType (get_FunDef pr2 fn2)).
                  setoid_rewrite bind_ret_l.

                  destruct (get_var_is (~~ direct_call) (evm e2) (f_res f));
                    simpl.
                  { 
                    destruct (mapM2 ErrType dc_truncate_val (f_tyout f) l0);
                      simpl.
                    { eapply rutt_Ret; eauto.
                    }
                    { eapply rutt_Ret; auto. }
                  }
                  
                  { eapply rutt_Ret; auto. }

                  { setoid_rewrite bind_ret_l.
                    eapply rutt_Ret; auto.
                  }
                }
                
                { eapply rutt_Ret; auto. }
              }
            }  
                
            { unfold exec_RC in H4.
              intuition.
            }
          }

          { destruct r2; unfold exec_RC in H4.

            (* PROBLEM: in order to make it work with the current
               relation, here we would need to prove *recursively*
               that the right hand-side terminates. But this is
               generally not possible. hence, in the current context
               the asymmetric relation is not sustainable *)
            admit.
            admit.
          }    
        }
      }
        
      { intuition. }
    }
 
    { destruct r2.

      { unfold ret_get_FunCode.
        (* PROBLEM: heading for the same problem *)
        admit.
      }
      { eapply rutt_Ret; auto. }
    }
Admitted.  
   
End Asym_test.


Section Sym_test.

(* DF: symmetric relation between call event outputs, i.e. over #
(exec (values * estate)) *)
Local Definition exec_RVS_s (pp1 pp2 : exec VS) : Prop :=
  match (pp1, pp2) with
  | (Ok vt1, Ok vt2) => RVS vt1 vt2
  | (Error _, Error _) => True                          
  | _ => False end.
Context (exec_rvs_def : PR (exec VS) = exec_RVS_s).  

(* DF: asymmetric relation between call outputs, i.e. over ##########
(exec (values * estate)) *)
Program Definition VR_D_DE_ex_s {T1 T2}
  (d1 : callE FVS (exec VS) T1) (t1: T1)
  (d2 : callE FVS (exec VS) T2) (t2: T2) : Prop.
  dependent destruction d1.
  dependent destruction d2.
  exact (exec_RVS_s t1 t2).
Defined.

Definition exec_RS_s (p1 p2: exec estate) : Prop :=
  match (p1, p2) with
  | (Ok st1, Ok st2) => RS st1 st2
  | (Error _, Error _) => True                           
  | _ => False end.                         

Definition exec_RV_s (p1 p2: exec values) : Prop :=
  match (p1, p2) with
  | (Ok vv1, Ok vv2) => RV vv1 vv2
  | (Error _, Error _) => True                           
  | _ => False end.                         

Definition exec_RC_s (pc1 pc2: exec cmd) : Prop :=
  match (pc1, pc2) with
  | (Ok c1, Ok c2) => RC c1 c2
  | (Error _, Error _) => True                           
  | _ => False end.                         

Definition exec_RFunDef_s (pf1 pf2: exec FunDef) : Prop :=
  match (pf1, pf2) with
  | (Ok f1, Ok f2) => RFunDef f1 f2
  | (Error _, Error _) => True                           
  | _ => False end.                         



Lemma rutt_cmd_tr_DF_step (cc: cmd) (st1 st2: estate) :  
   RS st1 st2 ->
              rutt (sum_prerel (@TR_D_DE_ex) (TR_E E))
    (sum_postrel (@VR_D_DE_ex_s) (VR_E E)) exec_RS_s
    (pst_cmd_map_r (peval_instr_call pr1) cc st1)
    (pst_cmd_map_r (peval_instr_call pr2) (Tr_cmd cc) st2).
  simpl; intros.
  
  set (Pr := fun (i: instr_r) => forall ii st1 st2, RS st1 st2 -> 
     @rutt (callE (funname * (values * estate)) (exec (values * estate))
                +' E) _ _ _
    (sum_prerel (@TR_D_DE_ex) (TR_E E))
    (sum_postrel (@VR_D_DE_ex_s) (VR_E E))
    exec_RS_s 
    (pst_cmd_map_r (peval_instr_call pr1) ((MkI ii i) :: nil) st1)
    (pst_cmd_map_r (peval_instr_call pr2) ((Tr_instr (MkI ii i)) :: nil) st2)).

  set (Pi := fun (i: instr) => forall st1 st2, RS st1 st2 -> 
     @rutt (callE (funname * (values * estate)) (exec (values * estate))
                +' E) _ _ _
    (sum_prerel (@TR_D_DE_ex) (TR_E E))
    (sum_postrel (@VR_D_DE_ex_s) (VR_E E))
    exec_RS_s 
    (pst_cmd_map_r (peval_instr_call pr1) (i :: nil) st1)
    (pst_cmd_map_r (peval_instr_call pr2) ((Tr_instr i) :: nil) st2)).

  set (Pc := fun (c: cmd) => forall st1 st2, RS st1 st2 -> 
     @rutt (callE (funname * (values * estate)) (exec (values * estate))
                +' E) _ _ _
    (sum_prerel (@TR_D_DE_ex) (TR_E E))
    (sum_postrel (@VR_D_DE_ex_s) (VR_E E))
    exec_RS_s 
    (pst_cmd_map_r (peval_instr_call pr1) c st1)
    (pst_cmd_map_r (peval_instr_call pr2) (Tr_cmd c) st2)).

  revert H.
  revert st1 st2.
  revert cc.
  apply (cmd_Ind Pr Pi Pc); rewrite /Pr /Pi /Pc; simpl; eauto.

  intros.
  { eapply rutt_Ret; eauto. }
  { intros.
    destruct i; simpl.
    eapply rutt_bind with (RR := exec_RS_s); simpl in *.

    specialize (H st1 st2 H1).
    (* PROBLEM: we need to invert H. probably need a coinductive proof *)
    admit.
  
    unfold exec_RS_s; simpl; intros.
    destruct r1.
    { destruct r2; simpl; try intuition; auto. }
    
    { destruct r2; simpl; try intuition; auto.
      eapply rutt_Ret; auto.
    }
  }  
Admitted.   

Lemma comp_gen_ok_DF_sym (fn: funname) (vs1 vs2: values) (st1 st2: estate) :
  RV vs1 vs2 ->
  RS st1 st2 ->
  @rutt E E
    (exec VS) (exec VS)
    (TR_E E) (VR_E E)  
    (fun (a1 a2: exec VS) => @VR_D_DE_ex_s _ _ (Call (fn, (vs1, st1))) a1
                             (Call (fn, (vs2, st2))) a2)  
    (peval_fcall_body pr1 (fn, (vs1, st1)))
    (peval_fcall_body pr2 (fn, (vs2, st2))).
  intros.
  unfold peval_fcall_body.
  unfold rec.

  eapply mrec_rutt.
  
  instantiate (1:= @TR_D_DE_ex).

  2: { unfold TR_D_DE_ex; simpl.
       split; eauto.
  }

  intros; simpl.
  
  destruct d1 as [f1].
  destruct d2 as [f2].
  simpl in *. 
  destruct f1 as [fn1 [v1 stt1]].
  destruct f2 as [fn2 [v2 stt2]].
  unfold TR_D_DE_ex in H1.
  destruct H1 as [H1 [H2 H3]].
  simpl in *.
  inv H1; simpl.
  
  eapply rutt_bind with (RR := exec_RS_s).
  - unfold ret_init_state.
    unfold exec_RS_s; simpl.
    eapply rutt_bind with (RR := exec_RFunDef_s).
    unfold ret_get_FunDef.
    eapply rutt_Ret.
    unfold exec_RFunDef_s; simpl.
    (* OK missing hyp about get_FunDef *)
    admit.

    unfold exec_RFunDef; simpl ; intros.
    destruct r1; simpl.
    { destruct r2; simpl.
      inv H1.
      eapply rutt_Ret.
      (* OK missing hyp about init_state *)
      admit.
      intuition.
    }
    { destruct r2; simpl.
      unfold exec_RFunDef_s in H1.
      intuition.
      eapply rutt_Ret; eauto. 
    }  
  
  - unfold exec_RS_s; simpl; intros.
    destruct r1; try congruence.
    { destruct r2; try congruence.

      { unfold ret_get_FunCode.
        unfold ret_get_FunDef.
        simpl.

        setoid_rewrite bind_bind; simpl.
        setoid_rewrite bind_ret_l.

        eapply rutt_bind with (RR := exec_RC_s); simpl.
        { (* OK missing hyp about get_FunDef *)
          admit.
        }
        { unfold exec_RC_s; simpl; intros.
          
          destruct r1.
          { destruct r2; try congruence.
            inv H4.

            eapply rutt_bind with (RR := exec_RS_s);
                unfold exec_RVS.
            
              { (* RR recursive lemma applied *)
                 eapply rutt_cmd_tr_DF_step; eauto.
              }
              { unfold exec_RS_s; simpl; intros.

                destruct r1.

                { destruct r2; try congruence.

                  { eapply rutt_bind with (RR := exec_RV_s);
                    unfold exec_RVS_s.  

                    { (* OK return val lemma needed *)
                      admit.
                    }  

                    { unfold exec_RV_s; simpl; intros.

                      destruct r1.
                      { destruct r2.
                        eapply rutt_Ret; eauto.
                        intuition.
                      }

                      { destruct r2.
                        { intuition. }
                        { eapply rutt_Ret; eauto.
                        }
                      }
                    }
                  }

                  { intuition. }
                }

                destruct r2.
                { intuition. }

                { eapply rutt_Ret.
                  unfold exec_RVS_s; simpl; auto.
                }
              }
              { intuition. }
          }

          destruct r2.
          { intuition. }

          eapply rutt_Ret.
          unfold exec_RVS_s; simpl; auto.
        }
      }
      { intuition. }
    }
    
    destruct r2.

    { intuition. }

    { eapply rutt_Ret.
      unfold exec_RVS_s; auto.
    }
Admitted. 

(* NOTE: double recursion requires two separate inductive lemmas (both
rutt_cmd_tr and comp_gen_ok are inductive) *)
Lemma rutt_cmd_tr_DF_sym (cc: cmd) (st1 st2: estate) : 
  RS st1 st2 ->
  @rutt (PCState +' E) _ _ _ 
    (TR_E _) (VR_E _) exec_RS_s
    (peval_flat_cmd pr1 cc st1) (peval_flat_cmd pr2 (Tr_cmd cc) st2).
  intros.
  unfold peval_flat_cmd; simpl.  
  (* RR recursive lemma needed, with peval_instr instead of
  peval_instr_call *)
  admit.
Admitted.   
  
End Sym_test.
                   

Definition TR_D_MF {T1 T2} (d1 : PCState T1)
                           (d2 : PCState T2) : Prop :=
  match (d1, d2) with
  | (PLCode c1 st1, PLCode c2 st2) => RC c1 c2 /\ RS st1 st2
  | (PFCall xs1 fn1 es1 st1, PFCall xs2 fn2 es2 st2) =>
      xs2 = map tr_lval xs1 /\ fn1 = fn2 /\ es2 = map tr_expr es1 /\ RS st1 st2
  | _ => False   
  end.               

Program Definition VR_D_MF {T1 T2} (d1 : PCState T1) (t1: T1)
                                 (d2 : PCState T2) (t2: T2) : Prop.
  dependent destruction d1.
  - dependent destruction d2.
    + exact (exec_RS_s t1 t2).
    + exact (False).
  - dependent destruction d2.
    + exact (False).
    + exact (exec_RS_s t1 t2).
Defined.      

Program Definition TR_DE_MF0 {T1 T2} (dd1 : PCState T1 + E T1)
                            (dd2 : PCState T2 + E T2) : Prop :=
  match (dd1, dd2) with
  | (inl d1, inl d2) => TR_D_MF d1 d2
  | (inr e1, inr e2) => TR_E _ _ _ e1 e2
  | _ => False end.                             

Program Definition TR_DE_MF1 (T1 T2: Type) (dd1 : (PCState +' E) T1)
                            (dd2 : (PCState +' E) T2) : Prop :=
  match (dd1, dd2) with
  | (inl1 d1, inl1 d2) => TR_D_MF d1 d2
  | (inr1 e1, inr1 e2) => TR_E _ _ _ e1 e2
  | _ => False end.                             

Program Definition VR_DE_MF1 (T1 T2: Type)
  (dd1 : (PCState +' E) T1) (t1: T1)
  (dd2 : (PCState +' E) T2) (t2: T2) : Prop :=
  match (dd1, dd2) with
  | (inl1 d1, inl1 d2) => VR_D_MF d1 t1 d2 t2
  | (inr1 e1, inr1 e2) => VR_E _ _ _ e1 t1 e2 t2
  | _ => False end.                             

Program Definition TR_DE_MF : prerel (PCState +' E) (PCState +' E) :=
  sum_prerel (@TR_D_MF) (TR_E E).

Program Definition VR_DE_MF : postrel (PCState +' E) (PCState +' E) :=
  sum_postrel (@VR_D_MF) (VR_E E).

Context (pcstate_t_def : TR_E (PCState +' E) = TR_DE_MF).
Context (pcstate_v_def : VR_E (PCState +' E) = VR_DE_MF).

(*
Definition exec_rvs_def (T1 T2: Type) :
  TR_E (PCState +' E) T1 T2 = @TR_DE_MF T1 T2. 
*)

(* NOTE: it seems this lemma does not actually require induction *)
Lemma comp_gen_ok_MF (fn: funname)
  (xs1 xs2: lvals) (es1 es2: pexprs) (st1 st2: estate) :
  xs2 = map tr_lval xs1 ->
  es2 = map tr_expr es1 -> 
  RS st1 st2 ->
  @rutt (PCState +' E) _ _ _ 
    (TR_E _) (VR_E _)
    (fun a1 a2 => @VR_D_MF _ _ (PFCall xs1 fn es1 st1) a1
                             (PFCall xs2 fn es2 st2) a2)  
    (pmeval_fcall pr1 xs1 fn es1 st1) (pmeval_fcall pr2 xs2 fn es2 st2).
  intros.
  unfold pmeval_fcall; simpl.

  eapply rutt_bind with (RR := exec_RFunDef_s).

  unfold ret_get_FunDef.
  eapply rutt_Ret.
  unfold exec_RFunDef_s.
  (* OK missing hyp about get_FunDef *)
  admit.
  
  unfold exec_RFunDef_s; simpl ; intros.
  destruct r1; simpl.
  2: { destruct r2.
       intuition.
       eapply rutt_Ret; auto.
     }  
   { destruct r2; simpl; try intuition.       
     inv H2.
     eapply rutt_bind with (RR := exec_RV_s); eauto.
     unfold ret_eval_Args.
     eapply rutt_bind with (RR := exec_RFunDef_s); simpl.
     (* OK missing hyp about get_FunDef *)
     admit.
     (* OK *)
     admit.
     
     unfold exec_RV_s; simpl; intros.
     destruct r1.
     { destruct r2.
       { eapply rutt_bind with (RR := exec_RS_s); eauto.
         (* OK missing hyp about init_state *)
         admit.

         unfold exec_RS_s; simpl; intros.
         destruct r1.
         { destruct r2; try intuition.
           eapply rutt_bind with (RR:= exec_RC_s).
           unfold ret_get_FunCode.
           simpl.
           eapply rutt_bind with (RR:= exec_RFunDef_s).
           unfold ret_get_FunDef.
           eapply rutt_Ret; auto.
           unfold exec_RFunDef_s; simpl.
           (* OK missing hyp about get_FunDef *)
           admit.

           unfold exec_RFunDef_s; simpl; intros.
           destruct r1.
           { destruct r2; try intuition.
             eapply rutt_Ret; eauto.
             unfold exec_RC_s.
             unfold Tr_FunDef in H2.
             destruct f1.
             destruct f0.
             inv H2.
             simpl; auto.
           }

           { destruct r2.
             intuition.
             eapply rutt_Ret; eauto.
           }
           
           unfold exec_RC_s; simpl; intros.
           destruct r1.
           { destruct r2; try intuition.
             inv H2.
             eapply rutt_bind with (RR:= exec_RS_s); simpl.
             { eapply rutt_trigger.
               { rewrite pcstate_t_def.              
                 unfold TR_DE_MF.
                 econstructor.
                 unfold TR_D_MF.
                 split; auto.
               }
               simpl; intros.
               unfold exec_RS_s; simpl.
               rewrite pcstate_v_def in H2.
               unfold VR_DE_MF in H2.
               dependent destruction H2.
             (*  unfold VR_D_MF in H2. *)
               unfold exec_RS_s in H2.
               destruct t1; auto.
             }

             unfold exec_RS_s; simpl; intros.
             destruct r1.
             { destruct r2; try intuition.
               eapply rutt_bind with (RR:= exec_RV_s).
               unfold ret_return_val.
               eapply rutt_bind with (RR := exec_RFunDef_s).
               unfold ret_get_FunDef.
               eapply rutt_Ret; auto.
               unfold exec_RFunDef_s; simpl.
              (* OK missing hyp about get_FunDef *)
              admit.

              unfold exec_RFunDef_s; simpl; intros.
              destruct r1.
              { destruct r2; try intuition.
                eapply rutt_Ret; eauto.
                unfold exec_RV_s; simpl.
                (* OK missing hyp about truncate *)
                admit.
              }
              { destruct r2; try intuition.
                eapply rutt_Ret; auto.
              }

              unfold exec_RV_s; simpl; intros.
              destruct r1.
              { destruct r2; try intuition.
                (* missing hyp about reinstate_caller *)
                admit.
              }
              { destruct r2; try intuition.
                eapply rutt_Ret; auto.
              }                 
            }

            destruct r2; try intuition.
            eapply rutt_Ret; auto. 
           }

           destruct r2; try intuition.
           eapply rutt_Ret; auto. 
         }

         destruct r2; intuition.
         eapply rutt_Ret; auto. 
       }
  
      { intuition. }
    }

    destruct r2; intuition.
    eapply rutt_Ret; auto. 
   }   
Admitted. 


(* Inductive lemma *)
Lemma rutt_cmd_tr_MF_step (cc: cmd) (st1 st2: estate) : 
  RS st1 st2 ->
  @rutt (PCState +' E) _ _ _
    (sum_prerel (@TR_D_MF) (TR_E E))
    (sum_postrel (@VR_D_MF) (VR_E E))
    exec_RS_s 
    (pst_cmd_map_r (pmeval_instr pr1) cc st1)
    (pst_cmd_map_r (pmeval_instr pr2) (Tr_cmd cc) st2).
  simpl; intros.

  set (Pr := fun (i: instr_r) => forall ii st1 st2, RS st1 st2 -> 
     @rutt (PCState +' E) _ _ _
    (sum_prerel (@TR_D_MF) (TR_E E))
    (sum_postrel (@VR_D_MF) (VR_E E))
    exec_RS_s 
    (pst_cmd_map_r (pmeval_instr pr1) ((MkI ii i) :: nil) st1)
    (pst_cmd_map_r (pmeval_instr pr2) ((Tr_instr (MkI ii i)) :: nil) st2)).

  set (Pi := fun (i: instr) => forall st1 st2, RS st1 st2 -> 
     @rutt (PCState +' E) _ _ _
    (sum_prerel (@TR_D_MF) (TR_E E))
    (sum_postrel (@VR_D_MF) (VR_E E))
    exec_RS_s 
    (pst_cmd_map_r (pmeval_instr pr1) (i :: nil) st1)
    (pst_cmd_map_r (pmeval_instr pr2) ((Tr_instr i) :: nil) st2)).

  set (Pc := fun (c: cmd) => forall st1 st2, RS st1 st2 -> 
     @rutt (PCState +' E) _ _ _
    (sum_prerel (@TR_D_MF) (TR_E E))
    (sum_postrel (@VR_D_MF) (VR_E E))
    exec_RS_s 
    (pst_cmd_map_r (pmeval_instr pr1) c st1)
    (pst_cmd_map_r (pmeval_instr pr2) (Tr_cmd c) st2)).

  revert H.
  revert st1 st2.
  revert cc.
  apply (cmd_Ind Pr Pi Pc); rewrite /Pr /Pi /Pc; simpl; eauto.

  intros.
  { eapply rutt_Ret; eauto. }
  { intros.
    destruct i; simpl.
    eapply rutt_bind with (RR := exec_RS_s); simpl in *.

    specialize (H st1 st2 H1).
    (* PROBLEM: we need to invert H. probably need a coinductive proof *)
    admit.

    unfold exec_RS_s; simpl; intros.
    destruct r1.
    { destruct r2; simpl; try intuition; auto. }
    
    { destruct r2; simpl; try intuition; auto.
      eapply rutt_Ret; auto.
    }
  }  

  { intros.
    eapply rutt_bind with (RR := exec_RS_s).
    unfold ret_mk_AssgnE.
    eapply rutt_Ret; simpl; auto.
    unfold exec_RS_s; simpl.
    (* OK admit *)
    admit.

    unfold exec_RS_s; simpl; intros.
    destruct r1.
    destruct r2; try intuition.
    eapply rutt_Ret; eauto.

    destruct r2; try intuition.
    eapply rutt_Ret; eauto.
  }

  { intros.
    eapply rutt_bind with (RR := exec_RS_s).
    unfold ret_mk_OpnE.
    eapply rutt_Ret; simpl; auto.
    unfold exec_RS_s; simpl.
    (* OK admit *)
    admit.

    unfold exec_RS_s; simpl; intros.
    destruct r1.
    destruct r2; try intuition.
    eapply rutt_Ret; eauto.

    destruct r2; try intuition.
    eapply rutt_Ret; eauto.
  }

  { intros.
    eapply rutt_bind with (RR := exec_RS_s).
    unfold ret_mk_SyscallE.
    eapply rutt_Ret; simpl; auto.
    unfold exec_RS_s; simpl.
    (* OK admit *)
    admit.

    unfold exec_RS_s; simpl; intros.
    destruct r1.
    destruct r2; try intuition.
    eapply rutt_Ret; eauto.

    destruct r2; try intuition.
    eapply rutt_Ret; eauto.
  }

  { intros.
    eapply rutt_bind with (RR := exec_RS_s).
    eapply rutt_bind with (RR := eq).
    
    unfold ret_mk_EvalCond.
    (* OK *)
    admit.

    intros.
    inv H2; simpl.
    destruct r2; simpl.
    destruct b; simpl.

    eapply H; eauto.
    eapply H0; eauto.

    eapply rutt_Ret; auto.
    unfold exec_RS_s; simpl; auto.

    unfold exec_RS_s; simpl; intros.
    destruct r1.
    destruct r2; try intuition.
    eapply rutt_Ret; auto.
    destruct r2; try intuition.
    eapply rutt_Ret; auto.
  }

  { intros.
    eapply rutt_bind with (RR := exec_RS_s); simpl.
    destruct rn.
    destruct p; simpl.    
    eapply rutt_bind with (RR := eq); simpl.
    unfold ret_mk_EvalBound; simpl.
    (* OK *)
    admit.

    intros.
    inv H1.
    destruct r2.
    eapply rutt_bind with (RR := eq); simpl.
    unfold ret_mk_EvalBound; simpl.
    (* OK *)
    admit.

    intros.
    inv H1.
    destruct r2.

    revert H0.
    revert st1 st2.
    induction (wrange d z z0); simpl; intros.
    { eapply rutt_Ret; eauto. }
    { eapply rutt_bind with (RR:= exec_RS_s); simpl.
      unfold ret_mk_WriteIndex.
      eapply rutt_Ret; eauto.
      (* OK *)
      admit.

      unfold exec_RS_s; simpl; intros.
      destruct r1.
      { destruct r2; try intuition.
        eapply rutt_bind with (RR := exec_RS_s).
        eapply H; eauto.
        unfold exec_RS_s; simpl; intros.
        destruct r1.
        destruct r2; try intuition. 
        (* eapply IHl.
           auto.  *)
        destruct r2; try intuition.
        eapply rutt_Ret; auto.
      }
      
      destruct r2; try intuition.
      eapply rutt_Ret; auto.
    }   
        
    eapply rutt_Ret; auto.
    intuition.
    eapply rutt_Ret; auto.
    intuition.

    unfold exec_RS_s; simpl; intros.
    destruct r1.
    destruct r2; try intuition.
    eapply rutt_Ret; auto.
    destruct r2; try intuition.
    eapply rutt_Ret; auto.
  }
    
  { intros.

    admit.
  }

  { intros.
    eapply rutt_bind with (RR := exec_RS_s).
    eapply rutt_trigger; simpl.
    econstructor.
    unfold TR_D_MF; simpl.
    split; eauto.

    unfold exec_RS_s; simpl; intros.
    destruct t1.
    destruct t2.
    (* OK *)
    admit.

    (* OK *)
    admit.

    destruct t2; auto.

    (* OK *)
    admit.

    unfold exec_RS_s; simpl; intros.
    destruct r1.
    destruct r2; try intuition.
    eapply rutt_Ret; auto.

    destruct r2; try intuition.
    eapply rutt_Ret; auto.
  }
Admitted.     
    

(* Here we apply the inductive lemma and comp_gen_ok *)
Lemma rutt_cmd_tr_MF (cc: cmd) (st1 st2: estate) : 
  RS st1 st2 ->
  @rutt E _ _ _ 
    (TR_E _) (VR_E _) exec_RS_s
    (pmeval_cmd pr1 cc st1) (pmeval_cmd pr2 (Tr_cmd cc) st2).
  intros.
  unfold pmeval_cmd; simpl.
  eapply interp_mrec_rutt.
  intros.
  instantiate (3 := @TR_D_MF).
  instantiate (1 := @VR_D_MF).
  unfold pmeval_cstate.
  destruct d1.
  unfold TR_D_MF in H0.
  destruct d2; try intuition.
  inv H1; simpl.
  eapply rutt_cmd_tr_MF_step; eauto.
   
  unfold TR_D_MF in H0.
  destruct d2; simpl in *; try intuition.
  inv H0.  
  set CC := (comp_gen_ok_MF f0 xs _ es _ _ _ erefl erefl H4).
  setoid_rewrite pcstate_t_def in CC.
  setoid_rewrite pcstate_v_def in CC.
  exact CC.
    
  simpl.
  eapply rutt_cmd_tr_MF_step; eauto.
Qed.   

End GEN_Flat.

End GEN_ErrAndFlat.

End TR_tests.

End TRANSF.

End WSW.

End Lang.
(** END *)

(*
Lemma rutt_cmd_tr_MF (cc: cmd) (st1 st2: estate) : 
  RS st1 st2 ->
  @rutt (PCState +' E) _ _ _ 
    (TR_E _) (VR_E _) exec_RS_s
    (pmeval_cmd pr1 cc st1) (pmeval_cmd pr2 (Tr_cmd cc) st2).
  intros.
  unfold pmeval_cmd; simpl.
  eapply interp_mrec_rutt.
  intros.
  instantiate (3 := @TR_D_MF).
  instantiate (1 := @VR_D_MF).
  unfold pmeval_cstate.
  destruct d1.
  unfold TR_D_MF in H0.
  destruct d2; try intuition.
  inv H1; simpl.
  (* RR recursive lemma needed *)
  admit.

  unfold TR_D_MF in H0.
  destruct d2; simpl in *; try intuition.

  rewrite pcstate_t_def.
  inv H0.
  
  set CC := (comp_gen_ok_MF f0 xs _ es _ _ _ erefl erefl H4).
  setoid_rewrite pcstate_t_def in CC.
  setoid_rewrite pcstate_v_def in CC.

Check @sum_prerel.
  
  assert ((sum_prerel (@TR_D_MF) TR_DE_MF) = TR_DE_MF).
  
(*   eapply comp_gen_ok_MF; eauto. *)
  admit.

  simpl.
  (* RR recursive lemma needed, as before *)
  admit.
Admitted. 
*)  

(*  eapply @interp_mrec_rutt.
  instantiate (1:= (TR_E (callE (FunDef * VS) (exec VS)))). *)

(*
Lemma comp_gen_okDF (fn: funname) (vs1 vs2: values) (st1 st2: estate) :
  RV vs1 vs2 ->
  RS st1 st2 ->
  @rutt (callE (FunDef * VS) (exec VS) +' E)
    (callE (FunDef * VS) (exec VS) +' E)
    (exec VS) (exec VS)
    (TR_E (callE (FunDef * VS) (exec VS) +' E))
    (VR_E (callE (FunDef * VS) (exec VS) +' E))
    (fun (a1 a2: exec VS) => @VR_DE' _ _ (Call (fn, (vs1, st1))) a1
                             (Call (fn, (vs2, st2))) a2)  
    (eval_fun_ pr1 fn vs1 st1) (eval_fun_ pr2 fn vs2 st2).
  intros.
  unfold eval_fun_; simpl.

  eapply rutt_bind with (RR := eq).
  admit.

  intros.
  inv H1; simpl.
  destruct r2.
  2: { eapply rutt_Ret.
       unfold exec_RVS.
       auto.
  }

  (**************************)

  unfold peval_fcall_body.

  unfold rec.

Check @rutt.
  
  unfold mrec.
  eapply interp_mrec_rutt.
  
(*  generalize (fun a1 : exec VS => [eta exec_RVS a1]).
  intro P.
*)
  move: (peval_fcall_body' pr1).
  intro body1.
  move: (peval_fcall_body' pr2).
  intro body2.

  assert (forall bd1 bd2, rutt (TR_E (callE (FunDef * VS) VS +' E))
    (VR_E (callE (FunDef * VS) VS +' E))
    (fun a1 : VS => [eta RVS a1]) (rec bd1 (f, (vs1, st1)))
    (rec bd2 (f, (vs2, st2)))).
  intros.
  unfold rec.
  unfold mrec.
  
  eapply @interp_mrec_rutt.
  
  move: (callE (FunDef * VS) (exec VS)).
  
  eapply @mrec_rutt.
  
  unfold peval_fcall_body'.
  unfold rec; simpl.
  unfold calling'; simpl.

  eapply @mrec_rutt.



  (***************************)
  
  eapply rutt_bind with (RR := exec_RS); eauto.
  admit.

  intros.
  unfold exec_RS in H1.
  destruct r1; try intuition.
  destruct r2; try intuition.
    
  2: { destruct r2; try intuition.
       admit.
  }

  eapply rutt_bind with (RR := exec_RS); eauto.
  
  admit.

  intros.
  destruct r1; try intuition.
  destruct r2; try intuition.
  
  2: { destruct r2; try intuition.
       admit.
  }

  eapply rutt_bind with (RR := exec_RV); eauto.
  admit.

  intros.
  destruct r1; try intuition.
  destruct r2; try intuition.

  admit.

  destruct r2; try intuition.
  admit.
Admitted. 
*)

(*
Context (hcomp : forall fn, code p2 fn = Tc (code p1 fn))
        (hcompe : forall s1 s2 e, RS s1 s2 -> 
           eval_cond s2 (te e) = eval_cond s1 e)
        (hcompci : forall s1 s2 ci, 
            RS s1 s2 -> 
            RS (eval_core s1 ci) (eval_core s2 (tci ci)))
        (hres : forall fn s1 s2,
            RS s1 s2 ->
            (* strengthened to equality *)
            (get_res s1 fn) = (get_res s2 fn))
        (hdests : forall s1 s2 v1 v2 xs,
            RS s1 s2 ->
            (* removed value condition *)
            RS (set_dests s1 xs v1) (set_dests s2 xs v2))
      (*  (hargs : forall s1 s2 es,
            RS s1 s2 ->
            RV (eval_args s1 es) (eval_args s2 es)) *)
        (strhargs : forall s1 s2 es,
            RS s1 s2 ->
            (eval_args s1 es) = (eval_args s2 es))
        (hinit : forall fn vs1 vs2,
            RV vs1 vs2 ->
            RS (init_state fn vs1) (init_state fn vs2)).
*)

(*
Fixpoint pst_cmd_map_r {E}
  (R: instr_r -> estate -> itree E (option estate))
  (c: cmd) (st: estate) : itree E (option estate) := 
  match c with 
  | nil => Ret (Some st) 
  | (MkI _ i) :: c' => pst' <- R i st ;;
                     (*  opt_lift (pst_cmd_map_r R c') pst' *)
                       match pst' with
                       | Some st' => pst_cmd_map_r R c' st'
                       | _ => Ret None end                           
  end.
*)
(*
Print result.
Variant result (E A : Type) : Type :=
    Ok : A -> result E A | Error : E -> result E A.
*)

(*
Fail Definition eval_fcall_body' {E} `{ErrState -< E} :
  (FunDef * values) -> estate -> 
  itree (callE (FunDef * values) (values * estate) +' E)
        (values * estate) :=
  fun fvst st =>
    let f := fst fvst in
    let va := snd fvst in
    st1 <- err_init_state f va st ;; 
    let c := funCode f in 
    st2 <- st_cmd_map_r eval_instr_call c st1 ;; 
    vs <- err_return_val f st2 ;;
    ret (vs, st2).
*)
(*
Definition mk_SetDests E `{StackE -< E} `{ErrState -< E}
  (f: FunDef) (xs: lvals) : itree E unit :=
  ITree.bind (trigger GetTopState) (fun st0 =>
    vres <- err_result _ _
      (get_var_is (~~ direct_call) st0.(evm) f.(f_res)) ;;
    vres' <- err_result _ _
      (mapM2 ErrType dc_truncate_val f.(f_tyout) vres) ;;
    let scs2 := st0.(escs) in
    let m2 := finalize f.(f_extra) st0.(emem) in    
    ITree.bind (trigger PopState) (fun st1 =>                                   
      st2 <- err_result _ _
              (write_lvals (~~direct_call) (p_globs pr)
                 (with_scs (with_mem st1 m2) scs2) xs vres') ;;
      trigger (PutTopState st2))).
*)

(*
Definition mk_SetDests E `{StackE -< E} `{ErrState -< E}
  (f: FunDef) (ld gd: lvals) : itree E unit :=
  ITree.bind (trigger GetTopState)
    (fun st0 =>
(**)
    get_var_is (~~ direct_call) s2.(evm) f.(f_res) = ok vres ->
    mapM2 ErrType dc_truncate_val f.(f_tyout) vres = ok vres' ->
    scs2 = s2.(escs) ->
    m2 = finalize f.(f_extra) s2.(emem)  ->
*)

(*
Definition mk_InitState E `{StackE -< E} `{ErrState -< E}
  (f: FunDef) (args: pexprs) : itree E unit :=
  ITree.bind (trigger GetFreshWithTopMem)
      (fun st0 =>
         vargs' <- err_result _ _ (eval_Args args st0) ;;
         vargs <- err_result _ _ (truncate_Args f vargs') ;;
         err_result _ _
           (write_vars (~~direct_call) (f_params f) vargs st0) ;;
         trigger (PushState st0)).
      
    (*     trigger (WriteVars vargs (f_params f))).  *)

(*         let scs1 := st0.(escs) in
         let m1 := st0.(emem) in  *)
*)       

