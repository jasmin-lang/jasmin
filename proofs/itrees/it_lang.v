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

(* Fail Fixpoint st_cmd_map (R: instr -> estate -> itree void1 estate)
  (c: cmd) (st: estate) : itree void1 estate := 
  match c with 
  | nil => Ret st 
  | i :: c' => ITree.bind (R i st) (fun st' => st_cmd_map R c' st')
  end.
*)

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

Fixpoint denote_for {E} `{FunE -< E} `{InstrE -< E}
  (R: cmd -> itree E unit) (i: var_i) (c: cmd) (ls: list Z) :
  itree E unit :=
    match ls with
    | nil => ret tt
    | (w :: ws) => trigger (WriteIndex i w) ;; R c ;; denote_for R i c ws
    end.


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

Definition denote_fun (fn: funname) (es: pexprs) :
  itree Eff unit :=
  trigger (InitState fn es) ;; 
  c <- trigger (FunCode fn) ;;   
  denote_cmd c.

End With_MREC_mod.


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


(***** INSTR EVENT SEMANTICS *******************************************)

(** Ccall *)

Definition pure_eval_Args (args: pexprs) (st: estate) :
  exec (seq value) := 
  sem_pexprs (~~direct_call) (p_globs pr) st args.

Definition truncate_Args (f: FunDef) (vargs: seq value) :
  exec (seq value) :=
  mapM2 ErrType dc_truncate_val f.(f_tyin) vargs.

Definition err_eval_Args {E} `{ErrState -< E}
  (f: FunDef) (args: pexprs) (st0: estate) : itree E (seq value) :=
  vargs' <- err_result _ _ (pure_eval_Args args st0) ;;
  err_result _ _ (truncate_Args f vargs').
  
Definition err_init_state {E} `{ErrState -< E}
   (f: FunDef) (vargs: seq value) (st0: estate) : itree E estate :=   
  let scs1 := st0.(escs) in
  let m1 := st0.(emem) in  
  st1 <- err_result _ _
       (init_state f.(f_extra) (p_extra pr) ev (Estate scs1 m1 Vm.init)) ;;
  err_result _ _
      (write_vars (~~direct_call) (f_params f) vargs st1).
      
Definition mk_InitState {E} `{StackE -< E} `{ErrState -< E}
  (f: FunDef) (args: pexprs) : itree E unit :=
  st0 <- trigger GetTopState ;;
  vargs <- err_eval_Args f args st0 ;;
  st1 <- err_init_state f vargs st0 ;;                                  
  trigger (PushState st1).

Definition err_return_val {E} `{ErrState -< E}
  (f: FunDef) (st0: estate) : itree E (seq value) :=                       
  vres <- err_result _ _
      (get_var_is (~~ direct_call) st0.(evm) f.(f_res)) ;;
  err_result _ _
      (mapM2 ErrType dc_truncate_val f.(f_tyout) vres).

Definition err_reinstate_caller {E} `{ErrState -< E}
  (f: FunDef) (xs: lvals) (vres: seq value)
  (st_ee st_er: estate) : itree E estate := 
  let scs2 := st_ee.(escs) in
  let m2 := finalize f.(f_extra) st_ee.(emem) in      
  err_result _ _
         (write_lvals (~~direct_call) (p_globs pr)
                      (with_scs (with_mem st_er m2) scs2) xs vres).
  
Definition mk_SetDests {E} `{StackE -< E} `{ErrState -< E}
  (f: FunDef) (xs: lvals) : itree E unit :=
  st0 <- trigger PopState ;;
  vres <- err_return_val f st0 ;;
  st1 <- trigger GetTopState ;;
  st2 <- err_reinstate_caller f xs vres st0 st1 ;;
  trigger (UpdateTopState st2).

Definition err_get_FunDef {E} `{ErrState -< E}
  (fn: funname) : itree E FunDef :=
  err_opt _ (get_FunDef fn).           

Definition ret_eval_Args {E: Type -> Type} 
  (f: FunDef) (args: pexprs) (st0: estate) : execT (itree E) (seq value) :=
  Ret (Let vargs' := pure_eval_Args args st0 in truncate_Args f vargs').

Definition ret_init_state {E: Type -> Type} 
   (f: FunDef) (vargs: seq value) (st0: estate) : execT (itree E) estate :=   
  let scs1 := st0.(escs) in
  let m1 := st0.(emem) in Ret 
  (Let st1 := init_state f.(f_extra) (p_extra pr) ev (Estate scs1 m1 Vm.init) in
   write_vars (~~direct_call) (f_params f) vargs st1).

Definition ret_return_val {E: Type -> Type} 
  (f: FunDef) (st0: estate) : execT (itree E) (seq value) := Ret           
  (Let vres := get_var_is (~~ direct_call) st0.(evm) f.(f_res) in
   mapM2 ErrType dc_truncate_val f.(f_tyout) vres).

Definition ret_reinstate_caller {E: Type -> Type} 
  (f: FunDef) (xs: lvals) (vres: seq value)
  (st_ee st_er: estate) : execT (itree E) estate := 
  let scs2 := st_ee.(escs) in
  let m2 := finalize f.(f_extra) st_ee.(emem) in      
  Ret (write_lvals (~~direct_call) (p_globs pr)
                      (with_scs (with_mem st_er m2) scs2) xs vres).

Definition ret_get_FunDef {E: Type -> Type} 
  (fn: funname) : execT (itree E) FunDef :=
  Ret (o2r ErrType (get_FunDef fn)).           


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
    | InitState fn es =>
        f <- err_get_FunDef fn ;; mk_InitState f es
    | SetDests fn xs =>
        f <- err_get_FunDef fn ;; mk_SetDests f xs
    end.                                            
        
Definition ext_handle_InstrE {E: Type -> Type} `{StackE -< E}
  `{ErrState -< E} : InstrE +' E ~> itree E :=
  case_ handle_InstrE (id_ E).

(* InstrE interpreter *)
Definition interp_InstrE {E: Type -> Type} `{StackE -< E}
  `{ErrState -< E} {A: Type}
  (t : itree (InstrE +' E) A) : itree E A :=
  interp ext_handle_InstrE t.


(*** FULL HIGH-LEVEL EVENT SEMANTICS  ********************************)

Definition HighE : Type -> Type := FunE +' InstrE.

Definition HighE_inv1 {E} {X: HighE -< E} : FunE -< E :=
  fun T (H : FunE T) => X T (inl1 H).
Definition HighE_inv2 {E} {X: HighE -< E} : InstrE -< E :=
  fun T (H : InstrE T) => X T (inr1 H).
Definition build_HighE {E: Type -> Type} 
  {X1: FunE -< E} {X2: InstrE -< E} :
  HighE -< E := @ReSum_sum (forall _ : Type, Type) IFun sum1 _
                FunE InstrE E X1 X2.

Definition handle_HighE {E: Type -> Type} `{StackE -< E}
  `{ErrState -< E} : HighE ~> itree E :=
  case_ handle_FunE handle_InstrE.

Definition ext_handle_HighE {E: Type -> Type} `{StackE -< E}
  `{ErrState -< E} : HighE +' E ~> itree E :=
  case_ handle_HighE (id_ E).

Definition interp_HighE {E: Type -> Type} `{StackE -< E}
  `{ErrState -< E} {A: Type}
  (t : itree (HighE +' E) A) : itree E A :=
  interp ext_handle_HighE t.


(***** LOW-LEVEL EVENT SEMANTICS **************************************)

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



(********* JASMIN INTERPRETERS *****************************************)

(* evaluation abstracting from stack and errors *)
Definition evalSE_cmd {E} `{ErrState -< E}
  (c: cmd) : itree (StackE +' E) unit :=
  interp_HighE (denote_cmd _ _ _ c).

(* evaluation abstracting from errors, return value paired with unit
*)
Definition evalEU_cmd {E} `{ErrState -< E}
  (c: cmd) : stateT estack (itree E) unit :=
  interp_StackE (evalSE_cmd c).

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


(************* SUPERFLUOUS *****************************************)

Definition evalSE_gen_cmd E `{StackE -< E} `{ErrState -< E}
  (c: cmd) : itree E unit :=
  interp_HighE (denote_cmd _ _ _ c).

(* full evaluation, return value paired with unit *)
Definition evalU_cmd {E} (c: cmd) :
  stateT estack (failT (itree E)) unit := 
  fun ss => @interp_Err E (estack * unit) (evalEU_cmd c ss).

Definition eval2kevalA {E} {R S V}
  (f: R -> S -> itree E V) : ktree E (R * S) V :=
  fun p2 => f (fst p2) (snd p2).

Definition keval2evalA {E} {R S V}
  (f: ktree E (R * S) V) : R -> S -> itree E V :=
  fun r s => f (r, s).

Definition forget_sndA {E} {R S V1 V2} 
  (f: R -> S -> itree E (V1 * V2)) : R -> S -> itree E V1 :=
  keval2evalA (k_forget_snd (eval2kevalA f)).

(* evaluation abstracting from errors, without unit *)
Definition evalE_cmd {E} {X: ErrState -< E} 
  (c: cmd) (ss: estack) : itree E estack :=
  forget_sndA (@evalEU_cmd E X) c ss.

End EventSem.

(*********************************************************************)
(*********************************************************************)

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


(** flat interpreter with double recursion *)
Section With_REC_error.

Local Notation continue_loop st := (ret (inl st)).
Local Notation exit_loop st := (ret (inr st)).
Local Notation rec_call x := (trigger_inl1 (Call x)). 

(* introduce events *)
Fixpoint eval_instr_call {E} `{ErrState -< E} (i : instr_r) (st: estate) :
    itree (callE (FunDef * (values * estate)) (values * estate) +' E) estate := 
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
      f <- err_get_FunDef fn ;;
      va <- err_eval_Args f es st ;;
      vst <- rec_call (f, (va, st)) ;;
      (* PROBLEM: we still need the calle state, so the function needs
      to return it *)
      err_reinstate_caller f xs (fst vst) (snd vst) st 
  end.

Definition eval_fcall_body {E} `{ErrState -< E} :
  (FunDef * (values * estate)) -> 
  itree (callE (FunDef * (values * estate)) (values * estate) +' E)
        (values * estate) :=
  fun fvst =>
    let '(f, (va, st)) := fvst in
    st1 <- err_init_state f va st ;; 
    let c := funCode f in 
    st2 <- st_cmd_map_r eval_instr_call c st1 ;; 
    vs <- err_return_val f st2 ;;
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
      f <- err_get_FunDef fn ;;
      va <- err_eval_Args f es st ;;
      vst <- rec eval_fcall_body (f, (va, st)) ;;  
      err_reinstate_caller f xs (fst vst) (snd vst) st 
  end.

(* denotational interpreter *)
Definition evalE_err_cmd {E} `{ErrState -< E} (c: cmd) (st: estate) :
  itree E estate := st_cmd_map_r eval_instr c st. 

(* MAIN: full evaluation returning an optional state *)
Definition eval_err_cmd {E} (c: cmd) (st: estate) : itree E (option estate) := 
  @interp_Err E estate (evalE_err_cmd c st).

Definition evalE_fun {E} `{ErrState -< E} :
  (FunDef * (values * estate)) -> 
  itree E (values * estate) :=
  fun fvst =>
    let '(f, (va, st)) := fvst in
    st1 <- err_init_state f va st ;;
    let c := funCode f in
    st2 <- evalE_err_cmd c st1 ;;
    vs <- err_return_val f st2 ;;
    ret (vs, st2).

Definition evalE_fun_ {E} `{ErrState -< E}
  (fn: funname) (vs: values) (st: estate) : 
  itree (callE (FunDef * (values * estate)) (values * estate) +' E)
        (values * estate) :=
  f <- err_get_FunDef fn ;;
  eval_fcall_body (f, (vs, st)).

End With_REC_error.


(* mutual recursion events *)
Variant FCState : Type -> Type :=
 | FLCode (c: cmd) (st: estate) : FCState estate
 | FFCall (xs: lvals) (f: funname) (es: pexprs) (st: estate) : FCState estate.

(** flat interpreter with mutual recursion *)
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
  f <- err_get_FunDef fn ;;
  va <- err_eval_Args f es st0 ;;
  st1 <- err_init_state f va st0 ;;
  let c := funCode f in
  st2 <- rec_call (FLCode c st1) ;;
  vs <- err_return_val f st2 ;;
  err_reinstate_caller f xs vs st2 st0.

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
  (FunDef * (values * estate)) -> 
  itree E (values * estate) :=
  fun fvst =>
    let '(f, (va, st)) := fvst in
    st1 <- err_init_state f va st ;;
    let c := funCode f in
    st2 <- mevalE_cmd c st1 ;;
    vs <- err_return_val f st2 ;;
    ret (vs, st2).

Definition meval_fun_ {E} `{ErrState -< E}
  (fn: funname) (va: values) (st0: estate) :
  itree (FCState +' E) (values * estate) :=
  f <- err_get_FunDef fn ;;
  st1 <- err_init_state f va st0 ;;
  let c := funCode f in
  st2 <- rec_call (FLCode c st1) ;;
  vs <- err_return_val f st2 ;;
  ret (vs, st2).

End With_MREC_error.


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
  va <- ret_eval_Args f es st0 ;;
  st1 <- ret_init_state f va st0 ;;
  let c := funCode f in
  rec_call (PLCode c st1) ;;
  vs <- ret_return_val f st1 ;;
  ret_reinstate_caller f xs vs st1 st0.

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
  f <- ret_get_FunDef fn ;;
  st1 <- ret_init_state f va st ;;
  let c := funCode f in
  st2 <- pmeval_cmd c st1 ;;
  vs <- ret_return_val f st2 ;;
  ret (vs, st2).

(*
Definition pmeval_fun {E} :
  (FunDef * (values * estate)) -> 
  execT (itree E) (values * estate) :=
  fun fvst =>
    let '(f, (va, st)) := fvst in
    st1 <- ret_init_state f va st ;;
    let c := funCode f in
    st2 <- pmeval_cmd c st1 ;;
    vs <- ret_return_val f st2 ;;
    ret (vs, st2).
*)

End With_MREC_flat.


(** flat interpreter with double recursion *)
Section With_REC_flat.

Local Notation continue_loop st := (ret (inl st)).
Local Notation exit_loop st := (ret (inr st)).
Local Notation rec_call x := (trigger_inl1 (Call x)). 

(* introduce events *)
Fixpoint peval_instr_call {E} (i : instr_r) (st: estate) :
  execT (itree (callE (FunDef * (values * estate)) (exec (values * estate))
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
      f <- ret_get_FunDef fn ;; 
      va <- ret_eval_Args f es st ;;      
      vst <- rec_call (f, (va, st)) ;; 
      (* PROBLEM: we still need the calle state, so the function needs
      to return it *)
      ret_reinstate_caller f xs (fst vst) (snd vst) st   
  end.

Definition peval_fcall_body {E} :
  (FunDef * (values * estate)) -> 
  execT (itree (callE (FunDef * (values * estate)) (exec (values * estate))
         +' E)) (values * estate) :=
  fun fvst =>
    let '(f, (va, st)) := fvst in
    st1 <- ret_init_state f va st ;; 
    let c := funCode f in 
    st2 <- pst_cmd_map_r peval_instr_call c st1 ;; 
    vs <- ret_return_val f st2 ;;
    ret (vs, st2).

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
      f <- ret_get_FunDef fn ;; 
      va <- ret_eval_Args f es st ;;      
      vst <- rec peval_fcall_body (f, (va, st)) ;; 
      ret_reinstate_caller f xs (fst vst) (snd vst) st   
  end.

(* MAIN: denotational interpreter *)
Definition peval_flat_cmd {E} (c: cmd) (st: estate) :
  execT (itree E) estate := pst_cmd_map_r peval_instr c st. 

Definition peval_fun {E} :
  (FunDef * (values * estate)) -> 
  execT (itree E) (values * estate) :=
  fun fvst =>
    let '(f, (va, st)) := fvst in
    st1 <- ret_init_state f va st ;; 
    let c := funCode f in 
    st2 <- peval_flat_cmd c st1 ;; 
    vs <- ret_return_val f st2 ;;
    ret (vs, st2).

Definition eval_fun_ {E} (fn: funname) (vs: values) (st: estate) : 
  execT (itree (callE (FunDef * (values * estate)) (exec (values * estate))
                +' E)) (values * estate) :=
  f <- ret_get_FunDef fn ;;
  peval_fcall_body (f, (vs, st)).

End With_REC_flat.

End OneProg.


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


Section TRANSF.
Context (tr_lval : lval -> lval)
        (tr_expr : pexpr -> pexpr)
        (tr_opn : sopn -> sopn)
        (tr_sysc : syscall_t -> syscall_t).

Definition Tr_i (Th: instr_r -> instr_r) (i: instr) : instr :=
  match i with MkI ii ir => MkI ii (Th ir) end.  

Fixpoint Tr_ir (i : instr_r) : instr_r :=
  let R := Tr_i Tr_ir in
  match i with
  | Cassgn x tg ty e => Cassgn (tr_lval x) tg ty (tr_expr e)
  | Copn x tg o es =>
      Copn (map tr_lval x) tg (tr_opn o) (map tr_expr es)
  | Csyscall x sc es =>
      Csyscall (map tr_lval x) (tr_sysc sc) (map tr_expr es)
  | Cif e c1 c2 => Cif (tr_expr e) (map R c1) (map R c2)
  | Cfor i rg c => Cfor i rg (map R c)                     
  | Cwhile a c1 e c2 => Cwhile a (map R c1) (tr_expr e) (map R c2)
  | Ccall xs fn es => Ccall (map tr_lval xs) fn (map tr_expr es)
  end.
Local Notation Tr_cmd c := (map (Tr_i Tr_ir) c).

Section GEN_tests.

Context (E: Type -> Type)
        (HasErr: ErrState -< E)             
        (pr1 pr2 : prog)
        (PR : forall T, T -> T -> Prop).
Context (TR_E : forall (E: Type -> Type) T1 T2,
            E T1 -> E T2 -> Prop)
        (VR_E : forall (E: Type -> Type) T1 T2,
            E T1 -> T1 -> E T2 -> T2 -> Prop).

Section GEN_test0.

Context (HasFunE : FunE -< E)
        (HasInstrE : InstrE -< E).     
  
Lemma comp_gen_okMM (fn: funname)
  (xs1 xs2: lvals) (es1 es2: pexprs) :
  xs2 = map tr_lval xs1 ->
  es2 = map tr_expr es1 -> 
  eutt eq  
    (denote_fcall E _ _ fn xs1 es1) (denote_fcall E _ _ fn xs2 es2).
  intros.
  unfold denote_fcall; simpl.
Admitted. 
  
End GEN_test0.

Section GEN_test1.

Local Notation RS := (PR estate).
Local Notation RV := (PR values).
Local Notation VS := (values * estate)%type.
Local Notation FVS := (funname * VS)%type.

Notation RVS := (fun (vs_st1 vs_st2 : VS) => 
  (RV vs_st1.1 vs_st2.1 /\ RS vs_st1.2 vs_st2.2)).
Notation RFVS := (fun (fvs1 fvs2 : FVS) => 
  (fvs1.1 = fvs2.1 /\ RVS fvs1.2 fvs2.2)).
Context (rvs_def : PR VS = RVS)
        (rfvs_def : PR FVS = RFVS).  

Definition TR_D2 {T1 T2} (d1 : callE FVS VS T1)
                         (d2 : callE FVS VS T2) : Prop :=
  match (d1, d2) with
  | (Call f1, Call f2) => RFVS f1 f2 end.               

Program Definition VR_D2 {T1 T2} (d1 : callE FVS VS T1) (t1: T1)
                                 (d2 : callE FVS VS T2) (t2: T2) : Prop.
  dependent destruction d1.
  dependent destruction d2.
  exact (RVS t1 t2).
Defined.

Lemma comp_gen_okDE (fn: funname) (vs1 vs2: values) (st1 st2: estate) :
  RV vs1 vs2 ->
  RS st1 st2 ->
  @rutt (callE (FunDef * VS) VS +' E)
    (callE (FunDef * VS) VS +' E)
    VS VS 
    (TR_E (callE (FunDef * VS) VS +' E))
    (VR_E (callE (FunDef * VS) VS +' E))
    (fun a1 a2 => @VR_D2 _ _ (Call (fn, (vs1, st1))) a1
                             (Call (fn, (vs2, st2))) a2)  
    (evalE_fun_ pr1 fn vs1 st1) (evalE_fun_ pr2 fn vs2 st2).
  intros.
  unfold evalE_fun_; simpl.
Admitted. 

Definition exec_RVS (pp1 pp2 : exec VS) : Prop :=
  match (pp1, pp2) with
  | (Ok vt1, Ok vt2) => RVS vt1 vt2
  | _ => False end.
Context (exec_rvs_def : PR (exec VS) = exec_RVS).  

Program Definition VR_D2' {T1 T2} (d1 : callE FVS (exec VS) T1) (t1: T1)
                                  (d2 : callE FVS (exec VS) T2) (t2: T2) : Prop.
  dependent destruction d1.
  dependent destruction d2.
  exact (exec_RVS t1 t2).
Defined.

Lemma comp_gen_okDF (fn: funname) (vs1 vs2: values) (st1 st2: estate) :
  RV vs1 vs2 ->
  RS st1 st2 ->
  @rutt (callE (FunDef * VS) (exec VS) +' E)
    (callE (FunDef * VS) (exec VS) +' E)
    (exec VS) (exec VS)
    (TR_E (callE (FunDef * VS) (exec VS) +' E))
    (VR_E (callE (FunDef * VS) (exec VS) +' E))
    (fun (a1 a2: exec VS) => @VR_D2' _ _ (Call (fn, (vs1, st1))) a1
                             (Call (fn, (vs2, st2))) a2)  
    (eval_fun_ pr1 fn vs1 st1) (eval_fun_ pr2 fn vs2 st2).
  intros.
  unfold eval_fun_; simpl.
Admitted. 
 
Definition TR_D3 {T1 T2} (d1 : FCState T1)
                         (d2 : FCState T2) : Prop :=
  match (d1, d2) with
  | (FLCode c1 st1, FLCode c2 st2) => c2 = Tr_cmd c1 /\ RS st1 st2
  | (FFCall xs1 fn1 es1 st1, FFCall xs2 fn2 es2 st2) =>
      xs2 = map tr_lval xs1 /\ fn1 = fn2 /\ es2 = map tr_expr es1 /\ RS st1 st2
  | _ => False   
  end.               

Program Definition VR_D3 {T1 T2} (d1 : FCState T1) (t1: T1)
                                 (d2 : FCState T2) (t2: T2) : Prop.
  dependent destruction d1.
  - dependent destruction d2.
    + exact (RS t1 t2).
    + exact (False).
  - dependent destruction d2.
    + exact (False).
    + exact (RS t1 t2).
Defined.      

Lemma comp_gen_okME (fn: funname)
  (xs1 xs2: lvals) (es1 es2: pexprs) (st1 st2: estate) :
  xs2 = map tr_lval xs1 ->
  es2 = map tr_expr es1 -> 
  RS st1 st2 ->
  @rutt (FCState +' E) _ _ _ 
    (TR_E _) (VR_E _)
    (fun a1 a2 => @VR_D3 _ _ (FFCall xs1 fn es1 st1) a1
                             (FFCall xs2 fn es2 st2) a2)  
    (meval_fcall pr1 xs1 fn es1 st1) (meval_fcall pr2 xs2 fn es2 st2).
  intros.
  unfold meval_fcall; simpl.
Admitted. 

Definition TR_D4 {T1 T2} (d1 : PCState T1)
                         (d2 : PCState T2) : Prop :=
  match (d1, d2) with
  | (PLCode c1 st1, PLCode c2 st2) => c2 = Tr_cmd c1 /\ RS st1 st2
  | (PFCall xs1 fn1 es1 st1, PFCall xs2 fn2 es2 st2) =>
      xs2 = map tr_lval xs1 /\ fn1 = fn2 /\ es2 = map tr_expr es1 /\ RS st1 st2
  | _ => False   
  end.               

Definition exec_RS (p1 p2: exec estate) : Prop :=
  match (p1, p2) with
  | (Ok st1, Ok st2) => RS st1 st2
  | _ => False end.                         

Program Definition VR_D4 {T1 T2} (d1 : PCState T1) (t1: T1)
                                 (d2 : PCState T2) (t2: T2) : Prop.
  dependent destruction d1.
  - dependent destruction d2.
    + exact (exec_RS t1 t2).
    + exact (False).
  - dependent destruction d2.
    + exact (False).
    + exact (exec_RS t1 t2).
Defined.      

Lemma comp_gen_okMF (fn: funname)
  (xs1 xs2: lvals) (es1 es2: pexprs) (st1 st2: estate) :
  xs2 = map tr_lval xs1 ->
  es2 = map tr_expr es1 -> 
  RS st1 st2 ->
  @rutt (PCState +' E) _ _ _ 
    (TR_E _) (VR_E _)
    (fun a1 a2 => @VR_D4 _ _ (PFCall xs1 fn es1 st1) a1
                             (PFCall xs2 fn es2 st2) a2)  
    (pmeval_fcall pr1 xs1 fn es1 st1) (pmeval_fcall pr2 xs2 fn es2 st2).
  intros.
  unfold pmeval_fcall; simpl.
Admitted. 

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

End GEN_test1.

End GEN_tests.

End TRANSF.

End WSW.

End Lang.
(** END *)

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

