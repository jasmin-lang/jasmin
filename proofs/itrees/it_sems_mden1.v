
From ITree Require Import
     Basics
     ITree
     ITreeFacts
     Events.Exception
     Interp.Recursion
     MonadState
     State
     StateFacts.
Import Basics.Monads.

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.

Require Import expr psem_defs psem_core it_exec it_sems_exec tfam_iso1.

Import MonadNotation.
Local Open Scope monad_scope.

Section Asm1.  
Context
  {asm_op: Type} {asmop: asmOp asm_op}.
(*
Context
  {asm_op: Type}
  {syscall_state : Type}
  {sip : SemInstrParams asm_op syscall_state}.  
  {wsw: WithSubWord} 
  {dc: DirectCall} 
  {ep : EstateParams syscall_state} 
  {spp : SemPexprParams} 
  {pT : progT}
  {scP : semCallParams}. *)

Section Sem1.
Context (FState : Type) {State: Type} {FunDef: Type}.
Context {err: error_data}.

Local Notation continue_loop := (ret (inl tt)).
Local Notation exit_loop := (ret (inr tt)).
Local Notation rec_call := (trigger_inl1). 

(* mutual recursion events (corresponding to call states) *)
Variant MREvent : Type -> Type :=
  | LCode (c: cmd) : MREvent unit
  | FCall (fn: funname) (fs: FState) : MREvent FState.

(* state events (similar to those provided by the library, 
   could be specialized to estate) *)
Variant StE : Type -> Type :=
  | GetSE : StE State
  | PutSE : State -> StE unit.                      

(* instruction events *)
Variant InstrE : Type -> Type :=
  | AssgnE : lval -> assgn_tag -> stype -> pexpr -> InstrE unit
  | OpnE : lvals -> assgn_tag -> sopn -> pexprs -> InstrE unit
  | SyscallE : lvals -> syscall_t -> pexprs -> InstrE unit
  | EvalCond (e: pexpr) : InstrE bool
  | EvalBound (e: pexpr) : InstrE Z
  | WriteIndex (x: var_i) (z: Z) : InstrE unit
  | EvalArgs (args: pexprs) : InstrE pexprs                
  | InitFState (args: pexprs) : InstrE FState
  | RetVal (xs: lvals) (fs: FState) (s: State) : InstrE unit.

(* function call events *)
Variant FunE : Type -> Type :=
  | GetFunDef (fn: funname) (fs: FState) : FunE FunDef
  | GetFunCode (fd: FunDef) : FunE cmd          
  | InitFunCall (fd: FunDef) (fs: FState) : FunE FState                     
  | FinalizeFunCall (fd: FunDef) : FunE FState.

(* folding instruction semantics on commands 
   (without state, it could be simply map) *)
Definition isem_foldr {E} (sem_i: instr -> itree E unit) (c: cmd) :
    itree E unit :=
  foldr (fun i k => sem_i i ;; k) (Ret tt) c.

Definition isem_for_round {E} (sem_i: instr -> itree E unit)
  (wrt: Z -> itree E unit)                        
  (i : var_i) (c : cmd) (w: Z) (k: itree E unit) : itree E unit :=
  wrt w ;; isem_foldr sem_i c ;; k.

Definition isem_for_loop  {E} (sem_i: instr -> itree E unit)
  (wrt: Z -> itree E unit) 
  (i : var_i) (c : cmd) (ls : list Z)
  : itree E unit :=
  foldr (isem_for_round sem_i wrt i c) (Ret tt) ls.

Definition isem_while_round {E} (sem_i: instr -> itree E unit)
  (cnd: pexpr -> itree E bool) 
  (c1 : cmd) (e : pexpr) (c2 : cmd) :
    itree E (unit + unit) :=
  isem_foldr sem_i c1 ;;
  b <- cnd e ;;
  if b then isem_foldr sem_i c2 ;; continue_loop 
  else exit_loop.

Definition isem_while_loop {E} (sem_i: instr -> itree E unit)
  (cnd: pexpr -> itree E bool)
  (c1 : cmd) (e: pexpr) (c2: cmd) :
    itree E unit :=
  ITree.iter (fun _ => isem_while_round sem_i cnd c1 e c2) tt.


Section Sem2.

Context {E}
  {XE : ErrEvent -< E} {XI : InstrE -< E} {XS: StE -< E} {XF: FunE -< E}.
  
(* semantics of instructions *)
Fixpoint esem_instr  
  (i : instr) : itree (MREvent +' E) unit :=  
  let R := isem_foldr esem_instr in
  let: (MkI ii ir) := i in 
  match ir with

  | Cassgn x tg ty e => trigger (AssgnE x tg ty e)
                                
  | Copn xs tg o es => trigger (OpnE xs tg o es)
                               
  | Csyscall xs o es => trigger (SyscallE xs o es)
        
  | Cif e c1 c2 =>
    b <- trigger (EvalCond e) ;; 
    R (if b then c1 else c2)

  | Cwhile a c1 e i c2 =>
      isem_while_loop esem_instr (fun e => trigger (EvalCond e))
        c1 e c2 
        
  | Cfor i (d, lo, hi) c =>
    lo_b <- trigger (EvalBound lo) ;;
    hi_b <- trigger (EvalBound hi) ;;   
    isem_for_loop esem_instr (fun w => trigger (WriteIndex i (Vint w)))
      i c (wrange d lo_b hi_b) 

  | Ccall xs fn args =>
    s0 <- trigger GetSE ;;  
    vargs <- trigger (EvalArgs args) ;;
    fs0 <- trigger (InitFState vargs) ;;
    fs1 <- rec_call (FCall fn fs0) ;; 
    (* discard current state, use s0 instead *)
    trigger (RetVal xs fs1 s0)
(* | _ => throw err end. *)
  end.

(* semantics of commands *)
Definition esem_cmd c := isem_foldr esem_instr c.

(* semantics of function calls *)
Definition esem_fcall (fn : funname) (fs : FState) :
  itree (MREvent +' E) FState :=
  fd <- trigger (GetFunDef fn fs) ;;  
  c <- trigger (GetFunCode fd) ;;
  trigger (InitFunCall fd fs) ;;
  rec_call (LCode c) ;;
  trigger (FinalizeFunCall fd).

(* call state handler *)
Definition esem_cstate : MREvent ~> itree (MREvent +' E) :=           
  fun _ fs => match fs with
              | LCode c => esem_cmd c 
              | FCall fn fs => esem_fcall fn fs     
              end.      

(* actual recursive semantics *)
Definition mrec_cmd (c: cmd) : itree E unit :=
  mrec esem_cstate (LCode c).

(**********************************************************************)

Definition esem_cstate_blank : MREvent ~> itree (MREvent +' E) :=           
  fun _ fs => match fs with
              | LCode c => esem_cmd c 
              | FCall fn fs => rec_call (FCall fn fs)     
              end.      

(* blank recursive semantics: does not interpret recursive calls *)
Definition mrec_cmd_blank (c: cmd) : itree E unit :=
  mrec esem_cstate_blank (LCode c).

End Sem2.

End Sem1.

End Asm1.

(********************* garbage **********)

From Jasmin Require Import oseq.
(* problematic *)
From Jasmin Require Import expr.
(* From Jasmin Require Import it_jasmin_lib. *)

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

From Jasmin Require Import expr psem_defs psem oseq.
(* From Jasmin Require Import it_gen_lib it_jasmin_lib. *)
From Jasmin Require Import compiler_util.
(* problematic *)
From Jasmin Require Import it_exec2.

(********************************************************)
(* TODO: clean up imports above this line *)

From mathcomp Require Import ssreflect ssrfun ssrbool.

Require Import xrutt xrutt_facts. 

Import ITreeNotations.
Local Open Scope itree_scope.

Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.
Local Open Scope option_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Obligation Tactic := done || idtac.

(*** SEMANTICS + ARRAY INIT *)

(************************************************************************)
(** from JLang7.v *)

Definition opt_fmap {A B} (f: A -> B) : option A -> option B :=
  fun m => match m with
           | Some x => Some (f x) | _ => None end.  

(*
Definition opt_map {A B} (f: A -> B) : option (list A) -> option (list B) :=
  opt_fmap (List.map f).

Definition opt_write {S} {V} (ms: option S) (v: V) :
  option (S * V) :=
  match ms with  
  | Some st' => Some (st', v)
  | _ => None end.    

Definition lift_rel {T} (R: T -> T -> Prop) : option T -> option T -> Prop :=
  fun x y => match (x, y) with
             | (Some x', Some y') => R x' y'
             | (None, None) => True
             | _ => False end.  
*)

(**** ERROR SEMANTICS *******************************************)
Section Errors.

Definition ErrEvent : Type -> Type := exceptE error_data.

(* failT (itree E) R = itree E (option R) *)
Definition handle_Err {E} : ErrEvent ~> failT (itree E) :=
  fun _ _ => Ret (None).

(* Err handler *)
Definition ext_handle_Err {E: Type -> Type} :
  ErrEvent +' E ~> failT (itree E) :=
  fun _ e =>
  match e with
  | inl1 e' => handle_Err e'
  | inr1 e' => Vis e' (pure (fun x => Some x)) end.                        

(* ErrEvent interpreter *)
Definition interp_Err {E: Type -> Type} {A}  
  (t: itree (ErrEvent +' E) A) : failT (itree E) A :=
  interp_fail ext_handle_Err t.

(*** auxiliary error functions *)

Definition err_f_get {E: Type -> Type} `{ErrEvent -< E} {S} {V}
  (err: error_data) (f: S -> option V) : stateT S (itree E) V :=
  fun st => match (f st) with
            | Some v => Ret (st, v)
            | None => throw err end.                

Definition err_f_put {E: Type -> Type} `{ErrEvent -< E} {S}
  (err : error_data) (f: S -> option S) : stateT S (itree E) unit :=
  fun st => match (f st) with
            | Some st' => Ret (st', tt)
            | None => throw err end.                

Definition err_opt {E: Type -> Type} `{ErrEvent -< E} (err : error_data) :
  option ~> itree E :=
  fun _ t => match t with
             | Some v => Ret v
             | None => throw err end.                

Definition err_result {E: Type -> Type} `{ErrEvent -< E} T (err : error_data) :
  result T ~> itree E :=
  fun _ t => match t with
             | Ok v => Ret v
             | Error _ => throw err end.                

End Errors.


(*********************************************************************)
(*** LANGUAGE DEFINITION *********************************************)

Section WSW.
Context (asm_op: Type) (asmop: asmOp asm_op).
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
  
Context (pr : prog).

(* default error *)  
Context (err: error_data).


(***** FUN-READER SEMANTICS ******************************************)
Section ModularSem.

(* Analysis info *)  
Context (AInfo: Type).
Context (empty_ainfo : AInfo).
Context (ainfo_updt : instr_info -> AInfo -> AInfo).

Notation ainfo_estate := (AInfo * estate)%type.
Notation ainfo_bool := (AInfo * bool)%type.
Notation ainfo_Z := (AInfo * Z)%type.
Notation ainfo_values := (AInfo * values)%type.

Definition FunDef : Type := _fundef extra_fun_t.

Definition get_FunDef (fn: funname) : option FunDef :=
  get_fundef (p_funcs pr) fn.

Definition funCode (f: FunDef) : cmd := 
  @f_body asm_op asmop extra_fun_t f.

Definition get_FunCode (fn: funname) : option cmd := 
  opt_fmap (@f_body asm_op asmop extra_fun_t) (get_FunDef fn).

Definition get_FunDests (fn: funname) : option lvals :=
  get_FunDef fn >>= fun f => Some (map Lvar (f.(f_res))). 


(***** INSTR AUX FUNCTIONS *******************************************)

(* option to execS *)
Definition o2xs {aT : Type} (o: option aT) : execS aT :=
match o with
| Some x => ESok x
| None => ESerror _ err
end.

(* result to execS *)
Definition r2xs {eT aT : Type} (o: result eT aT) : execS aT :=
match o with
| Ok x => ESok x
| Error _ => ESerror _ err
end.

(* option to execS with ainfo *)
Definition o2aixs {aT : Type} (ai: AInfo) (o: option aT) :
  execS (AInfo * aT) :=
match o with
| Some x => ESok (ai, x)
| None => ESerror _ err
end.
Definition o2axs {aT : Type} (o: option aT) := o2aixs empty_ainfo o.

(* result to execS with ainfo *) 
Definition r2aixs {eT aT : Type} (ai: AInfo) (o: result eT aT) :
  execS (AInfo * aT) :=
match o with
| Ok x => ESok (ai, x)
| Error _ => ESerror _ err
end.
Definition r2axs {eT aT : Type} (o: result eT aT) := r2aixs empty_ainfo o.

Definition o2aio {T} : AInfo -> option T -> option (AInfo * T) :=
  fun ai o => match o with
           | Some y => Some (ai, y)
           | None => None end.                 
Definition o_add_info {T} (o: option T) := o2aio empty_ainfo o.       

Definition r2air {eT aT} :
  AInfo -> result eT aT -> result eT (AInfo * aT) :=
  fun ai x => match x with
           | Ok y => ok (ai, y)
           | Error e => Error e end.                 
Definition r_add_info T (x: exec T) : exec (AInfo * T) :=
  r2air empty_ainfo x.


(******************************************************)

Definition ret_get_FunDef {E: Type -> Type} 
  (fn: funname) : execT (itree E) FunDef :=
  Ret (o2xs (get_FunDef fn)).           

Definition ret_get_FunDef' {E: Type -> Type} 
  (fn: funname) : execT (itree E) (AInfo * FunDef) :=
  Ret (o2axs (get_FunDef fn)).           

Definition err_get_FunDef {E} `{ErrEvent -< E}
  (fn: funname) : itree E FunDef :=
  err_opt err (get_FunDef fn).           

Definition err_get_FunDef' {E} `{ErrEvent -< E}
  (fn: funname) : itree E (AInfo * FunDef) :=
  err_opt err (o_add_info (get_FunDef fn)).           

Definition ret_get_FunCode {E: Type -> Type}
  (fn: funname) : execT (itree E) cmd :=
  f <- ret_get_FunDef fn ;;
  Ret (ESok (funCode f)).

Definition ret_get_FunCode' {E: Type -> Type}
  (fn: funname) : execT (itree E) (AInfo * cmd) :=
  f <- ret_get_FunDef fn ;;
  Ret (ESok (empty_ainfo, funCode f)).

Definition err_get_FunCode {E} `{ErrEvent -< E}
  (fn: funname) : itree E cmd :=
  f <- err_get_FunDef fn ;;
  Ret (funCode f).

Definition err_get_FunCode' {E} `{ErrEvent -< E}
  (fn: funname) : itree E (AInfo * cmd) :=
  f <- err_get_FunDef fn ;;
  Ret (empty_ainfo, funCode f).

(******************)

Definition pure_eval_Args (args: pexprs) (st: estate) :
  exec (seq value) := 
  sem_pexprs (~~direct_call) (p_globs pr) st args.

Definition truncate_Args (f: FunDef) (vargs: seq value) :
  exec (seq value) :=
  mapM2 ErrType dc_truncate_val f.(f_tyin) vargs.

Definition err_eval_Args {E} `{ErrEvent -< E}
  (fn: funname) (args: pexprs) (st0: estate) : itree E values :=
  f <- err_get_FunDef fn ;;
  vargs' <- err_result err (pure_eval_Args args st0) ;;
  err_result err (truncate_Args f vargs').

Definition err_eval_Args' {E} `{ErrEvent -< E}
  (fn: funname) (args: pexprs) (st0: ainfo_estate) : itree E ainfo_values :=
  f <- err_get_FunDef fn ;;
  vargs' <- err_result err (pure_eval_Args args (snd st0)) ;;
  err_result err (r_add_info (truncate_Args f vargs')).
 
Definition err_init_state {E} `{ErrEvent -< E}
   (fn: funname) (vargs: seq value) (st0: estate) : itree E estate :=   
  let scs1 := st0.(escs) in
  let m1 := st0.(emem) in
  f <- err_get_FunDef fn ;;
  st1 <- err_result err 
       (init_state f.(f_extra) (p_extra pr) ev (Estate scs1 m1 Vm.init)) ;;
  err_result err
      (write_vars (~~direct_call) (f_params f) vargs st1).

Definition err_init_state' {E} `{ErrEvent -< E}
   (fn: funname) (vargs: seq value) (st0: estate) : itree E ainfo_estate :=   
  let scs1 := st0.(escs) in
  let m1 := st0.(emem) in
  f <- err_get_FunDef fn ;;
  st1 <- err_result err 
       (init_state f.(f_extra) (p_extra pr) ev (Estate scs1 m1 Vm.init)) ;;
  err_result err
      (r_add_info (write_vars (~~direct_call) (f_params f) vargs st1)).

Definition err_return_val {E} `{ErrEvent -< E}
  (fn: funname) (st0: estate) : itree E values :=
  f <- err_get_FunDef fn ;;
  vres <- err_result err 
      (get_var_is (~~ direct_call) st0.(evm) f.(f_res)) ;;
  err_result err
      (mapM2 ErrType dc_truncate_val f.(f_tyout) vres).

Definition err_return_val' {E} `{ErrEvent -< E}
  (fn: funname) (st0: estate) : itree E ainfo_values :=
  f <- err_get_FunDef fn ;;
  vres <- err_result err 
      (get_var_is (~~ direct_call) st0.(evm) f.(f_res)) ;;
  err_result err
     (r_add_info (mapM2 ErrType dc_truncate_val f.(f_tyout) vres)).


Definition err_reinstate_caller {E} `{ErrEvent -< E}
  (fn: funname) (xs: lvals) (vres: values)
  (st_ee st_er: estate) : itree E estate :=
  f <- err_get_FunDef fn ;;
  let scs2 := st_ee.(escs) in
  let m2 := finalize f.(f_extra) st_ee.(emem) in      
  err_result err 
         (write_lvals (~~direct_call) (p_globs pr)
                      (with_scs (with_mem st_er m2) scs2) xs vres).

Definition err_reinstate_caller' {E} `{ErrEvent -< E}
  (fn: funname) (xs: lvals) (vres: values)
  (st_ee st_er: estate) : itree E ainfo_estate :=
  f <- err_get_FunDef fn ;;
  let scs2 := st_ee.(escs) in
  let m2 := finalize f.(f_extra) st_ee.(emem) in      
  err_result err 
       (r_add_info (write_lvals (~~direct_call) (p_globs pr)
                      (with_scs (with_mem st_er m2) scs2) xs vres)).


(** WriteIndex *)

Definition ret_mk_WriteIndex {E} 
  (x: var_i) (z: Z) (st1: estate) : execT (itree E) estate :=  
    Ret (r2xs (write_var true x (Vint z) st1)).                             

Definition err_mk_WriteIndex {E} `{ErrEvent -< E}
  (x: var_i) (z: Z) (st1: estate) : itree E estate :=  
    err_result err (write_var true x (Vint z) st1).                             

Definition err_mk_WriteIndex0' {E} `{ErrEvent -< E}
  (x: var_i) (z: Z) (st1: estate) : itree E ainfo_estate :=  
    err_result err (r_add_info (write_var true x (Vint z) st1)).                             
Definition err_mk_WriteIndex' {E} `{ErrEvent -< E}
  (x: var_i) (z: Z) (st: ainfo_estate) : itree E ainfo_estate :=  
  err_result err
    (r2air (fst st) (write_var true x (Vint z) (snd st))).                             

(** EvalCond *)

Definition ret_mk_EvalCond {E} 
  (e: pexpr) (st1: estate) : execT (itree E) bool :=
   let vv := sem_pexpr true (p_globs pr) st1 e in                               
   match vv with
   | Ok (Vbool bb) => ret (ESok bb)
   | _ => ret (ESerror _ err) end.                       

Definition err_mk_EvalCond {E} `{ErrEvent -< E}
  (e: pexpr) (st1: estate) : itree E bool :=
   let vv := sem_pexpr true (p_globs pr) st1 e in                               
   match vv with
   | Ok (Vbool bb) => ret bb
   | _ => throw err end.                       

Definition err_mk_EvalCond' {E} `{ErrEvent -< E}
  (e: pexpr) (st: ainfo_estate) : itree E ainfo_bool :=
   let vv := sem_pexpr true (p_globs pr) (snd st) e in                      
   match vv with
   | Ok (Vbool bb) => ret (fst st, bb)
   | _ => throw err end.                       



(** EvalBound *)

Definition ret_mk_EvalBound {E} 
  (e: pexpr) (st1: estate) : execT (itree E) Z :=
   let vv := sem_pexpr true (p_globs pr) st1 e in                               
   match vv with
   | Ok (Vint zz) => ret (ESok zz)
   | _ => ret (ESerror _ err) end.                       

Definition err_mk_EvalBound {E} `{ErrEvent -< E}
  (e: pexpr) (st1: estate) : itree E Z :=
   let vv := sem_pexpr true (p_globs pr) st1 e in                               
   match vv with
   | Ok (Vint zz) => ret zz
   | _ => throw err end.                       

Definition err_mk_EvalBound' {E} `{ErrEvent -< E}
  (e: pexpr) (st: ainfo_estate) : itree E ainfo_Z :=
   let vv := sem_pexpr true (p_globs pr) (snd st) e in   
   match vv with
   | Ok (Vint zz) => ret (fst st, zz)
   | _ => throw err end.                       


(** AssgnE *)

(* terminating *)
Definition ret_mk_AssgnE {E: Type -> Type} 
  (x: lval) (tg: assgn_tag) (ty: stype) (e: pexpr) 
  (st1: estate) : execT (itree E) estate := Ret
   (r2xs (Let v := sem_pexpr true (p_globs pr) st1 e in 
    Let v' := truncate_val ty v in
    write_lval true (p_globs pr) x v' st1)).

Definition err_mk_AssgnE {E: Type -> Type} `{ErrEvent -< E}
  (x: lval) (tg: assgn_tag) (ty: stype) (e: pexpr) 
  (st1: estate) : itree E estate :=
    v <- err_result err (sem_pexpr true (p_globs pr) st1 e) ;;
    v' <- err_result err (truncate_val ty v) ;;
    err_result err (write_lval true (p_globs pr) x v' st1).

Definition err_mk_AssgnE' {E: Type -> Type} `{ErrEvent -< E}
  (x: lval) (tg: assgn_tag) (ty: stype) (e: pexpr) 
  (st: ainfo_estate) : itree E ainfo_estate :=
    v <- err_result err (sem_pexpr true (p_globs pr) (snd st) e) ;;
    v' <- err_result err (truncate_val ty v) ;;
    err_result err (r2air (fst st)
                      (write_lval true (p_globs pr) x v' (snd st))).


(** OpnE *)

(* terminating *)
Definition ret_mk_OpnE {E: Type -> Type} 
  (xs: lvals) (tg: assgn_tag) (o: sopn)
  (es : pexprs) (st1: estate) : execT (itree E) estate := Ret
    (r2xs (sem_sopn (p_globs pr) o st1 xs es)).

Definition err_mk_OpnE {E: Type -> Type} `{ErrEvent -< E}
  (xs: lvals) (tg: assgn_tag) (o: sopn)
   (es : pexprs) (st1: estate) : itree E estate :=
    err_result err (sem_sopn (p_globs pr) o st1 xs es).

Definition err_mk_OpnE' {E: Type -> Type} `{ErrEvent -< E}
  (xs: lvals) (tg: assgn_tag) (o: sopn)
   (es : pexprs) (st: ainfo_estate) : itree E ainfo_estate :=
  err_result err (r2air (fst st)
                    (sem_sopn (p_globs pr) o (snd st) xs es)).


(** SyscallE *)

(* terminating *)
Definition ret_mk_SyscallE {E: Type -> Type}
  (xs: lvals) (o: syscall_t)
  (es: pexprs) (st1: estate) : execT (itree E) estate := Ret 
   (r2xs (Let ves := sem_pexprs true (p_globs pr) st1 es in 
    Let r3 := exec_syscall st1.(escs) st1.(emem) o ves in 
    match r3 with
    | (scs, m, vs) =>
        write_lvals true (p_globs pr)
                    (with_scs (with_mem st1 m) scs) xs vs end)).

Definition err_mk_SyscallE {E: Type -> Type} `{ErrEvent -< E}
  (xs: lvals) (o: syscall_t) (es: pexprs) (st1: estate) :
  itree E estate :=
    ves <- err_result err (sem_pexprs true (p_globs pr) st1 es ) ;;
    r3 <- err_result err (exec_syscall st1.(escs) st1.(emem) o ves) ;;
    match r3 with
    | (scs, m, vs) =>
        err_result err (write_lvals true (p_globs pr)
                       (with_scs (with_mem st1 m) scs) xs vs) end.

Definition err_mk_SyscallE' {E: Type -> Type} `{ErrEvent -< E}
  (xs: lvals) (o: syscall_t) (es: pexprs) (st: ainfo_estate) :
  itree E ainfo_estate :=
    ves <- err_result err (sem_pexprs true (p_globs pr) (snd st) es ) ;;
    r3 <- err_result err (exec_syscall (snd st).(escs) (snd st).(emem) o ves) ;;
    match r3 with
    | (scs, m, vs) =>
        err_result err
          (r2air (fst st) (write_lvals true (p_globs pr)
                       (with_scs (with_mem (snd st) m) scs) xs vs)) end.


(*********************************************************************)
(*** INTERPRETERS WITH ERROR ******************************)

Definition ainfo_estate_updt (ii: instr_info) (ii_st: ainfo_estate) :
  ainfo_estate :=
 let inf' := ainfo_updt ii (fst ii_st) in (inf', snd ii_st). 

(** Auxiliary functions for recursion on list (seq) *)
Fixpoint st_cmd_map_r {E} (R: instr -> ainfo_estate -> itree E ainfo_estate)
  (c: cmd) (ii_st: ainfo_estate) : itree E ainfo_estate := 
  match c with 
  | nil => Ret ii_st 
  | i :: c' => ii_st' <- R i ii_st ;; st_cmd_map_r R c' ii_st'
  end.

Definition isem_foldr_r {E} (R: instr -> ainfo_estate -> itree E ainfo_estate)
  (c: cmd) : ainfo_estate -> itree E ainfo_estate :=
  foldr (fun i k s => s' <- R i s ;; k s')
        (fun s: ainfo_estate => Ret s) c.

(* state events *)
Variant InstrE : Type -> Type :=
  | AssgnE : lval -> assgn_tag -> stype -> pexpr -> instr_info ->
             ainfo_estate -> InstrE ainfo_estate
  | OpnE : lvals -> assgn_tag -> sopn -> pexprs ->
           instr_info -> ainfo_estate -> InstrE ainfo_estate
  | SyscallE : lvals -> syscall_t -> pexprs ->
               instr_info -> ainfo_estate -> InstrE ainfo_estate
  | EvalCond (e: pexpr) : instr_info -> ainfo_estate -> InstrE ainfo_bool
  | EvalBound (e: pexpr) : instr_info -> ainfo_estate -> InstrE ainfo_Z
  | WriteIndex (x: var_i) (z: Z) :
    instr_info -> ainfo_estate -> InstrE ainfo_estate
  | InitState (fn: funname) (vs: values) :
    instr_info -> ainfo_estate -> InstrE ainfo_estate
  | RetVal (fn: funname) : instr_info -> ainfo_estate -> InstrE ainfo_values.  

(* mutual recursion events *)
Variant MREvent : Type -> Type :=
  | LCode (c: cmd) (st: ainfo_estate) : MREvent ainfo_estate
  | FCall (xs: lvals) (f: funname) (es: pexprs) (st: ainfo_estate) :
    MREvent ainfo_estate.
  
Local Notation continue_loop st := (ret (inl st)).
Local Notation exit_loop st := (ret (inr st)).
Local Notation rec_call := (trigger_inl1). 

Fixpoint eval_for {E} `{ErrEvent -< E} `{InstrE -< E}
  (R: cmd -> ainfo_estate -> itree E ainfo_estate)                
  (i: var_i) (c: cmd) (ii: instr_info)
  (ls: list Z) (ai_st: ainfo_estate) :
  itree E ainfo_estate :=
    match ls with
    | nil => fun ai_st' => ret ai_st'
    | (w :: ws) => fun ai_st' =>
                     ai_st1 <- trigger (WriteIndex i w ii ai_st') ;;
                     ai_st2 <- R c ai_st1 ;;
                     eval_for R i c ii ws ai_st2
    end ai_st.

Fixpoint esem_instr {E} `{ErrEvent -< E} `{InstrE -< E}
  (i : instr) (ai_st: ainfo_estate) :
  itree (MREvent +' E) ainfo_estate := 
  let R := st_cmd_map_r esem_instr in
  let: (MkI ii ir) := i in 
  match ir with
  | Cassgn x tg ty e => trigger (AssgnE x tg ty e ii ai_st)
  | Copn xs tg o es => trigger (OpnE xs tg o es ii ai_st)
  | Csyscall xs o es => trigger (SyscallE xs o es ii ai_st)
  | Cif e c1 c2 =>
      let st := snd ai_st in
      ib <- trigger (EvalCond e ii ai_st) ;;
      if snd ib then R c1 (fst ib, st) else R c2 (fst ib, st)                
  | Cfor i (d, lo, hi) c => 
      let st := snd ai_st in
      ai_vlo <- trigger (EvalBound lo ii ai_st) ;;
      ai_vhi <- trigger (EvalBound hi ii (fst ai_vlo, st)) ;;
      eval_for R i c ii (wrange d (snd ai_vlo) (snd ai_vhi)) (fst ai_vhi, st)
  | Cwhile a c1 e inf c2 => 
      ITree.iter (fun ai_st0 =>
           ai_st1 <- R c1 ai_st0 ;;          
           ai_b <- trigger (EvalCond e ii ai_st1) ;;
           let ai_st1' := (fst ai_b, snd ai_st1) in 
           if snd ai_b then ai_st2 <- R c2 ai_st1' ;; continue_loop ai_st2
           else exit_loop ai_st1') ai_st
  | Ccall xs fn es => rec_call (FCall xs fn es ai_st)      
  end.

Definition meval_fcall {E} `{ErrEvent -< E} `{InstrE -< E}
  (xs: lvals) (fn: funname) (es: pexprs) (st0: ainfo_estate) :
  itree (MREvent +' E) ainfo_estate :=
  va <- err_eval_Args fn es (snd st0) ;; 
  st1 <- err_init_state' fn va (snd st0) ;; 
  c <- err_get_FunCode fn ;; 
  st2 <- rec_call (LCode c st1) ;; 
  vs <- err_return_val' fn (snd st2) ;; 
  err_reinstate_caller' fn xs (snd vs) (snd st2) (snd st0).

Definition meval_cstate {E} `{ErrEvent -< E} `{InstrE -< E} :
  MREvent ~> itree (MREvent +' E) :=           
  fun _ fs => match fs with
              | LCode c st => st_cmd_map_r esem_instr c st
              | FCall xs fn es st => meval_fcall xs fn es st      
              end.      

Definition mevalE_cmd {E} `{ErrEvent -< E} `{InstrE -< E}
  (c: cmd) (st: ainfo_estate) :
  itree E ainfo_estate :=
  mrec meval_cstate (LCode c st).

(*
Definition meval_cmd {E} (c: cmd) (st: estate) : itree E (option estate) := 
  @interp_Err E estate (mevalE_cmd c st).
*)

Definition mevalE_fun {E} `{ErrEvent -< E} `{InstrE -< E} :
  instr_info -> AInfo -> (funname * (values * estate)) -> 
  itree E (ainfo_values * ainfo_estate) :=
  fun ii ai fvst =>
    let '(fn, (va, st)) := fvst in
    st1 <- trigger (InitState fn va ii (ai, st)) ;;
    c <- err_get_FunCode fn ;;
    st2 <- mevalE_cmd c st1 ;;
    vs <- trigger (RetVal fn ii st2) ;;
    ret (vs, st2).

Definition meval_fun_ {E} `{ErrEvent -< E} `{InstrE -< E} 
  (ai: AInfo) (fn: funname) (va: values) (st0: estate) :
  itree (MREvent +' E) (ainfo_values * ainfo_estate) :=
  st1 <- err_init_state' fn va st0 ;;
  c <- err_get_FunCode fn ;;
  st2 <- rec_call (LCode c st1) ;;
  vs <- err_return_val' fn (snd st2) ;;
  ret (vs, st2).

(** InstrE handler *)
Definition handle_InstrE {E: Type -> Type} 
  `{ErrEvent -< E} : InstrE ~> itree E :=
  fun _ e =>
    match e with
    | AssgnE xs tg ty es ii st => err_mk_AssgnE' xs tg ty es st
    | OpnE xs tg o es ii st => err_mk_OpnE' xs tg o es st
    | SyscallE xs o es ii st => err_mk_SyscallE' xs o es st                              
    | EvalCond e ii st => err_mk_EvalCond' e st
    | EvalBound e ii st => err_mk_EvalBound' e st
    | WriteIndex x z ii st => err_mk_WriteIndex' x z st                              
    | InitState fn es ii st => err_init_state' fn es (snd st)
    | RetVal fn ii st => err_return_val' fn (snd st)
    end.                                            
        
Definition ext_handle_InstrE {E: Type -> Type} 
  `{ErrEvent -< E} : InstrE +' E ~> itree E :=
  case_ handle_InstrE (id_ E).

(* InstrE interpreter *)
Definition interp_InstrE {E: Type -> Type} 
  `{ErrEvent -< E} {A: Type}
  (t : itree (InstrE +' E) A) : itree E A :=
  interp ext_handle_InstrE t.


End ModularSem.


(****************************************************************)

Require Import array_init.

Section ArrayInit.

  (* Analysis info *)
Local Notation AInfo := Sv.t.  
Context (empty_ainfo : AInfo).
Context (ainfo_updt : instr_info -> AInfo -> AInfo).

Notation ainfo_estate := (AInfo * estate)%type.
Notation ainfo_bool := (AInfo * bool)%type.
Notation ainfo_Z := (AInfo * Z)%type.
Notation ainfo_values := (AInfo * values)%type.


(*
Check @add_init_i.
@add_init_i : forall (asm_op : Type) (asmop : asmOp asm_op),
       Sv.t -> instr -> cmd * Sv.t
*)

Definition add_init_Aux_g (ai: AInfo) (ii: instr_info) (ir: instr_r) :
  (cmd * Sv.t) := 
    let Wi := write_i ir in
    let Ri := read_i ir in
    let extra := Sv.union Wi Ri in
    (add_init (ii_with_location ii) ai extra (MkI ii ir), Sv.union ai Wi).


(** InstrE handler for Array Init *)
Definition handle_InstrE_init {E: Type -> Type} 
  `{ErrEvent -< E} `{InstrE AInfo -< E} : InstrE AInfo ~> itree E :=
  fun _ e =>
    match e with
    | AssgnE xs tg ty es ii ai_st =>
        let ir := Cassgn xs tg ty es in
        let '(cmd1, ai1) := add_init_Aux_g (fst ai_st) ii ir in
        @mevalE_cmd AInfo empty_ainfo _ _ _ cmd1 (ai1, snd ai_st)
    | OpnE xs tg o es ii ai_st =>
        let ir := Copn xs tg o es in
        let '(cmd1, ai1) := add_init_Aux_g (fst ai_st) ii ir in
        @mevalE_cmd AInfo empty_ainfo _ _ _ cmd1 (ai1, snd ai_st)
    | SyscallE xs o es ii ai_st => 
        let ir := Csyscall xs o es in
        let '(cmd1, ai1) := add_init_Aux_g (fst ai_st) ii ir in
        @mevalE_cmd AInfo empty_ainfo _ _ _ cmd1 (ai1, snd ai_st)
   | _ => throw err
    end.             

(* Remark: R does not use ainfo, which comes from aic. the monad
   shoudl be fixed. *)
Definition isem_foldr2 {E} 
  (R: instr -> ainfo_estate -> itree E ainfo_estate)
  (aic: (cmd * AInfo)) : ainfo_estate -> itree E ainfo_estate :=
  foldr (fun i k (s: ainfo_estate) => s' <- R i (snd aic, snd s) ;; k s')
        (fun s: ainfo_estate => Ret s) (fst aic).

(* *)
Definition isem_foldr1 {E} 
  (R: instr -> estate -> itree E estate)
  (aic: (cmd * AInfo)) : estate -> itree E ainfo_estate :=
  foldr (fun i k (s: estate) => s' <- R i s ;; k s')
        (fun s: estate => Ret (snd aic, s)) (fst aic).

Fixpoint st_cmd_map_r_AI2 {E}
  (R: instr -> ainfo_estate -> itree E ainfo_estate)
  (c: cmd) (ii_st: ainfo_estate) : itree E ainfo_estate := 
  match c with 
  | nil => Ret ii_st 
  | i :: c' =>
      ii_st' <- isem_foldr2 R (add_init_i (fst ii_st) i) ii_st ;;
      st_cmd_map_r_AI2 R c' ii_st'
  end.

Fixpoint st_cmd_map_r_AI1 {E} (R: instr -> estate -> itree E estate)
  (c: cmd) (ii_st: ainfo_estate) : itree E ainfo_estate := 
  match c with 
  | nil => Ret ii_st 
  | i :: c' => ii_st' <- isem_foldr1 R (add_init_i (fst ii_st) i) (snd ii_st) ;;
               st_cmd_map_r_AI1 R c' ii_st'
  end.

(*   
initialization of I in a function call: 
let I := vrvs [seq (Lvar i) | i <- f_params fd] in
*)
Definition meval_cstate_AI2 {E} {X1: ErrEvent -< E} {X2: InstrE AInfo -< E} :
  MREvent AInfo ~> itree (MREvent AInfo +' E) :=           
  fun _ fs => match fs with
              | LCode c ai_st => st_cmd_map_r_AI2
                                   (@esem_instr AInfo E X1 X2) c ai_st
              | FCall xs fn es ai_st =>
                  @meval_fcall AInfo empty_ainfo E X1 X2 xs fn es ai_st      
              end.      


End ArrayInit.

End WSW.

