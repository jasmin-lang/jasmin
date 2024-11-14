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

From Jasmin Require Import expr it_lib psem_defs psem.

Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.

Obligation Tactic := done || idtac.

(**** ERROR SEMANTICS *******************************************)
Section Errors.

(* type of errors (this might becom richer) *)
Variant ErrType : Type := Err : ErrType. 
(* error events *)
Definition ErrState : Type -> Type := exceptE ErrType.

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


(*** auxiliary functions *)

Definition err_get {E: Type -> Type} 
  `{ErrState -< E} {S} {V} (f: S -> option V) :
  stateT S (itree E) V :=
  fun st => match (f st) with
            | Some v => Ret (st, v)
            | None => throw Err end.                

Definition err_put {E: Type -> Type} 
  `{ErrState -< E} {S} (f: S -> option S) :
  stateT S (itree E) unit :=
  fun st => match (f st) with
            | Some st' => Ret (st', tt)
            | None => throw Err end.                

Definition err_write {E: Type -> Type} 
  `{ErrState -< E} {S} (ms: option S) :
  stateT S (itree E) unit :=
  fun st => match ms with
            | Some st' => Ret (st', tt)
            | None => throw Err end.                

Definition err_opt {E: Type -> Type} 
  `{ErrState -< E} : option ~> itree E :=
  fun _ t => match t with
             | Some v => Ret v
             | None => throw Err end.                

Definition err_st_opt {E: Type -> Type} 
  `{ErrState -< E} {S} : option ~> stateT S (itree E) :=
  fun _ t st => match t with
                | Some v => Ret (st, v)
                | None => throw Err end.                

End Errors.

(*********************************************************************)

(*
Inductive instr_r :=
| Cassgn   : lval -> assgn_tag -> stype -> pexpr -> instr_r
| Copn     : lvals -> assgn_tag -> sopn -> pexprs -> instr_r
| Csyscall : lvals -> syscall_t -> pexprs -> instr_r 
| Cif      : pexpr -> seq instr -> seq instr  -> instr_r
| Cfor     : var_i -> range -> seq instr -> instr_r
| Cwhile   : align -> seq instr -> pexpr -> seq instr -> instr_r
| Ccall    : lvals -> funname -> pexprs -> instr_r
*)

Section Lang.
Context `{asmop:asmOp}.

(** Events *)

(* neutral reader events; here args and dests are meant to be symbolic
locations associated to the function (concretely, stackframe
locations) *)
Variant FunE : Type -> Type :=
  | FunCode (fn : funname) : FunE cmd
  | FunArgs (fn: funname) : FunE lvals
  | FunDests (fn: funname) : FunE lvals.                               

(* neutral state events *)
Variant StE : Type -> Type :=
  | EvalCond (e: pexpr) : StE bool 
  | EvalBound (e: pexpr) : StE Z
  | WriteVar (x: var_i) (z: Z) : StE unit                             
(* evaluates the expressions es and copy the values to la (local
addresses in the stack frame) *)
  | InitState (es: pexprs) (la: lvals) : StE unit
(* copy the results in ld (local addesses in the stack frame) to gd
(global ones) *)  
  | SetDests (ld gd: lvals) : StE unit.  

Variant InstrE : Type -> Type :=
  | AssgnE : lval -> assgn_tag -> stype -> pexpr -> InstrE unit
  | OpnE : lvals -> assgn_tag -> sopn -> pexprs -> InstrE unit
  | SyscallE : lvals -> syscall_t -> pexprs -> InstrE unit. 
  
(* neutral mutual recursion events *)
Variant CState : Type -> Type :=
 | LCode (c: cmd) : CState unit
 | FCall (xs: lvals) (f: funname) (es: pexprs) : CState unit.

(** Auxiliary, for recursion on list (seq) *)

Fixpoint cmd_map {E} (R: instr -> itree E unit)
  (c: cmd) : itree E unit := 
  match c with 
  | nil => Ret tt 
  | i :: c => R i ;; cmd_map R c
  end.

Fixpoint cmd_map_r {E} (R: instr_r -> itree E unit)
  (c: cmd) : itree E unit := 
  match c with 
  | nil => Ret tt 
  | (MkI _ i) :: c => R i ;; cmd_map_r R c
  end.


Section With_MREC.
Context (Eff : Type -> Type)
        (HasFunE : FunE -< Eff)
        (HasStE : StE -< Eff)
        (HasInstrE : InstrE -< Eff).   

Definition denote_fcall (xs: lvals) (fn: funname) (es: pexprs) :
  itree (CState +' Eff) unit :=
  la <- trigger (FunArgs fn) ;;
  trigger (InitState es la) ;; 
  c <- trigger (FunCode fn) ;;   
  trigger_inl1 (LCode c) ;; 
  ld <- trigger (FunDests fn) ;; 
  trigger (SetDests ld xs).

Fixpoint denote_instr (i : instr_r) : itree (CState +' Eff) unit := 
  let R := cmd_map_r denote_instr in
  match i with
  | Cassgn x tg ty e => trigger (AssgnE x tg ty e)
  | Copn xs tg o es => trigger (OpnE xs tg o es)
  | Csyscall xs o es => trigger (SyscallE xs o es)                          
                                
  | Cif e c1 c2 =>
      b <- trigger (EvalCond e) ;;
      if b then R c1 else R c2 

  | Cfor i rng c =>
      match rng with
      | (d, e1, e2) =>
          ITree.iter (fun _ =>
            ITree.bind (trigger (EvalBound e1))
            (fun lb => ITree.bind (trigger (EvalBound e2))
            (fun ub =>                     
            match (wrange d lb ub) with
            | nil => ret (inr tt)
            | (w :: ws) => trigger (WriteVar i w) ;; R c ;; ret (inl tt)
            end))) tt
      end
        
  | Cwhile a c1 e c2 => 
      ITree.iter (fun _ =>
           R c1 ;;          
           b <- trigger (EvalCond e) ;;
           if b then (R c2) ;; ret (inl tt) 
           else ret (inr tt)) tt 
  
  | Ccall xs fn es => trigger_inl1 (FCall xs fn es)      
  end.

Definition denote_cstate : CState ~> itree (CState +' Eff) :=           
  fun _ fs => match fs with
              | LCode c => cmd_map_r denote_instr c
              | FCall xs fn es => denote_fcall xs fn es       
              end.      

(* denotational interpreter *)
Definition denote_cmd (c: cmd) : itree Eff unit :=
  mrec denote_cstate (LCode c).

(* for single instructions *)
Definition denote_cmd1 (i: instr) : itree Eff unit :=
  denote_cmd (i :: nil).

End With_MREC.

End Lang.


