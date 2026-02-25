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

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat ssralg. 
From Coq Require Import ZArith Utf8.

Require Import expr fexpr label sopn.
Require Import fexpr_sem compiler_util label one_varmap
               linear sem_one_varmap linear_sem label
               psem_defs psem_core it_exec it_exec_sem tfam_iso
               eutt_extras rec_facts it_cflow_sem it_effect_sem.
Require Import linearization_ext.

Require Import it_cflow_semS it_effect_semS equiv_extras rutt_extras.

From ITree Require Import Rutt RuttFacts.

Import Memory.
Require oseq.
Require Import Relations.
Require Import List.

Import ListNotations. 
Import MonadNotation.
Local Open Scope monad_scope.

(** some is GENERAL -> move elsewhere *)

Definition conv_obj T1 T2 (ee: T1 = T2) (u: T1) : T2 :=
  eq_rect T1 (fun T : Type => T) u T2 ee.

(* point in the linear code of a function *)
Definition lpoint : Type := (funname * nat)%type.

Definition incr_lpoint (l: lpoint) : lpoint :=
  match l with (fn, pt) => (fn, S pt) end.

(* abstract stack *)
Definition astack := list lpoint.

(* Push and Pop are only needed in the Linear semantics, to model
   control-flow while abstracting from the state. In the Intermediate
   one, we can model control-flow without maintaining a stack as we
   have recursive calls. So in there these events should disappear (by
   interpreting them as skips). FindLabel might need to be interpreted
   differently in Linear and Intermediate, too.  Basically: need to be
   interpreted in both Linear and Intermediate, but possibly in
   different ways.  *)
Variant AStackE : Type -> Type :=
  | Push (l: lpoint) : AStackE unit
  | Pop : AStackE lpoint
  | FindLabel (lbl: remote_label) : AStackE lpoint. 

(* Linear actions we are currently abstracting on (might ultimately
   replaced by parameters). Need to be interpreted only for the
   comparison with Source. *)
Variant LEvalE : Type -> Type :=
  | EvalLoc (e: rexpr) : LEvalE remote_label
  | EvalExp (e: fexpr) : LEvalE bool.

(* Ultimately, both the abtract stack and the abstract pc (as an
   lpoint) will come from the lstate and should agree it. Needed as
   internal check in Linear. However, these might just be invariants
   in the end. *)
Variant LCheckE : Type -> Type :=
  | MatchLabel (lbl: lpoint) : LCheckE unit
  | MatchStack : LCheckE unit. 
                              
Section Asm1.  

Context  {asm_op: Type}
         {syscall_state : Type}
         {sip : SemInstrParams asm_op syscall_state}.  
Context {err: error_data}. 
(* | _ => throw err end. *) 
(* Context {asm_op: Type} {asmop: asmOp asm_op}. *)
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
  {scP : semCallParams}.
Context {err: error_data}. 
*)

Section LinSemClass.

Context (S: Type).

(* We use this class to help abstracting over the paramters required
   by lstate, with which we will instantiate S. *)
Class LinSem : Type := {
  Lopn_sem (xs: seq.seq lexpr) (o: sopn) (es: seq.seq rexpr) (s1: S) : exec S ;

  Lsyscall_sem (o: syscall_t) (s1: S) : exec S ;

  Lcall_sem (ov: option var_i) (d: remote_label) (s1: S) : exec S ;

  Lret_sem (s1: S) : exec S ;

  Lalign_sem (s1: S) : exec S ;

  Llabel_sem (k: label_kind) (lbl: label) (s1: S) : exec S ;

  Lgoto_sem (d: remote_label) (s1: S) : exec S ;

  Ligoto_sem (e: rexpr) (s1: S) : exec S ;

  Lstorelabel_sem (x: var) (lbl: label) (s1: S) : exec S ;

  Lcond_sem (e: fexpr) (lbl: label) (s1: S) : exec S ; }.

(* basically, same as eval_instr (in the old semantics, with S =
   lstate) *)
Definition linstr_sem {LS_I : LinSem} (i : linstr_r)
  (s1: S) : exec S := match i with
  | Lopn xs o es => Lopn_sem xs o es s1
  | Lsyscall o => Lsyscall_sem o s1
  | Lcall o d => Lcall_sem o d s1
  | Lret => Lret_sem s1
  | Lalign => Lalign_sem s1
  | Llabel x y => Llabel_sem x y s1
  | Lgoto d => Lgoto_sem d s1
  | Ligoto e => Ligoto_sem e s1
  | LstoreLabel x lbl => Lstorelabel_sem x lbl s1
  | Lcond e lbl => Lcond_sem e lbl s1
  end.

End LinSemClass.


Section LinearSem.
  
Context (LState: Type) (LS_I : LinSem LState).

Context {E} {XA: AStackE -< E} {XL: LEvalE -< E }
            {XSl: @stateE LState -< E} {XE: ErrEvent -< E}.

(* core semantics of linear instructions, abstracting LState in
   linstr_sem *)
Definition isem_i_core (i : linstr_r) : itree E unit :=
  s1 <- trigger (@Get LState) ;;
  s2 <- iresult (linstr_sem i s1) s1 ;;
  trigger (@Put LState s2).

(* semantics of control-flow abstraction *)
Definition isem_i_lflow (ir : linstr_r) (l0 : lpoint) : itree E lpoint :=
  match ir with
  | Lopn xs o es => Ret (incr_lpoint l0)
  | Lsyscall o => Ret (incr_lpoint l0)
  | Lcall o d => trigger (Push (incr_lpoint l0)) ;; trigger (FindLabel d)
  | Lret => trigger Pop
  | Lalign => Ret (incr_lpoint l0)
  | Llabel x y => Ret (incr_lpoint l0)
  | Lgoto d => trigger (FindLabel d)
  | Ligoto e => d <- trigger (EvalLoc e) ;; trigger (FindLabel d)
  | LstoreLabel x lbl => Ret (incr_lpoint l0)
  | Lcond e lbl => b <- trigger (EvalExp e) ;;
                   if b then trigger (FindLabel (fst l0, lbl))
                   else Ret (incr_lpoint l0)
end.

(* semantics of linear instruction, instrumented with control-flow
   abstraction *)
Definition isem_linstr (i : linstr_r) (l0: lpoint) : itree E lpoint :=
  isem_i_core i ;; isem_i_lflow i l0.


Section HandleStackA.

Context {XSa: @stateE astack -< E}.

(* AStack handling for Linear *)
Definition handle_AStackL {T} (e: AStackE T) : itree E T :=
  match e with    
  | Push l => stk <- trigger (@Get astack) ;;
              trigger (@Put astack (l :: stk))
  | Pop => stk <- trigger (@Get astack) ;;
           match stk with
           | nil => throw err
           | l0 :: ls => trigger (@Put astack ls) ;; Ret l0 end
  (* TODO *)           
  | FindLabel lbl => throw err           
  end.   

End HandleStackA.


Section Iterator.

(* the output of the linearization pass *)
Notation LFEnv := (funname -> option lcmd). 
Context (lfenv: LFEnv).
Context {S: Type} {PC : S -> lpoint}. 

Definition find_linstr_in_env (lc: lcmd) (pt: nat) : option linstr :=
  oseq.onth lc pt.

Definition is_final (lc: lcmd) (pt: nat) : bool :=
  pt =? (length lc).

(* the program point is in the interval *)
Definition lcp_in_interval (fn: funname) (nS nE: nat) (l1: lpoint) : bool :=
  match l1 with
  | (fn0, n0) => (fn == fn0) && (nS <= n0) && (n0 < nE) end. 

Definition halt_pred (l: lpoint) : bool :=
  let fn := fst l in
  let lbl := snd l in
  let plc := lfenv fn in
  match plc with
  | Some lc => is_final lc lbl 
  | _ => false
  end.             


(* the 'local' iteration body used in the linear projection semantics
   of the source code. nS and nE are the start and end points of the
   linear code interval that contextualize the execution. l1 is the
   linear code point being executed. *)
Definition LCntr {E} {XE: ErrEvent -< E}  
  (F: linstr_r -> S -> itree E S)
  (fn: funname) (nS nE: nat) (l0: S) : itree E (S + S) :=
  let l1 := PC l0 in
  match l1 with
  | (fn1, n1) =>
  (* the optional function body *)
    match lfenv fn1 with
    | None => throw err      
    (* the function exists: find the instruction in its body *)
    | Some lc =>
      if (length lc < nE) then throw err else
      if lcp_in_interval fn nS nE l1
      (* (fn == fn1) && (nS <= n1) && (n1 < nE) *)
      (* the instruction exists in the segment: execute it and
         return the next label *) 
      then match find_linstr_in_env lc n1 with
           | Some (MkLI _ i) => l2 <- F i l0 ;; Ret (inl l2)
           (* n1 < nE and nE <= length lc, so this cannot happen *) 
           | _ => throw err                                         
           end
      (* the instruction is not in the function code segment *)         
      else Ret (inr l0)
    end
  end.        

(* iterate LCntr *)
Definition LCntrI {E} {XE: ErrEvent -< E}  
  (F: linstr_r -> S -> itree E S)
  (fn: funname) (nS nE: nat) (l0: S) : itree E S :=
  ITree.iter (@LCntr E XE F fn nS nE) l0.

End Iterator.


