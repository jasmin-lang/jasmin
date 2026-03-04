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

(* the program point is in the interval *)
Definition lcp_in_interval (nS nE: nat) (l1: lpoint) : bool :=
  match l1 with
  | (_, n0) => (nS <= n0) && (n0 < nE) end. 

(* FindLabel could be interpreted differently in Linear and
   Intermediate (using LFenv and IFEnv; anyway, GLFEnvAx makes the
   difference inessential). *)
Variant LFindE : Type -> Type :=
  | FindLabel (lbl: remote_label) : LFindE lpoint. 

(* JumpForth and JumpBack are used to instrument the Linear semantics;
   two possible interpretations: directly with LState, or more
   abstractly with astack.  *)
Variant LFunE : Type -> Type :=
  | JumpForth (l: lpoint) (lbl: remote_label) : LFunE lpoint
  | JumpBack : LFunE lpoint.

(* Linear actions we are abstracting on (might be ultimately replaced
   by parameters). Need to be interpreted only for the comparison with
   Source.  *)
Variant LEvalE : Type -> Type :=
  | EvalLoc (e: rexpr) : LEvalE remote_label
  | EvalExp (e: fexpr) : LEvalE bool. 


Section Asm1.  

Notation plinfo := (nat * label)%type.

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

Definition find_linstr (lc: lcmd) (pt: nat) : option linstr :=
  oseq.onth lc pt.

Definition is_final (lc: lcmd) (pt: nat) : bool :=
  pt =? (length lc).


Section LinSemClass.

Context (S: Type).

(* We use this class on S to abstract over the paramters required by
   lstate. *)
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

Context {E} {XF: LFindE -< E} {XA: LFunE -< E} {XL: LEvalE -< E }
            {XSl: @stateE LState -< E} {XE: ErrEvent -< E}.

(* the core semantics of linear instructions, based on linstr_sem *)
Definition isem_li_core (i : linstr_r) (s: LState) :
  itree E LState :=
  iresult (linstr_sem i s) s.

(* abstract core semantics of linear instructions, hiding the state *)
Definition isem_li_acore (i : linstr_r) : itree E unit :=
  s1 <- trigger (@Get LState) ;;
  s2 <- isem_li_core i s1 ;;
  trigger (@Put LState s2).

(* instrumenting semantics of control-flow abstraction, used to
   instrument the core one *)
Definition instrum_lflow (ir : linstr_r) (l0 : lpoint) : itree E lpoint :=
  match ir with
  | Lopn xs o es => Ret (incr_lpoint l0)
  | Lsyscall o => Ret (incr_lpoint l0)
  | Lcall o d => trigger (JumpForth (incr_lpoint l0) d)
  | Lret => trigger JumpBack 
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
Definition isem_li_flow (i : linstr_r) (l0: lpoint) : itree E lpoint :=
  isem_li_acore i ;; instrum_lflow i l0.


Section Iterators.

(* the output of the linearization pass; lfenv should be defined using
   linear_l2r_fd and imed_fun. then the axiom holds by
   forget_imed_fun_ok. *)
Notation GLFEnv :=
    (forall fn: funname, option (plinfo * lfundef * LTreeFun fn)). 
Context (glfenv: GLFEnv).
Context (GLFEnvAx : forall (fn: funname) pl fd lt,
            glfenv fn = Some (pl, fd, lt) ->
            forget_imed_fun lt = (pl, lfd_body fd)).

Notation LFEnv := (funname -> option lcmd).
Notation IFEnv := (forall fn: funname, option (LTreeFun fn)).

Definition lfenv : LFEnv := fun fn => match glfenv fn with
                       | Some (_, fd, _) => Some (lfd_body fd)
                       | _ => None end.                              

Definition ifenv : IFEnv := fun fn => match glfenv fn with
                       | Some (_, _, lt) => Some lt
                       | _ => None end.                              

Definition halt_pred (l: lpoint) : option bool :=
  let fn := fst l in
  let lbl := snd l in
  let plc := lfenv fn in
  match plc with
  | Some lc => Some (is_final lc lbl) 
  | _ => None
  end.             

Definition not_possible (fn: funname) (n: nat) : bool :=
  let lc := lfenv fn in
  match lc with
  | Some lc => if (length lc < n) then true else false 
  | _ => true
  end.             

Definition find_linstr_in_fun (lp : lpoint) : option linstr :=
  match lfenv (fst lp) with
  | Some lc => find_linstr lc (snd lp)
  | _ => None
  end.                         

(* the generic iteration body used in the Linear and Intermediate
    semantics. l0 is the linear code point being executed. *)
Definition ACntr {L: Type} {E} {XE: ErrEvent -< E}                 
  (Sem: linstr_r -> L -> itree E L)
  (NoExit: L -> option bool) (TryFnd: L -> option linstr)
  (l0: L) : itree E (L + L) :=
  (* check whether the exit condition is satisfied *)
  match NoExit l0 with
  | Some b =>
    (* tries to find the next instruction *)  
    if b then match TryFnd l0 with
              | Some (MkLI _ i) => l1 <- Sem i l0 ;; Ret (inl l1)
              | None => throw err                                         
              end        
    else Ret (inr l0)
  | None => throw err
  end.

(* iterate ACntr *)
Definition ACntrI {L: Type} {E} {XE: ErrEvent -< E}  
  (Sem: linstr_r -> L -> itree E L)
  (NoExit: L -> option bool) (TryFnd: L -> option linstr)
  (lp0: L) : itree E L :=
  ITree.iter (@ACntr L E XE Sem NoExit TryFnd) lp0.

(*
Definition LACntr {L: Type} {PC: L -> lpoint} {E} {XE: ErrEvent -< E}  
  (Sem: linstr_r -> L -> itree E L)
  (fn: funname) (nS nE: nat) (l1: L) :
  itree E (L + L) :=
  ACntr Sem
    (* exit condition: when it jumps to another function, gets out of
       the range, or makes a recursive call (n0 = 0) *)
    (fun l0 =>
       let '(fn0, n0) := PC l0 in  
       if (not_possible fn0 nE) then None
       else Some ((fn == fn0) 
            && (nS <= n0) && (n0 < nE) && (0 < n0)))
    (fun l0 => find_linstr_in_fun (PC l0)) l1.

Definition LACntrI {L: Type} {PC: L -> lpoint} {E} {XE: ErrEvent -< E}  
  (Sem: linstr_r -> L -> itree E L)
  (fn: funname) (nS nE: nat) (lp0: L) : itree E L :=
  ITree.iter (@LACntr L PC E XE Sem fn nS nE) lp0.
*)

(* the 'local' iteration body for the Intermediate semantics. nS and
   nE are the start and end points in the fn linear code wrt to which
   execution is contextual. *)
Definition LCntr {E} {XE: ErrEvent -< E}  
  (Sem: linstr_r -> lpoint -> itree E lpoint)
  (fn: funname) (nS nE: nat) (lp0: lpoint) :
  itree E (lpoint + lpoint) :=
  ACntr Sem
    (* exit condition: when it jumps to another function, gets out of
       the range, or makes a recursive call (n0 = 0) *)
    (fun '(fn0, n0) => 
       if (not_possible fn0 nE) then None
       else Some ((fn == fn0) 
            && (nS <= n0) && (n0 < nE) && (0 < n0)))
    find_linstr_in_fun lp0.

(* iterate LCntr *)
Definition LCntrI {E} {XE: ErrEvent -< E}  
  (Sem: linstr_r -> lpoint -> itree E lpoint)
  (fn: funname) (nS nE: nat) (lp0: lpoint) : itree E lpoint :=
  ITree.iter (@LCntr E XE Sem fn nS nE) (fn, nS).

(* the 'global' iteration body for the Linear semantics. *)
Definition GCntr {E} {XE: ErrEvent -< E}  
  (Sem: linstr_r -> lpoint -> itree E lpoint)
  (lp0: lpoint) : itree E (lpoint + lpoint) :=
  ACntr Sem halt_pred find_linstr_in_fun lp0.

(* iterate GCntr *)
Definition GCntrI {E} {XE: ErrEvent -< E}  
  (Sem: linstr_r -> lpoint -> itree E lpoint)
  (lp0: lpoint) : itree E lpoint :=
  ITree.iter (@GCntr E XE Sem) lp0.

(* iterative semantics body *)
Definition isem_lcmd_flow_body (lbl: lpoint) :
  itree E (lpoint + lpoint) := GCntr isem_li_flow lbl.

(* iterative semantics of a linear program, from any starting point *)
Definition isem_lcmd_flow (lp : lpoint) : itree E lpoint :=
  ITree.iter isem_lcmd_flow_body lp.

(* iterative semantics of a linear function from its entry point *)
Definition isem_lfun_flow (fn: funname) : itree E lpoint :=
  isem_lcmd_flow (fn, 0).

(* stateful iterative semantics body *)
Definition isem_lcmd_core_body (Hlt: LState -> option bool)
  (Fnd: LState -> option linstr) (lbl: LState) :
  itree E (LState + LState) := ACntr isem_li_core Hlt Fnd lbl.

(* stateful iterative semantics of a linear program, from any state *)
Definition isem_lcmd_core (Hlt: LState -> option bool)
  (Fnd: LState -> option linstr) (lbl: LState) : itree E LState :=
  ITree.iter (isem_lcmd_core_body Hlt Fnd) lbl.


(* LFindE handling *)
Definition handle_LFind {T} (e: LFindE T) : itree E T :=
  match e with    
  | FindLabel rlbl =>
      match lfenv (fst rlbl) with
      | Some lc =>
          n <- err_result (fun _ => err) (find_label (snd rlbl) lc) ;;
          Ret (fst rlbl, n)
      | _ => throw err
      end             
  end.   


Section HandleStackS.
  
Context {readRA : LState -> lpoint}.

(* LFunE handling for Linear *)
Definition handle_LFunS {T} (e: LFunE T) : itree E T :=
  match e with    
  | JumpForth l rlbl => st <- trigger (@Get LState) ;;
                  match (readRA st == l) with
                  | true => trigger (FindLabel rlbl)
                  | _ => throw err
                  end     
  | JumpBack => st <- trigger (@Get LState) ;; Ret (readRA st) 
  end.   

End HandleStackS.


(* abstract stack *)
Definition astack := list lpoint.

Section HandleStackA.

Context {XSa: @stateE astack -< E}.

(* AStack handling for Linear *)
Definition handle_AStackA {T} (e: LFunE T) : itree E T :=
  match e with    
  | JumpForth l rlbl => stk <- trigger (@Get astack) ;;
                        trigger (@Put astack (l :: stk)) ;;
                         trigger (FindLabel rlbl)
  | JumpBack => stk <- trigger (@Get astack) ;;
           match stk with
           | nil => throw err
           | l0 :: ls => trigger (@Put astack ls) ;; Ret l0 end
  end.   

End HandleStackA.

End Iterators.


(*******************************************************************)

Notation LCall := (callE funname unit).

Definition LLeaf_ok (li: linstr) : bool :=
  match li with
  | MkLI ii (Lopn xs o es) => true 
  | MkLI ii (Lsyscall o) => true      
  | _ => false
  end.   

Definition LIf1Node_ok (li1 li2: linstr) : bool :=
  match (li1, li2) with
  | (MkLI ii0 (Lcond e lbl), MkLI ii1 (Llabel InternalLabel lbl')) =>
      lbl == lbl'
  | _ => false
  end.         

Definition LCallNode_ok (nb na: nat) (fn: funname)
  (lcb lca: lcmd) (li1 li2: linstr) :
  bool :=
  if (length lcb == nb)
  then if (length lca == na)   
       then match (li1, li2) with
       | (MkLI ii0 (Lcall _ (fn0, xH)),
           MkLI ii1 (Llabel ExternalLabel _)) => fn == fn0
       | _ => false
       end         
       else false
  else false.            

(* linear semantics of the source code, for the intermediate
   representation. assuming lfenv gives the linear code *)
Fixpoint lsem_i_imed 
  {E} {XE: ErrEvent -< E}
  (LS1: linstr_r -> lpoint -> itree (LCall +' E) lpoint)
  (LSC: lcmd -> itree (LCall +' E) unit)
  (LS2: funname -> nat -> nat ->
        lpoint -> itree (LCall +' E) (lpoint + lpoint))
  (fn: funname) (plS plE: plinfo)
  (lt : LTree fn plS plE) : itree (LCall +' E) lpoint :=
  let '(p0, lbl0) := plS in 
  let LRec := @lsem_cmd_imed E XE LS1 LSC LS2 in
  match lt with
  | LErrLeaf _ => throw err
  | LLeaf _ (MkLI ii ir) => if LLeaf_ok (MkLI ii ir)
                            then LS1 ir (fn, p0)
                            else throw err                                 
(*  | LLeafL _ _ => throw err *)
  | LIf1Node _ pl1 li1 lc li2 =>
      match LIf1Node_ok li1 li2 with
      | false => throw err
      | true => 
          let Bd := fun '(fnA, pA) =>
                      if (fnA == fn)
                      then if (pA == p0) then LS2 fn p0 (fst pl1) (fn, pA)
                           else if (pA == S p0)
                                then x <- LRec _ _ _ lc ;; Ret (inl x)
                                else if pA == fst pl1
                                     then LS2 fn p0 (fst pl1) (fn, pA)
                                     else Ret (inr (fn, (fst plE)))     
                      else throw err in
          ITree.iter Bd (fn, p0) 
      end
  | LCallNode _ nb na fn' lcb lca li1 li2 =>
      match LCallNode_ok nb na fn' lcb lca li1 li2 with
      | false => throw err  
      | true => LSC (lcb ++ [li1]) ;;
                (trigger_inl1 (Call fn')) ;;
                LSC (li2 :: lca) ;;
                Ret (fn, p0 + nb + S (S na))            
      end 
  | _ => throw err end
with lsem_cmd_imed 
  {E} {XE: ErrEvent -< E}
  (LS1: linstr_r -> lpoint -> itree (LCall +' E) lpoint)  
  (LSC: lcmd -> itree (LCall +' E) unit)
  (LS2: funname -> nat -> nat ->
        lpoint -> itree (LCall +' E) (lpoint + lpoint))
  (fn: funname) (plS plE: plinfo)
  (lt : LTreeList fn plS plE) : itree (LCall +' E) lpoint :=
  throw err.     

(* linear semantics of source functions. l1 is the return address *)
Definition lsem_fun {E} {XE: ErrEvent -< E}
  (LS1: linstr_r -> lpoint -> itree (LCall +' E) lpoint)  
  (LSC: lcmd -> itree (LCall +' E) unit)
  (LS2: funname -> nat -> nat ->
        lpoint -> itree (LCall +' E) (lpoint + lpoint))
  (fn: funname) (fd: LTreeFun fn) : itree (LCall +' E) lpoint :=
  match fd with
  | LTFun lbl pl1 lc1 lc2 lt =>
      LSC lc1 ;; l <- @lsem_cmd_imed E XE LS1 LSC LS2 _ _ _ lt ;;
      LSC lc2 ;; Ret l
  end.                   
  
             
End LinearSem.

End Asm1.


