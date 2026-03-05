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

Require Import it_cflow_sem it_effect_sem equiv_extras rutt_extras.

From ITree Require Import Rutt RuttFacts.

Import Memory.
Require oseq.
Require Import Relations.
Require Import List.

Import ListNotations. 
Import MonadNotation.
Local Open Scope monad_scope.

(** some is GENERAL -> move elsewhere *)

Definition err_def_option {E: Type -> Type} `{ErrEvent -< E} {V}
  (o: option V) : itree E V := err_option (ErrType, tt) o.

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


(***** EVENTS *)

(* FindLabel is interpreted in Linear, but GLFEnvAx makes this agree
   with Intermediate. *)
Variant LFindE : Type -> Type :=
  | FindLabelE (lbl: remote_label) : LFindE lpoint. 

(* events mainly used to intstrument the Linear semantics (though
   EvalLoc and EvalExp play a role also in Intermediate) *)
Variant LEvalE : Type -> Type :=
  | RA_readE : LEvalE lpoint
  | RA_isE (x: lpoint) : LEvalE unit                    
  | PC_isE (x: lpoint) : LEvalE unit
  | EvalLocE (e: rexpr) : LEvalE remote_label
  | EvalExpE (e: fexpr) : LEvalE bool. 
                              

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


Section LinSemContext.
  
Context (LState: Type) (LS_I : LinSem LState).

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


Section LinSem.

Context {E} {XE: ErrEvent -< E}.


Section AbsIterators.
(***** ABSTRACT ITERATORS *)
Context {L: Type}.

(* the generic iteration body used in the Linear and Intermediate
    semantics. l0 is the linear code point being executed. *)
Definition ACntr (Bd: L -> itree E L) (NoExit: L -> option bool)
  (l0: L) : itree E (L + L) :=
  (* check whether the exit condition is satisfied *)
  match NoExit l0 with
  | Some b =>
    if b then l1 <- Bd l0 ;; Ret (inl l1)      
    else Ret (inr l0)
  | None => throw err
  end.

(* 'abstract' semantics of linear instruction *)
Definition ALSem (Sem: linstr_r -> L -> itree E L)
  (TryFnd: L -> option linstr) : L -> itree E L :=
  fun l => match TryFnd l with
              | Some (MkLI _ i) => Sem i l
              | None => throw err                                         
           end.  

(* generic iterator specialized to a semantics of instructions *)
Definition SCntr (Sem: linstr_r -> L -> itree E L)
  (NoExit: L -> option bool) (TryFnd: L -> option linstr)
  (l0: L) : itree E (L + L) :=
  ACntr (ALSem Sem TryFnd) NoExit l0.
         
(* iterate SCntr *)
Definition SCntrI (Sem: linstr_r -> L -> itree E L)
  (NoExit: L -> option bool) (TryFnd: L -> option linstr)
  (lp0: L) : itree E L :=
  ITree.iter (@SCntr Sem NoExit TryFnd) lp0.

End AbsIterators.


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

(***** LOCAL ITERATORS *)

(* the 'local' iteration body for the Intermediate semantics. nS and
   nE are the start and end points in the fn linear code wrt to which
   execution is contextual. *)
Definition LACntr (Bd: lpoint -> itree E lpoint)
  (fn: funname) (nS nE: nat) (lp0: lpoint) : itree E (lpoint + lpoint) :=
  ACntr Bd
    (* exit condition: when it jumps to another function, gets out of
       the range, or makes a recursive call (n0 = 0) *)
    (fun '(fn0, n0) => 
       if (not_possible fn0 nE) then None
       else Some ((fn == fn0) 
            && (nS <= n0) && (n0 < nE) && (0 < n0)))
    lp0.

(* iterate LACntr *)
Definition LACntrI (Bd: lpoint -> itree E lpoint)
  (fn: funname) (nS nE: nat) (lp0: lpoint) : itree E lpoint :=
  ITree.iter (@LACntr Bd fn nS nE) (fn, nS).

(* specialized version *)
Definition LCntr (Sem: linstr_r -> lpoint -> itree E lpoint)
  (fn: funname) (nS nE: nat) (lp0: lpoint) :
  itree E (lpoint + lpoint) :=
  LACntr (ALSem Sem find_linstr_in_fun) fn nS nE lp0.

(* iterate LCntr *)
Definition LCntrI (Sem: linstr_r -> lpoint -> itree E lpoint)
  (fn: funname) (nS nE: nat) (lp0: lpoint) : itree E lpoint :=
  ITree.iter (@LCntr Sem fn nS nE) (fn, nS).


(***** GLOBAL ITERATORS *)

(* the 'global' iteration body for the Linear semantics. *)
Definition GCntr (Sem: linstr_r -> lpoint -> itree E lpoint)
  (lp0: lpoint) : itree E (lpoint + lpoint) :=
  SCntr Sem halt_pred find_linstr_in_fun lp0.

(* iterate GCntr *)
Definition GCntrI (Sem: linstr_r -> lpoint -> itree E lpoint)
  (lp0: lpoint) : itree E lpoint :=
  ITree.iter (@GCntr Sem) lp0.

(* the core semantics of linear instructions, based on linstr_sem *)
Definition isem_li_core (i : linstr_r) (s: LState) : itree E LState :=
  iresult (linstr_sem i s) s.


Section CoreLinSem.
Context {readPC: LState -> option lpoint}.

Definition state_find_linstr (st: LState) : option linstr :=
  match (readPC st) with
  | Some l => find_linstr_in_fun l
  | None => None
  end.            

Definition halt_state_pred (st: LState) : option bool :=
  match (readPC st) with
  | Some l => halt_pred l
  | _ => None
  end.         

(* LINEAR CORE SEMANTICS (with explicit state) *)
(* iterative core semantics body, relying on Hlt (halting condition)
   and readPC (to find the next instruction from the state) *)
Definition isem_lcmd_core_body (st: LState) :
  itree E (LState + LState) :=
  SCntr isem_li_core halt_state_pred state_find_linstr st.

(* iterative core semantics of a linear program, from any state *)
Definition isem_lcmd_core (st: LState) : itree E LState :=
  ITree.iter isem_lcmd_core_body st.

End CoreLinSem.


Section InstrumentedSem.

Context {XF: LFindE -< E} {XL: LEvalE -< E } {XSl: @stateE LState -< E}.

(* abstract core semantics of linear instructions, hiding the state *)
Definition isem_li_acore (i : linstr_r) : itree E unit :=
  s1 <- trigger (@Get LState) ;;
  s2 <- isem_li_core i s1 ;;
  trigger (@Put LState s2).

Notation RA_read := (trigger RA_readE).
Notation RA_is x := (trigger (RA_isE x)).
Notation PC_is x := (trigger (PC_isE x)).
Notation PC_ret x := (PC_is x ;; Ret x).
Notation EvalLoc x := (trigger (EvalLocE x)).
Notation EvalExp x := (trigger (EvalExpE x)).
Notation FindLabel x := (trigger (FindLabelE x)).

(* instrumented semantics, used to highlight control flow information
   on top of the core semantics *)
Definition lflow_abs (t: itree E unit)
  (ir : linstr_r) (l0 : lpoint) : itree E lpoint :=
  match ir with
  | Lopn xs o es => t ;; PC_ret (incr_lpoint l0)
  | Lsyscall o => t ;; PC_ret (incr_lpoint l0)
  | Lcall o d => x <- FindLabel d ;; t ;;
                 RA_is (incr_lpoint l0) ;; PC_ret x 
  | Lret => x <- RA_read ;; t ;; PC_ret x 
  | Lalign => t ;; PC_ret (incr_lpoint l0)
  | Llabel x y => t ;; PC_ret (incr_lpoint l0)
  | Lgoto d => x <- FindLabel d ;; t ;; PC_ret x
  | Ligoto e => d <- EvalLoc e ;; x <- FindLabel d ;;
                t ;; PC_ret x 
  | LstoreLabel x lbl => t ;; PC_ret (incr_lpoint l0)
  | Lcond e lbl => b <- EvalExp e ;;
                   if b then x <- FindLabel (fst l0, lbl) ;; t ;; PC_ret x
                   else t ;; PC_ret (incr_lpoint l0)
end.

(* semantics of linear instruction, instrumented with control-flow
   abstraction *)
Definition isem_li_flow (i : linstr_r) (l0: lpoint) : itree E lpoint :=
  PC_is l0 ;; lflow_abs (isem_li_acore i) i l0.

(* instrumented semantics of linear instruction abstracted from
   instructions *)
Definition isem_li_aflow (l0: lpoint) : itree E lpoint :=
  ALSem isem_li_flow find_linstr_in_fun l0.

(* similar for linear commands; only meaningful when lcmd is
   straightline code (used in Intermediate) *)
Fixpoint isem_lcmd_acore (lc: lcmd) : itree E unit :=
  match lc with
  | nil => Ret tt
  | (MkLI ii li) :: lc0 => isem_li_acore li ;; isem_lcmd_acore lc0
  end.             

(***** INSTRUMENTED LINEAR SEMANTICS *)
(* iterative flow semantics body *)
Definition isem_lcmd_flow_body (lbl: lpoint) :
  itree E (lpoint + lpoint) := GCntr isem_li_flow lbl.

(* iterative flow semantics of a linear program, from any starting point *)
Definition isem_lcmd_flow (lp : lpoint) : itree E lpoint :=
  ITree.iter isem_lcmd_flow_body lp.

(* iterative flow semantics of a linear function from its entry point
*)
Definition isem_lfun_flow (fn: funname) : itree E lpoint :=
  isem_lcmd_flow (fn, 0).


(***** HANDLERS *)

(* LFindE handling (defined wrt lfenv ) *)
Definition handle_LFind {T} (e: LFindE T) : itree E T :=
  match e with    
  | FindLabelE rlbl =>
      match lfenv (fst rlbl) with
      | Some lc =>
          n <- err_result (fun _ => err) (find_label (snd rlbl) lc) ;;
          Ret (fst rlbl, n)
      | _ => throw err
      end             
  end.   


Section HandleLEval.
  
Context {readRA : LState -> option lpoint}
        {readPC: LState -> option lpoint}
        {evalLoc : LState -> rexpr -> option remote_label}
        {evalExp : LState -> fexpr -> option bool}.

(* LEvalE handling for Linear and Intermediate *)
Definition handle_LEval {T} (e: LEvalE T) : itree E T :=
  match e with    
  | RA_readE => st <- trigger (@Get LState) ;;
                err_option err (readRA st) 
  | RA_isE l => st <- trigger (@Get LState) ;;
                match (readRA st == Some l) with
                | true => Ret tt 
                | _ => throw err 
                end
  | PC_isE l => st <- trigger (@Get LState) ;;
                match (readPC st == Some l) with
                | true => Ret tt
                | _ => throw err
                end       
  | EvalLocE e => st <- trigger (@Get LState) ;;
                  err_option err (evalLoc st e)            
  | EvalExpE e => st <- trigger (@Get LState) ;;
                  err_option err (evalExp st e)            
  end.   

End HandleLEval.

End InstrumentedSem.

End LinSem.


Definition LLeaf_ok (li: linstr) : bool :=
  match li with
  | MkLI ii (Lopn xs o es) => true 
  | MkLI ii (Lsyscall o) => true      
  | _ => false
  end.   

Definition LIf1Node_ok (li1 li2: linstr) : bool :=
  match (li1, li2) with
  | (MkLI ii (Lcond e lbl), MkLI ii' (Llabel InternalLabel lbl')) =>
      lbl == lbl'
  | _ => false
  end.         

Definition LIfNode_ok (li1 li2 li3 li4: linstr) : bool :=
  match (li1, li2, li3, li4) with
  | (MkLI _ (Lcond e lbl),
     MkLI _ (Lgoto (fn, lbl1)),
     MkLI _ (Llabel InternalLabel lbl'),  
     MkLI _ (Llabel InternalLabel lbl1')) =>
      (lbl == lbl') && (lbl1 == lbl1')
  | _ => false
  end.         

Definition LWhileTNode_ok (li1 li2: linstr) : bool :=
  match (li1, li2) with
  | (MkLI _ (Llabel InternalLabel lbl1), MkLI _ (Lgoto (fn, lbl2))) =>
      lbl1 == lbl2 
  | _ => false
  end.         

Definition LWhile1Node_ok (li1 li2: linstr) : bool :=
  match (li1, li2) with
  | (MkLI _ (Llabel InternalLabel lbl1), MkLI _ (Lcond e lbl2)) =>
      lbl1 == lbl2 
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


Section IntermediateSem.

(* the return value is not really used; it is the instruction after
   the call, but interpretation inlines the function code. *)  
Notation LCall := (callE funname lpoint).

Context {E} {XE: ErrEvent -< E}.

(* intermediate semantics of instructions.
     LC -> isem_lcmd_acore 
     LSI -> isem_li_aflow *)
(* TODO: complete with the remaining cases *)
Fixpoint lsem_i_imed 
  (LSC: lcmd -> itree (LCall +' E) unit)
  (LSI: lpoint -> itree (LCall +' E) lpoint)
  (fn: funname) (plS plE: plinfo)
  (lt : LTree fn plS plE) : itree (LCall +' E) lpoint :=
  let '(pS, _) := plS in 
  let '(pE, _) := plE in 
  let LRec := @lsem_cmd_imed LSC LSI in
  match lt with
  | LErrLeaf _ => throw err
  | LLeaf _ (MkLI ii ir) => if LLeaf_ok (MkLI ii ir)
                            then LSI (fn, pS)
                            else throw err                                 
  | LIf1Node _ (p1, _) li1 lc li2 =>
      (* note: fst plE = S p1 *)
      match LIf1Node_ok li1 li2 with
      | false => throw err
      | true => let Bd := fun '(fnA, pA) =>


                            if (pA == pS) || (pA == p1) then LSI (fn, pA)
            else if (pA == S pS) then LRec _ _ _ lc 
            else throw err in 
          LACntrI Bd fn pS pE (fn, pS) 
      end
  | LIfNode _ (p1, _) (p2, _) li1 lc2 li2 li3 lc1 li4 =>
      (* note: fst plE = S p2 *)
      match LIfNode_ok li1 li2 li3 li4 with
      | false => throw err
      | true => let Bd := fun '(fnA, pA) =>
            if (pA == pS) || (pA == p1) ||
               (pA == S p1) || (pA == p2) then LSI (fn, pA)
            else if (pA == S pS) then LRec _ _ _ lc2
            else if (pA == S (S p1)) then LRec _ _ _ lc1 
            else throw err in
          LACntrI Bd fn pS pE (fn, pS)
      end     
  | LWhileTNode _ (p1, _) (p2, _) b ii li1 lc1 lc2 li2 =>
      (* note: fst plE = S p2 *)
      match LWhileTNode_ok li1 li2 with
      | false => throw err
      | true =>
         let bn := if b then 1 else 0 in  
         let Bd := fun '(fnA, pA) => 
            if (pA == pS) || (pA == pS + bn) || (pA == p2) then LSI (fn, pA)
            else if (pA == S (pS + bn)) then LRec _ _ _ lc1
            else if (pA == p1) then LRec _ _ _ lc2
            else throw err in                                       
          LACntrI Bd fn pS pE (fn, pS)
      end
  | LWhileFNode _ _ lc => LRec _ _ _ lc
  | LWhile1Node _ (p1, _) b ii li1 lc li2 =>
      (* note: fst plE = S p2 *)
      match LWhile1Node_ok li1 li2 with
      | false => throw err
      | true =>
         let bn := if b then 1 else 0 in  
         let Bd := fun '(fnA, pA) => 
            if (pA == pS) || (pA == pS + bn) || (pA == p1) then LSI (fn, pA)
            else if (pA == S (pS + bn)) then LRec _ _ _ lc
            else throw err in                                       
          LACntrI Bd fn pS pE (fn, pS)
      end
   
  | LCallNode _ nb na fn' lc_bef lc_aft li1 li2 =>
      match LCallNode_ok nb na fn' lc_bef lc_aft li1 li2 with
      | false => throw err  
      | true => LSC (lc_bef ++ [li1]) ;;
                (trigger_inl1 (Call fn')) ;;
                LSC (li2 :: lc_aft) ;;
                Ret (fn, pS + nb + S (S na))            
      end 
  | _ => throw err end
with lsem_cmd_imed 
  (LSC: lcmd -> itree (LCall +' E) unit)
  (LSI: lpoint -> itree (LCall +' E) lpoint)
  (fn: funname) (plS plE: plinfo)
  (lt : LTreeList fn plS plE) : itree (LCall +' E) lpoint :=
   match lt with
   | LListNil pl => Ret (fn, fst pl)
   | LListCons _ pl1 pl2 lt ltl =>
       @lsem_i_imed LSC LSI _ _ _ lt ;;
       @lsem_cmd_imed LSC LSI _ _ _ ltl
   end.                   

(* linear semantics of source functions. l1 is the return address *)
Definition lsem_fun_imed_aux 
  (LSC: lcmd -> itree (LCall +' E) unit)
  (LSI: lpoint -> itree (LCall +' E) lpoint)
  (fn: funname) (fd: LTreeFun fn) : itree (LCall +' E) lpoint :=
  match fd with
  | LTFun lbl pl1 lc1 lc2 lt =>
      LSC lc1 ;; l <- @lsem_cmd_imed LSC LSI _ _ _ lt ;;
      LSC lc2 ;; Ret l
  end.                   

Definition lsem_fun_imed 
  (LSC: lcmd -> itree (LCall +' E) unit)
  (LSI: lpoint -> itree (LCall +' E) lpoint)
  (fn: funname) : itree (LCall +' E) lpoint :=
  fd <- err_def_option (ifenv fn) ;;
  lsem_fun_imed_aux LSC LSI fd.


(***** INTERMEDIATE SEMANTICS *)

Section InterSemDef.
Context {XF: LFindE -< E} {XL: LEvalE -< E } {XSl: @stateE LState -< E}.
  
Definition lsem_i_imedI  
  (fn: funname) (plS plE: plinfo)
  (lt : LTree fn plS plE) : itree (LCall +' E) lpoint :=
  lsem_i_imed isem_lcmd_acore isem_li_aflow lt.

Definition lsem_cmd_imedI  
  (fn: funname) (plS plE: plinfo)
  (lt : LTreeList fn plS plE) : itree (LCall +' E) lpoint :=
  lsem_cmd_imed isem_lcmd_acore isem_li_aflow lt.

Definition lsem_fun_imedI  
  (fn: funname) : itree (LCall +' E) lpoint :=
  lsem_fun_imed isem_lcmd_acore isem_li_aflow fn.

Definition handle_LRec : LCall ~> itree (LCall +' E) :=
  fun T  (rc : callE _ _ T) =>
   match rc with
   | Call fn => lsem_fun_imedI fn
   end.                            

(* LRec interpretation *)
Definition lsem_imed_rec (fn: funname) (plS plE: plinfo)
  (lt : LTreeList fn plS plE) : itree E lpoint := 
  interp_mrec handle_LRec (lsem_cmd_imedI lt).

End InterSemDef.


Section Lemmas.
(* TODO: The points to prove *)
Context {XF: LFindE -< E} {XL: LEvalE -< E }.
Context {readPC: LState -> option lpoint}.

(* equivalence between core and instrumented semantics *)
Lemma core2instrumented_lfun (fn: funname) (st: LState) :
  readPC st = Some (fn, 0) ->
  eutt (fun x y => x = fst y) (@isem_lcmd_core E _ readPC st)
    (run_state (@isem_lfun_flow (@stateE LState +' E) _ _ _ inl1 fn) st).
Admitted.

(* equivalence between instrumented and intermediate semantics.
   note: both semantics depend implicitly on glfenv *)
Lemma instrumented2intermediate_lcmd {XS: stateE LState -< E}
  (fn: funname) (plS plE: plinfo)
  (lt : LTreeList fn plS plE) :
  eutt eq (isem_lcmd_flow (fn, fst (fst (forget_imed_cmd lt))))
             (lsem_imed_rec lt). 
Admitted.

(* TODO: cleanup it_cflow_sem and redefine the lemma *)
(* equivalence between intermediate and source semantics *)
(* Lemma intermediate2source  *)

End Lemmas.

End IntermediateSem.

End LinSemContext.

End Asm1.

