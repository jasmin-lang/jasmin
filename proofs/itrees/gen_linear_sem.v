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
(***** ABSTRACT (GENERIC) ITERATORS *)
Context {L: Type}.
  
(* the generic iteration body used in the Linear and Intermediate
    semantics. l0 is the linear code point being executed. *)
Definition ACntr (Sem: linstr_r -> L -> itree E L)
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
Definition ACntrI (Sem: linstr_r -> L -> itree E L)
  (NoExit: L -> option bool) (TryFnd: L -> option linstr)
  (lp0: L) : itree E L :=
  ITree.iter (@ACntr Sem NoExit TryFnd) lp0.

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

(***** SPECIALIZED ITERATORS *)

(* the 'local' iteration body for the Intermediate semantics. nS and
   nE are the start and end points in the fn linear code wrt to which
   execution is contextual. *)
Definition LCntr (Sem: linstr_r -> lpoint -> itree E lpoint)
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
Definition LCntrI (Sem: linstr_r -> lpoint -> itree E lpoint)
  (fn: funname) (nS nE: nat) (lp0: lpoint) : itree E lpoint :=
  ITree.iter (@LCntr Sem fn nS nE) (fn, nS).

(* the 'global' iteration body for the Linear semantics. *)
Definition GCntr (Sem: linstr_r -> lpoint -> itree E lpoint)
  (lp0: lpoint) : itree E (lpoint + lpoint) :=
  ACntr Sem halt_pred find_linstr_in_fun lp0.

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
  ACntr isem_li_core halt_state_pred state_find_linstr st.

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


Section IntermediateSem.

(* the return value is not really used; it is the instruction after
   the call, but interpretation inlines the function code. *)  
Notation LCall := (callE funname lpoint).

Context {E} {XE: ErrEvent -< E}.

(* intermediate semantics of instructions.
     LS1 -> isem_li_flow
     LC -> binding isem_li_acore 
     LS2 ->  LCntr isem_li_flow *)
(* TODO: Complete lsem_i_imed with the remaining cases (anyway, all
   similar to LIf1Node) *)
Fixpoint lsem_i_imed 
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
  | LIf1Node _ (p1, _) li1 lc li2 =>
      (* note: fst plE = S p1 *)
      let OneStep := LS2 fn p0 (S p1) in 
      match LIf1Node_ok li1 li2 with
      | false => throw err
      | true => let Bd := fun '(fnA, pA) =>
          if (fnA == fn) 
          then if (pA == p0) || (pA == p1) then OneStep (fn, pA)
               else if (pA == S p0)
                    then x <- LRec _ _ _ lc ;; Ret (inl x)
                    else if (pA == S p1)
                         then Ret (inr (fn, (fst plE)))
                         else throw err         
          else throw err in
          ITree.iter Bd (fn, p0) 
      end
  | LIfNode _ (p1, _) (p2, _) li1 lc2 li2 li3 lc1 li4 =>
      (* note: fst plE = S p2 *)
      let OneStep := LS2 fn p0 (S p2) in 
      match LIf1Node_ok li1 li2 with
      | false => throw err
      | true => let Bd := fun '(fnA, pA) =>
          if (fnA == fn) 
          then if (pA == p0) || (pA == p1) ||
                  (pA == S p1) || (pA == p2) then OneStep (fn, pA)
               else if (pA == S p0)
                    then x <- LRec _ _ _ lc2 ;; Ret (inl x)
                    else if (pA == S (S p1))
                         then x <- LRec _ _ _ lc1 ;; Ret (inl x) 
                         else if (pA == S p2)
                              then Ret (inr (fn, (fst plE)))
                              else throw err         
          else throw err in
          ITree.iter Bd (fn, p0)
       end                    
  | LCallNode _ nb na fn' lc_bef lc_aft li1 li2 =>
      match LCallNode_ok nb na fn' lc_bef lc_aft li1 li2 with
      | false => throw err  
      | true => LSC (lc_bef ++ [li1]) ;;
                (trigger_inl1 (Call fn')) ;;
                LSC (li2 :: lc_aft) ;;
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
Definition lsem_fun_imed_aux 
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

Definition lsem_fun_imed 
  (LS1: linstr_r -> lpoint -> itree (LCall +' E) lpoint)  
  (LSC: lcmd -> itree (LCall +' E) unit)
  (LS2: funname -> nat -> nat ->
        lpoint -> itree (LCall +' E) (lpoint + lpoint))
  (fn: funname) : itree (LCall +' E) lpoint :=
  fd <- err_def_option (ifenv fn) ;;
  lsem_fun_imed_aux LS1 LSC LS2 fd.


(***** INTERMEDIATE SEMANTICS *)

Section InterSemDef.
Context {XF: LFindE -< E} {XL: LEvalE -< E } {XSl: @stateE LState -< E}.
  
Definition lsem_i_imedI  
  (fn: funname) (plS plE: plinfo)
  (lt : LTree fn plS plE) : itree (LCall +' E) lpoint :=
  lsem_i_imed isem_li_flow isem_lcmd_acore (LCntr isem_li_flow) lt.

Definition lsem_cmd_imedI  
  (fn: funname) (plS plE: plinfo)
  (lt : LTreeList fn plS plE) : itree (LCall +' E) lpoint :=
  lsem_cmd_imed isem_li_flow isem_lcmd_acore (LCntr isem_li_flow) lt.

Definition lsem_fun_imedI  
  (fn: funname) : itree (LCall +' E) lpoint :=
  lsem_fun_imed isem_li_flow isem_lcmd_acore (LCntr isem_li_flow) fn.

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

