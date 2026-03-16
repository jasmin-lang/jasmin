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


Section ICMD_RECT.

Variable (fn0: funname).

Variable (Pt : forall pl0 pl1, LTree fn0 pl0 pl1 -> Type).
Variable (Ptl : forall pl0 pl1, LTreeList fn0 pl0 pl1 -> Type).
Variable (Pf : LTreeFun fn0 -> Type).

Hypothesis HErr : forall pl : plinfo, Pt (LErrLeaf fn0 pl). 
Hypothesis HLeaf : forall (pl : plinfo) (l : linstr), Pt (LLeaf fn0 pl l). 
Hypothesis HIf1 : forall (pl0 pl1 : plinfo) (la_cond1 : linstr)
                         (lcm1 : LTreeList fn0 (incrP1 pl0) pl1),
    Ptl lcm1 -> forall la_lbl1 : linstr,
      Pt (LIf1Node la_cond1 lcm1 la_lbl1).
Hypothesis HIf : forall (pl0 pl1 pl2 : plinfo) (la_cond3 : linstr) 
          (lcm2 : LTreeList fn0 (incrP1 pl0) pl1),
          Ptl lcm2
          -> forall (la_goto2 la_lbl3 : linstr)
                    (lcm1 : LTreeList fn0 (incrP2 pl1) pl2),
              Ptl lcm1
              -> forall la_lbl2 : linstr,
                  Pt (LIfNode la_cond3 lcm2 la_goto2 la_lbl3 lcm1 la_lbl2).
Hypothesis HWhileT : forall (pl0 pl1 pl2 : plinfo) (la_align : bool) 
          (ii : instr_info) (n0 := pl0.1) (lbl0 := pl0.2) 
          (n00 := if la_align then n0.+1 else n0) (la_lbl1 : linstr) 
          (lcm1 : LTreeList fn0 (n00.+1, lbl0) pl1),
          Ptl lcm1
          -> forall lcm2 : LTreeList fn0 pl1 pl2,
              Ptl lcm2
              -> forall la_goto1 : linstr,
                  Pt (LWhileTNode ii la_lbl1 lcm1 lcm2 la_goto1).
Hypothesis HWhileF : forall (pl0 pl1 : plinfo)
                            (lcm1 : LTreeList fn0 pl0 pl1),
          Ptl lcm1 → Pt (LWhileFNode lcm1).
Hypothesis HWhile1 : forall (pl0 pl1 : plinfo) (la_align : bool)
       (ii : instr_info) (n0 := pl0.1) (lbl0 := pl0.2)
       (n00 := if la_align then n0.+1 else n0) 
       (la_lbl1 : linstr) (lcm1 : LTreeList fn0 (n00.+1, lbl0) pl1),
    Ptl lcm1 -> forall la_cond1 : linstr,
      Pt (LWhile1Node ii la_lbl1 lcm1 la_cond1).
Hypothesis HWhile : forall (pl0 pl1 pl2 : plinfo) (la_align : bool) 
          (ii : instr_info) (n0 := pl0.1) (lbl0 := pl0.2) 
          (n00 := if la_align then n0.+1 else n0) (la_goto2 la_lbl3 : linstr) 
          (lcm2 : LTreeList fn0 (n00.+2, lbl0) pl1),
          Ptl lcm2
          -> forall (la_lbl2 : linstr) (lcm1 : LTreeList fn0 (incrP1 pl1) pl2),
              Ptl lcm1
              -> forall la_cond3 : linstr,
               Pt (LWhileNode ii la_goto2 la_lbl3 lcm2 la_lbl2 lcm1 la_cond3).
Hypothesis HCall : forall (pl0 : plinfo) (nb na : nat) (n0 := pl0.1) 
          (lbl0 := pl0.2) (n1 := n0 + nb + na.+2) (fn' : funname) 
          (la_before la_after : lcmd) (la_call la_ret : linstr),
          Pt (LCallNode fn0 pl0 nb na fn' la_before la_after la_call la_ret).
Hypothesis HLNil : forall pl : plinfo, Ptl (LListNil fn0 pl).
Hypothesis HLCons : forall (pl0 pl1 pl2 : plinfo) (l : LTree fn0 pl0 pl1),
    Pt l -> forall l0 : LTreeList fn0 pl1 pl2,
      Ptl l0 -> Ptl (LListCons l l0).

Hypothesis HLFun : forall (lbl : label) (pl1 : plinfo) (lc1 lc2 : lcmd) 
          (n1 := Datatypes.length lc1) (lt : LTreeList fn0 (n1, lbl) pl1),
          Pf (LTFun lc2 lt).

(*
Hypothesis HH : forall 

Check (@LTree_mut asm_op _ fn0 Pt Ptl HErr HLeaf HIf1 HIf HWhileT
         HWhileF HWhile1 HWhile HCall HLNil HLCons).

Check (@LTreeList_mut asm_op _ fn0 Pt Ptl HErr HLeaf HIf1 HIf HWhileT
         HWhileF HWhile1 HWhile HCall HLNil HLCons).

Check (@LTreeFun_rect  asm_op _ fn0 Pf).

Hypothesis HLFun : forall (lbl : label) (pl1 : plinfo) (lc1 lc2 : lcmd) 
          (n1 := Datatypes.length lc1) (lt : LTreeList fn0 (n1, lbl) pl1),
          Pf (LTFun lc2 lt).


Definition LTreeFun_Rect 

Check LTreeFun_Rect.


Search LTreeFun.
About LTreeFun.
Search "Fun_ind".

Check @LTreeFun_ind.

Variables (Pr: )
*)
  
End ICMD_RECT.  


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
    semantics. l0 is the linear code point being executed. used for
    Instrumented Function-Localised Linear Semantics. *)
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

(* generic iterator specialized to a semantics of instructions. used
   for Linear Core Semantics *)
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
    (* exit condition: whenever either it jumps to another function,
       it gets out of range, or it makes a recursive call (n0 = 0).
       note: actually, the last dijunct makes the first redundant, as
       0 is the entry point in every function. *)
    (fun '(fn0, n0) => 
       if (not_possible fn0 nE) then None
       else Some ((fn == fn0) && (nS <= n0) && (n0 < nE) && (0 < n0)))
    lp0.

(* iterate LACntr *)
Definition LACntrI (Bd: lpoint -> itree E lpoint)
  (fn: funname) (nS nE: nat) (lp0: lpoint) : itree E lpoint :=
  ITree.iter (@LACntr Bd fn nS nE) (fn, nS).

(* specialized version, using ALSem. used for Instrumented
    Function-Localised Linear Semantics. *)
Definition LCntr (Sem: linstr_r -> lpoint -> itree E lpoint)
  (fn: funname) (nS nE: nat) (lp0: lpoint) :
  itree E (lpoint + lpoint) :=
  LACntr (ALSem Sem find_linstr_in_fun) fn nS nE lp0.

(* iterate LCntr *)
Definition LCntrI (Sem: linstr_r -> lpoint -> itree E lpoint)
  (fn: funname) (nS nE: nat) (lp0: lpoint) : itree E lpoint :=
  ITree.iter (@LCntr Sem fn nS nE) (fn, nS).


(***** GLOBAL ITERATORS *)

(* the 'global' iteration body for the Linear semantics. used for
   Instrumented Global Linear Semantics *)
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

Context {code_length: funname -> nat}.

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

(* combinator for sequential linear commands; only meaningful when
   lcmd is straightline code (used in Intermediate) *)
Fixpoint lcmd_seq {T} (S: linstr_r -> T -> itree E T)
  (lc: lcmd) (l0: T) : itree E T :=
  match lc with
  | nil => Ret l0
  | (MkLI ii li) :: lc0 =>
      l1 <- S li l0 ;; lcmd_seq S lc0 l1
  end.             

(* only meaningful when lcmd is straightline code *)
Definition isem_lcmd_seq_flow (lc: lcmd) (l0: lpoint) : itree E lpoint :=
  lcmd_seq isem_li_flow lc l0.

(* only meaningful when lcmd is straightline code *)
Definition isem_lcmd_seq_acore (lc: lcmd) : itree E unit :=
  lcmd_seq (fun li _ => isem_li_acore li) lc tt.

(* only meaningful when lcmd is straightline code *)
Definition isem_lcmd_seq_inl_flow (lc: lcmd) (l0: lpoint) :
  itree E (lpoint + lpoint) :=
  lcmd_seq (fun li pp =>
              match pp with
              | inl l1 => l2 <- isem_li_flow li l1 ;; Ret (inl l2)
              | _ => throw err end) lc 
    (inl l0).


(***** INSTRUMENTED GLOBAL LINEAR SEMANTICS *)

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


(***** INSTRUMENTED FUNCTION-LOCALISED LINEAR SEMANTICS *)

(* note: the exit condition is the local one, defined in LACntr; so it
   covers all function calls (inclusive of recursive ones to fn) *)
Definition isem_lfun_lfloc_body (fn: funname) (lp0: lpoint) :
  itree E (lpoint + lpoint) :=
  LCntr isem_li_flow fn 0 (code_length fn) lp0.

(* iterates over all internal jumps *)
Definition isem_lfun_lfloc (fn: funname) (lp0: lpoint) :
  itree E lpoint := ITree.iter (isem_lfun_lfloc_body fn) lp0.

(* note: here the exit condition is the global one *)
Definition isem_lfloc_body (lp0: lpoint) :
  itree E (lpoint + lpoint) := let fn := fst lp0 in
   ACntr (isem_lfun_lfloc fn) halt_pred lp0.                

(* iterates on the function calls *)
Definition isem_lfloc (lp0: lpoint) :
  itree E lpoint := ITree.iter isem_lfloc_body lp0.
                    
End InstrumentedSem.

End LinSem. 

  
(***** HANDLERS *)

(* LFindE handling (defined wrt lfenv ) *)
  Definition handle_LFind {E0} {XE: ErrEvent -< E0}
    {T} (e: LFindE T) : itree E0 T :=
  match e with    
  | FindLabelE rlbl =>
      match lfenv (fst rlbl) with
      | Some lc =>
          n <- err_result (fun _ => err) (find_label (snd rlbl) lc) ;;
          Ret (fst rlbl, n)
      | _ => throw err
      end             
  end.   

Definition interp_LFind {E0} {XE: ErrEvent -< E0}
    {T} (t: itree (LFindE +' E0) T) : itree E0 T :=
  interp (ext_handler (@handle_LFind _ _)) t.
(*  interp (case_ (@handle_LFind) id_) t.   *)                          


Section HandleLEval.
  
Context {readRA : LState -> option lpoint}
        {readPC: LState -> option lpoint}
        {evalLoc : LState -> rexpr -> option remote_label}
        {evalExp : LState -> fexpr -> option bool}.

(* LEvalE handling for Linear and Intermediate *)
Definition handle_LEval {E0} {XE: ErrEvent -< E0} {XSl: @stateE LState -< E0}
  {T} (e: LEvalE T) : itree E0 T :=
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

Definition interp_LEval {E0} {XE: ErrEvent -< E0}
  {XSl: @stateE LState -< E0} {T}
  (t: itree (LEvalE +' E0) T) : itree E0 T :=
  interp (ext_handler (@handle_LEval _ _ _)) t.

Definition interp_LInstr {E0} {XE: ErrEvent -< E0}
  {XSl: @stateE LState -< E0} {T}
  (t: itree (LEvalE +' LFindE +' E0) T) : itree E0 T :=
  interp_LFind (interp_LEval t).

End HandleLEval.


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

Definition LWhileNode_ok (li1 li2 li3 li4: linstr) : bool :=
  match (li1, li2, li3, li4) with
  | (MkLI _ (Lgoto (fn, lbl)),
     MkLI _ (Llabel InternalLabel lbl1),
     MkLI _ (Llabel InternalLabel lbl'),
     MkLI _ (Lcond e lbl1')) =>
           (lbl == lbl') && (lbl1 == lbl1')
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

Context {code_length: funname -> nat}.
Context {E} {XE: ErrEvent -< E}.

Definition in_btw (n1 n2 n3: nat) : bool :=
  (n1 <= n3) && (n3 < n2). 

Definition at_start (n1 _ n3: nat) : bool :=
  n3 == n1.

Definition Bind_cmb : (lpoint -> itree (LCall +' E) lpoint) ->
        (lpoint -> itree (LCall +' E) lpoint) ->
        nat -> nat -> nat -> nat -> lpoint -> itree (LCall +' E) lpoint :=
  fun f g _ _ _ _ x => ITree.bind (f x) g.

Definition Switch_cmb : (lpoint -> itree (LCall +' E) lpoint) ->
        (lpoint -> itree (LCall +' E) lpoint) ->
        nat -> nat -> nat -> nat -> lpoint -> itree (LCall +' E) lpoint :=
  fun f g n1 n2 n3 n4 '(fn0, n0) =>
       if in_btw n1 n2 n0 then f (fn0, n0)
       else if in_btw n3 n4 n0 then g (fn0, n0)
       else throw err.

Definition Id_cmb {E0} : (lpoint -> itree E0 lpoint) ->
  funname -> nat -> nat -> lpoint -> itree E0 lpoint :=
  fun f _ _ _ => f.

(* parameterized semantics of intermediate instructions and commands *)
(* IBT -> (L) at_start (F) in_btw
   CNT -> (L) LACntrI (F) id    
   CNN -> (L) bind (G) switch 
   LC -> isem_lcmd_seq_flow (in principle, isem_lcmd_acore could also do).  
   LSI -> isem_li_aflow 
 *)
Fixpoint lsem_i_imedA 
  (IBT: nat -> nat -> nat -> bool)
  (CNT: (lpoint -> itree (LCall +' E) lpoint) ->
         funname -> nat -> nat -> lpoint -> itree (LCall +' E) lpoint)
  (CNN: (lpoint -> itree (LCall +' E) lpoint) ->
        (lpoint -> itree (LCall +' E) lpoint) ->
        nat -> nat -> nat -> nat -> lpoint -> itree (LCall +' E) lpoint)
  (LSC: lcmd -> lpoint -> itree (LCall +' E) lpoint)
  (LSI: lpoint -> itree (LCall +' E) lpoint)
  (fn: funname) (plS plE: plinfo)
  (lt : LTree fn plS plE) : lpoint -> itree (LCall +' E) lpoint :=
  let '(pS, _) := plS in 
  let '(pE, _) := plE in 
  CNT 
  (fun lpA =>
  let '(fnA, pA) := lpA in
  let LRec := @lsem_cmd_imedA IBT CNT CNN LSC LSI in
  if fst lpA == fn then 
  match lt with
  | LErrLeaf _ => throw err
  | LLeaf _ (MkLI ii ir) =>
                            if LLeaf_ok (MkLI ii ir)
                            then LSI lpA
                            else throw err                                 
  | LIf1Node _ (p1, _) li1 lc li2 =>
      (* note: fst plE = S p1 *)
      match LIf1Node_ok li1 li2 with
      | false => throw err
      | true => 
             if (pA == pS) || (pA == p1) then LSI lpA
             else if IBT (S pS) p1 pA then LRec _ _ _ lc lpA
             else throw err 
      end
  | LIfNode _ (p1, _) (p2, _) li1 lc2 li2 li3 lc1 li4 => 
      (* note: fst plE = S p2 *)
      match LIfNode_ok li1 li2 li3 li4 with
      | false => throw err
      | true => 
            if (pA == pS) || (pA == p1) ||
               (pA == S p1) || (pA == p2) then LSI lpA
            else if IBT (S pS) p1 pA then LRec _ _ _ lc2 lpA
            else if IBT (S (S p1)) p2 pA then LRec _ _ _ lc1 lpA
            else throw err 
      end     
  | LWhileTNode _ (p1, _) (p2, _) b ii li1 lc1 lc2 li2 =>
      (* note: fst plE = S p2 *)
      match LWhileTNode_ok li1 li2 with
      | false => throw err
      | true => 
            let bn := if b then 1 else 0 in  
            if (pA == pS) || (pA == pS + bn) || (pA == p2) then LSI lpA
            else if IBT (S (pS + bn)) p1 pA then LRec _ _ _ lc1 lpA
            else if IBT p1 p2 pA then LRec _ _ _ lc2 lpA
            else throw err 
      end
  | LWhileFNode _ _ lc => LRec _ _ _ lc lpA
  | LWhile1Node _ (p1, _) b ii li1 lc li2 =>
      (* note: fst plE = S p1 *)
      match LWhile1Node_ok li1 li2 with
      | false => throw err
      | true => 
            let bn := if b then 1 else 0 in   
            if (pA == pS) || (pA == pS + bn) || (pA == p1) then LSI lpA
            else if IBT (S (pS + bn)) p1 pA then LRec _ _ _ lc lpA
            else throw err 
      end
  | LWhileNode _ (p1, _) (p2, _) b ii li1 li2 lc2 li3 lc1 li4 =>
      (* note: fst plE = S p2 *)
      match LWhileNode_ok li1 li2 li3 li4 with
      | false => throw err
      | true =>
            let bn := if b then 1 else 0 in
            let pS1 := pS + bn in  
            if (pA == pS) || (pA == pS1) || (pA == S pS1)
               || (pA == p1) || (pA == p2) then LSI lpA
            else if IBT (S (S (pS1))) p1 pA then LRec _ _ _ lc2 lpA
            else if IBT (S p1) p2 pA then LRec _ _ _ lc1 lpA
            else throw err 
      end        
  | LCallNode _ nb na fn' lc_bef lc_aft li1 li2 =>
      match LCallNode_ok nb na fn' lc_bef lc_aft li1 li2 with
      | false => throw err  
      | true => LSC (lc_bef ++ [li1]) lpA ;;
                l1 <- (trigger_inl1 (Call fn')) ;;
                LSC (li2 :: lc_aft) l1 ;;
                Ret (fn, pS + nb + S (S na))            
      end 
  end
  else throw err) fn pS pE    
with lsem_cmd_imedA 
  (IBT: nat -> nat -> nat -> bool)
  (CNT: (lpoint -> itree (LCall +' E) lpoint) ->
         funname -> nat -> nat -> lpoint -> itree (LCall +' E) lpoint)
  (CNN: (lpoint -> itree (LCall +' E) lpoint) ->
        (lpoint -> itree (LCall +' E) lpoint) ->
        nat -> nat -> nat -> nat -> lpoint -> itree (LCall +' E) lpoint)
  (LSC: lcmd -> lpoint -> itree (LCall +' E) lpoint)
  (LSI: lpoint -> itree (LCall +' E) lpoint)
  (fn: funname) (plS plE: plinfo)
  (lt : LTreeList fn plS plE) : lpoint -> itree (LCall +' E) lpoint :=
   fun lpA =>
   if fst lpA == fn then       
   match lt with
   | LListNil pl0 => if snd lpA == fst pl0 then Ret (fn, fst pl0)
                     else throw err                               
   | LListCons _ (p1, _) (p2, _) lt ltl =>
       CNN (@lsem_i_imedA IBT CNT CNN LSC LSI _ _ _ lt)
         (@lsem_cmd_imedA IBT CNT CNN LSC LSI _ _ _ ltl)
         (fst plS) p1 p1 p2 lpA 
   end
   else throw err.                   

(* parameterized intermediate local semantics of
   instructions. NOTE: here at_start can replace in_btw. *)
Definition lsem_i_imedAL 
  (LSC: lcmd -> lpoint -> itree (LCall +' E) lpoint)
  (LSI: lpoint -> itree (LCall +' E) lpoint)
  (fn: funname) (plS plE: plinfo)
  (lt : LTree fn plS plE) : lpoint -> itree (LCall +' E) lpoint :=
  lsem_i_imedA in_btw LACntrI Bind_cmb LSC LSI lt.

(* parameterized intermediate local semantics of
   commands. NOTE: here at_start can replace in_btw. *)
Definition lsem_cmd_imedAL 
  (LSC: lcmd -> lpoint -> itree (LCall +' E) lpoint)
  (LSI: lpoint -> itree (LCall +' E) lpoint)
  (fn: funname) (plS plE: plinfo)
  (lt : LTreeList fn plS plE) : lpoint -> itree (LCall +' E) lpoint :=
  lsem_cmd_imedA in_btw LACntrI Bind_cmb LSC LSI lt.

Definition lsem_fun_imed_auxAL 
  (LSC: lcmd -> lpoint -> itree (LCall +' E) lpoint)
  (LSI: lpoint -> itree (LCall +' E) lpoint)
  (fn: funname) (fd: LTreeFun fn) : itree (LCall +' E) lpoint :=
  match fd with
  | LTFun lbl pl1 lc1 lc2 lt =>
      lp0 <- LSC lc1 (fn, 0) ;;
      lp1 <- @lsem_cmd_imedAL LSC LSI _ _ _ lt lp0 ;; LSC lc2 lp1 
  end.                   

(* parameterized intermediate local semantics of functions. *)
Definition lsem_fun_imedAL 
  (LSC: lcmd -> lpoint -> itree (LCall +' E) lpoint)
  (LSI: lpoint -> itree (LCall +' E) lpoint)
  (fn: funname) : itree (LCall +' E) lpoint :=
  fd <- err_def_option (ifenv fn) ;;
  lsem_fun_imed_auxAL LSC LSI fd.

(* parameterized intermediate function-globablized semantics of
   instructions. *)
Definition lsem_i_imedAF 
  (LSC: lcmd -> lpoint -> itree (LCall +' E) lpoint)
  (LSI: lpoint -> itree (LCall +' E) lpoint)
  (fn: funname) (plS plE: plinfo)
  (lt : LTree fn plS plE) : lpoint -> itree (LCall +' E) lpoint :=
  lsem_i_imedA in_btw Id_cmb Switch_cmb LSC LSI lt.

(* parameterized intermediate function-globablized semantics of
   commands. *)
Definition lsem_cmd_imedAF  
  (LSC: lcmd -> lpoint -> itree (LCall +' E) lpoint)
  (LSI: lpoint -> itree (LCall +' E) lpoint)
  (fn: funname) (plS plE: plinfo)
  (lt : LTreeList fn plS plE) : lpoint -> itree (LCall +' E) lpoint :=
  lsem_cmd_imedA in_btw Id_cmb Switch_cmb LSC LSI lt.

Definition lsem_fun_imed_auxAF 
  (LSC: lcmd -> lpoint -> itree (LCall +' E) lpoint)
  (LSI: lpoint -> itree (LCall +' E) lpoint)
  (fn: funname) (fd: LTreeFun fn) : itree (LCall +' E) lpoint :=
  match fd with
  | LTFun lbl pl1 lc1 lc2 lt =>
    let clen := code_length fn in 
    let nE := clen + List.length lc1 + List.length lc2 in  
    LACntrI (fun lpA => lp0 <- LSC lc1 lpA ;;
       lp1 <- @lsem_cmd_imedAF LSC LSI _ _ _ lt lp0 ;; LSC lc2 lp1)
       fn 0 nE (fn, 0) 
  end.                   

(* parameterized intermediate function-globablised semantics of functions. *)
Definition lsem_fun_imedAF 
  (LSC: lcmd -> lpoint -> itree (LCall +' E) lpoint)
  (LSI: lpoint -> itree (LCall +' E) lpoint)
  (fn: funname) : itree (LCall +' E) lpoint :=
  fd <- err_def_option (ifenv fn) ;;
  lsem_fun_imed_auxAF LSC LSI fd.


(***** INTERMEDIATE LOCAL SEMANTICS *)
(* introduce an iteration for each Intermediate instruction *)

Section LInterSemDef.
Context {XF: LFindE -< E} {XL: LEvalE -< E } {XSl: @stateE LState -< E}.
  
Definition lsem_i_imedL  
  (fn: funname) (plS plE: plinfo)
  (lt : LTree fn plS plE) : lpoint -> itree (LCall +' E) lpoint :=
  @lsem_i_imedAL 
    isem_lcmd_seq_flow isem_li_aflow _ _ _ lt.
               
Definition lsem_cmd_imedL  
  (fn: funname) (plS plE: plinfo)
  (lt : LTreeList fn plS plE) : lpoint -> itree (LCall +' E) lpoint :=
  @lsem_cmd_imedAL
    isem_lcmd_seq_flow isem_li_aflow _ _ _ lt.

Definition lsem_fun_imedL  
  (fn: funname) : itree (LCall +' E) lpoint :=
  lsem_fun_imedAL 
    isem_lcmd_seq_flow isem_li_aflow fn.

Definition handle_LRecL : LCall ~> itree (LCall +' E) :=
  fun T  (rc : callE _ _ T) =>
   match rc with
   | Call fn => lsem_fun_imedL fn
   end.                            

(* LRec interpretation *)
Definition lsem_imed_recL (fn: funname) (plS plE: plinfo)
  (lt : LTreeList fn plS plE) (lp0: lpoint) : itree E lpoint := 
  interp_mrec handle_LRecL (lsem_cmd_imedL lt lp0).

End LInterSemDef.


(***** INTERMEDIATE FUNCTION-GLOBALISED SEMANTICS *)
(* introduces an iteration for each function *)

Section FInterSemDef.
Context {XF: LFindE -< E} {XL: LEvalE -< E } {XSl: @stateE LState -< E}.
  
Definition lsem_i_imedF  
  (fn: funname) (plS plE: plinfo)
  (lt : LTree fn plS plE) : lpoint -> itree (LCall +' E) lpoint :=
  @lsem_i_imedAF 
    isem_lcmd_seq_flow isem_li_aflow _ _ _ lt.
               
Definition lsem_cmd_imedF  
  (fn: funname) (plS plE: plinfo)
  (lt : LTreeList fn plS plE) : lpoint -> itree (LCall +' E) lpoint :=
  @lsem_cmd_imedAF
    isem_lcmd_seq_flow isem_li_aflow _ _ _ lt.

Definition lsem_fun_imedF  
  (fn: funname) : itree (LCall +' E) lpoint :=
  lsem_fun_imedAF 
    isem_lcmd_seq_flow isem_li_aflow fn.

Definition handle_LRecF : LCall ~> itree (LCall +' E) :=
  fun T  (rc : callE _ _ T) =>
   match rc with
   | Call fn => lsem_fun_imedF fn
   end.                            

(* LRec interpretation *)
Definition lsem_imed_recF (fn: funname) (plS plE: plinfo)
  (lt : LTreeList fn plS plE) (lp0: lpoint) : itree E lpoint := 
  interp_mrec handle_LRecF (lsem_cmd_imedF lt lp0).

End FInterSemDef.


Section Lemmas.
  (* TODO: The points to prove *) 
Context {readRA : LState -> option lpoint}
        {readPC: LState -> option lpoint}
        {evalLoc : LState -> rexpr -> option remote_label}
        {evalExp : LState -> fexpr -> option bool}.

(* equivalence between core and instrumented global semantics; where
   most of the low-level effort will go. notice that in Instrumented
   events LEval and LFind need to be handled first, even if they do
   not actually change the state. *)
Lemma core2instrumented_global_lfun (fn: funname) (st: LState) :
  readPC st = Some (fn, 0) ->
  eutt (fun x y => x = fst y) (@isem_lcmd_core E _ readPC st)
    (run_state (@interp_LInstr readRA readPC evalLoc evalExp _ _ _ _
    (@isem_lfun_flow (LEvalE +' LFindE +' @stateE LState +' E) _ _ _ _ fn)) st).
Admitted.


Section Lemmas1.
Context {XF: LFindE -< E} {XL: LEvalE -< E }.

(* equivalence between instrumented global and function-localised
   semantics; se we can semantically distinguish between internal
   jumps, controlled by a function-level iterations, and external
   jumps, controlled by the global iteration. *)
Lemma instrumented_local2instrumented_funloc_lfun {XS: stateE LState -< E}
  (fn: funname) :
  eutt eq (@isem_lfun_flow E _ _ _ _ fn)
    (@isem_lfloc E _ _ _ _ code_length (fn, 0)).  
Admitted. 
  
(* equivalence between intemediate local and function-globablised
   semantics; the idea being that in Intermediate, local iterations
   can be pushed out up to functions; should be proved before
   interpreting LRec, otherwise one might end up with an infinite
   number of local iterations. probably the hardest bit *)
Lemma intemediate_local2intermediate_funglobal_fun {XS: stateE LState -< E}
  (fn: funname) :
  eutt eq (lsem_fun_imedL fn) (lsem_fun_imedF fn).
Proof.
  unfold lsem_fun_imedL, lsem_fun_imedF; simpl.
  unfold lsem_fun_imedAL, lsem_fun_imedAF; simpl.
  eapply eqit_bind; eauto; try reflexivity.
  intros ltf.
  
  destruct ltf as [lbl0 plf lc1 lc2 n1 ltt] eqn:was_ltf.
  set lsemAL := (lsem_fun_imed_auxAL _ _).
  set lsemAF := (lsem_fun_imed_auxAF _ _).
  clear was_ltf.
  revert ltt.
  revert n1.
  revert lc1 lc2.
 (* 
  set (Pt := fun pl0 pl1 (lt0: LTree fn pl0 pl1) =>
               eutt eq (lsemAL fn (LTFun lc2 []
               eutt eq (lsem_i_imedL lt0 (fn, fst pl0))
                       (lsem_i_imedF lt0 (fn, fst pl0))). 
  set (Ptl := fun pl0 pl1 (lts: LTreeList fn pl0 pl1) =>
               eutt eq (lsem_cmd_imedL lts (fn, fst pl0))
                       (lsem_cmd_imedF lts (fn, fst pl0))). 



  simpl.
  unfold LACntrI; simpl.
  unfold LACntr; simpl.
  rewrite unfold_iter; simpl.
  eapply eqit_bind'; simpl.
  unfold isem_lcmd_seq_flow.
  unfold ACntr; simpl.
*)
(*  
  set (Pltree := fun lt => forall pl0,
      eutt eq (@lsem_i_imedAL isem_lcmd_seq_flow isem_li_aflow fn _ _ lt pl0)
              (@lsem_i_imedAF isem_lcmd_seq_flow isem_li_aflow fn _ _ lt pl0)).

  eapply LTreeList_mut; simpl.
*)  
Admitted. 

Check  (@LTreeList_mut asm_op _).

(* similar, for commands. but NOTE: this does not hold, need to add a
   top-level iteration on the left *)
Lemma intemediate_local2intermediate_funglobal_lcmd0 {XS: stateE LState -< E}
  (fn: funname) (plS plE: plinfo)
  (lt : LTreeList fn plS plE) (pl0: lpoint) :
  eutt eq (lsem_cmd_imedL lt pl0) (lsem_cmd_imedF lt pl0).
Admitted.

Lemma intemediate_local2intermediate_funglobal_lcmd {XS: stateE LState -< E}
  (fn: funname) (plS plE: plinfo)
  (lt : LTreeList fn plS plE) (lp0: lpoint) :
  eutt eq (lsem_cmd_imedL lt lp0)
          (LACntrI (lsem_cmd_imedF lt) fn (fst plS) (fst plE) lp0).
Proof.
  unfold lsem_imed_recL, isem_lcmd_flow, lsem_imed_recF; simpl.
  revert lp0.
  revert lt.
  revert plS plE.
  
  set (Pt := fun plS plE (lt0: LTree fn plS plE) =>
             forall lp0, eutt eq (lsem_i_imedL lt0 lp0)
                 (LACntrI (lsem_i_imedF lt0)
                    fn (fst plS) (fst plE) lp0)). 
  set (Ptl := fun plS plE (lts: LTreeList fn plS plE) =>
             forall lp0, eutt eq (lsem_cmd_imedL lts lp0)
                 (LACntrI (lsem_cmd_imedF lts)
                    fn (fst plS) (fst plE) lp0)). 
  eapply (@LTreeList_mut asm_op _ fn Pt Ptl). 
  { intros; subst Pt; simpl; intros.
    unfold lsem_i_imedL, lsem_i_imedF; simpl.
    unfold lsem_i_imedAL, lsem_i_imedAF; simpl.
    destruct pl eqn: was_pl ; simpl.
    unfold Id_cmb; simpl.
    reflexivity.
  }
  { intros; subst Pt; simpl; intros.
    unfold lsem_i_imedL, lsem_i_imedF; simpl.
    unfold lsem_i_imedAL, lsem_i_imedAF; simpl.
    destruct pl eqn: was_pl ; simpl.
    unfold Id_cmb; simpl.
    reflexivity.
  }
  { intros; subst Pt; simpl; intros.
    unfold lsem_i_imedL, lsem_i_imedF; simpl.
    unfold lsem_i_imedAL, lsem_i_imedAF; simpl.
    destruct pl0 eqn: was_pl0 ; simpl.
    unfold Id_cmb; simpl.
    unfold Ptl in *.
    unfold LACntrI; simpl.
    destruct lp0 eqn: was_lp0; simpl.
    (* here unfolding the top iter does not make sense, because on the
       left threre is an inner iter while on the right there is
       none. Indeed, we've got an induction hypothesis that does the
       right job, as clearly shown in the mock-proof below (where we
       unfold the iter, leading to a mismatch). However, in order to
       apply the induction hyp without unfolding, we need some lemmas,
       and in particular one that is very similar to
       'loop_asm_correct'; however, this lemma is proved for loop. We
       would need something for iter, and even more specifically for
       LCntrI. But then it seems perhaps more convenient to try
       encoding LCntrI as a loop. *)
    unfold lsem_cmd_imedL in H; simpl in *.
    unfold lsem_cmd_imedF in H; simpl in *.
    unfold lsem_cmd_imedAL in H; simpl in *.
    unfold lsem_cmd_imedAF in H; simpl in *.
    unfold LACntr; simpl.


(* (* mock-proof, by unfolding iter *)    
    eapply eutt_iter.
    intros lp1.
    destruct lp1 eqn: was_lp1; simpl.
    unfold LACntr; simpl.
    unfold ACntr; simpl.
    destruct (not_possible f0 pl1.1.+1); try reflexivity.
    destruct ((fn == f0) && (n <= n1) && (n1 < pl1.1.+1) && (0 < n1));
      try reflexivity.
    eapply eqit_bind; try reflexivity.
    destruct (f0 == fn); try reflexivity; simpl.
    destruct (LIf1Node_ok la_cond1 la_lbl1); try reflexivity; simpl.

    destruct pl1 eqn: was_pl1; simpl.
    destruct ((n1 == n) || (n1 == n2)); try reflexivity; simpl.
    destruct (in_btw n.+1 n2 n1); try reflexivity; simpl.

    unfold lsem_cmd_imedL in H; simpl in *.
    unfold lsem_cmd_imedF in H; simpl in *.
    unfold lsem_cmd_imedAL in H; simpl in *.
    unfold lsem_cmd_imedAF in H; simpl in *.
    rewrite H.
*) 
   
    admit.
  }

Admitted.


(* equivalence between instrumented function-localised and
   intermediate function-globalised; basically, we need to match the
   global iteration with the mrec interpretation. *)
Lemma instrumented_funlocal2intermediate_funglobal_lcmd {XS: stateE LState -< E}
  (fn: funname) (plS plE: plinfo)
  (lt : LTreeList fn plS plE) :
  eutt eq (@isem_lfloc E _ _ _ _ code_length (fn, fst plS))
    (lsem_imed_recF lt (fn, fst plS)).
Proof.
Admitted.

(* equivalence between instrumented global and intermediate local
   semantics then will follow. note: both semantics depend implicitly
   on glfenv *)
Lemma intermediate_local2instrumented_lcmd {XS: stateE LState -< E}
  (fn: funname) (plS plE: plinfo)
  (lt : LTreeList fn plS plE) :
  eutt eq (lsem_imed_recL lt (fn, fst plS))
    (isem_lcmd_flow (fn, fst (fst (forget_imed_cmd lt)))).
Proof.
Admitted.

(* TODO: cleanup it_cflow_sem and redefine the lemma *)
(* equivalence between intermediate and source semantics *)
(* Lemma intermediate2source  *)

End Lemmas1.

End Lemmas.


(* MAYBE USEFUL *)
(* probably useless; similar to Intermediate Local; the only
  difference is that it inserts only the iterators that are strictly
  necessary. noethelss it reads slightly better, so for now I'm
  keeping it for reference. 
  parameterized intermediate local strict semantics.  
  LC -> isem_lcmd_seq_flow (isem_lcmd_acore could also do).  
  LSI -> isem_li_aflow *)
Fixpoint lsem_i_imedSL 
  (LSC: lcmd -> lpoint -> itree (LCall +' E) lpoint)
  (LSI: lpoint -> itree (LCall +' E) lpoint)
  (fn: funname) (plS plE: plinfo)
  (lt : LTree fn plS plE) : itree (LCall +' E) lpoint :=
  let '(pS, _) := plS in 
  let '(pE, _) := plE in 
  let LRec := @lsem_cmd_imedSL LSC LSI in
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
      (* note: fst plE = S p1 *)
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
  | LWhileNode _ (p1, _) (p2, _) b ii li1 li2 lc2 li3 lc1 li4 =>
      (* note: fst plE = S p2 *)
      match LWhileNode_ok li1 li2 li3 li4 with
      | false => throw err
      | true =>
         let bn := if b then 1 else 0 in
         let pS1 := pS + bn in 
         let Bd := fun '(fnA, pA) => 
            if (pA == pS) || (pA == pS1) || (pA == S pS1)
               || (pA == p1) || (pA == p2) then LSI (fn, pA)
            else if (pA == S (S (pS1))) then LRec _ _ _ lc2
            else if (pA == S p1) then LRec _ _ _ lc1
            else throw err in                                       
          LACntrI Bd fn pS pE (fn, pS)
      end        
  | LCallNode _ nb na fn' lc_bef lc_aft li1 li2 =>
      match LCallNode_ok nb na fn' lc_bef lc_aft li1 li2 with
      | false => throw err  
      | true => LSC (lc_bef ++ [li1]) (fn, pS) ;;
                l1 <- (trigger_inl1 (Call fn')) ;;
                LSC (li2 :: lc_aft) l1 ;;
                Ret (fn, pS + nb + S (S na))            
      end 
  end
with lsem_cmd_imedSL 
  (LSC: lcmd -> lpoint -> itree (LCall +' E) lpoint)
  (LSI: lpoint -> itree (LCall +' E) lpoint)
  (fn: funname) (plS plE: plinfo)
  (lt : LTreeList fn plS plE) : itree (LCall +' E) lpoint :=
   match lt with
   | LListNil pl => Ret (fn, fst pl)
   | LListCons _ pl1 pl2 lt ltl =>
       @lsem_i_imedSL LSC LSI _ _ _ lt ;;
       @lsem_cmd_imedSL LSC LSI _ _ _ ltl
   end.                   

(* linear semantics of source functions. l1 is the return address (not
   used here, because LSC returns an lpoint) *)
Definition lsem_fun_imed_auxSL 
  (LSC: lcmd -> lpoint -> itree (LCall +' E) lpoint)
  (LSI: lpoint -> itree (LCall +' E) lpoint)
  (fn: funname) (fd: LTreeFun fn) : itree (LCall +' E) lpoint :=
  match fd with
  | LTFun lbl pl1 lc1 lc2 lt =>
      LSC lc1 (fn, 0) ;;
      l <- @lsem_cmd_imedSL LSC LSI _ _ _ lt ;; LSC lc2 l 
  end.                   

Definition lsem_fun_imedSL 
  (LSC: lcmd -> lpoint -> itree (LCall +' E) lpoint)
  (LSI: lpoint -> itree (LCall +' E) lpoint)
  (fn: funname) : itree (LCall +' E) lpoint :=
  fd <- err_def_option (ifenv fn) ;;
  lsem_fun_imed_auxSL LSC LSI fd.

  
(***** INTERMEDIATE LOCAL STRICT SEMANTICS *)
(* probably not needed *)

Section SLInterSemDef.
Context {XF: LFindE -< E} {XL: LEvalE -< E } {XSl: @stateE LState -< E}. 
  
Definition lsem_i_imedI  
  (fn: funname) (plS plE: plinfo)
  (lt : LTree fn plS plE) : itree (LCall +' E) lpoint :=
  @lsem_i_imedSL isem_lcmd_seq_flow isem_li_aflow _ _ _ lt.

Definition lsem_cmd_imedI  
  (fn: funname) (plS plE: plinfo)
  (lt : LTreeList fn plS plE) : itree (LCall +' E) lpoint :=
  lsem_cmd_imedSL isem_lcmd_seq_flow isem_li_aflow lt.

Definition lsem_fun_imedI  
  (fn: funname) : itree (LCall +' E) lpoint :=
  lsem_fun_imedSL isem_lcmd_seq_flow isem_li_aflow fn.

Definition handle_LRecI : LCall ~> itree (LCall +' E) :=
  fun T (rc : callE _ _ T) =>
   match rc with
   | Call fn => lsem_fun_imedI fn
   end.                            

(* LRec interpretation *)
Definition lsem_imed_recSL (fn: funname) (plS plE: plinfo)
  (lt : LTreeList fn plS plE) : itree E lpoint := 
  interp_mrec handle_LRecI (lsem_cmd_imedI lt).

End SLInterSemDef.

End IntermediateSem.

End LinSemContext.

End Asm1.


(* LEGACY - NOT USED 
(* intermediate semantics of instructions.
     LC -> isem_lcmd_seq_flow (isem_lcmd_acore could also do).  
     LSI -> isem_li_aflow *)
Definition lsem_i_imed_body 
  (LSC: lcmd -> lpoint -> itree (LCall +' E) lpoint)
  (LSI: lpoint -> itree (LCall +' E) lpoint)
  (LRec: forall (fn: funname) (plS plE: plinfo),
           LTreeList fn plS plE -> lpoint -> itree (LCall +' E) lpoint)
  (fn: funname) (plS plE: plinfo)
  (lt : LTree fn plS plE) : lpoint -> itree (LCall +' E) lpoint :=
  fun lpA =>
  let '(fnA, pA) := lpA in
  let '(pS, _) := plS in 
  let '(pE, _) := plE in 
(*  let LRec := @lsem_cmd_imed LSC LSI CNT in *)
  if fst lpA == fn then 
  match lt with
  | LErrLeaf _ => throw err
  | LLeaf _ (MkLI ii ir) =>
                            if LLeaf_ok (MkLI ii ir)
                            then LSI lpA
                            else throw err                                 
  | LIf1Node _ (p1, _) li1 lc li2 =>
      (* note: fst plE = S p1 *)
      match LIf1Node_ok li1 li2 with
      | false => throw err
      | true => 
             if (pA == pS) || (pA == p1) then LSI lpA
             else if in_btw (S pS) p1 pA then LRec _ _ _ lc lpA
             else throw err 
      end
  | LIfNode _ (p1, _) (p2, _) li1 lc2 li2 li3 lc1 li4 => 
      (* note: fst plE = S p2 *)
      match LIfNode_ok li1 li2 li3 li4 with
      | false => throw err
      | true => 
            if (pA == pS) || (pA == p1) ||
               (pA == S p1) || (pA == p2) then LSI lpA
            else if in_btw (S pS) p1 pA then LRec _ _ _ lc2 lpA
            else if in_btw (S (S p1)) p2 pA then LRec _ _ _ lc1 lpA
            else throw err 
      end     
  | LWhileTNode _ (p1, _) (p2, _) b ii li1 lc1 lc2 li2 =>
      (* note: fst plE = S p2 *)
      match LWhileTNode_ok li1 li2 with
      | false => throw err
      | true => 
            let bn := if b then 1 else 0 in  
            if (pA == pS) || (pA == pS + bn) || (pA == p2) then LSI lpA
            else if in_btw (S (pS + bn)) p1 pA then LRec _ _ _ lc1 lpA
            else if in_btw p1 p2 pA then LRec _ _ _ lc2 lpA
            else throw err 
      end
  | LWhileFNode _ _ lc => LRec _ _ _ lc lpA
  | LWhile1Node _ (p1, _) b ii li1 lc li2 =>
      (* note: fst plE = S p1 *)
      match LWhile1Node_ok li1 li2 with
      | false => throw err
      | true => 
            let bn := if b then 1 else 0 in   
            if (pA == pS) || (pA == pS + bn) || (pA == p1) then LSI lpA
            else if in_btw (S (pS + bn)) p1 pA then LRec _ _ _ lc lpA
            else throw err 
      end
  | LWhileNode _ (p1, _) (p2, _) b ii li1 li2 lc2 li3 lc1 li4 =>
      (* note: fst plE = S p2 *)
      match LWhileNode_ok li1 li2 li3 li4 with
      | false => throw err
      | true =>
            let bn := if b then 1 else 0 in
            let pS1 := pS + bn in  
            if (pA == pS) || (pA == pS1) || (pA == S pS1)
               || (pA == p1) || (pA == p2) then LSI lpA
            else if in_btw (S (S (pS1))) p1 pA then LRec _ _ _ lc2 lpA
            else if in_btw (S p1) p2 pA then LRec _ _ _ lc1 lpA
            else throw err 
      end        
  | LCallNode _ nb na fn' lc_bef lc_aft li1 li2 =>
      match LCallNode_ok nb na fn' lc_bef lc_aft li1 li2 with
      | false => throw err  
      | true => LSC (lc_bef ++ [li1]) lpA ;;
                l1 <- (trigger_inl1 (Call fn')) ;;
                LSC (li2 :: lc_aft) l1 ;;
                Ret (fn, pS + nb + S (S na))            
      end 
  end
  else throw err.   
*)

(*
(* used to introduce function-global iterations *)
Definition lsem_fun_imed_aux_F 
  (LSC: lcmd -> lpoint -> itree (LCall +' E) lpoint)
  (LSI: lpoint -> itree (LCall +' E) lpoint)
  (CNT: (lpoint -> itree (LCall +' E) lpoint) ->
         funname -> nat -> nat -> lpoint -> itree (LCall +' E) lpoint)
  (CNT_F: (lpoint -> itree (LCall +' E) lpoint) ->
         funname -> nat -> nat -> lpoint -> itree (LCall +' E) lpoint)
  (fn: funname) (fd: LTreeFun fn) : itree (LCall +' E) lpoint :=
  let clen := code_length fn in 
  match fd with
  | LTFun lbl pl1 lc1 lc2 lt =>
      let nE := clen + List.length lc1 + List.length lc2 in
      CNT_F (fun pl0 => LSC lc1 pl0 ;;
             l1 <- @lsem_cmd_imed LSC LSI CNT _ _ _ lt ;;
             LSC lc2 l1)
          fn 0 nE (fn, 0) 
  end.                   

Definition lsem_fun_imed_F
  (LSC: lcmd -> lpoint -> itree (LCall +' E) lpoint)
  (LSI: lpoint -> itree (LCall +' E) lpoint)
  (CNT: (lpoint -> itree (LCall +' E) lpoint) ->
         funname -> nat -> nat -> lpoint -> itree (LCall +' E) lpoint)
  (CNT_F: (lpoint -> itree (LCall +' E) lpoint) ->
         funname -> nat -> nat -> lpoint -> itree (LCall +' E) lpoint)
  (fn: funname) : itree (LCall +' E) lpoint :=
  fd <- err_def_option (ifenv fn) ;;
  lsem_fun_imed_aux_F LSC LSI CNT CNT_F fd.
*)


(* WRONG 
(***** INTERMEDIATE FUNCTION-GLOBAL SEMANTICS *)

Section FInterSemDef.
Context {XF: LFindE -< E} {XL: LEvalE -< E } {XSl: @stateE LState -< E}.

Definition lsem_fun_imedF  
  (fn: funname) : itree (LCall +' E) lpoint :=
  lsem_fun_imed_F
    isem_lcmd_seq_flow isem_li_aflow (fun f _ _ _ => f) LACntrI fn.

Definition handle_LRecF : LCall ~> itree (LCall +' E) :=
  fun T  (rc : callE _ _ T) =>
   match rc with
   | Call fn => lsem_fun_imedF fn
   end.                            

(* LRec interpretation *)
Definition lsem_imed_recF (fn: funname) (plS plE: plinfo)
  (lt : LTreeList fn plS plE) : itree E lpoint := 
  interp_mrec handle_LRecF (lsem_cmd_imedG lt).

End FInterSemDef.
*)

(*
(* given only global iteration, intermediate and instrumented are
   equivalent; after interpreting LRec *)
Lemma intermediate_global2instrumented_lcmd {XS: stateE LState -< E}
  (fn: funname) (plS plE: plinfo)
  (lt : LTreeList fn plS plE) :
  eutt eq (lsem_imed_recF lt)
    (isem_lcmd_flow (fn, fst (fst (forget_imed_cmd lt)))).
Proof.
Admitted. 
 *)

(*
(* similar for sequential linear commands; only meaningful when lcmd is
   straightline code (used in Intermediate) *)
Fixpoint isem_lcmd_seq_flow (lc: lcmd) (l0: lpoint) : itree E lpoint :=
  match lc with
  | nil => Ret l0
  | (MkLI ii li) :: lc0 =>
      l1 <- isem_li_flow li l0 ;; isem_lcmd_seq_flow lc0 l1
  end.             

(* version based on the core semantics *)
Fixpoint isem_lcmd_acore (lc: lcmd) : itree E unit :=
  match lc with
  | nil => Ret tt
  | (MkLI ii li) :: lc0 => isem_li_acore li ;; isem_lcmd_acore lc0
  end.             
*)


