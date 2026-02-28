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

(* Ultimately, both the abstract pc (as an lpoint) and the abtract
   stack will come from the lstate and should agree it. This are
   invariants that can be treated as internal to Linear.  *)


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

Definition find_linstr (lc: lcmd) (pt: nat) : option linstr :=
  oseq.onth lc pt.

Definition is_final (lc: lcmd) (pt: nat) : bool :=
  pt =? (length lc).


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
Definition isem_i_lcore (i : linstr_r) : itree E unit :=
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
  isem_i_lcore i ;; isem_i_lflow i l0.

(* the concrete semantics, where the lpoint is derived from the lstate
*)
Definition isem_i_lplain (i : linstr_r) (s: LState) :
  itree E LState :=
  iresult (linstr_sem i s) s.

(*
Definition isem_i_lplain (PC: LState -> lpoint) (i : linstr_r) :
  itree E lpoint :=
  s1 <- trigger (@Get LState) ;;
  s2 <- iresult (linstr_sem i s1) s1 ;;
  trigger (@Put LState s2) ;; Ret (PC s2).
*)

Section Iterators.

(* the output of the linearization pass; should use linear_l2r_fd *)
Notation LFEnv := (funname -> option lcmd). 
Context (lfenv: LFEnv).

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
  ITree.iter (@LCntr E XE Sem fn nS nE) lp0.

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
Definition iisem_lcmd_body (lbl: lpoint) :
  itree E (lpoint + lpoint) := GCntr isem_linstr lbl.

(* iterative semantics of a linear program, from any starting point *)
Definition iisem_lcmd (lbl: lpoint) : itree E lpoint :=
  ITree.iter iisem_lcmd_body lbl.

(* iterative semantics of a linear function from its entry point *)
Definition iisem_lfun (fn: funname) : itree E lpoint :=
  iisem_lcmd (fn, 0).

(* stateful iterative semantics body *)
Definition isem_lcmd_body (Hlt: LState -> option bool)
  (Fnd: LState -> option linstr) (lbl: LState) :
  itree E (LState + LState) := ACntr isem_i_lplain Hlt Fnd lbl.

(* stateful iterative semantics of a linear program, from any state *)
Definition isem_lcmd (Hlt: LState -> option bool)
  (Fnd: LState -> option linstr) (lbl: LState) : itree E LState :=
  ITree.iter (isem_lcmd_body Hlt Fnd) lbl.


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
  | FindLabel rlbl =>
      match lfenv (fst rlbl) with
      | Some lc =>
          n <- err_result (fun _ => err) (find_label (snd rlbl) lc) ;;
          Ret (fst rlbl, n)
      | _ => throw err
      end             
  end.   

End HandleStackA.

End Iterators.


(*******************************************************************)

Notation plinfo := (nat * label)%type.

(* maps a point to a left (continue) or right (exit) return value,
   depending on whether it satisfies P *)
Definition ret_lp_select {L: Type} {PC: L -> lpoint}
  E (P: lpoint -> bool) (l0: L) :
  itree E (L + L) :=
  if P (PC l0) then Ret (inl l0) else Ret (inr l0).

(* basically, switches between different ktrees, depending on an
   ordered list of intervals. ls are the (well-ordered) interval
   end-points; ks are the ktrees *)
Fixpoint nat_kt_switch_n {E} {T} (t: T)
  (ls: list nat) (ks: list (nat -> itree E T)) (n: nat) : itree E T :=
  match (ls, ks) with
  | (nil, _) => Ret t
  | (_, nil) => Ret t                
  | (n0 :: ns0, k0 :: ks0) =>
    if n < n0 then k0 n0 else nat_kt_switch_n t ns0 ks0 n end.            

Fixpoint nat_kt_switch {L: Type} {PC: L -> lpoint} {E} {T} (t: T)
  (ls: list nat) (ks: list (L -> itree E T)) (s: L) : itree E T :=
  match (ls, ks) with
  | (nil, _) => Ret t
  | (_, nil) => Ret t                
  | (n0 :: ns0, k0 :: ks0) =>  
      if (snd (PC s)) < n0 then k0 s
      else @nat_kt_switch L PC E T t ns0 ks0 s end.

(* sequentialize the application of lsem_instr within a function. used
   to map lsem_instr to commands *)
Fixpoint lsem_c {L: Type} {PC: L -> lpoint}
  {E} {XE: ErrEvent -< E} (R: instr -> L -> itree E L)
  (fn: funname) (cc: cmd) (s: L) : itree E L :=
  let: (fn0, n) := PC s in
  if fn0 == fn then 
     match cc with
     | nil => Ret s
     | i :: cc0 => s' <- R i s ;;
                   @lsem_c L PC E XE R fn cc0 s' end
  else throw err.     

(* applies nat_kt_switch to produce an iterative body out of a list of
   alternatives; the exit point is determined by the interval (nS, nE)
   in the linear code of fn *)
Definition ktree_switch_n {L: Type} {PC: L -> lpoint}
  {E} {XE: ErrEvent -< E}
  (fn: funname) (nS nE: nat)
  (ls: list nat) (ks: list (nat -> itree E L))
  (s0: L) : itree E (L + L) := 
  let l0 := PC s0 in 
  let InInterval := lcp_in_interval nS nE in 
  let RetS := @ret_lp_select L PC E InInterval in
  let RSLift := fun f n => ITree.bind (f n) RetS in 
  if InInterval l0 && ((fst l0) == fn)
  then @nat_kt_switch_n E (L + L)
          (inr s0) ls (map RSLift ks) (snd l0)
  else Ret (inr s0).         

Definition ktree_switch {L: Type} {PC: L -> lpoint}
  {E} {XE: ErrEvent -< E} 
  (fn: funname) (nS nE: nat)
  (ls: list nat) (ks: list (L -> itree E L))
  (s0: L) : itree E (L + L) :=
  let l0 := PC s0 in 
  let InInterval := lcp_in_interval nS nE in
  let RetS := @ret_lp_select L PC E InInterval in
  let RSLift := fun f n => ITree.bind (f n) RetS in 
  if InInterval l0 && ((fst l0) == fn)
  then @nat_kt_switch L PC E (L + L)
          (inr s0) ls (map RSLift ks) s0
  else Ret (inr s0).         


Definition lsem_instr 
  (fn0: funname) (pl0 pl1: plinfo)
  (lt : LTree fn0 pl0 pl1) (l0: lpoint) : itree E lpoint :=
  match lt with
  | LErrLeaf => throw err
  | LLeaf li => match li with
                | Copn xs _ o es => isem_linstr i l0    
                | Csyscall xs o es => isem_linstr i l0      
                | _ => throw err
                end
  | LLeafL _ -> throw err                
  | LIf1Node (Lcond e lbl) lc (Llabel InternalLabel lbl') =>
      match (lbl == lbl') with
      | false => throw err
      | true => let
                 
                

                  
(* linear semantics of the source code, for the intermediate
   representation. assuming lfenv gives the linear code *)
Fixpoint lsem_instr E {XE: ErrEvent -< E}
  (LS: funname -> nat -> nat -> S -> itree (LCall +' E) S)
  (loc_instr : instr -> lcpoint -> nat)
  (i : instr) (s0: S) : itree (LCall +' E) S :=
  let l1 := PC s0 in 
  let: (MkI ii ir) := i in
  let: (fn, n0) := l1 in
  let: nE := loc_instr i l1 in
  let K1 := fun s => let n := snd (PC s) in LS fn n (Datatypes.S n) s in
  let LocC := fun c nA => localize_cmd loc_instr fn c nA in
  let LRec := fun c nA =>
                 lsem_c (lsem_instr LS loc_instr) fn c nA in
  match ir with
  | Cassgn x tg ty e => throw err

  | Copn xs tg o es => LS fn n0 nE s0                

  | Csyscall xs o es => LS fn n0 nE s0   

  | Cif e c1 c2 =>
      let Kc1 := LRec c1 in 
      let Kc2 := LRec c2 in 
      let k1_n := LocC c1 in
      let k2_n := LocC c2 in
      let n1 := Datatypes.S n0 in
      let n2 := k2_n n1 in
      let n3 := Datatypes.S n2 in
      let n4 := Datatypes.S n3 in
      let n5 := k1_n n4 in
      let n6 := Datatypes.S n5 in
      ITree.iter (ktree_switch fn n0 nE
        [n1; n2; n3; n4; n5; n6] [K1; Kc2; K1; K1; Kc1; K1]) s0 
      
  | Cwhile a c1 e ii0 c2 =>
      let Kc1 := LRec c1 in 
      let Kc2 := LRec c2 in 
      let k1_n := LocC c1 in
      let k2_n := LocC c2 in
      let n1 := Datatypes.S n0 in
      let n2 := Datatypes.S n1 in
      let n3 := k2_n n2 in
      let n4 := Datatypes.S n3 in
      let n5 := Datatypes.S n4 in
      let n6 := k1_n n5 in
      let n7 := Datatypes.S n6 in
      ITree.iter (ktree_switch fn n0 nE
        [n1; n2; n3; n4; n5; n6; n7] [K1; K1; Kc2; K1; K1; Kc1; K1]) s0 

  | Cfor i (d, lo, hi) c => throw err 

  (* TODO: double-check how to take ReturnTarget into account *) 
  | Ccall xs fn1 args => trigger_inl1 (Call (fn1, s0))
                                  
 end.

