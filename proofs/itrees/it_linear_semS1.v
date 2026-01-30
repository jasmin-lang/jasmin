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
Require Import linearization.

Require Import it_cflow_semS it_effect_semS equiv_extras rutt_extras.

From ITree Require Import Rutt RuttFacts.

Import Memory.
Require oseq.
Require Import Relations.
Require Import List.

Import ListNotations. 
Import MonadNotation.
Local Open Scope monad_scope.

(** GENERAL -> move elsewhere *)

Definition conv_obj T1 T2 (ee: T1 = T2) (u: T1) : T2 :=
  eq_rect T1 (fun T : Type => T) u T2 ee.


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

(* the output of the linearization pass *)
Notation LFEnv := (funname -> option lcmd). 
Context (lfenv: LFEnv).

(* point in the linear code of a function *)
Definition lcpoint : Type := (funname * nat)%type.

(* these events represent the actual linear semantics *)
Variant LinstrE (S: Type) : Type -> Type :=
  | ELopn        : lexprs -> sopn -> rexprs -> S -> LinstrE S
  | ELsyscall    : syscall_t -> S -> LinstrE S 
  | ELcall       : option var_i -> remote_label -> S -> LinstrE S
  | ELret        : S -> LinstrE S
  | ELalign      : S -> LinstrE S
  | ELlabel      : label_kind -> label -> S -> LinstrE S 
  | ELgoto       : remote_label -> S -> LinstrE S
  | ELigoto      : rexpr -> S -> LinstrE S
  | ELstoreLabel : var -> label -> S -> LinstrE S
  | ELcond       : fexpr -> label -> S -> LinstrE S.

(* not used here. these events are used to provide a dataflow
   abstraction. however, the abstraction might not be so useful, in
   which case LinstrE and LFlowE should probably be merged. *)
Variant LFlowE : Type -> Type :=
  | LFopn        : lexprs -> sopn -> rexprs -> lcpoint ->
                   LFlowE lcpoint
  | LFsyscall    : syscall_t ->
                   lcpoint -> LFlowE lcpoint 
  | LFcall       : option var_i -> remote_label -> lcpoint ->
                   LFlowE lcpoint
  | LFret        : lcpoint -> LFlowE lcpoint
  | LFalign      : lcpoint -> LFlowE lcpoint
  | LFlabel      : label_kind -> label -> lcpoint ->
                   LFlowE lcpoint 
  | LFgoto       : remote_label -> lcpoint -> LFlowE lcpoint
  | LFigoto      : rexpr -> lcpoint -> LFlowE lcpoint
  | LFstoreLabel : var -> label -> lcpoint -> LFlowE lcpoint
  | LFcond       : fexpr -> label -> lcpoint -> LFlowE lcpoint.

Definition find_linstr_in_env (lc: lcmd) (pt: nat) : option linstr :=
  oseq.onth lc pt.

Definition is_final (lc: lcmd) (pt: nat) : bool :=
  pt =? (length lc).

Definition incr_label (l: lcpoint) : lcpoint :=
  match l with (fn, pt) => (fn, S pt) end.

(* the program point is in the interval *)
Definition lcp_in_interval (fn: funname) (nS nE: nat) (l1: lcpoint) : bool :=
  match l1 with
  | (fn0, n0) => (fn == fn0) && (nS <= n0) && (n0 < nE) end. 

Definition halt_pred (l: lcpoint) : bool :=
  let fn := fst l in
  let lbl := snd l in
  let plc := lfenv fn in
  match plc with
  | Some lc => is_final lc lbl 
  | _ => false
  end.             

(* abstract for the stack *)
Definition alstate := list lcpoint.

(* not used *)
Definition lcpoint2remote (l: lcpoint) : remote_label :=
  match l with (fn, n) => (fn, Pos.of_nat n) end. 
(* not used *)
Definition remote2lcpoint (l: remote_label) : lcpoint :=
  match l with (fn, l) => (fn, Pos.to_nat l) end. 


Section IterativeSem.

Context {S: Type} {PC : S -> lcpoint}. 

(* the global iteration body used in the 'direct' linear
   semantics. is_final is the halting condition *)
Definition GCntr {E} {XE: ErrEvent -< E}  
  (F: linstr_r -> S -> itree E S)
  (l0: S) : itree E (S + S) :=
  let fpt := PC l0 in
  match fpt with 
  | (fn, pt) =>  
  (* the optional function body *)
    match (lfenv fn) with
    (* the function exists: find the instruction in its body *)
    | Some lc => 
      match (find_linstr_in_env lc pt) with
      (* the instruction exists: execute it and return the next position *) 
      | Some (MkLI _ i) => l1 <- F i l0 ;; Ret (inl l1)
      (* the instruction does not exists: the execution terminates if the
         label equals the code length, otherwise throws an error *)        
      | _ => if is_final lc pt then Ret (inr l0) else throw err end
    (* the function does not exist: throw an error *)    
    | _ => throw err end
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


(**************************************************************)

Section LinstrSem.

Context {E} {XE: ErrEvent -< E}. 


Section LinstrSemCore.
  
Context {XI : LinstrE S -< E}. 

(* denotational semantics of instructions *)
Definition isem_linstr (ir : linstr_r) (s: S) :
  itree E S :=
  match ir with
  | Lopn xs o es => trigger (ELopn xs o es s)

  | Lsyscall o => trigger (ELsyscall o s)
                                     
  | Lcall or d => trigger (ELcall or d s) 

  | Lret => trigger (ELret s)

  | Lalign => trigger (ELalign s) 
      
  | Llabel x y => trigger (ELlabel x y s) 

  | Lgoto d => trigger (ELgoto d s) 

  | Ligoto e => trigger (ELigoto e s) 

  | LstoreLabel x lbl => trigger (ELstoreLabel x lbl s)                      

  | Lcond e lbl => trigger (ELcond e lbl s)
  end.                         

(* iterative semantics body *)
Definition isem_lcmd_body (lbl: S) : itree E (S + S) :=
  GCntr isem_linstr lbl.

(* iterative semantics of a linear program, from any starting point *)
Definition isem_lcmd (lbl: S) : itree E S :=
  ITree.iter isem_lcmd_body lbl.

End LinstrSemCore.


Section LinSemClass.

Class LinSem : Type := {
  Lopn_sem (xs: seq.seq lexpr) (o: sopn) (es: seq.seq rexpr)
     (s1: S) : exec S  ;

  Lsyscall_sem (o: syscall_t) (s1: S) : exec S ;

  Lcall_sem (ov: option var_i) (d: remote_label) (s1: S) :
    exec S ;

  Lret_sem (s1: S) : exec S ;

  Lalign_sem (s1: S) : exec S ;

  Llabel_sem (k: label_kind) (lbl: label) (s1: S) : exec S ;

  Lgoto_sem (d: remote_label) (s1: S) : exec S ;

  Ligoto_sem (e: rexpr) (s1: S) : exec S ;

  Lstorelabel_sem (x: var) (lbl: label) (s1: S) : exec S ;

  Lcond_sem (e: fexpr) (lbl: label) (s1: S) : exec S ;           
}.

(* same as eval_instr (in the old semantics, with S = lstate) *)
Definition linstr_sem {LS_I : LinSem} 
  (i : linstr_r) (s1: S) : exec S :=
  match i with 
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

Definition handle_StE_L {InitFun: lcpoint -> S -> option S} :
  @StE S S funname S ~> itree E :=
  fun _ e =>
    match e with
    | GetSE s => Ret s
    | PutSE s => Ret s
    | InitFunCall fd fs => err_def_option (InitFun (fd,0) fs)
    end.                             

End LinSemClass.

End LinstrSem.


Section StateRecSem.

Context {LS_I : LinSem} {InitFun: lcpoint -> S -> option S}.

Notation LCall := (callE (funname * S) S).


Section LinstrInterp.
          
Context {E} {XE: ErrEvent -< E} {XS0: @StE S S funname S -< E}.

Definition Linstr_sem (i : linstr_r) (s: S) : itree E S :=
  s1 <- trigger (@GetSE S S funname S s) ;;
  s2 <- iresult (linstr_sem i s1) s1 ;;
  trigger (@PutSE S S funname S s2).

Definition handle_Linstr {T}
  (e: LinstrE S T) : itree E T :=
  match e with
  | ELopn xs o es s => Linstr_sem (Lopn xs o es) s
  | ELsyscall o s => Linstr_sem (Lsyscall o) s
  | ELcall o d s => Linstr_sem (Lcall o d) s
  | ELret s => Linstr_sem Lret s 
  | ELalign s => Linstr_sem Lalign s
  | ELlabel x y s => Linstr_sem (Llabel x y) s
  | ELgoto d s => Linstr_sem (Lgoto d) s
  | ELigoto e s => Linstr_sem (Ligoto e) s
  | ELstoreLabel x lbl s => Linstr_sem (LstoreLabel x lbl) s
  | ELcond e lbl s => Linstr_sem (Lcond e lbl) s
  end.

Definition interp_Linstr {T} (t: itree (@LinstrE S +' E) T) : itree E T :=
  interp (ext_handler (@handle_Linstr)) t.

End LinstrInterp.


Section StackAllocEvs.

(* tmp, just to patch up *)
Variant StackAllocE : Type -> Type :=
  | Before : S -> StackAllocE S
  | After : S -> StackAllocE S.
(*  | GetFunSourceCode (fn: funname) : StackAllocE cmd. *)

Definition handle_StackAlloc {E0} {XE0: ErrEvent -< E0}
  (* {XLS: stateE lstate -< E}*)
  {T} (e: @StackAllocE T) : itree E0 T. 
Admitted. 

Definition interp_StackAlloc {E0} {XE0: ErrEvent -< E0}
  (* {XLS: stateE lstate -< E} *)
  {T} (t: itree (StackAllocE +' E0) T) : itree E0 T :=
  interp (ext_handler (fun T x => @handle_StackAlloc E0 XE0 T x)) t.

End StackAllocEvs.


Section FunFromEntry.

Context {E} {XE: ErrEvent -< E}
        {XL: LinstrE S -< E} {XS: @StE S S funname S -< E}.  

(* iterative semantics of a linear function from its entry point *)
Definition isem_lfun_abs (fn: funname) (s: S) : itree E S :=
  s1 <- trigger (@InitFunCall S S funname S fn s) ;;
  isem_lcmd s1.

End FunFromEntry.


Section LSemDefs.

Context {E} {XE: ErrEvent -< E}.

Definition interp_St_L {T} (t: itree (@StE S S funname S +' E) T) :
  itree E T :=
  interp (ext_handler (@handle_StE_L _ _ InitFun)) t.

Definition handle_Linstr_LS {T} (e: LinstrE S T) : itree E T :=
  interp_St_L (handle_Linstr e).

Definition interpLS1 {T} (t: itree (@LinstrE S +' E) T) : itree E T :=
  interp (ext_handler (@handle_Linstr_LS)) t.

Definition interpLS2 {T}
  (t: itree (@LinstrE S +' @StE S S funname S +' E) T) : itree E T :=
  interp_St_L (interp_Linstr t).

Definition isem_lfun (fn: funname) (s: S) : itree E S :=
  interpLS2 (isem_lfun_abs fn s).

(* if the linear translation of i is straightline code that ends
   without jumps, it will return (fn, n1); the first jump destination
   otherwise *)
Definition lsem_LCntr (fn: funname) (n0 n1: nat) s : itree E (S + S) :=
  LCntr (fun i l => interpLS1 (isem_linstr i l)) fn n0 n1 s.
  (* (fn, n0). *)

(* iterate lsem_LCntr *)
Definition lsem_LCntrI (fn: funname) (n0 n1: nat) s : itree E S :=
  LCntrI (fun i l => interpLS1 (isem_linstr i l)) fn n0 n1 s.
 (* (fn, n0). *)

(* used to 'localize' cc, by computing the linear code interval
   associated to the translation of cc *)
Definition localize_cmd (loc_instr : instr -> lcpoint -> nat)
  (fn0: funname) (cc: cmd) (n0: nat) : nat :=
  linear_end_c (fun fn i n => loc_instr i (fn, n)) fn0 cc n0. 

(* maps a point to a left (continue) or right (exit) return value,
   depending on whether it satisfies P *)
Definition lcp_ret_select E (P: lcpoint -> bool) (s0: S) :
  itree E (S + S) :=
  if P (PC s0) then Ret (inl s0) else Ret (inr s0).

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

Fixpoint nat_kt_switch {E} {T} (t: T)
  (ls: list nat) (ks: list (S -> itree E T)) (s: S) : itree E T :=
  match (ls, ks) with
  | (nil, _) => Ret t
  | (_, nil) => Ret t                
  | (n0 :: ns0, k0 :: ks0) =>  
    if (snd (PC s)) < n0 then k0 s else nat_kt_switch t ns0 ks0 s end.


(* Section LSemCore. *)
(* Context {XS: @StE S S funname S -< E}. *)

(* sequentialize the application of lsem_instr within a function. used
   to map lsem_instr to commands *)
Fixpoint lsem_c {E} {XE: ErrEvent -< E} (R: instr -> S -> itree E S)
  (fn: funname) (cc: cmd) (s: S) : itree E S :=
  let: (fn0, n) := PC s in
  if fn0 == fn then 
     match cc with
     | nil => Ret s
     | i :: cc0 => s' <- R i s ;;
                   lsem_c R fn cc0 s' end
  else throw err.     

(* applies nat_kt_switch to produce an iterative body out of a list of
   alternatives; the exit point is determined by the interval (nS, nE)
   in the linear code of fn *)
Definition ktree_switch_n  
  (fn: funname) (nS nE: nat)
  (ls: list nat) (ks: list (nat -> itree E S))
  (s0: S) : itree E (S + S) :=
  let l0 := PC s0 in 
  let InInterval := lcp_in_interval fn nS nE in
  let RetS := lcp_ret_select E InInterval in
  let RSLift := fun f n => ITree.bind (f n) RetS in 
  if InInterval l0 
  then @nat_kt_switch_n E (S + S)
          (inr s0) ls (map RSLift ks) (snd l0)
  else Ret (inr s0).         

Definition ktree_switch E {XE: ErrEvent -< E} 
  (fn: funname) (nS nE: nat)
  (ls: list nat) (ks: list (S -> itree E S))
  (s0: S) : itree E (S + S) :=
  let l0 := PC s0 in 
  let InInterval := lcp_in_interval fn nS nE in
  let RetS := lcp_ret_select E InInterval in
  let RSLift := fun f n => ITree.bind (f n) RetS in 
  if InInterval l0 
  then @nat_kt_switch E (S + S)
          (inr s0) ls (map RSLift ks) s0
  else Ret (inr s0).         

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

(* basically, the sequential alternative to LCntrI, relying on cc *)
Fixpoint lsem_cX E {XE: ErrEvent -< E}            
  (R: instr -> S -> itree E S)
  (fn: funname) (nS nE: nat)
  (cc: cmd) (s0: S) : itree E S :=
  let l0 := PC s0 in 
  if lcp_in_interval fn nS nE l0
  then match cc with
       | nil => Ret s0
       | i :: cc0 => l2 <- R i s0 ;;
                     lsem_cX R fn nS nE cc0 l2 end
  else Ret s0.
(*  else throw err. *)

Definition lsem_c_seq E {XE: ErrEvent -< E}
  (loc_instr : instr -> lcpoint -> nat)               
  (R: instr -> S -> itree E S)
  (cc: cmd) (l0 : lcpoint) s0 : itree E S :=
  match l0 with
  | (fn0, nS) =>
    let nE := localize_cmd loc_instr fn0 cc nS in
    lsem_cX R fn0 nS nE cc s0 end.

(* linear semantics of source commands *)
Definition lsem_cmd E {XE: ErrEvent -< E}
  (LS: funname -> nat -> nat -> S -> itree (LCall +' E) S)
  (loc_instr : instr -> lcpoint -> nat)
  (cc : cmd) (l0 : lcpoint) (s0 : S) :
     itree (LCall +' E) S := 
  @lsem_c_seq (LCall +' E) _
              loc_instr (lsem_instr LS loc_instr) cc l0 s0.

(* End LSemCore. *)
End LSemDefs.


Section LSemSpec.

Context {Prog State FState FunDef: Type}.
Context {GetFunDef : Prog -> funname -> option FunDef}.
Context {GetFunCode : FunDef -> cmd}.
Context {pp : Prog}.

(* linear semantics of source functions. l1 is the return address *)
Definition lsem_fun0 E {XE: ErrEvent -< E} {XTSA: StackAllocE -< E}
  (LS: funname -> nat -> nat -> S -> itree (LCall +' E) S)
  (loc_instr : instr -> lcpoint -> nat)
  (fn: funname) (s0: S) : itree (LCall +' E) S :=
  fd <- err_def_option (GetFunDef pp fn) ;;  
  s1 <- trigger (Before s0) ;;
  let cc := GetFunCode fd in  
  s2 <- @lsem_cmd E XE LS loc_instr cc (fn, 0) s1 ;;
  trigger (After s2).

(* linear semantics of source functions. l1 is the return address *)
Definition lsem_fun E {XE: ErrEvent -< E}
  (LS: funname -> nat -> nat -> S -> itree (LCall +' E) S)
  (HA: StackAllocE ~> itree E)
  (loc_instr : instr -> lcpoint -> nat)
  (fn: funname) (s0: S) : itree (LCall +' E) S :=
  let HA1 := fun _ e => translate inr1 (HA _ e) in 
  fd <- err_def_option (GetFunDef pp fn) ;;  
  s1 <- HA1 S (Before s0) ;;
  let cc := GetFunCode fd in
  (* the PC in s2 must be the return target, which is a label *)
  s2 <- @lsem_cmd E XE LS loc_instr cc (fn, 0) s1 ;;
  (* After can keep the label into account, increasing PC by one as
     first step. Alternatively, we could introduce a K1 step before
     After, but this seems more complicated than necessary *)
  HA1 S (After s2).

Definition handle_LRec E {XE: ErrEvent -< E} 
  (LS: funname -> nat -> nat -> S -> itree (LCall +' E) S)
  (HA: StackAllocE ~> itree E)
  (loc_instr : instr -> lcpoint -> nat) :
  LCall ~> itree (LCall +' E) :=
  fun T (rc : callE _ _ T) =>
   match rc with
   | Call (fn, s1) => lsem_fun LS HA loc_instr fn s1
   end.
  
Definition interp_LRec E {XE: ErrEvent -< E} 
  (LS: funname -> nat -> nat -> S -> itree (LCall +' E) S)
  (HA: StackAllocE ~> itree E)
  (loc_instr : instr -> lcpoint -> nat) 
  T (t: itree (LCall +' E) T) : itree E T :=
  interp_mrec (handle_LRec LS HA loc_instr) t.

Definition interp_LRec_cmd E {XE: ErrEvent -< E}
  (LS: funname -> nat -> nat -> S -> itree (LCall +' E) S)
  (HA: StackAllocE ~> itree E)
  (loc_instr : instr -> lcpoint -> nat)
  (c: cmd) (s0: S) : itree E S :=
  interp_LRec LS HA loc_instr (lsem_cmd LS loc_instr c (PC s0) s0).


Section LinearWithRec.
  
Notation SCall := (callE (funname * FState) FState).

Context (RR : State -> S -> Prop).
Context (FRR : FState -> S -> Prop).

Definition ConvFRR T1 T2 (u1: T1) (u2: T2) :=
  exists (ee1: T1 = FState) (ee2: T2 = S),
    FRR (conv_obj ee1 u1) (conv_obj ee2 u2).

Definition RecPreRel T1 T2 
  (e1: SCall T1) (e2: LCall T2) : Prop :=
   match (e1, e2) with
   | (Call (fn1, fs), Call (fn2, s)) => (fn1 = fn2) /\ (FRR fs s)
   end. 

Definition RecPostRel T1 T2 
  (e1: SCall T1) (u1: T1) (e2: LCall T2) (u2: T2) : Prop :=
  RecPreRel e1 e2 /\ ConvFRR u1 u2.
      
Definition RecPreC {E1 E2: Type -> Type}
  {XR1: SCall -< E1} {XR2: LCall -< E2}             
  T1 T2 (e1: E1 T1) (e2: E2 T2) : Prop :=
  exists (e01: SCall T1) (e02: LCall T2),
    e1 = (subevent _ e01) /\ e2 = (subevent _ e02) /\
    RecPreRel e01 e02.  

Definition RecPostC {E1 E2: Type -> Type}
  {XR1: SCall -< E1} {XR2: LCall -< E2}   
  T1 T2 (e1: E1 T1) (u1: T1) (e2: E2 T2) (u2: T2) : Prop :=
  exists (e01: SCall T1) (e02: LCall T2),
    e1 = (subevent _ e01) /\ e2 = (subevent _ e02) /\
    RecPreRel e01 e02 /\ RecPostRel e01 u1 e02 u2. 


Section Transl.

Context {E1} {XE1: ErrEvent -< E1}.
Context {E2} {XE2: ErrEvent -< E2}. 

Notation RecE1 := (SCall +' E1).
Notation RecE2 := (LCall +' E2).

Context {HI : @InstrE asm_op syscall_state sip State FState FunDef State ~>
                itree (@StE State FState FunDef State +' E1)}
        {HS : @StE State FState FunDef State ~> itree E1}.
Context {HA: StackAllocE ~> itree E2}.

(* source semantics defs *)
Definition source_isem_instr (i: instr) (s: State) :
  itree (SCall +' E1) State :=
  @isem_instr_State asm_op syscall_state sip
    State FState FunDef E1 HI HS i s.                                        

Definition source_isem_cmd (c: cmd) (s: State) :
  itree (SCall +' E1) State :=
  @isem_cmd_State asm_op syscall_state sip
    State FState FunDef E1 HI HS c s.                                        

Definition source_isem_fun (p: Prog) (fn: funname) (fs: FState) :
  itree (SCall +' E1) FState :=
  @isem_fun_State asm_op syscall_state sip
    Prog State FState FunDef GetFunDef GetFunCode E1 HI HS XE1 p fn fs.

Definition source_denote_instr (p: Prog) (i: instr) (s: State) :
  itree E1 State :=
  @denote_instr_State asm_op syscall_state sip
    Prog State FState FunDef GetFunDef GetFunCode E1 HI HS XE1 p i s.

Definition source_denote_cmd (p: Prog) (c: cmd) (s: State) :
  itree E1 State :=
  @denote_cmd_State asm_op syscall_state sip
    Prog State FState FunDef GetFunDef GetFunCode E1 HI HS XE1 p c s.

Definition source_denote_fun (p: Prog) (fn: funname) (fs: FState) :
  itree E1 FState :=
  @denote_fun_State asm_op syscall_state sip
    Prog State FState FunDef GetFunDef GetFunCode E1 HI HS XE1 p fn fs.

(* linear semantics defs *)
Definition linsem_instr (loc_instr : instr -> lcpoint -> nat)
  (i : instr) (s0: S) : itree (LCall +' E2) S :=
  lsem_instr (@lsem_LCntrI RecE2 _) loc_instr i s0.

Definition linsem_cmd (loc_instr : instr -> lcpoint -> nat)
  (c : cmd) (s0: S) : itree (LCall +' E2) S :=
  lsem_cmd (@lsem_LCntrI RecE2 _) loc_instr c (PC s0) s0.

Definition linsem_fun (loc_instr : instr -> lcpoint -> nat)
  (fn : funname) (s0: S) : itree (LCall +' E2) S :=
  lsem_fun (@lsem_LCntrI RecE2 _) HA loc_instr fn s0.

Definition linsem_rec_instr (loc_instr : instr -> lcpoint -> nat)
  (i : instr) (s0: S) : itree E2 S :=
  interp_LRec (@lsem_LCntrI RecE2 _) HA loc_instr
    (linsem_instr loc_instr i s0).

Definition linsem_rec_cmd (loc_instr : instr -> lcpoint -> nat)
  (c : cmd) (s0: S) : itree E2 S :=
  interp_LRec (@lsem_LCntrI RecE2 _) HA loc_instr
    (linsem_cmd loc_instr c s0).

Definition linsem_rec_fun (loc_instr : instr -> lcpoint -> nat)
  (fn : funname) (s0: S) : itree E2 S :=
  interp_LRec (@lsem_LCntrI RecE2 _) HA loc_instr
    (linsem_fun loc_instr fn s0).


Definition lc_end {pd : PointerData} (sp: sprog) :=
  fun i '(fn, n) => linear_end_i sp fn i n. 

Definition sp_is_ok (pd : PointerData) (sp: sprog)
  (lin_params: linearization_params) : Prop :=
  forall (fn: funname) (fd: sfundef),
      get_fundef (p_funcs sp) fn = Some fd ->
      let c0 := fd.(f_body) in     
      let: (_, lc0) :=
        (linear_c (@linear_i asm_op pd _ lin_params sp fn) c0 xH [::]) in
      lfenv fn = Some lc0. 
             
(* relating the linear semantics of a source function (intermediate
   representation) with its source semantics (tentative). as it is, we
   probably need to interpret state events. a better way could be to
   combine higher-level events together. WIP *)
Lemma LinearSem_fun_body_correct (pd : PointerData) (sp: sprog)
  (lin_params: linearization_params)  :
  check_prog lin_params sp = ok tt ->
  sp_is_ok sp lin_params ->
  let LS := @lsem_LCntrI RecE2 _ in 
  forall fn xs es ii sst lst,
    RR sst lst ->
    let lin_sem := lsem_fun LS HA (lc_end sp) fn lst in
    let source_sem := source_isem_instr (MkI ii (Ccall xs fn es)) sst in
    @rutt RecE1 RecE2 _ _ RecPreC RecPostC 
        (fun _ s => halt_pred (PC s)) source_sem lin_sem. 
Proof.
  intros.
  unfold lin_sem, source_sem.
  unfold source_isem_instr, lsem_fun, lsem_cmd. simpl.
  unfold lsem_cX. simpl.
  unfold lsem_instr. simpl.
Admitted.   

Lemma LinearSem_instr_correct (pd : PointerData) (sp: sprog) 
  (lin_params: linearization_params)  :
  check_prog lin_params sp = ok tt ->
  sp_is_ok sp lin_params ->
  forall i sst lst,
    RR sst lst ->
    let source_sem := source_denote_instr pp i sst in
    let lin_sem := linsem_rec_instr (lc_end sp) i lst in
    @rutt E1 E2 _ _ (fun _ _ _ _ => True) (fun _ _ _ _ _ _ => True) 
        (fun _ s => halt_pred (PC s)) source_sem lin_sem. 
Proof.
Admitted.

Lemma LinearSem_cmd_correct (pd : PointerData) (sp: sprog) 
  (lin_params: linearization_params)  :
  check_prog lin_params sp = ok tt ->
  sp_is_ok sp lin_params ->
  forall c sst lst,
    RR sst lst ->
    let source_sem := source_denote_cmd pp c sst in
    let lin_sem := linsem_rec_cmd (lc_end sp) c lst in
    @rutt E1 E2 _ _ (fun _ _ _ _ => True) (fun _ _ _ _ _ _ => True) 
        (fun _ s => halt_pred (PC s)) source_sem lin_sem. 
Proof.
Admitted.

Lemma LinearSem_fun_correct (pd : PointerData) (sp: sprog) 
  (lin_params: linearization_params)  :
  check_prog lin_params sp = ok tt ->
  sp_is_ok sp lin_params ->
  forall fn sst lst,
    FRR sst lst ->
    let source_sem := source_denote_fun pp fn sst in
    let lin_sem := linsem_rec_fun (lc_end sp) fn lst in
    @rutt E1 E2 _ _ (fun _ _ _ _ => True) (fun _ _ _ _ _ _ => True) 
        (fun _ s => halt_pred (PC s)) source_sem lin_sem. 
Proof.
  intros.
  eapply interp_mrec_rutt with (RPreInv := RecPreC) (RPostInv := RecPostC);
    simpl; intros;
    set RPreX := (HeterogeneousRelations.sum_prerel _ _);
    set RPpstX := (HeterogeneousRelations.sum_postrel _ _).
  { destruct d1 as [[fn1 fs]].
    destruct d2 as [[fn2 st]]; simpl.
    unfold isem_fcall, lsem_fun; simpl.
    admit.
  }
  { unfold isem_fcall, linsem_fun, lsem_fun; simpl.
    admit.
  }  
Admitted.

End Transl.

End LinearWithRec.
  
End LSemSpec.

End StateRecSem.

End IterativeSem.

End Asm1.
       

