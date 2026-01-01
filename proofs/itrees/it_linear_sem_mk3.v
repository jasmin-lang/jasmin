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

Import Memory.
Require oseq.
Require Import Relations.
Require Import List.

Import MonadNotation.
Local Open Scope monad_scope.

Section Asm1.  
(* Context
  `{asmop: asmOp}.  *)
Context  {asm_op: Type}
         {syscall_state : Type}
         {sip : SemInstrParams asm_op syscall_state}.  
Context {err: error_data}. 
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
(* Memo *)
(* | _ => throw err end. *) 

(* instruction events. InitFState allows storing instr_info in FState
 *)

Notation FEnv := (funname -> option lcmd). 
Context (fenv: FEnv).

Definition rlabel : Type := (funname * nat)%type.

Definition alstate := list rlabel.

Definition rlabel2remote (l: rlabel) : remote_label :=
  match l with (fn, n) => (fn, Pos.of_nat n) end. 

Definition remote2rlabel (l: remote_label) : rlabel :=
  match l with (fn, l) => (fn, Pos.to_nat l) end. 

(*
Variant LinstrE : Type -> Type :=
  | ELopn        : lexprs -> sopn -> rexprs -> LinstrE unit
  | ELsyscall    : syscall_t -> LinstrE unit
  | ELcall       : option var_i -> remote_label -> LinstrE unit
  | ELret        : LinstrE unit
  | ELalign      : LinstrE unit
  | ELlabel      : label_kind -> label -> LinstrE unit
  | ELgoto       : remote_label -> LinstrE unit
  | ELigoto      : rexpr -> LinstrE unit
  | ELstoreLabel : var -> label -> LinstrE unit
  | ELcond       : fexpr -> label -> LinstrE unit.
*)
    
Variant LinstrE : Type -> Type :=
  | ELopn        : lexprs -> sopn -> rexprs -> LinstrE unit
  | ELsyscall    : syscall_t -> LinstrE unit
  | ELcall       : option var_i -> remote_label -> LinstrE unit
  | ELret        : LinstrE unit
  | ELalign      : LinstrE unit
  | ELlabel      : label_kind -> label -> LinstrE unit
  | ELgoto       : remote_label -> LinstrE unit
  | ELigoto      : rexpr -> LinstrE unit
  | ELstoreLabel : var -> label -> LinstrE unit
  | ELcond       : fexpr -> label -> LinstrE unit.

Variant LFlowE : Type -> Type :=
  | LFopn        : lexprs -> sopn -> rexprs -> rlabel ->
                   LFlowE rlabel
  | LFsyscall    : syscall_t ->
                   rlabel -> LFlowE rlabel 
  | LFcall       : option var_i -> remote_label -> rlabel ->
                   LFlowE rlabel
  | LFret        : rlabel -> LFlowE rlabel
  | LFalign      : rlabel -> LFlowE rlabel
  | LFlabel      : label_kind -> label -> rlabel ->
                   LFlowE rlabel 
  | LFgoto       : remote_label -> rlabel -> LFlowE rlabel
  | LFigoto      : rexpr -> rlabel -> LFlowE rlabel
  | LFstoreLabel : var -> label -> rlabel -> LFlowE rlabel
  | LFcond       : fexpr -> label -> rlabel -> LFlowE rlabel.

Definition find_linstr_in_env (lc: lcmd) (lbl: nat) : option linstr :=
  oseq.onth lc lbl.

Definition is_final (lc: lcmd) (lbl: nat) : bool :=
  lbl =? (length lc).

Definition incr_label (l: rlabel) : rlabel :=
  match l with (fn, lbl) => (fn, S lbl) end.

Definition LCntr {E} {XE: ErrEvent -< E}  
  (F: linstr_r -> rlabel -> itree E rlabel)
  (X: lcmd -> nat -> bool)
  (rlbl: rlabel) : itree E (rlabel + rlabel) :=
  let fn := fst rlbl in
  let lbl := snd rlbl in 
  (* the optional function body *)
  let plc := fenv fn in
  match plc with
  (* the function exists: find the instruction in its body *)
  | Some lc => let pi := find_linstr_in_env lc lbl in
    match pi with
    (* the instruction exists: execute it and return the next label *) 
    | Some (MkLI _ i) => rlbl1 <- F i rlbl ;; Ret (inl rlbl1)
    (* the instruction does not exists: the execution terminates if the
       label equals the code length, otherwise throws an error *)        
    | _ => if X lc lbl then Ret (inr rlbl) else throw err end
  (* the function does not exist: throw an error *)    
  | _ => throw err end.        


Section SemRec.
  
Context {E} {XF : LFlowE -< E} {XI : LinstrE -< E} {XE: ErrEvent -< E}. 

(* one-step semantics of instructions *)
Definition exec_linstr (ir : linstr_r) (l: rlabel) :
  itree E rlabel :=
  match ir with
  | Lopn xs o es => trigger (ELopn xs o es) ;; trigger  (LFopn xs o es l)

  | Lsyscall o => trigger (ELsyscall o) ;; trigger (LFsyscall o l)

  | Lcall or d => trigger (ELcall or d) ;; trigger (LFcall or d l)

  | Lret => trigger ELret ;; trigger (LFret l)

  | Lalign => trigger ELalign ;; trigger (LFalign l) 
      
  | Llabel x y => trigger (ELlabel x y) ;; trigger (LFlabel x y l)

  | Lgoto d => trigger (ELgoto d) ;; trigger (LFgoto d l)

  | Ligoto e => trigger (ELigoto e) ;; trigger (LFigoto e l)

  | LstoreLabel x lbl => trigger (ELstoreLabel x lbl) ;;
                         trigger (LFstoreLabel x lbl l)                      

  | Lcond e lbl => trigger (ELcond e lbl) ;; trigger (LFcond e lbl l)
  end.                         

(* iterative semantics body *)
Definition isem_linstr (lbl: rlabel) :
  itree E (rlabel + rlabel) := LCntr exec_linstr is_final lbl.

(* iterative semantics of a program, from any starting point *)
Definition isem_liniter (lbl: rlabel) : itree E rlabel :=
  ITree.iter isem_linstr lbl.

(* iterative semantics of a function from its entry point *)
Definition isem_fun (fn: funname) : itree E rlabel :=
  isem_liniter (fn, 0).

End SemRec.


Section GInterp.

Context
  {ep : EstateParams syscall_state}
  {spp : SemPexprParams}
  {ovm_i : one_varmap_info}
  (P : lprog).

#[local] Existing Instance withsubword.
Local Open Scope seq_scope.
Notation labels := label_in_lprog.

Variant LinE : Type -> Type :=
  | MatchLabel (lbl: rlabel) : LinE unit
  | MatchStack : LinE unit 
  | EvalLoc (e: rexpr) : LinE remote_label
  | EvalExp (e: fexpr) : LinE bool
  | FindLabel (lbl: remote_label) : LinE rlabel
  | FindLocalLabel (fn: funname) (lbl: label) : LinE rlabel. 
(*  | NewInstr (i: linstr_r) (l: rlabel) : LinE rlabel. *)
(*  | IsFinal (lbl: rlabel) : LinE bool.  *)                 

Variant StackE : Type -> Type :=
  | Push (l: rlabel) : StackE unit
  | Pop : StackE rlabel. 


Section HandleLFlow.
  
Context {E: Type -> Type} {XL: LinE -< E} {XST: StackE -< E} {XE: ErrEvent -< E}. 

(* in progress ... %%%%%%%%%%%%%%%% not needed *)
Definition linstr_rlabel (i : linstr_r) (l0: rlabel) :
  itree E rlabel :=
  match i with 
  | Lopn xs o es => Ret (incr_label l0)
  | Lsyscall o => Ret (incr_label l0)
  | Lcall o d => trigger (Push l0) ;;
                 l1 <- trigger (FindLabel d) ;;
                 Ret l1                          
  | Lret => l1 <- trigger Pop ;; Ret l1
  | Lalign => Ret (incr_label l0) 
  | Llabel x y => Ret (incr_label l0)
  | Lgoto d => l1 <- trigger (FindLabel d) ;;
               Ret l1
  | Ligoto e => d <- trigger (EvalLoc e) ;;
                l1 <- trigger (FindLabel d) ;;
                Ret l1
  | LstoreLabel x lbl => Ret (incr_label l0)                           
  | Lcond e lbl => b <- trigger (EvalExp e) ;;
                   if b then
                     l1 <- trigger (FindLocalLabel (fst l0) lbl) ;;
                     Ret l1
                   else Ret (incr_label l0)      
  end.

(* this is the one *)
Definition handle_LFlow {T} (e: LFlowE T) : itree E T :=
  match e with 
  | LFopn xs o es l0 => Ret (incr_label l0)
  | LFsyscall o l0 => Ret (incr_label l0)
  | LFcall o d l0 => trigger (Push l0) ;;
                     l1 <- trigger (FindLabel d) ;;
                     Ret l1                          
  | LFret l0 => l1 <- trigger Pop ;; Ret l1
  | LFalign l0 => Ret (incr_label l0) 
  | LFlabel x y l0 => Ret (incr_label l0)
  | LFgoto d l0 => l1 <- trigger (FindLabel d) ;;
                   Ret l1
  | LFigoto e l0 => d <- trigger (EvalLoc e) ;;
                    l1 <- trigger (FindLabel d) ;;
                    Ret l1
  | LFstoreLabel x lbl l0 => Ret (incr_label l0)                           
  | LFcond e lbl l0 => b <- trigger (EvalExp e) ;;
                       if b 
                       then l1 <- trigger (FindLocalLabel (fst l0) lbl) ;;
                            Ret l1
                       else Ret (incr_label l0)      
  end.
  
(* not needed *)
Definition LFlow_isem (i : linstr_r) (l0: rlabel) : itree E rlabel :=
  trigger (MatchLabel l0) ;;
  trigger MatchStack ;;
  l1 <- linstr_rlabel i l0 ;;
  trigger (MatchLabel l1) ;;
  trigger MatchStack ;;
  Ret l1.

(*
Definition handle_linstr {T} (e: LFlowE T) (l0: rlabel) : itree E T :=
  match e with
  | ELopn xs o es l0 => LFlow_isem (Lopn xs o es) l0
  | ELsyscall o l0 => LFlow_isem (Lsyscall o) l0
  | ELcall o d l0 => LFlow_isem (Lcall o d) l0
  | ELret l0 => LFlow_isem Lret l0
  | ELalign l0 => LFlow_isem Lalign l0
  | ELlabel x y l0 => LFlow_isem (Llabel x y) l0
  | ELgoto d l0 => LFlow_isem (Lgoto d) l0
  | ELigoto e l0 => LFlow_isem (Ligoto e) l0
  | ELstoreLabel x lbl l0 => LFlow_isem (LstoreLabel x lbl) l0
  | ELcond e lbl l0 => LFlow_isem (Lcond e lbl) l0
  end.
*)

End HandleLFlow.


Section HandleStack.

Context {E: Type -> Type} {XA: @stateE alstate -< E} {XE: ErrEvent -< E}.

Definition StackE_handle {T} (e: StackE T) : itree E T :=
  match e with    
  | Push l => stk <- trigger (@Get alstate) ;;
              trigger (@Put alstate (l :: stk))
  | Pop => stk <- trigger (@Get alstate) ;;
           match stk with
           | nil => throw err
           | l0 :: ls => trigger (@Put alstate ls) ;; Ret l0 end
  end.   

End HandleStack.


Section HandleLin.

Context {stackAgree : lstate -> alstate -> bool}.

Context {E: Type -> Type} {XA: @stateE alstate -< E}
        {XS: @stateE lstate -< E}  {XE: ErrEvent -< E}.

(* TODO: add missing constructors *)
Definition handle_lin {XE: ErrEvent -< E} {T} (e: LinE T) :
  itree E T := match e with
  | MatchLabel (fn, lbl)%type =>
      s <- trigger (@Get lstate) ;;
      if (fn == s.(lfn)) && (lbl == lpc s)
      then Ret tt else throw err
  | MatchStack =>
      s <- trigger (@Get lstate) ;;
      stk <- trigger (@Get alstate) ;;
      if (stackAgree s stk) then Ret tt else throw err         
  | _ => throw err end.

End HandleLin.


Section HandleState.

Context {E: Type -> Type} (* {XL: LinE -< E} *)
        {XS: @stateE lstate -< E} {XE: ErrEvent -< E}.
                                           
Definition lopn_sem (xs: seq.seq lexpr) (o: sopn) (es: seq.seq rexpr)
  (s1: lstate) : exec lstate :=
    let s := to_estate s1 in
    (Let args := sem_rexprs s es in
    Let res := exec_sopn o args in
    Let s' := write_lexprs xs res s in
    ok (lnext_pc (lset_estate' s1 s'))).

Definition lsyscall_sem (o: syscall_t)
  (s1: lstate) : exec lstate :=                        
  let sig := @syscall_sig ovm_i o in
    Let ves := get_vars true s1.(lvm) sig.(scs_vin) in
    Let: (scs, m, vs) :=
      exec_syscall (semCallParams := sCP_stack) s1.(lscs) s1.(lmem) o ves
    in
    let s :=
      {|
        escs := scs;
        emem := m;
        evm := vm_after_syscall s1.(lvm);
      |}
    in
    Let s' := write_lvals true [::] s (to_lvals sig.(scs_vout)) vs in
    ok (lnext_pc (lset_estate' s1 s')).

Definition lcall_sem (ov: option var_i) (d: remote_label)  
  (s1: lstate) : exec lstate :=                        
  match ov with
  | None =>   
    let vrsp := v_var (vid (lp_rsp P)) in
    Let sp := Result.bind to_pointer (get_var true s1.(lvm) vrsp) in
    let nsp := (sp - wrepr Uptr (wsize_size Uptr))%R in
    Let vm := set_var true s1.(lvm) vrsp (Vword nsp) in
    Let lbl := get_label_after_pc P s1 in
    Let p := rencode_label (labels P) (lfn s1, lbl) in
    Let m := write s1.(lmem) Aligned nsp p in
              eval_jump P d (lset_mem_vm s1 m vm)
  | Some r => Let lbl := get_label_after_pc P s1 in
    Let p := rencode_label (labels P) (lfn s1, lbl) in
    Let vm := set_var true s1.(lvm) r (Vword p) in
    eval_jump P d (lset_vm s1 vm)
  end.                    

Definition lret_sem (s1: lstate) : exec lstate :=
  let vrsp := v_var (vid (lp_rsp P)) in
  Let sp := Result.bind to_pointer (get_var true s1.(lvm) vrsp) in
  Let p  := read s1.(lmem) Aligned sp Uptr in
  Let d := rdecode_label (labels P) p in
  let nsp := (sp + wrepr Uptr (wsize_size Uptr))%R in
  Let vm := set_var true s1.(lvm) vrsp (Vword nsp) in
  eval_jump P d (lset_vm s1 vm).

Definition lalign_sem (s1: lstate) : exec lstate :=
  ok (lnext_pc s1).

Definition llabel_sem (k: label_kind) (lbl: label)
  (s1: lstate) : exec lstate :=  
  ok (lnext_pc s1).

Definition lgoto_sem (d: remote_label) 
  (s1: lstate) : exec lstate :=
  eval_jump P d s1.

Definition ligoto_sem (e: rexpr) 
  (s1: lstate) : exec lstate :=
  Let p := Result.bind to_pointer (sem_rexpr s1.(lmem) s1.(lvm) e) in
  Let d := rdecode_label (labels P) p in
  eval_jump P d s1.

Definition lstorelabel_sem (x: var) (lbl: label) 
  (s1: lstate) : exec lstate :=
  Let p := rencode_label (labels P) (lfn s1, lbl) in
  Let vm := set_var true s1.(lvm) x (Vword p) in
  ok (lnext_pc (lset_vm s1 vm)).

Definition lcond_sem (e: fexpr) (lbl: label)
  (s1: lstate) : exec lstate :=
  Let b := Result.bind to_bool (sem_fexpr s1.(lvm) e) in
  if b then
     eval_jump P (s1.(lfn),lbl) s1
  else ok (lnext_pc s1).

(* same as eval_instr *)
Definition linstr_isem (i : linstr_r) (s1: lstate) : exec lstate :=
  match i with 
  | Lopn xs o es => lopn_sem xs o es s1
  | Lsyscall o => lsyscall_sem o s1
  | Lcall o d => lcall_sem o d s1
  | Lret => lret_sem s1 
  | Lalign => lalign_sem s1
  | Llabel x y => llabel_sem x y s1
  | Lgoto d => lgoto_sem d s1
  | Ligoto e => ligoto_sem e s1
  | LstoreLabel x lbl => lstorelabel_sem x lbl s1
  | Lcond e lbl => lcond_sem e lbl s1
  end.

Definition Linstr_isem (i : linstr_r) : itree E unit :=
  s1 <- trigger (@Get lstate) ;;
  s2 <- iresult (linstr_isem i s1) s1 ;;
  trigger (@Put lstate s2).

Definition handle_linstr {XL: LinE -< E} {T}
  (e: LinstrE T) : itree E T :=
  match e with
  | ELopn xs o es => Linstr_isem (Lopn xs o es)
  | ELsyscall o => Linstr_isem (Lsyscall o)
  | ELcall o d => Linstr_isem (Lcall o d)
  | ELret => Linstr_isem Lret 
  | ELalign => Linstr_isem Lalign
  | ELlabel x y => Linstr_isem (Llabel x y)
  | ELgoto d => Linstr_isem (Lgoto d)
  | ELigoto e => Linstr_isem (Ligoto e)
  | ELstoreLabel x lbl => Linstr_isem (LstoreLabel x lbl)
  | ELcond e lbl => Linstr_isem (Lcond e lbl)
  end.


End HandleState.


Section Interp.

Context {E: Type -> Type} {XE: ErrEvent -< E}.

Context {stackAgree : lstate -> alstate -> bool}.

Definition interp_LinstrE {XL: LinE -< E} {XST: StackE -< E} {A: Type}
  (t : itree (LinstrE +' E) A) : rlabel -> itree E A :=
  fun l => interp (ext_handler (fun T x => @handle_linstr E XL XST _ x l)) t.

(* iterative semantics body *)
Definition isem_linstrD {XL: LinE -< E} {XST: StackE -< E} (lbl: rlabel) :
  itree E (rlabel + rlabel) :=
  LCntr (fun i l => interp_LinstrE (exec_linstr i l) l) is_final lbl.

(* iterative semantics of a program, from any starting point *)
Definition isem_liniterD {XL: LinE -< E} {XST: StackE -< E}
  (lbl: rlabel) : itree E rlabel :=
  ITree.iter isem_linstrD lbl.

Definition interp_LinE {XA: @stateE alstate -< E}
  {XS: @stateE lstate -< E} {A: Type} 
  (t : itree (LinE +' E) A) : itree E A :=
  interp (ext_handler (@handle_lin stackAgree E XA XS XE)) t.

(* two errors so far.

1) handle_linstr consumes LinstrE events, but this is wrong.  we need
Linstr_isem_with_state as in mk1.

2) actual labels are symbolic, they do not coincide with code position
(look at the linerization translation). This means that in
linstr_rlabel the treatment of eg Lgoto is not right. This also means
that the code is needed, not just the rlabel.

*)




Definition handle2lin (i: instr) (lbl: rlabel) : itree E (rlabel * rlabel) :=
  let: (MkI ii ir) := i in
  match ir with
  | Cassgn x tg ty e => throw err

  | Copn xs tg o es => trigger (OpnE xs tg o es)

  | Csyscall xs o es => trigger (SyscallE xs o es) 
                                
  | Cif e c1 c2 =>
    b <- trigger (EvalCond e) ;;
    isem_foldr isem_instr (if b then c1 else c2) 
               
  | Cwhile a c1 e ii0 c2 =>
      isem_while_loop isem_instr (fun e => trigger (EvalCond e))
        c1 e c2 

  | Cfor i (d, lo, hi) c =>
    zz <- trigger (EvalBounds lo hi) ;;  
    isem_for_loop isem_instr (fun w => trigger (WriteIndex i (Vint w)))
      i c (wrange d (fst zz) (snd zz)) 

  | Ccall xs fn args =>
    s0 <- trigger (@Get State) ;;  
    vargs <- trigger (EvalArgs args) ;;
    fs0 <- trigger (InitFState vargs ii) ;;
    fs1 <- trigger_inl1 (Call (fn, fs0)) ;; 
    (* discard current state, use s0 instead *)
    trigger (RetVal xs fs1 s0)
  end.



End Interp.


Section FInterp.

Context {E: Type -> Type} {XE: ErrEvent -< E} {XS: @stateE lstate -< E}
  {XA: @stateE alstate -< E} {XST: StackE -< E}.

Context {stackAgree : lstate -> alstate -> bool}.

(* still need to to interpret StackE *)
Definition interp_up2state_lin T 
  (t: itree (LinstrE +' LinE +' E) T) : rlabel -> itree E T :=
  fun l => @interp_LinE _ _ stackAgree _ _ _ (interp_LinstrE t l).

End FInterp.


Require Import linearization.
Require Import it_cflow_sem it_effect_sem.
From ITree Require Import State StateFacts MonadState Rutt.
Require Import equiv_extras rutt_extras.


Definition conv_obj T1 T2 (ee: T1 = T2) (u: T1) : T2 :=
  eq_rect T1 (fun T : Type => T) u T2 ee.


Section Transl0.

Fixpoint linear_it (i: instr) (lbl: rlabel) : 
   

End transl0.
  

Section Transl.

Notation StE1 := (stateE estate).
Notation StE2 := (stateE lstate).

Context {E1} {XS1: StE1 -< E1} {XE1: ErrEvent -< E1}.
Context {E2} {XS2: StE2 -< E2} {XE2: ErrEvent -< E2}. 
Context (RR : estate -> lstate -> Prop).

Context {dc: DirectCall} {pT : progT} {scP : semCallParams}.
Context {p: prog} {ev : extra_val_t}.

Definition ConvRelate T1 T2 (u1: T1) (u2: T2) :=
  exists (ee1: T1 = estate) (ee2: T2 = lstate),
    RR (conv_obj ee1 u1) (conv_obj ee2 u2).

Definition StatePreRel T1 T2 
  (e1: @stateE estate T1) (e2: @stateE lstate T2) : Prop :=
   match (e1, e2) with
   | (Get, Get) => True
   | (Put s1, Put s2) => RR s1 s2
   | _ => False end. 

Definition StatePostRel T1 T2 
  (e1: @stateE estate T1) (u1: T1) (e2: @stateE lstate T2) (u2: T2) : Prop :=
  StatePreRel e1 e2 /\
   match (e1, e2) with
   | (Get, Get) => ConvRelate u1 u2
   | (Put s1, Put s2) => True
   | _ => False end. 

Definition PreC T1 T2 (e1: E1 T1) (e2: E2 T2) : Prop :=
  exists (e01: @stateE estate T1) (e02: @stateE lstate T2),
    e1 = (subevent _ e01) /\ e2 = (subevent _ e02) /\
    StatePreRel e01 e02.  

Definition PostC T1 T2 (e1: E1 T1) (u1: T1) (e2: E2 T2) (u2: T2) : Prop :=
  exists (e01: @stateE estate T1) (e02: @stateE lstate T2),
    e1 = (subevent _ e01) /\ e2 = (subevent _ e02) /\
    StatePreRel e01 e02 /\ StatePostRel e01 u1 e02 u2. 

Lemma linearization_lemma (pd : PointerData) (sp: sprog)
  (lin_params: linearization_params) :
  check_prog lin_params sp = ok tt ->
  (forall (fn: funname) (fd: sfundef),
      get_fundef (p_funcs sp) fn = Some fd ->
      let c0 := fd.(f_body) in     
      let: (_, lc0) :=
        (linear_c (@linear_i asm_op pd _ lin_params sp fn) c0 xH [::]) in
      fenv fn = Some lc0) ->
  forall (fn: funname),
    let lin_sem := @interp_up2state_lin E2 XE2 XS2 _
                     (isem_liniter (fn, 0)%type) in
    forall xs es ii,
      let sden := @isem_instr asm_op syscall_state sip
                    estate fstate _ _ _ (MkI ii (Ccall xs fn es)) in
      let source_sem := @interp_up2state asm_op syscall_state
                          sip withsubword dc ep spp pT scP p ev E1 XE1 XS1
                          unit sden in  
      @rutt E1 E2 _ _ PreC PostC eq source_sem lin_sem.
Proof.
  intros.  
Admitted. 

End Transl.


Section Test1.

Context {State: Type} {FState : Type} {FunDef: Type}.
Context {LState: Type}.

Notation StE1 := (stateE State).
Notation StE2 := (stateE LState).

Context {E1} {XI1 : @InstrE asm_op syscall_state _ State FState -< E1}
  {XS1: StE1 -< E1} {XF1: @FunE asm_op syscall_state _ FState FunDef -< E1}.
 
Context {E2} {XI2 : LinstrE -< E2} {XL2: LinE -< E2} {XS2: StE2 -< E2}
  {XE2: ErrEvent -< E2}. 

Context (RR : State -> LState -> Prop).

(* just a test *)
Lemma lin_lemma1 (pd : PointerData) (sp: sprog)
  (lin_params: linearization_params) :
  check_prog lin_params sp = ok tt ->
  (forall (fn: funname) (fd: sfundef),
      get_fundef (p_funcs sp) fn = Some fd ->
      let c0 := fd.(f_body) in     
      let: (_, lc0) :=
        (linear_c (@linear_i asm_op pd _ lin_params sp fn) c0 xH [::]) in
      fenv fn = Some lc0) ->
  forall (fn: funname),
    let lin_sem := @isem_liniter E2 XI2 XL2 XE2 ((fn, xH)%type) in
    forall xs es ii, 
      let source_sem := @denote_instr _ _ _ _ _ _ E1 XI1 XS1 XF1
                          (MkI ii (Ccall xs fn es)) in
      @rutt E1 E2 _ _ (fun _ _ _ _ => True) (fun _ _ _ _ _ _ => True)
            eq source_sem lin_sem.
Proof.
  intros.  
Admitted. 


(* another test *)
Lemma lin_lemma2 (pd : PointerData) (sp: sprog)
  (lin_params: linearization_params) :
  check_prog lin_params sp = ok tt ->
  (forall (fn: funname) (fd: sfundef),
      get_fundef (p_funcs sp) fn = Some fd ->
      let c0 := fd.(f_body) in     
      let: (_, lc0) :=
        (linear_c (@linear_i asm_op pd _ lin_params sp fn) c0 xH [::]) in
      fenv fn = Some lc0) ->
  forall (fn: funname) (fd: sfundef),
  get_fundef (p_funcs sp) fn = Some fd ->
  let c0 := fd.(f_body) in     
  let lin_sem := @isem_liniter E2 XI2 XL2 XE2 ((fn, xH)%type) in
  let source_sem := @denote_cmd _ _ _ _ _ _ E1 XI1 XS1 XF1 c0 in
  @rutt E1 E2 _ _ (fun _ _ _ _ => True) (fun _ _ _ _ _ _ => True)
    eq source_sem lin_sem.
Proof.
  intros.  
Admitted. 
  
End Test1. 

End GInterp.

End Asm1.


(*
(* here we consider just one function *)
Lemma linearization_lemma (pd : PointerData) (sp: sprog)
  (lin_params: linearization_params)
  (fn: funname) (fd: sfundef) lbl :
  check_prog lin_params sp = ok tt ->
  get_fundef (p_funcs sp) fn = Some fd ->
  let c0 := fd.(f_body) in     
  let lc0 := (linear_c (@linear_i asm_op pd _ lin_params sp fn) c0 lbl [::]) in
  fenv fn = Some (snd lc0) ->
  let lin_sem := @isem_liniter E2 XI2 XL2 XE2 ((fn, lbl)%type) in
  let source_sem := @denote_cmd _ _ _ _ _ _ E1 XI1 XS1 XF1 c0 in
  @rutt E1 E2 _ _ (fun _ _ _ _ => True) (fun _ _ _ _ _ _ => True)
    eq source_sem lin_sem.
Proof.
  intros.  
Admitted. 
*)

(*
Lemma xxx (s1: lstate) : lret_sem s1 = ok s1.
  unfold lret_sem.
  unfold Result.bind.
  simpl.
  unfold get_var. simpl.
  set rrr := (lvm s1). simpl.
  unfold rdecode_label. simpl.
  Print decode_label.
*)  
