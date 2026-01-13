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

Require Import it_cflow_sem it_effect_sem equiv_extras rutt_extras.

Import Memory.
Require oseq.
Require Import Relations.
Require Import List.

Import ListNotations. 
Import MonadNotation.
Local Open Scope monad_scope.

Section Asm1.  
(* Context
  `{asmop: asmOp}.  *)
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
Notation FEnv := (funname -> option lcmd). 
Context (fenv: FEnv).

(* point in the linear code of a function *)
Definition lcpoint : Type := (funname * nat)%type.

(* just the stack *)
Definition alstate := list lcpoint.

Definition lcpoint2remote (l: lcpoint) : remote_label :=
  match l with (fn, n) => (fn, Pos.of_nat n) end. 

Definition remote2lcpoint (l: remote_label) : lcpoint :=
  match l with (fn, l) => (fn, Pos.to_nat l) end. 
    
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

(* the iterator used in the 'direct' linear semantics. X is the
   halting condition *)
Definition LCntr {E} {XE: ErrEvent -< E}  
  (F: linstr_r -> lcpoint -> itree E lcpoint)
  (X: lcmd -> nat -> bool)
  (fpt: lcpoint) : itree E (lcpoint + lcpoint) :=
  match fpt with 
  | (fn, pt) =>  
  (* the optional function body *)
    match (fenv fn) with
    (* the function exists: find the instruction in its body *)
    | Some lc => 
      match (find_linstr_in_env lc pt) with
      (* the instruction exists: execute it and return the next label *) 
      | Some (MkLI _ i) => fpt1 <- F i fpt ;; Ret (inl fpt1)
      (* the instruction does not exists: the execution terminates if the
         label equals the code length, otherwise throws an error *)        
      | _ => if X lc pt then Ret (inr fpt) else throw err end
    (* the function does not exist: throw an error *)    
    | _ => throw err end
  end.    

Definition halt_pred (l: lcpoint) : bool :=
  let fn := fst l in
  let lbl := snd l in
  let plc := fenv fn in
  match plc with
  | Some lc => if is_final lc lbl then true else false 
  | _ => false
  end.             

(********************************************************************)

(* the iterator used in the linear projection semantics of the source
   code. nS and nE are the start and end points of the linear code
   interval that contextualize the execution. l1 is the executed
   linear code point. *)
Definition XCntrK {E} {XE: ErrEvent -< E}  
  (F: linstr_r -> lcpoint -> itree E lcpoint)
  (fn: funname) (nS nE: nat) (l1: lcpoint) : itree E (lcpoint + lcpoint) :=
  match l1 with
  | (fn1, n1) =>
  (* the optional function body *)
    match fenv fn1 with
    | None => throw err      
    (* the function exists: find the instruction in its body *)
    | Some lc =>
      if (length lc < nE) then throw err else
      if (fn == fn1) && (nS <= n1) && (n1 < nE)
      (* the instruction exists in the segment: execute it and
         return the next label *) 
      then match find_linstr_in_env lc n1 with
           | Some (MkLI _ i) => l2 <- F i l1 ;; Ret (inl l2)
           (* n1 < nE and nE <= length lc, so this cannot happen *) 
           | _ => throw err                                         
           end
      (* the instruction is not in the function code segment *)         
      else Ret (inr l1)
    end
  end.        

(* iterate XContrK *)
Definition ICntrK {E} {XE: ErrEvent -< E}  
  (F: linstr_r -> lcpoint -> itree E lcpoint)
  (fn: funname) (nS nE: nat) (l0: lcpoint) : itree E lcpoint :=
  ITree.iter (@XCntrK E XE F fn nS nE) l0.
                 
(**************************************************************)

Section LinearSem.
  
Context {E} {XF : LFlowE -< E} {XI : LinstrE -< E} {XE: ErrEvent -< E}. 

(* one-step semantics of instructions *)
Definition exec_linstr (ir : linstr_r) (l: lcpoint) :
  itree E lcpoint :=
  match ir with
  | Lopn xs o es => trigger (ELopn xs o es) ;; trigger (LFopn xs o es l)

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
Definition isem_lcmd_body (lbl: lcpoint) :
  itree E (lcpoint + lcpoint) := LCntr exec_linstr is_final lbl.

(* iterative semantics of a program, from any starting point *)
Definition isem_lcmd (lbl: lcpoint) : itree E lcpoint :=
  ITree.iter isem_lcmd_body lbl.

(* iterative semantics of a function from its entry point *)
Definition isem_lfun (fn: funname) : itree E lcpoint :=
  isem_lcmd (fn, 0).

End LinearSem.


Section AStateLinSem.

Context
  {ep : EstateParams syscall_state}
  {spp : SemPexprParams}
  {ovm_i : one_varmap_info}
  (P : lprog).

#[local] Existing Instance withsubword.
Local Open Scope seq_scope.
Notation labels := label_in_lprog.

Variant LinE : Type -> Type :=
  | MatchLabel (lbl: lcpoint) : LinE unit
  | MatchStack : LinE unit 
  | EvalLoc (e: rexpr) : LinE remote_label
  | EvalExp (e: fexpr) : LinE bool
  | FindLabel (lbl: remote_label) : LinE lcpoint
  | FindLocalLabel (fn: funname) (lbl: label) : LinE lcpoint. 

Variant StackE : Type -> Type :=
  | Push (l: lcpoint) : StackE unit
  | Pop : StackE lcpoint. 


Section HandleLFlow.
  
Context {E: Type -> Type} {XL: LinE -< E} {XST: StackE -< E}
    {XE: ErrEvent -< E}. 

(* important one *)
Definition handle_LFlow {T} (e: LFlowE T) : itree E T :=
  match e with 
  | LFopn xs o es l0 => Ret (incr_label l0)
  | LFsyscall o l0 => Ret (incr_label l0)
  | LFcall o d l0 => trigger (Push (incr_label l0)) ;;
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

End HandleLFlow.


Section HandleStack.

Context {E: Type -> Type} {XA: @stateE alstate -< E} {XE: ErrEvent -< E}.

Definition handle_StackE {T} (e: StackE T) : itree E T :=
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
        {XS: @stateE lstate -< E} {XE: ErrEvent -< E}.

(* TODO: incomplete, add missing constructors *)
Definition handle_LinE {XE: ErrEvent -< E} {T} (e: LinE T) :
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

Context {E: Type -> Type} 
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

Definition handle_LinstrE {XL: LinE -< E} {T}
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

Context {stackAgree : lstate -> alstate -> bool}.

(* only cosmetics *)
Definition interp_LinstrE E {XE: ErrEvent -< E}
  {XL: LinE -< E} {XLS: stateE lstate -< E}
  {XST: StackE -< E} {A: Type}
  (t : itree (LinstrE +' E) A) : itree E A :=
  interp (ext_handler (fun T x => @handle_LinstrE E XLS XE XL T x)) t.

(* only cosmetics *)
Definition interp_LFlowE E {XL: LinE -< E} {XST: StackE -< E} {A: Type}
  (t : itree (LFlowE +' E) A) : itree E A :=
  interp (ext_handler (fun T x => @handle_LFlow E XL XST T x)) t.

(* stack events (alstate-based) *)
Definition interp_StackE E {XE: ErrEvent -< E}
  {XL: LinE -< E} {XLS: stateE alstate -< E} {A: Type}
  (t : itree (StackE +' E) A) : itree E A :=
  interp (ext_handler (fun T x => @handle_StackE E XLS XE T x)) t.

(* lstate-based events *)
Definition interp_LinE E {XE: ErrEvent -< E}
  {XLS: stateE alstate -< E}
  {XS: stateE lstate -< E} {A: Type}
  (t : itree (LinE +' E) A) : itree E A :=
  interp (ext_handler
            (fun T x => @handle_LinE stackAgree E XLS XS XE T x)) t.

Definition interp_up2lstate E {XE: ErrEvent -< E}
  {XLS: stateE alstate -< E}
  {XS: stateE lstate -< E} {A: Type}
  (t : itree (LinstrE +' LFlowE +' StackE +' LinE +' E) A) : itree E A :=
  interp_LinE (interp_StackE (interp_LFlowE (interp_LinstrE t))).

Definition interp_up2lstateL E {XE: ErrEvent -< E}
  {XLS: stateE alstate -< E}
  {XS: stateE lstate -< E} {A: Type}
  (t : itree (LinstrE +' StackE +' LinE +' E) A) : itree E A :=
  interp_LinE (interp_StackE (interp_LinstrE t)).

Definition alstate2lstate E {XS: stateE lstate -< E} T
  (t: itree (stateE alstate +' E) T) : itree E T.
Admitted. 

Definition interp_up2lstate_lin E {XE: ErrEvent -< E}
  {XS: stateE lstate -< E} {A: Type}
  (t : itree (LinstrE +' LFlowE +' StackE +' LinE +' stateE alstate +' E) A) :
  itree E A := alstate2lstate (interp_up2lstate t).

Definition interp_up2lstateL_lin E {XE: ErrEvent -< E}
  {XS: stateE lstate -< E} {A: Type}
  (t : itree (LinstrE +' StackE +' LinE +' stateE alstate +' E) A) :
  itree E A := alstate2lstate (interp_up2lstateL t).


(* if the linear translation of i is straightline code that ends
   without jumps, it will return (fn, n1); the first jump destination
   otherwise *)
Definition isem_XCntrK E {XE: ErrEvent -< E} {XI : LinstrE -< E}
  {XL: LinE -< E} {XLS: stateE lstate -< E} {XST: StackE -< E}
  (fn: funname) (n0 n1: nat) : itree E (lcpoint + lcpoint) :=
  XCntrK (fun i l => interp_LFlowE (exec_linstr i l)) fn n0 n1 (fn, n0).

(* iterate isem_XCntrK *)
Definition isem_ICntrK E {XE: ErrEvent -< E} {XI : LinstrE -< E}
  {XL: LinE -< E} {XLS: stateE lstate -< E} {XST: StackE -< E}
  (fn: funname) (n0 n1: nat) : itree E lcpoint :=
  ICntrK (fun i l => interp_LFlowE (exec_linstr i l)) fn n0 n1 (fn, n0).

(************************************************************)

Section LinearProjSem.

Context
(*  {asm_op : Type} {pd : PointerData} *)
(* {asmop : asmOp asm_op} *) 
  (liparams : @linearization_params asm_op (@_asmop asm_op syscall_state sip)).
Context (SP : sprog).

(* used to 'localize' cc, by computing the linear code interval
   associated to the translation of cc *)
Definition localize_cmd (loc_instr : instr -> lcpoint -> nat)
  (fn0: funname) (cc: cmd) (n0: nat) : nat :=
  linear_end_c (fun fn i n => loc_instr i (fn, n)) fn0 cc n0. 

(* maps a point to a left (continue) or right (exit) return value,
   depending on whether it satisfies P *)
Definition lcp_ret_select E (P: lcpoint -> bool) (l0: lcpoint) :
  itree E (lcpoint + lcpoint) :=
  if P l0 then Ret (inl l0) else Ret (inr l0).

(* the program point is in the interval *)
Definition lcp_in_interval (fn: funname) (nS nE: nat) (l1: lcpoint) : bool :=
  match l1 with
  | (fn0, n0) => (fn == fn0) && (nS <= n0) && (n0 < nE) end. 
  
(* sequentialize the application of lsem_instr within a function. used
   to map lsem_instr to commands *)
Fixpoint lsem_c E {XE: ErrEvent -< E}  
  (R: instr -> lcpoint -> itree E lcpoint)
  (fn: funname) (cc: cmd) (n: nat) : itree E lcpoint :=
  match cc with
  | nil => Ret (fn, n)
  | i :: cc0 => '(fn1, n1) <- R i (fn, n) ;;
                if fn == fn1 then lsem_c R fn cc0 n1 else throw err end.

(* basically, the sequential alternative to ICntrK, relying on cc *)
Fixpoint lsem_cX E {XE: ErrEvent -< E}            
  (R: instr -> lcpoint -> itree E lcpoint)
  (fn: funname) (nS nE: nat)
  (cc: cmd) (l0: lcpoint) : itree E lcpoint :=
  if lcp_in_interval fn nS nE l0
  then match cc with
       | nil => Ret l0
       | i :: cc0 => l2 <- R i l0 ;;
                     lsem_cX R fn nS nE cc0 l2 end
  else throw err.

Definition lsem_c_seq E {XE: ErrEvent -< E}
  (loc_instr : instr -> lcpoint -> nat)               
  (R: instr -> lcpoint -> itree E lcpoint)
  (cc: cmd) (l0 l1: lcpoint) : itree E lcpoint :=
  match l0 with
  | (fn0, nS) =>
    let nE := localize_cmd loc_instr fn0 cc nS in
    lsem_cX R fn0 nS nE cc l1 end.

(* basically, switches between different ktrees, depending on an
   ordered list of intervals. ls are the (well-ordered) interval
   end-points; ks are the ktrees *)
Fixpoint nat_kt_switch {E} {T} (f: nat -> T)
  (ls: list nat) (ks: list (nat -> itree E T)) (n: nat) : itree E T :=
  match (ls, ks) with
  | (nil, _) => Ret (f n)
  | (_, nil) => Ret (f n)                
  | (n0 :: ns0, k0 :: ks0) =>
    if n < n0 then k0 n0 else nat_kt_switch f ns0 ks0 n end.            

(* applies nat_kt_switch to produce an iterative body out of a list of
   alternatives; the exit point is determined by the interval (nS, nE)
   in the linear code of fn *)
Definition ktree_switch E {XE: ErrEvent -< E}  
  (R: instr -> lcpoint -> itree E lcpoint)
  (fn: funname) (nS nE: nat)
  (ls: list nat) (ks: list (nat -> itree E lcpoint))
  (l0: lcpoint) : itree E (lcpoint + lcpoint) :=
  let InInterval := lcp_in_interval fn nS nE in
  let RetS := lcp_ret_select E InInterval in
  let RSLift := fun f n => ITree.bind (f n) RetS in 
  if InInterval l0 
  then @nat_kt_switch E (lcpoint + lcpoint)
          (fun n => (inr (fn, n))) ls (map RSLift ks) (snd l0)
  else Ret (inr l0).         
      
(* crucially, by assuming fenv gives the linear code *)
Fixpoint lsem_instr E {XE: ErrEvent -< E} {XI : LinstrE -< E}
  {XL: LinE -< E} {XLS: stateE lstate -< E} {XST: StackE -< E}
  (loc_instr : instr -> lcpoint -> nat)
  (i : instr) (l1: lcpoint) :
          itree (callE (lcpoint * funname) lcpoint +' E) lcpoint := 
  let: (MkI ii ir) := i in
  let: (fn, n0) := l1 in
  let: nE := loc_instr i l1 in
  let K1 := fun n => isem_ICntrK fn n (S n) in
  let LocC := fun c nA => localize_cmd loc_instr fn c nA in
  let LRec := fun c nA =>
                 @lsem_c (callE (lcpoint * funname) lcpoint +' E) _
                   (lsem_instr loc_instr) fn c nA in
  match ir with
  | Cassgn x tg ty e => throw err

  | Copn xs tg o es => isem_ICntrK fn n0 nE                 

  | Csyscall xs o es => isem_ICntrK fn n0 nE    

  | Cif e c1 c2 =>
      let Kc1 := LRec c1 in 
      let Kc2 := LRec c2 in 
      let k1_n := LocC c1 in
      let k2_n := LocC c2 in
      let n1 := S n0 in
      let n2 := k2_n n1 in
      let n3 := S n2 in
      let n4 := S n3 in
      let n5 := k1_n n4 in
      let n6 := S n5 in
      ITree.iter (@ktree_switch (callE (lcpoint * funname) lcpoint +' E) _
        (lsem_instr loc_instr) fn n0 nE
        [n1; n2; n3; n4; n5; n6] [K1; Kc2; K1; K1; Kc1; K1]) (fn, n0) 
      
  | Cwhile a c1 e ii0 c2 =>
      let Kc1 := LRec c1 in 
      let Kc2 := LRec c2 in 
      let k1_n := LocC c1 in
      let k2_n := LocC c2 in
      let n1 := S n0 in
      let n2 := S n1 in
      let n3 := k2_n n2 in
      let n4 := S n3 in
      let n5 := S n4 in
      let n6 := k1_n n5 in
      let n7 := S n6 in
      ITree.iter (@ktree_switch (callE (lcpoint * funname) lcpoint +' E) _
        (lsem_instr loc_instr) fn n0 nE
        [n1; n2; n3; n4; n5; n6; n7] [K1; K1; Kc2; K1; K1; Kc1; K1]) (fn, n0) 

  | Cfor i (d, lo, hi) c => throw err 

  | Ccall xs fn1 args => trigger_inl1 (Call (l1, fn1))
                                  
 end.

Fixpoint lsem_cmd E {XE: ErrEvent -< E} {XI : LinstrE -< E}
  {XL: LinE -< E} {XLS: stateE lstate -< E} {XST: StackE -< E}
  (loc_instr : instr -> lcpoint -> nat)
  (cc : cmd) (l0 l1: lcpoint) :
     itree (callE (lcpoint * funname) lcpoint +' E) lcpoint := 
  @lsem_c_seq (callE (lcpoint * funname) lcpoint +' E) _
              loc_instr (lsem_instr loc_instr) cc l0 l1.
  
Definition lsem_instrI E {XE: ErrEvent -< E} {XI : LinstrE -< E}
  {XL: LinE -< E} {XLS: stateE lstate -< E} {XST: StackE -< E}
  (i : instr) (l1: lcpoint) :
          itree (callE (lcpoint * funname) lcpoint +' E) lcpoint := 
  lsem_instr (fun i '(fn, n) => linear_end_i SP fn i n) i l1.

Definition lsem_cmdI E {XE: ErrEvent -< E} {XI : LinstrE -< E}
  {XL: LinE -< E} {XLS: stateE lstate -< E} {XST: StackE -< E}
  (cc : cmd) (l0 l1: lcpoint) :
     itree (callE (lcpoint * funname) lcpoint +' E) lcpoint :=
  lsem_cmd (fun i '(fn, n) => linear_end_i SP fn i n) cc l0 l1.

Variant StackAllocE {FD0: Type} {FS0: Type} : Type -> Type :=
  | Before : lcpoint -> StackAllocE unit
  | After : StackAllocE lcpoint
  | LGetFunDef (fn: funname) : StackAllocE FD0
  | LGetFunCode (fd: FD0) : StackAllocE cmd.

Definition handle_StackAlloc E
  {XE: ErrEvent -< E} {XST: StackE -< E} {FD0: Type} {FS0: Type} {T}
  (e: @StackAllocE FD0 FS0 T) : itree E T. 
Admitted. 

Definition interp_StackAlloc E {XE: ErrEvent -< E} {XST: StackE -< E}
  {FD0: Type} {FS0: Type} {T}
  (t: itree (StackAllocE +' E) T) : itree E T :=
  interp (ext_handler (fun T x => @handle_StackAlloc E XE XST FD0 FS0 T x)) t.

(* l1 is the return address *)
Definition lsem_fun E {XE: ErrEvent -< E} {XI : LinstrE -< E}
  {XL: LinE -< E} {XLS: stateE lstate -< E} {XST: StackE -< E}
  {FD0: Type} {FS0: Type}
  {XTSA: @StackAllocE FD0 FS0 -< E}
  (loc_instr : instr -> lcpoint -> nat)
  (l1: lcpoint) (fn: funname) : 
  itree (callE (lcpoint * funname) lcpoint +' E) lcpoint :=
  trigger (Before l1) ;; 
  fd <- trigger (LGetFunDef fn) ;;  
  cc <- trigger (LGetFunCode fd) ;;
  lsem_cmd loc_instr cc (fn, 0) (fn, 0) ;;
  trigger After. 

Definition handle_LRec E {XE: ErrEvent -< E} {XI : LinstrE -< E}
  {XL: LinE -< E} {XLS: stateE lstate -< E} {XST: StackE -< E}
  {FD0: Type} {FS0: Type}
  {XTSA: @StackAllocE FD0 FS0 -< E}
  (loc_instr : instr -> lcpoint -> nat) :
  callE (lcpoint * funname) lcpoint ~>
    itree (callE (lcpoint * funname) lcpoint +' E) :=
 fun T (rc : callE _ _ T) =>
   match rc with
   | Call (l1, fn) => lsem_fun loc_instr l1 fn
   end.
  
Definition interp_LRec E {XE: ErrEvent -< E} {XI : LinstrE -< E}
  {XL: LinE -< E} {XLS: stateE lstate -< E} {XST: StackE -< E}
  {FD0: Type} {FS0: Type}
  {XTSA: @StackAllocE FD0 FS0 -< E}
  (loc_instr : instr -> lcpoint -> nat)
  T (t: itree (callE (lcpoint * funname) lcpoint +' E) T) : itree E T :=
  interp_mrec (handle_LRec loc_instr) t.

Lemma LinearSemProj_fun_ok E {XE: ErrEvent -< E} {XI : LinstrE -< E}
  {XL: LinE -< E} {XLS: stateE lstate -< E} {XST: StackE -< E}
  {FD0: Type} {FS0: Type}
  {XTSA: @StackAllocE FD0 FS0 -< E} 
  (loc_instr : instr -> lcpoint -> nat)
  (l0: lcpoint) (c: cmd) :
  eutt eq
       (interp_mrec (@handle_LRec E XE XI XL XLS XST FD0 FS0
                          XTSA loc_instr) (lsem_cmdI c l0 l0))
          (interp_LFlowE (isem_lcmd l0)). 
Admitted. 

Definition interp_LRec1 E {XE: ErrEvent -< E} {XI : LinstrE -< E}
  {XL: LinE -< E} {XLS: stateE lstate -< E} {XST: StackE -< E}
  {FD0: Type} {FS0: Type}
  (loc_instr : instr -> lcpoint -> nat)
  T (t: itree (callE (lcpoint * funname) lcpoint +'
                       @StackAllocE FD0 FS0 +' E) T) :
  itree E T :=
  interp_StackAlloc (interp_mrec (handle_LRec loc_instr) t).

Lemma LinearSemProj_fun_ok1 E {XE: ErrEvent -< E} {XI : LinstrE -< E}
  {XL: LinE -< E} {XLS: stateE lstate -< E} {XST: StackE -< E}
  {FD0: Type} {FS0: Type}
  (loc_instr : instr -> lcpoint -> nat)
  (l0: lcpoint) (c: cmd) :
  eutt eq ((@interp_LRec1 E XE XI XL XLS XST 
                      FD0 FS0 loc_instr) _ (lsem_cmdI c l0 l0))
          (interp_LFlowE (isem_lcmd l0)). 
Admitted. 


From ITree Require Import Rutt.

Section Transl.

Notation StE1 := (stateE estate).
Notation StE2 := (stateE lstate).

Context {E1} {XS1: StE1 -< E1} {XE1: ErrEvent -< E1}.
Context {E2} {XS2: StE2 -< E2} {XE2: ErrEvent -< E2}. 
Context (RR : estate -> lstate -> Prop).

Context {dc: DirectCall} {pT : progT} {scP : semCallParams}.
Context {p: prog} {ev : extra_val_t}.

Definition conv_obj T1 T2 (ee: T1 = T2) (u: T1) : T2 :=
  eq_rect T1 (fun T : Type => T) u T2 ee.

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

Definition lc_end := fun i '(fn, n) => linear_end_i SP fn i n.

Lemma linearization_proj_lemma (pd : PointerData) (sp: sprog)
  (lin_params: linearization_params) (FD0 FS0: Type) :
  check_prog lin_params sp = ok tt ->
  (forall (fn: funname) (fd: sfundef),
      get_fundef (p_funcs sp) fn = Some fd ->
      let c0 := fd.(f_body) in     
      let: (_, lc0) :=
        (linear_c (@linear_i asm_op pd _ lin_params sp fn) c0 xH [::]) in
      fenv fn = Some lc0) -> 
  forall (fn: funname),
    let lin_sem := @interp_up2lstateL_lin E2 XE2 XS2 _ 
      (@interp_StackAlloc _ _ _ FD0 FS0 _ (interp_mrec (handle_LRec lc_end) 
                 (lsem_fun lc_end (fn,0) fn))) in 
    forall xs es ii,
      let sden := @isem_instr asm_op syscall_state sip
                    estate fstate _ _ _ (MkI ii (Ccall xs fn es)) in
      let source_sem := @interp_up2state asm_op syscall_state
                          sip withsubword dc ep spp pT scP p ev E1 XE1 XS1
                          unit sden in  
      @rutt E1 E2 _ _ PreC PostC (fun n _ => True) source_sem lin_sem.
Admitted. 

(* to be proved using linearization_proj_lemma and
   LinearSemProj_fun_ok1 *)
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
    let lin_sem := @interp_up2lstate_lin E2 XE2 XS2 _ 
                     (isem_lfun fn) in 
    forall xs es ii,
      let sden := @isem_instr asm_op syscall_state sip
                    estate fstate _ _ _ (MkI ii (Ccall xs fn es)) in
      let source_sem := @interp_up2state asm_op syscall_state
                          sip withsubword dc ep spp pT scP p ev E1 XE1 XS1
                          unit sden in  
      @rutt E1 E2 _ _ PreC PostC (fun n _ => True) source_sem lin_sem. 
Admitted. 

End Transl.
  
End LinearProjSem.

End Interp.

End AStateLinSem.

End Asm1.
       
