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
Definition isem_linstr (lbl: lcpoint) :
  itree E (lcpoint + lcpoint) := LCntr exec_linstr is_final lbl.

(* iterative semantics of a program, from any starting point *)
Definition isem_liniter (lbl: lcpoint) : itree E lcpoint :=
  ITree.iter isem_linstr lbl.

(* iterative semantics of a function from its entry point *)
Definition isem_fun (fn: funname) : itree E lcpoint :=
  isem_liniter (fn, 0).

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

Definition interp_up2state E {XE: ErrEvent -< E}
  {XLS: stateE alstate -< E}
  {XS: stateE lstate -< E} {A: Type}
  (t : itree (LinstrE +' LFlowE +' StackE +' LinE +' E) A) : itree E A :=
  interp_LinE (interp_StackE (interp_LFlowE (interp_LinstrE t))).

(* if the linear translation of i is straightline code, it should
   return (fn, n1), otherwise the first jump destination *)
Definition isem_XCntrK E {XE: ErrEvent -< E} {XI : LinstrE -< E}
  {XL: LinE -< E} {XLS: stateE lstate -< E} {XST: StackE -< E}
  (fn: funname) (n0 n1: nat) : itree E (lcpoint + lcpoint) :=
  XCntrK (fun i l => interp_LFlowE (exec_linstr i l)) fn n0 n1 (fn, n0).

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

(* used to 'locate' cc, ie compute the linear code interval associated
   to the translation of cc *)
Definition loc_cmd (loc_instr : instr -> lcpoint -> nat)
  (fn0: funname) (cc: cmd) (n0: nat) : nat :=
  linear_end_c (fun fn i n => loc_instr i (fn, n)) fn0 cc n0. 

(* maps a point to a left (continue) or right (stop) return value, 
   depending on whether it satisfies P *)
Definition lcp_select E (P: lcpoint -> bool) (l0: lcpoint) :
  itree E (lcpoint + lcpoint) :=
  if P l0 then Ret (inl l0) else Ret (inr l0).

(*
Definition lcp_select1 E (fn: funname) (nS nE: nat) (l0: lcpoint) :
  itree E (lcpoint + lcpoint) :=
  let P := fun '(fn1 , n1) => (fn1 == fn) && (nS <= n1) && (n1 < nE) in   
  lcp_select E P l0. 
*)

Definition lcp_sem1 E {XE: ErrEvent -< E}  
  (F: linstr_r -> lcpoint -> itree E lcpoint)
  (loc_instr : instr -> lcpoint -> nat)
  (cc: cmd) (l0 l1: lcpoint) : itree E (lcpoint + lcpoint) :=
  let: (fn0, n0) := l0 in
  let n2 := loc_cmd loc_instr fn0 cc n0 in
  XCntrK F fn0 n0 n2 l1. 

Definition lcp_sem2 E {XE: ErrEvent -< E}  
  (F: linstr_r -> lcpoint -> itree E lcpoint)
  (loc_instr : instr -> lcpoint -> nat)
  (fn: funname) (n0: nat) (cc: cmd) (n1: nat) :
  itree E (lcpoint + lcpoint) :=
  lcp_sem1 F loc_instr cc (fn, n0) (fn, n1).

Definition lcp_sem1I E {XE: ErrEvent -< E} {XI : LinstrE -< E}
  {XL: LinE -< E} {XLS: stateE lstate -< E} {XST: StackE -< E}
  (loc_instr : instr -> lcpoint -> nat)
  (cc: cmd) (l0 l1: lcpoint) : itree E (lcpoint + lcpoint) :=
  lcp_sem1 (fun i l => interp_LFlowE (exec_linstr i l)) loc_instr
           cc l0 l1.

Definition lcp_sem2I E {XE: ErrEvent -< E} {XI : LinstrE -< E}
  {XL: LinE -< E} {XLS: stateE lstate -< E} {XST: StackE -< E}
  (loc_instr : instr -> lcpoint -> nat)
  (fn: funname) (n0: nat) (cc: cmd) (n1: nat) :
  itree E (lcpoint + lcpoint) :=
  lcp_sem2 (fun i l => interp_LFlowE (exec_linstr i l)) loc_instr
           fn n0 cc n1.

(*
Definition lcp_ksem0 E {XE: ErrEvent -< E}  
  (F: linstr_r -> lcpoint -> itree E lcpoint)
  (loc_instr : instr -> lcpoint -> nat)
  (fn: funname) (cc: cmd) (n0: nat) (l1: lcpoint) :
  itree E (lcpoint + lcpoint) :=
  lcp_isem F loc_instr cc (fn, n0) l1.
*)
(*
Definition lcp_select00 E fn (l0: lcpoint) (n1: nat) :
  itree E (lcpoint + lcpoint) :=
  let: (fn0, n0) := l0 in
  if (fn0 == fn) && (n0 < n1) then Ret (inl l0) else Ret (inr l0).
*)
(* tries to execute point l1 wrt to the linear translation of cc;
   basically, uses l1 as starting point for the translation of cc, and
   executes it *)
(*
Fixpoint lsm_cmd_NS E
  (loc_instr : instr -> lcpoint -> nat)                  
  (R: instr -> lcpoint -> itree E lcpoint)
  (cc: cmd) (l1: lcpoint) : itree E lcpoint :=
  let: (fn0, n0) := l1 in 
  match cc with
  | nil => Ret l1
  | i :: cc0 =>
      let n2 := loc_instr i l1 in
      let n3 := loc_cmd loc_instr fn0 cc0 n2 in
      ITree.iter (fun '(fn, n) => if (n < n2) && (fn == fn0)
          then (l0 <- R i (fn, n) ;; lcp_select E fn l0 n3)
          else (l0 <- lsm_cmd_NS loc_instr R cc0 (fn, n) ;;
                lcp_select E fn l0 n3)) l1
  end.                        
*)
(* a list of k-trees executed from fpt (start point) until either
   there's a jump to another function, or ptE is passed. *)
(*
Fixpoint lsm_lcmd_list E (ptE: nat) (ts: list (nat -> itree E lcpoint)) 
  (fpt: lcpoint) : itree E lcpoint :=
  let: (fn, pt) := fpt in
  match ts with
  | nil => Ret fpt  
  | k1 :: ks0 =>
      ITree.iter (fun '(fn0, pt0) => '(fn1, pt1) <- k1 npt0 ;;           
        if (pt == pt0) && (pt0 < pt1) && (fn1 == fn0)
        then lcp_select E fn0 (fn1, pt1) ptE
        else fpt2 <- lsm_lcmd_list ptE ks0 (fn0, pt0) ;;
             lcp_select E fn0 fpt2 ptE) fpt
 end.                
*)
(*
Fixpoint lsm_lcmd_list E (n3: nat) (ts: list (nat -> itree E lcpoint)) 
  (l1: lcpoint) : itree E lcpoint :=
  let: (fn0, n0) := l1 in
  match ts with
  | nil => Ret l1  
  | k1 :: ks0 =>
      ITree.iter (fun '(fn, n) => l2 <- k1 n ;;                           
        if (n0 <= n) && (n < snd l2) && (fst l2 == fn)
        then lcp_select E fn l2 n3
        else l3 <- lsm_lcmd_list n3 ks0 (fn, n) ;; lcp_select E fn l3 n3) l1
 end.                
*)

(* assuming fenv *)
Fixpoint lsem_instr E {XE: ErrEvent -< E} {XI : LinstrE -< E}
  {XL: LinE -< E} {XLS: stateE lstate -< E} {XST: StackE -< E}
  (loc_instr : instr -> lcpoint -> nat)
  (i : instr) (l1: lcpoint) :
(*   itree E lcpoint := *)
          itree (callE (lcpoint * funname) lcpoint +' E) lcpoint := 
  let: (MkI ii ir) := i in
  let: (fn, n0) := l1 in
  let: n3 := loc_instr i l1 in 
  match ir with
  | Cassgn x tg ty e => throw err

  | Copn xs tg o es => let n1 := loc_instr i l1 in
      isem_ICntrK fn n0 n1                 

  | Csyscall xs o es => let n1 := loc_instr i l1 in
      isem_ICntrK fn n0 n1    

  | Cif e c1 c2 =>
      let k0 := fun n => isem_ICntrK fn n (S n) in
      let k1 :=
        fun n => @lsm_cmd_NS (callE (lcpoint * funname) lcpoint +' E)
                   loc_instr (lsem_instr loc_instr)
                     c1 (fn, n) in
      let k2 :=
        fun n => @lsm_cmd_NS (callE (lcpoint * funname) lcpoint +' E)
                   loc_instr (lsem_instr loc_instr)
                     c2 (fn, n) in
      let ls := ([k0; k2; k0; k0; k1; k0]) in 
      lsm_lcmd_list n3 ls l1 

  | Cwhile a c1 e ii0 c2 =>
      let k0 := fun n => isem_ICntrK fn n (S n) in
      let k1 :=
        fun n => @lsm_cmd_NS (callE (lcpoint * funname) lcpoint +' E)
                   loc_instr (lsem_instr loc_instr)
                     c1 (fn, n) in
      let k2 :=
        fun n => @lsm_cmd_NS (callE (lcpoint * funname) lcpoint +' E)
                   loc_instr (lsem_instr loc_instr)
                     c2 (fn, n) in
      let ls := ([k0; k0; k2; k0; k0; k1; k0]) in 
      lsm_lcmd_list n3 ls l1 

  | Cfor i (d, lo, hi) c => throw err 

  | Ccall xs fn1 args => trigger_inl1 (Call (l1, fn1))
                                  
 end.


Fixpoint lsem_cmd E {XE: ErrEvent -< E} {XI : LinstrE -< E}
  {XL: LinE -< E} {XLS: stateE lstate -< E} {XST: StackE -< E}
  (loc_instr : instr -> lcpoint -> nat)
  (cc : cmd) (l1: lcpoint) :
  itree (callE (lcpoint * funname) lcpoint +' E) lcpoint :=
  @lsm_cmd_NS (callE (lcpoint * funname) lcpoint +' E)
                   loc_instr (lsem_instr loc_instr)
                     cc l1.

Variant StackAllocE : Type -> Type :=
  | Before : lcpoint -> StackAllocE unit
  | After : StackAllocE lcpoint.                                  

Definition lsem_fun E {XE: ErrEvent -< E} {XI : LinstrE -< E}
  {XL: LinE -< E} {XLS: stateE lstate -< E} {XST: StackE -< E}
  {FunDef0: Type} {FState0: Type}
  {XF: @FunE asm_op syscall_state _ FunDef0 FState0 -< E}
  {XTSA: StackAllocE -< E}
  (loc_instr : instr -> lcpoint -> nat)
  (l0: lcpoint) (fn: funname) : 
  itree (callE (lcpoint * funname) lcpoint +' E) lcpoint :=
  trigger (Before l0) ;; 
  fd <- trigger (GetFunDef fn) ;;  
  cc <- trigger (GetFunCode fd) ;;
  lsem_cmd loc_instr cc (fn, 0) ;;
  trigger After. 

Definition handle_LRec E {XE: ErrEvent -< E} {XI : LinstrE -< E}
  {XL: LinE -< E} {XLS: stateE lstate -< E} {XST: StackE -< E}
  {FunDef0: Type} {FState0: Type}
  {XF: @FunE asm_op syscall_state _ FunDef0 FState0 -< E}
  {XTSA: StackAllocE -< E}
  (loc_instr : instr -> lcpoint -> nat) :
  callE (lcpoint * funname) lcpoint ~>
    itree (callE (lcpoint * funname) lcpoint +' E) :=
 fun T (rc : callE _ _ T) =>
   match rc with
   | Call (l1, fn) => lsem_fun loc_instr l1 fn
   end.
  
Definition interp_LRec E {XE: ErrEvent -< E} {XI : LinstrE -< E}
  {XL: LinE -< E} {XLS: stateE lstate -< E} {XST: StackE -< E}
  {FunDef0: Type} {FState0: Type}
  {XF: @FunE asm_op syscall_state _ FunDef0 FState0 -< E}
  {XTSA: StackAllocE -< E}
  (loc_instr : instr -> lcpoint -> nat)
  T (t: itree (callE (lcpoint * funname) lcpoint +' E) T) : itree E T :=
  interp_mrec (handle_LRec loc_instr) t.

End LinearProjSem.

End Interp.


(******************************************************)
(******************************************************)

(* USELESS *)

Fixpoint lsm_lcmd_list0 E (n3: nat) (ts: list (nat * itree E lcpoint)) 
  (l1: lcpoint) : itree E lcpoint :=
  let: (fn0, n0) := l1 in
  match ts with
  | nil => Ret l1  
  | (n1, t1) :: ts0 =>
      ITree.iter (fun '(fn, n) =>
       if (n0 <= n) && (n < n1) then l2 <- t1 ;; lcp_select E fn l2 n3
       else l2 <- lsm_lcmd_list0 n3 ts0 (fn, n) ;; lcp_select E fn l2 n3) l1
 end.                

Fixpoint lsm_cmd E 
  (R: instr -> lcpoint -> itree E lcpoint)
  (cc: cmd) (l1: lcpoint) : itree E lcpoint :=
  match cc with
  | nil => Ret l1
  | i :: cc0 =>
      l2 <- R i l1 ;; lsm_cmd R cc0 l2 end.

(* cc: linear code. 
   fn: function cc belongs to.
   n0: starting point of cc in 'code fn'. 
   l1: the linear code point (a linear instruction) being executed.
   the position of the executed intruction in fn is 'n1'.
   need to check whether the position returned by F is in fn. *)
Definition XCntrL {E} {XE: ErrEvent -< E}  
  (F: linstr_r -> lcpoint -> itree E lcpoint)
  (fn: funname) (cc: lcmd) (n0: nat) (l1: lcpoint) :
  itree E (lcpoint + lcpoint) :=
  match l1 with
  | (fn1, n1) =>
      if (fn1 == fn) && (n0 <= n1)
      then let pi := find_linstr_in_env cc (n1 - n0) in
           match pi with
           | Some (MkLI _ i) => l2 <- F i l1 ;; Ret (inl l2)  
           | _ => Ret (inr l1)
           end
      else Ret (inr l1)
  end.             

Definition XCntrS {E} {XE: ErrEvent -< E}  
  (F: linstr_r -> lcpoint -> itree E lcpoint)
  (N: lcpoint -> lcmd * nat)
  (l0: lcpoint) : itree E (lcpoint + lcpoint) :=
  let fn := fst l0 in
  let '(lc, n0) := N l0 in
  XCntrL F fn lc n0 l0.

(* iterate XContrS *)
Definition ICntrS {E} {XE: ErrEvent -< E}  
  (F: linstr_r -> lcpoint -> itree E lcpoint)
  (N: lcpoint -> lcmd * nat)
  (l0: lcpoint) : itree E lcpoint :=
  ITree.iter (@XCntrS E XE F N) l0.

(* add a termination check to XCntrLF *)
Definition XCntrSG {E} {XE: ErrEvent -< E}  
  (F: linstr_r -> lcpoint -> itree E lcpoint)
  (N: lcpoint -> lcmd * nat)
  (X: lcpoint -> bool)
  (l0: lcpoint) : itree E (lcpoint + lcpoint) :=
  if (X l0)
  then Ret (inr l0)
  else l1 <- ICntrS F N l0 ;; Ret (inl l1).

Definition ICntrSG {E} {XE: ErrEvent -< E}  
  (F: linstr_r -> lcpoint -> itree E lcpoint)
  (N: lcpoint -> lcmd * nat)
  (X: lcpoint -> bool)
  (l0: lcpoint) : itree E lcpoint :=
  ITree.iter (@XCntrSG E XE F N X) l0.

Definition XCntrSF {E} {XE: ErrEvent -< E}  
  (F: linstr_r -> lcpoint -> itree E lcpoint)
  (N: lcpoint -> lcmd * nat)
  (X: lcpoint -> bool)
  (fn: funname) (l0: lcpoint) : itree E (lcpoint + lcpoint) :=
  if (X l0) && ~~(fn == fst l0) 
  then Ret (inr l0)
  else l1 <- ICntrS F N l0 ;; Ret (inl l1).
            
Definition ICntrSF {E} {XE: ErrEvent -< E}  
  (F: linstr_r -> lcpoint -> itree E lcpoint)
  (N: lcpoint -> lcmd * nat)
  (X: lcpoint -> bool)
  (fn: funname) (l0: lcpoint) : itree E lcpoint :=
  ITree.iter (@XCntrSF E XE F N X fn) l0.

Definition XCntrSFG {E} {XE: ErrEvent -< E}  
  (F: linstr_r -> lcpoint -> itree E lcpoint)
  (N: lcpoint -> lcmd * nat)
  (X: lcpoint -> bool)
  (l0: lcpoint) : itree E (lcpoint + lcpoint) :=
  if (X l0)
  then Ret (inr l0)
  else l1 <- ICntrSF F N X (fst l0) l0 ;; Ret (inl l1).

Definition ICntrSFG {E} {XE: ErrEvent -< E}  
  (F: linstr_r -> lcpoint -> itree E lcpoint)
  (N: lcpoint -> lcmd * nat)
  (X: lcpoint -> bool)
  (l0: lcpoint) : itree E lcpoint :=
  ITree.iter (@XCntrSFG E XE F N X) l0.

(* execute the code of fn from 0. can jump into any function code at
   any point *)
Definition XCntrLF {E} {XE: ErrEvent -< E}  
  (F: linstr_r -> lcpoint -> itree E lcpoint)
  (l1: lcpoint) : itree E (lcpoint + lcpoint) :=
  let fn := fst l1 in
  let plc := fenv fn in
  match plc with
  | Some lc => XCntrL F fn lc 0 l1
  | _ => throw err
  end.             

(* add a termination check to XCntrLF *)
Definition XCntrLG {E} {XE: ErrEvent -< E}  
  (F: linstr_r -> lcpoint -> itree E lcpoint)
  (X: lcpoint -> bool)
  (l1: lcpoint) : itree E (lcpoint + lcpoint) :=
  if (X l1)
  then Ret (inr l1)
  else XCntrLF F l1.

(* iterate XContrLG *)
Definition ICntrG {E} {XE: ErrEvent -< E}  
  (F: linstr_r -> lcpoint -> itree E lcpoint)
  (X: lcpoint -> bool)
  (l1: lcpoint) : itree E lcpoint :=
  ITree.iter (@XCntrLG E XE F X) l1.

(* ok, can jump into a function at any point *)
Definition XCntrFF {E} {XE: ErrEvent -< E}  
  (F: linstr_r -> lcpoint -> itree E lcpoint)
  (fn: funname) (l1: lcpoint) :
  itree E (lcpoint + lcpoint) :=
  let plc := fenv fn in
  match plc with
  | Some lc => XCntrL F fn lc 0 l1
  | _ => throw err
  end.             

Definition ICntrFF {E} {XE: ErrEvent -< E}  
  (F: linstr_r -> lcpoint -> itree E lcpoint)
  (fn: funname) (l1: lcpoint) : itree E lcpoint :=
  ITree.iter (@XCntrFF E XE F fn) l1.    

Definition XCntrFG {E} {XE: ErrEvent -< E}  
  (F: linstr_r -> lcpoint -> itree E lcpoint)
  (X: lcpoint -> bool)
  (l1: lcpoint) : itree E (lcpoint + lcpoint) :=
  if (X l1)
  then Ret (inr l1)
  else l2 <- ICntrFF F (fst l1) l1 ;; Ret (inl l2).

Definition ICntrFG {E} {XE: ErrEvent -< E}  
  (F: linstr_r -> lcpoint -> itree E lcpoint)
  (X: lcpoint -> bool)
  (l1: lcpoint) : itree E lcpoint :=
  ITree.iter (@XCntrFG E XE F X) l1.   
   
Definition ICntrL {E} {XE: ErrEvent -< E}  
  (F: linstr_r -> lcpoint -> itree E lcpoint)
  (fn: funname) (cc: lcmd) (n0: nat) (l1: lcpoint) :
  itree E lcpoint :=
  ITree.iter (@XCntrL E XE F fn cc n0) l1.

Definition XCntrFG0 {E} {XE: ErrEvent -< E}  
  (F: linstr_r -> lcpoint -> itree E lcpoint)
  (X: lcpoint -> bool)
  (fn: funname) (l1: lcpoint) : itree E (lcpoint + lcpoint) :=
  if (X l1)
  then Ret (inr l1)
  else XCntrFF F fn l1.

(*********************************************************)

(* USELESS *)

(* iterative semantics body *)
Definition isem_linstrD E {XE: ErrEvent -< E} {XI : LinstrE -< E}
  {XL: LinE -< E} {XLS: stateE lstate -< E}
  {XST: StackE -< E} (lbl: lcpoint) :
  itree E (lcpoint + lcpoint) :=
  LCntr (fun i l => interp_LFlowE (exec_linstr i l)) is_final lbl.

(* iterative semantics of a program, from any starting point *)
Definition isem_liniterD E {XE: ErrEvent -< E} {XI : LinstrE -< E}
  {XL: LinE -< E} {XLS: stateE lstate -< E}
  {XST: StackE -< E} (lbl: lcpoint) : itree E lcpoint :=
  ITree.iter (@isem_linstrD E XE XI XL XLS XST) lbl.

Definition isem_ICntrG E {XE: ErrEvent -< E} {XI : LinstrE -< E}
  {XL: LinE -< E} {XLS: stateE lstate -< E}
  {XST: StackE -< E} (lbl: lcpoint) : itree E lcpoint :=
  ICntrG (fun i l => interp_LFlowE (exec_linstr i l)) halt_pred lbl.

Definition isem_ICntrFG E {XE: ErrEvent -< E} {XI : LinstrE -< E}
  {XL: LinE -< E} {XLS: stateE lstate -< E}
  {XST: StackE -< E} (lbl: lcpoint) : itree E lcpoint :=
  ICntrFG (fun i l => interp_LFlowE (exec_linstr i l)) halt_pred lbl.

Definition isem_ICntrL E {XE: ErrEvent -< E} {XI : LinstrE -< E}
  {XL: LinE -< E} {XLS: stateE lstate -< E} {XST: StackE -< E}
  (fn: funname) (cc: lcmd) (n0: nat) (lbl0: lcpoint) : itree E lcpoint :=
  ICntrL (fun i l => interp_LFlowE (exec_linstr i l)) fn cc n0 lbl0.


Section Interp02.

Context {stackAgree : lstate -> alstate -> bool}.
Context
(*  {asm_op : Type} {pd : PointerData} *)
(* {asmop : asmOp asm_op} *) 
  (liparams : @linearization_params asm_op (@_asmop asm_op syscall_state sip)).
Context (SP : sprog).

Definition handle2lin 
  E {XE: ErrEvent -< E} {XI : LinstrE -< E}
  {XL: LinE -< E} {XLS: stateE lstate -< E} {XST: StackE -< E}
  (fn: funname) (i:instr) (n0: nat) (lbl0: label) :
   itree E (nat * label * lcpoint) :=
  let '(n1, lbl1, lc) := linear_full_i liparams SP fn i n0 lbl0 in
  l1 <- isem_ICntrL fn lc n0 (fn, n0) ;; Ret (n1, lbl1, l1). 

(*
1) define the source code interpretation recursively. ultimately, each
   source instruction should be mapped to a linear iteration, and so
   commands (by folding with bind?? no!! by joining and iterating, see
   below). use rec call triggers for function calls.

2) define the translation globally (or at least function-wise).  so,
   basically, lc should be the global code, while a source instruction
   should be associated to n0 and n1 (start and end of the code
   segment).

localize_instr : lcmd -> funname -> instr -> nat -> nat

or:

localize_instr : fenv -> funname -> instr -> nat -> nat

or:

localize_instr_rel : fenv -> funname -> instr -> nat -> nat -> Prop

3) introduce halting conditions as parameters on iteration, to model
   the interpretation of source instructions. so, the exit condition
   on isem_ICntr should be parameterized on (fn, n0, n1). Also needed:
   entry conditions (join combinator).

exit: funname -> nat -> nat -> lcpoint -> bool

iter n1 n3 (join (iter n1 n2) (iter n2 n3)) = iter n1 n3
*)

End Interp02.


(*
Section FInterp.

Context {E: Type -> Type} {XE: ErrEvent -< E} {XS: @stateE lstate -< E}
  {XA: @stateE alstate -< E} {XST: StackE -< E}.

Context {stackAgree : lstate -> alstate -> bool}.

(* still need to to interpret StackE *)
Definition interp_up2state_lin T 
  (t: itree (LinstrE +' LinE +' E) T) : lcpoint -> itree E T :=
  fun l => @interp_LinE _ _ stackAgree _ _ _ (interp_LinstrE t l).

End FInterp.
*)

Definition conv_obj T1 T2 (ee: T1 = T2) (u: T1) : T2 :=
  eq_rect T1 (fun T : Type => T) u T2 ee.


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

(*
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
*)

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

(*
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
*)  

End Test1. 

End AStateLinSem.

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
