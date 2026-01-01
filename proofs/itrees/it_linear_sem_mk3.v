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

(********************************************************************)

(* cc: linear code. 
   fn: function cc belongs to.
   n0: starting point of cc in 'code fn'. 
   l1: the instruction being executed.
   the position of the executed intruction in fn is 'n1'.
   need to check whether the position returned by F is in fn. *)
Definition XCntrL {E} {XE: ErrEvent -< E}  
  (F: linstr_r -> rlabel -> itree E rlabel)
  (fn: funname) (cc: lcmd) (n0: nat) (l1: rlabel) :
  itree E (rlabel + rlabel) :=
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

Definition XCntrK {E} {XE: ErrEvent -< E}  
  (F: linstr_r -> rlabel -> itree E rlabel)
  (fn: funname) (nS nE: nat) (l1: rlabel) : itree E (rlabel + rlabel) :=
  match l1 with
  | (fn1, n1) =>
  (* the optional function body *)
    match fenv fn1 with
    | None => throw err      
    (* the function exists: find the instruction in its body *)
    | Some lc =>
      if (length lc < nE) then throw err else
      if (fn == fn1) && (nS <= n1) && (n1 < nE)
      then match find_linstr_in_env lc n1 with
           (* the instruction exists in the segment: execute it and
              return the next label *) 
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
  (F: linstr_r -> rlabel -> itree E rlabel)
  (fn: funname) (nS nE: nat) (l0: rlabel) : itree E rlabel :=
  ITree.iter (@XCntrK E XE F fn nS nE) l0.
                 
Definition XCntrS {E} {XE: ErrEvent -< E}  
  (F: linstr_r -> rlabel -> itree E rlabel)
  (N: rlabel -> lcmd * nat)
  (l0: rlabel) : itree E (rlabel + rlabel) :=
  let fn := fst l0 in
  let '(lc, n0) := N l0 in
  XCntrL F fn lc n0 l0.

(* iterate XContrS *)
Definition ICntrS {E} {XE: ErrEvent -< E}  
  (F: linstr_r -> rlabel -> itree E rlabel)
  (N: rlabel -> lcmd * nat)
  (l0: rlabel) : itree E rlabel :=
  ITree.iter (@XCntrS E XE F N) l0.

(* add a termination check to XCntrLF *)
Definition XCntrSG {E} {XE: ErrEvent -< E}  
  (F: linstr_r -> rlabel -> itree E rlabel)
  (N: rlabel -> lcmd * nat)
  (X: rlabel -> bool)
  (l0: rlabel) : itree E (rlabel + rlabel) :=
  if (X l0)
  then Ret (inr l0)
  else l1 <- ICntrS F N l0 ;; Ret (inl l1).

Definition ICntrSG {E} {XE: ErrEvent -< E}  
  (F: linstr_r -> rlabel -> itree E rlabel)
  (N: rlabel -> lcmd * nat)
  (X: rlabel -> bool)
  (l0: rlabel) : itree E rlabel :=
  ITree.iter (@XCntrSG E XE F N X) l0.

Definition XCntrSF {E} {XE: ErrEvent -< E}  
  (F: linstr_r -> rlabel -> itree E rlabel)
  (N: rlabel -> lcmd * nat)
  (X: rlabel -> bool)
  (fn: funname) (l0: rlabel) : itree E (rlabel + rlabel) :=
  if (X l0) && ~~(fn == fst l0) 
  then Ret (inr l0)
  else l1 <- ICntrS F N l0 ;; Ret (inl l1).
            
Definition ICntrSF {E} {XE: ErrEvent -< E}  
  (F: linstr_r -> rlabel -> itree E rlabel)
  (N: rlabel -> lcmd * nat)
  (X: rlabel -> bool)
  (fn: funname) (l0: rlabel) : itree E rlabel :=
  ITree.iter (@XCntrSF E XE F N X fn) l0.

Definition XCntrSFG {E} {XE: ErrEvent -< E}  
  (F: linstr_r -> rlabel -> itree E rlabel)
  (N: rlabel -> lcmd * nat)
  (X: rlabel -> bool)
  (l0: rlabel) : itree E (rlabel + rlabel) :=
  if (X l0)
  then Ret (inr l0)
  else l1 <- ICntrSF F N X (fst l0) l0 ;; Ret (inl l1).

Definition ICntrSFG {E} {XE: ErrEvent -< E}  
  (F: linstr_r -> rlabel -> itree E rlabel)
  (N: rlabel -> lcmd * nat)
  (X: rlabel -> bool)
  (l0: rlabel) : itree E rlabel :=
  ITree.iter (@XCntrSFG E XE F N X) l0.

(*********************************************************)

(* execute the code of fn from 0. can jump into any function code at
   any point *)
Definition XCntrLF {E} {XE: ErrEvent -< E}  
  (F: linstr_r -> rlabel -> itree E rlabel)
  (l1: rlabel) : itree E (rlabel + rlabel) :=
  let fn := fst l1 in
  let plc := fenv fn in
  match plc with
  | Some lc => XCntrL F fn lc 0 l1
  | _ => throw err
  end.             

(* add a termination check to XCntrLF *)
Definition XCntrLG {E} {XE: ErrEvent -< E}  
  (F: linstr_r -> rlabel -> itree E rlabel)
  (X: rlabel -> bool)
  (l1: rlabel) : itree E (rlabel + rlabel) :=
  if (X l1)
  then Ret (inr l1)
  else XCntrLF F l1.

(* iterate XContrLG *)
Definition ICntrG {E} {XE: ErrEvent -< E}  
  (F: linstr_r -> rlabel -> itree E rlabel)
  (X: rlabel -> bool)
  (l1: rlabel) : itree E rlabel :=
  ITree.iter (@XCntrLG E XE F X) l1.

(* ok, can jump into a function at any point *)
Definition XCntrFF {E} {XE: ErrEvent -< E}  
  (F: linstr_r -> rlabel -> itree E rlabel)
  (fn: funname) (l1: rlabel) :
  itree E (rlabel + rlabel) :=
  let plc := fenv fn in
  match plc with
  | Some lc => XCntrL F fn lc 0 l1
  | _ => throw err
  end.             

Definition ICntrFF {E} {XE: ErrEvent -< E}  
  (F: linstr_r -> rlabel -> itree E rlabel)
  (fn: funname) (l1: rlabel) : itree E rlabel :=
  ITree.iter (@XCntrFF E XE F fn) l1.    

Definition XCntrFG {E} {XE: ErrEvent -< E}  
  (F: linstr_r -> rlabel -> itree E rlabel)
  (X: rlabel -> bool)
  (l1: rlabel) : itree E (rlabel + rlabel) :=
  if (X l1)
  then Ret (inr l1)
  else l2 <- ICntrFF F (fst l1) l1 ;; Ret (inl l2).

Definition ICntrFG {E} {XE: ErrEvent -< E}  
  (F: linstr_r -> rlabel -> itree E rlabel)
  (X: rlabel -> bool)
  (l1: rlabel) : itree E rlabel :=
  ITree.iter (@XCntrFG E XE F X) l1.   
   
Definition ICntrL {E} {XE: ErrEvent -< E}  
  (F: linstr_r -> rlabel -> itree E rlabel)
  (fn: funname) (cc: lcmd) (n0: nat) (l1: rlabel) :
  itree E rlabel :=
  ITree.iter (@XCntrL E XE F fn cc n0) l1.

Definition halt_pred (l: rlabel) : bool :=
  let fn := fst l in
  let lbl := snd l in
  let plc := fenv fn in
  match plc with
  | Some lc => if is_final lc lbl then true else false 
  | _ => false
  end.             

(* useless *)
Definition XCntrFG0 {E} {XE: ErrEvent -< E}  
  (F: linstr_r -> rlabel -> itree E rlabel)
  (X: rlabel -> bool)
  (fn: funname) (l1: rlabel) : itree E (rlabel + rlabel) :=
  if (X l1)
  then Ret (inr l1)
  else XCntrFF F fn l1.

(**************************************************************)

Section SemRec.
  
Context {E} {XF : LFlowE -< E} {XI : LinstrE -< E} {XE: ErrEvent -< E}. 

(* one-step semantics of instructions *)
Definition exec_linstr (ir : linstr_r) (l: rlabel) :
  itree E rlabel :=
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

Variant StackE : Type -> Type :=
  | Push (l: rlabel) : StackE unit
  | Pop : StackE rlabel. 


Section HandleLFlow.
  
Context {E: Type -> Type} {XL: LinE -< E} {XST: StackE -< E}
    {XE: ErrEvent -< E}. 

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

(* iterative semantics body *)
Definition isem_linstrD E {XE: ErrEvent -< E} {XI : LinstrE -< E}
  {XL: LinE -< E} {XLS: stateE lstate -< E}
  {XST: StackE -< E} (lbl: rlabel) :
  itree E (rlabel + rlabel) :=
  LCntr (fun i l => interp_LFlowE (exec_linstr i l)) is_final lbl.

(* iterative semantics of a program, from any starting point *)
Definition isem_liniterD E {XE: ErrEvent -< E} {XI : LinstrE -< E}
  {XL: LinE -< E} {XLS: stateE lstate -< E}
  {XST: StackE -< E} (lbl: rlabel) : itree E rlabel :=
  ITree.iter (@isem_linstrD E XE XI XL XLS XST) lbl.

Definition isem_ICntrG E {XE: ErrEvent -< E} {XI : LinstrE -< E}
  {XL: LinE -< E} {XLS: stateE lstate -< E}
  {XST: StackE -< E} (lbl: rlabel) : itree E rlabel :=
  ICntrG (fun i l => interp_LFlowE (exec_linstr i l)) halt_pred lbl.

Definition isem_ICntrFG E {XE: ErrEvent -< E} {XI : LinstrE -< E}
  {XL: LinE -< E} {XLS: stateE lstate -< E}
  {XST: StackE -< E} (lbl: rlabel) : itree E rlabel :=
  ICntrFG (fun i l => interp_LFlowE (exec_linstr i l)) halt_pred lbl.

Definition isem_ICntrL E {XE: ErrEvent -< E} {XI : LinstrE -< E}
  {XL: LinE -< E} {XLS: stateE lstate -< E} {XST: StackE -< E}
  (fn: funname) (cc: lcmd) (n0: nat) (lbl0: rlabel) : itree E rlabel :=
  ICntrL (fun i l => interp_LFlowE (exec_linstr i l)) fn cc n0 lbl0.

(* if the linear translation of i is straightline code, it should
   return (fn, n1) *)
Definition isem_ICntrK E {XE: ErrEvent -< E} {XI : LinstrE -< E}
  {XL: LinE -< E} {XLS: stateE lstate -< E} {XST: StackE -< E}
  (fn: funname) (n0 n1: nat) : itree E rlabel :=
  ICntrK (fun i l => interp_LFlowE (exec_linstr i l)) fn n0 n1 (fn, n0).

(* two errors so far.

1) handle_linstr consumes LinstrE events, but this is wrong.  we need
Linstr_isem_with_state as in mk1.

2) actual labels are symbolic, they do not coincide with code position
(look at the linerization translation). This means that in
linstr_rlabel the treatment of eg Lgoto is not right. This also means
that the code is needed, not just the rlabel.

*)

Require Import linearization.

Context
(*  {asm_op : Type}
  {pd : PointerData} *)
 (* {asmop : asmOp asm_op} *) 
  (liparams : @linearization_params asm_op (@_asmop asm_op syscall_state sip)).
Context (SP : sprog).

Definition handle2lin 
  E {XE: ErrEvent -< E} {XI : LinstrE -< E}
  {XL: LinE -< E} {XLS: stateE lstate -< E} {XST: StackE -< E}
  (fn: funname) (i:instr) (n0: nat) (lbl0: label) :
   itree E (nat * label * rlabel) :=
  let '(n1, lbl1, lc) := linear_Xi liparams SP fn i n0 lbl0 in
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

exit: funname -> nat -> nat -> rlabel -> bool

iter n1 n3 (join (iter n1 n2) (iter n2 n3)) = iter n1 n3
*)

Fixpoint lsm_cmd E 
  (R: instr -> rlabel -> itree E rlabel)
  (cc: cmd) (l1: rlabel) : itree E rlabel :=
  match cc with
  | nil => Ret l1
  | i :: cc0 =>
      l2 <- R i l1 ;; lsm_cmd R cc0 l2 end.

Fixpoint loc_cmd (loc_instr : instr -> rlabel -> nat)
  (fn: funname) (cc: cmd) (n0: nat) : nat :=
  match cc with
  | nil => n0
  | i :: cc0 => let n2 := loc_instr i (fn, n0) in
                loc_cmd loc_instr fn cc0 n2 end.

Definition select E fn (l0: rlabel) (n1: nat) : itree E (rlabel + rlabel) :=
  let: (fn0, n0) := l0 in
  if (fn0 == fn) && (n0 < n1) then Ret (inl l0) else Ret (inr l0).

Fixpoint lsm_cmd_NS E
  (loc_instr : instr -> rlabel -> nat)                  
  (R: instr -> rlabel -> itree E rlabel)
  (cc: cmd) (l1: rlabel) : itree E rlabel :=
  let: (fn, n0) := l1 in 
  match cc with
  | nil => Ret l1
  | i :: cc0 =>
      let n2 := loc_instr i l1 in
      let n3 := loc_cmd loc_instr fn cc0 n2 in
      ITree.iter (fun '(fn, n) => if n < n2
          then (l0 <- R i (fn, n) ;; select E fn l0 n3)
          else (l0 <- lsm_cmd_NS loc_instr R cc0 (fn, n) ;;
                select E fn l0 n3)) l1
  end.                        
                
(* assuming fenv *)
Fixpoint lsem_instr E {XE: ErrEvent -< E} {XI : LinstrE -< E}
  {XL: LinE -< E} {XLS: stateE lstate -< E} {XST: StackE -< E}
  (loc_instr : instr -> rlabel -> nat)
  (i : instr) (l1: rlabel) :
          itree (callE rlabel rlabel +' E) rlabel :=
  let: (MkI ii ir) := i in
  let: (fn, n0) := l1 in  
  match ir with
  | Cassgn x tg ty e => throw err

  | Copn xs tg o es => let n1 := loc_instr i l1 in
      isem_ICntrK fn n0 n1                 

  | Csyscall xs o es => let n1 := loc_instr i l1 in
      isem_ICntrK fn n0 n1    
                  
  | _ => throw err end.
                  




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








(****************


Definition handle2lin 
  E {XE: ErrEvent -< E} {XI : LinstrE -< E}
  {XL: LinE -< E} {XLS: stateE lstate -< E} {XST: StackE -< E}
  (fn: funname) (i:instr) (n0: nat) (lbl0: label) :
   itree E (label * rlabel) :=
  let '(n1, lbl1, lc) := linear_Xi liparams SP fn i n0 lbl0 in
  l1 <- isem_ICntrL fn lc n1 (fn, n1) ;; Ret (lbl1, l1). 

(* basically, we need to translate all the source code, and then for
each linear code position get the chunk it is included in. need to
pass n0 around. *)



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
