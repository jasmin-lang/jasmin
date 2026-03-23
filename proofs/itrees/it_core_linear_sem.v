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
               psem_defs psem_core.

Require Import it_exec it_exec_sem tfam_iso
               eutt_extras rec_facts.
Require Import linearization_ext.
Require Import it_cflow_sem it_effect_sem equiv_extras rutt_extras.

From ITree Require Import Rutt RuttFacts.
From ITree Require Import CategorySub.

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

(*
Definition incr_lpoint (l: lpoint) : lpoint :=
  match l with (fn, pt) => (fn, S pt) end.

(* the program point is in the interval *)
Definition lcp_in_interval (nS nE: nat) (l1: lpoint) : bool :=
  match l1 with
  | (_, n0) => (nS <= n0) && (n0 < nE) end. 
*)

(************************************************************)

Section Asm1.
  
Context {err: error_data}. 


Section AbsIterators.
(***** ABSTRACT ITERATORS *)
Context {St L: Type}.
(* Section LinSem. *)
Context {E} {XE: ErrEvent -< E}.

(* the generic iteration body used to define the semantics. *)
Definition ACntr (Bd: St -> itree E St) (NoExit: St -> option bool)
  (s0: St) : itree E (St + St) :=
  (* check whether the exit condition is satisfied *)
  match NoExit s0 with
  | Some b =>
    if b then s1 <- Bd s0 ;; Ret (inl s1)      
    else Ret (inr s0)
  | None => throw err
  end.

(* 'abstract' semantics of linear instruction *)
Definition ASem (Sem: L -> St -> itree E St)
  (TryFnd: St -> option L) : St -> itree E St :=
  fun s0 => match TryFnd s0 with
            | Some l => Sem l s0
            | None => throw err                                         
            end.  

(* generic iterator specialized to a semantics of instructions, used
   in the Linear Core Semantics *)
Definition SACntr (Sem: L -> St -> itree E St)
  (NoExit: St -> option bool) (TryFnd: St -> option L)
  (s0: St) : itree E (St + St) :=
  ACntr (ASem Sem TryFnd) NoExit s0.
         
(* iterates SCntr *)
Definition SACntrI (Sem: L -> St -> itree E St)
  (NoExit: St -> option bool) (TryFnd: St -> option L)
  (s0: St) : itree E St :=
  ITree.iter (@SACntr Sem NoExit TryFnd) s0.

End AbsIterators.


Section AbsLinear.  

Context  {asm_op: Type}
         {syscall_state : Type}
         {sip : SemInstrParams asm_op syscall_state}.

Definition find_linstr (lc: lcmd) (pt: nat) : option linstr :=
  oseq.onth lc pt.

Definition is_final (lc: lcmd) (pt: nat) : bool :=
  pt =? (length lc).


Section LinSemClass.
Context (LState: Type).

(* We use this class on S to abstract over the paramters required by
   lstate. *)
Class LinSem : Type := {
  Lopn_sem (xs: seq.seq lexpr) (o: sopn) (es: seq.seq rexpr)
    : LState -> exec LState ;

  Lsyscall_sem (o: syscall_t) : LState -> exec LState ;

  Lcall_sem (ov: option var_i) (d: remote_label) : LState -> exec LState ;

  Lret_sem : LState -> exec LState ;

  Lalign_sem : LState -> exec LState ;

  Llabel_sem (k: label_kind) (lbl: label) : LState -> exec LState ;

  Lgoto_sem (d: remote_label) : LState -> exec LState ;

  Ligoto_sem (e: rexpr) : LState -> exec LState ;

  Lstorelabel_sem (x: var) (lbl: label) : LState -> exec LState ;

  Lcond_sem (e: fexpr) (lbl: label) : LState -> exec LState ; }.

(* basically, same as eval_instr (in the old semantics, with S =
   lstate) *)
Definition linstr_asem {LS_I : LinSem} (i : linstr_r)
  (s1: LState) : exec LState := match i with
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


Section ALinSem.

Context (LState: Type).
Context {E} {XE: ErrEvent -< E}.

Definition SCntr (Sem: linstr -> LState -> itree E LState)
  (NoExit: LState -> option bool) (TryFnd: LState -> option linstr)
  (s0: LState) : itree E (LState + LState) :=
  SACntr Sem NoExit TryFnd s0.

Definition SCntrI (Sem: linstr -> LState -> itree E LState)
  (NoExit: LState -> option bool) (TryFnd: LState -> option linstr)
  (s0: LState) : itree E LState :=
  SACntrI Sem NoExit TryFnd s0.


Section CoreLinSem.
Context {LS_I : LinSem LState}.

Notation LFDEnv := (funname -> option lfundef). 
Context (lfdenv: LFDEnv).
Notation LFEnv := (funname -> option lcmd).
Definition lfenv : LFEnv := fun fn => match lfdenv fn with
                       | Some fd => Some (lfd_body fd)
                       | _ => None end.                              

Definition halt_pred (l: lpoint) : option bool :=
  let fn := fst l in
  let lbl := snd l in
  let plc := lfenv fn in
  match plc with
  | Some lc => Some (is_final lc lbl) 
  | _ => None
  end.             

Definition find_linstr_in_fun (lp : lpoint) : option linstr :=
  match lfenv (fst lp) with
  | Some lc => find_linstr lc (snd lp)
  | _ => None
  end.                         

Definition state_find_linstr {readPC: LState -> option lpoint}
  (st: LState) : option linstr :=
  match (readPC st) with
  | Some l => find_linstr_in_fun l
  | None => None
  end.            

Definition halt_state_pred {readPC: LState -> option lpoint}
  (st: LState) : option bool :=
  match (readPC st) with
  | Some l => halt_pred l
  | _ => None
  end.         

(* the 'abstract' core semantics of linear instructions, based on
   linstr_asem *)
Definition acore_li_sem {readPC: LState -> option lpoint}
  (i : linstr) (s: LState) : itree E LState :=
  match i with MkLI _ ir => iresult (linstr_asem ir s) s end.

(*** LINEAR CORE SEMANTICS *)
(* core semantics body *)
Definition acore_lcmd_sem_body {readPC: LState -> option lpoint} :
  LState -> itree E (LState + LState) :=
  SCntr (@acore_li_sem readPC)
    (@halt_state_pred readPC)
    (@state_find_linstr readPC).

(* iterative core semantics of a linear program, from any state *)
Definition acore_lcmd_sem {readPC: LState -> option lpoint}
  (s: LState) : itree E LState :=
  SCntrI (@acore_li_sem readPC)
    (@halt_state_pred readPC)
    (@state_find_linstr readPC) s.

End CoreLinSem.

End ALinSem.


Section ConcreteSem.

Context
  {ep : EstateParams syscall_state}
  {spp : SemPexprParams}
  {ovm_i : one_varmap_info}
  (P : lprog).

Context {E} {XE: ErrEvent -< E}.

#[local] Existing Instance withsubword.
Local Open Scope seq_scope.
Notation labels := label_in_lprog.

(* FIXME *)
Context (lfdenv: funname -> option lfundef). 
Context (IsFinalP : lprog -> lstate -> bool).
Context (readPC: lstate -> option lpoint).

Definition final_state_sem (s: lstate) : itree E bool :=
  Ret (IsFinalP P s).  

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
  let nsp := (sp + wrepr Uptr (wsize_size Uptr))%R in
  Let p  := read s1.(lmem) Aligned sp Uptr in
  Let vm := set_var true s1.(lvm) vrsp (Vword nsp) in
  Let d := rdecode_label (labels P) p in
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

Instance lstate_LinSem : LinSem lstate :=
  {|
    Lopn_sem := lopn_sem ;
    Lsyscall_sem := lsyscall_sem ;
    Lcall_sem := lcall_sem ;
    Lret_sem := lret_sem ;
    Lalign_sem := lalign_sem ;
    Llabel_sem := llabel_sem ;
    Lgoto_sem := lgoto_sem ;
    Ligoto_sem := ligoto_sem ;
    Lstorelabel_sem := lstorelabel_sem ;
    Lcond_sem := lcond_sem ;
  |}.  

(* same as eval_instr in the old semantics *)
Definition linstr_sem (i : linstr_r)
  (s1: lstate) : exec lstate := linstr_asem i s1.

Definition core_li_sem (i : linstr) (s: lstate) : itree E lstate :=
   @acore_li_sem _ _ _ _ readPC i s.

(*** LINEAR CORE SEMANTICS *)
(* core semantics body *)
Definition core_lcmd_sem_body 
  (s: lstate) : itree E (lstate + lstate) :=
  @acore_lcmd_sem_body _ _ _ _ lfdenv readPC s.

(* iterative core semantics of a linear program, from any state *)
Definition core_lcmd_sem (s: lstate) : itree E lstate :=
  ITree.iter core_lcmd_sem_body s.

End ConcreteSem.

End AbsLinear.

End Asm1.

