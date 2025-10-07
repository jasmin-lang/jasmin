(* -> was it_sems_mden4.v *)

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

Variant LinstrE : Type -> Type :=
  | ELopn   : lexprs -> sopn -> rexprs -> LinstrE unit
  | ELsyscall : syscall_t -> LinstrE unit
  | ELcall    : option var_i -> remote_label -> LinstrE unit
  | ELret     : LinstrE unit
  | ELalign :  LinstrE unit
  | ELlabel : label_kind -> label -> LinstrE unit
  | ELgoto  : remote_label -> LinstrE unit
  | ELigoto : rexpr -> LinstrE unit
  | ELstoreLabel : var -> label -> LinstrE unit
  | ELcond  : fexpr -> label -> LinstrE unit.

Variant LinE : Type -> Type :=
  | FindInstr : LinE linstr
  | IsFinal : LinE bool.                   

Definition LCntr {E} `{LE: LinE -< E}
  (f: linstr_r -> itree E unit) (i: linstr_r) :
  itree E (linstr + unit) :=
  f i ;;
  b <- trigger IsFinal ;;
  if b then Ret (inr tt)
  else li <- trigger FindInstr ;;
       Ret (inl li).
            

Section SemRec.
  
Context {E} {XI : LinstrE -< E} {XL: LinE -< E}. 

(* one-step semantics of instructions *)
Definition exec_linstr (ir : linstr_r) : itree E unit :=
(*  let ir := li_i i in *)
  match ir with
  | Lopn xs o es => trigger (ELopn xs o es)

  | Lsyscall o => trigger (ELsyscall o)

  | Lcall or d => trigger (ELcall or d)

  | Lret => trigger ELret

  | Lalign => trigger ELalign 
      
  | Llabel x y => trigger (ELlabel x y)

  | Lgoto d => trigger (ELgoto d)

  | Ligoto e => trigger (ELigoto e)

  | LstoreLabel x lbl => trigger (ELstoreLabel x lbl)                      

  | Lcond e lbl => trigger (ELcond e lbl)
  end.                         

Definition isem_linstr (i: linstr_r) : itree E (linstr + unit) :=
  LCntr exec_linstr i.

(* iterative semantics of a (start) instruction *)
Definition isem_cmd (i: linstr) : itree E unit :=
  ITree.iter (fun x => isem_linstr (li_i x)) i.

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


Section Handle.

Context {E: Type -> Type}  
        {XS: @stateE lstate -< E} {XE: ErrEvent -< E}.

(* fixme *)
Context (IsFinalP : lprog -> lstate -> bool).

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

Definition find_instr_sem (s: lstate) : itree E linstr :=
  @err_option E XE _ plain_err (find_instr P s).

Definition handle_lin {T}
  (e: LinE T) : itree E T :=
  match e with
  | FindInstr => s <- trigger (@Get lstate) ;; find_instr_sem s
  | IsFinal => s <- trigger (@Get lstate) ;; final_state_sem s                   end.                                         

End Handle.

Section Interp.

Context {E: Type -> Type} {XE: ErrEvent -< E} {XS: @stateE lstate -< E}.

(* fixme *)
Context (IsFinalP : lprog -> lstate -> bool).

Definition interp_LinstrE {XL: LinE -< E} {A: Type}
  (t : itree (LinstrE +' E) A) : itree E A :=
  interp (ext_handler (@handle_linstr E XS XE XL)) t.

Definition interp_LinE {A: Type}
  (t : itree (LinE +' E) A) : itree E A :=
  interp (ext_handler (@handle_lin E XS XE IsFinalP)) t.

End Interp.

Section FInterp.

Context {E: Type -> Type} {XE: ErrEvent -< E} {XS: @stateE lstate -< E}.

(* fixme *)
Context (IsFinalP : lprog -> lstate -> bool).

Definition up2state_lin_interp T 
  (t: itree (LinstrE +' LinE +' E) T) : itree E T :=
  interp_LinE IsFinalP (interp_LinstrE t).

End FInterp.

End GInterp.

End Asm1.

