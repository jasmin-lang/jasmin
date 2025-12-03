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

Variant LinE : Type -> Type :=
  | MatchExec (lbl: remote_label) : LinE unit
  | NewExec : LinE remote_label
  | IsFinal (lbl: remote_label) : LinE bool.                   

Definition find_linstr_in_env (lc: lcmd) (lbl: label) : option linstr :=
  oseq.onth lc (Pos.to_nat lbl).

Definition is_final (lc: lcmd) (lbl: label) : bool :=
  (Pos.to_nat lbl) =? (length lc).

Definition LCntr {E} {XL: LinE -< E} {XE: ErrEvent -< E} 
  (f: linstr_r -> itree E unit) (rlbl: remote_label) :
  itree E (remote_label + unit) :=
  (* the state agrees with the function and the PC agrees with the
  label (throw error if it doesn't) *)
  trigger (MatchExec rlbl) ;;
  let fn := fst rlbl in
  let lbl := snd rlbl in 
  (* the optional function body *)
  let plc := fenv fn in
  match plc with
  (* the function exists: find the instruction in its body *)
  | Some lc => let pi := find_linstr_in_env lc lbl in
    match pi with
    (* the instruction exists: execute it and return the next label *) 
    | Some (MkLI _ i) => f i ;; lbl1 <- trigger NewExec ;; Ret (inl lbl1)
    (* the instruction does not exists: the execution terminates if the
       label equals the code length, otherwise throws an error *)        
    | _ => if is_final lc lbl then Ret (inr tt) else throw err end
  (* the function does not exist: throw an error *)    
  | _ => throw err end.        


Section SemRec.
  
Context {E} {XI : LinstrE -< E} {XL: LinE -< E} {XE: ErrEvent -< E}. 

(* one-step semantics of instructions *)
Definition exec_linstr (ir : linstr_r) : itree E unit :=
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

(* iterative semantics body *)
Definition isem_linstr (lbl: remote_label) :
  itree E (remote_label + unit) := LCntr exec_linstr lbl.

(* iterative semantics of a program, from any starting point *)
Definition isem_liniter (lbl: remote_label) : itree E unit :=
  ITree.iter isem_linstr lbl.

(* iterative semantics of a function from its entry point *)
Definition isem_fun (fn: funname) : itree E unit :=
  isem_liniter (fn, xH).

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

Definition handle_lin {XE: ErrEvent -< E} {T} (e: LinE T) :
  itree E T := match e with
  | MatchExec (fn, lbl)%type =>
      s <- trigger (@Get lstate) ;;
      if (fn == s.(lfn)) && (Pos.to_nat lbl == s.(lpc))
      then Ret tt else throw err 
  | NewExec =>   
      s <- trigger (@Get lstate) ;;
      Ret (s.(lfn), Pos.of_nat (s.(lpc)))
  | IsFinal (fn, lbl)%type =>
      match (fenv fn) with
      | None => throw err
      | Some lc => Ret (size lc == Pos.to_nat lbl)
      end               
  end.
    
End Handle.


Section Interp.

Context {E: Type -> Type} {XE: ErrEvent -< E} {XS: @stateE lstate -< E}.

Definition interp_LinstrE {XL: LinE -< E} {A: Type}
  (t : itree (LinstrE +' E) A) : itree E A :=
  interp (ext_handler (@handle_linstr E XS XE XL)) t.

Definition interp_LinE {A: Type} 
  (t : itree (LinE +' E) A) : itree E A :=
  interp (ext_handler (@handle_lin E XS XE)) t.

End Interp.


Section FInterp.

Context {E: Type -> Type} {XE: ErrEvent -< E} {XS: @stateE lstate -< E}.

Definition up2state_lin_interp T 
  (t: itree (LinstrE +' LinE +' E) T) : itree E T :=
  interp_LinE (interp_LinstrE t).

End FInterp.


Require Import linearization.
Require Import it_cflow_sem it_effect_sem.
From ITree Require Import State StateFacts MonadState Rutt.
Require Import equiv_extras rutt_extras.


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
    let lin_sem := @up2state_lin_interp E2 XE2 XS2 _
                     (isem_liniter (fn, xH)%type) in
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
