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

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.

Require Import expr psem_defs psem_core it_exec rec_facts.
Require Export it_sems_core_defs eutt_extras.

Require Import List.

Import MonadNotation.
Local Open Scope monad_scope.

(*
Section WSW.
Context
  {asm_op: Type}
  {wsw: WithSubWord}
  {dc: DirectCall}
  {syscall_state : Type}
  {ep : EstateParams syscall_state}
  {spp : SemPexprParams}
  {wa: WithAssert}
  {sip : SemInstrParams asm_op syscall_state}
  {pT : progT}
  {scP : semCallParams}.

Record fstate := { fscs : syscall_state_t; fmem : mem; fvals : values }.


(**** Auxiliary definitions ******************************************)
Section CORE.
  
Context {E} {wE : ErrEvent -< E} (p : prog) (ev : extra_val_t).

Definition kget_fundef (funcs: fun_decls) (fn: funname) :
    ktree E fstate fundef :=
  fun _ => ioget ErrType (get_fundef funcs fn).

Definition iwrite_var (wdb : bool) (x : var_i) (v : value) (s : estate) :
    itree E estate :=
  iresult (write_var wdb x v s).

Definition iwrite_lval (wdb : bool) (gd : glob_decls) (x : lval)
    (v : value) (s : estate) : itree E estate :=
  iresult (write_lval wdb gd x v s).

Definition iwrite_lvals (wdb : bool) (gd : glob_decls) (xs : lvals)
    (vs : values) (s : estate) : itree E estate :=
  iresult (write_lvals wdb gd s xs vs).

Definition isem_pexprs (wdb : bool) (gd : glob_decls) (es: pexprs)
    (s : estate) : itree E values :=
  iresult (sem_pexprs wdb gd s es).

Definition sem_assgn  (x : lval) (tg : assgn_tag) (ty : atype) (e : pexpr)
    (s : estate) : exec estate :=
  Let v := sem_pexpr true (p_globs p) s e in
  Let v' := truncate_val (eval_atype ty) v in
  write_lval true (p_globs p) x v' s.

Definition fexec_syscall (o : syscall_t) (fs:fstate) : exec fstate :=
  Let: (scs, m, vs) := exec_syscall fs.(fscs) fs.(fmem) o fs.(fvals) in
  ok {| fscs := scs; fmem := m; fvals := vs |}.

Definition mk_fstate (vs:values) (s:estate) :=
  {| fscs := escs s; fmem:= emem s; fvals := vs |}.

Definition upd_estate wdb (gd : glob_decls) (xs:lvals) (fs : fstate)
    (s:estate) :=
  write_lvals wdb gd (with_scs (with_mem s fs.(fmem)) fs.(fscs)) xs fs.(fvals).

(*
Definition sem_syscall (xs : lvals) (o : syscall_t) (es : pexprs)
    (s : estate) : exec estate :=
  Let ves := sem_pexprs true (p_globs p) s es in
  Let fs := fexec_syscall o (mk_fstate ves s) in
  upd_estate true (p_globs p) xs fs s.
*)

Definition sem_cond (gd : glob_decls) (e : pexpr) (s : estate) : exec bool :=
  (sem_pexpr true gd s e >>= to_bool)%result.

Lemma sem_cond_sem_pexpr gd e s b :
  sem_cond gd e s = ok b -> sem_pexpr true gd s e = ok (Vbool b).
Proof. rewrite /sem_cond /=; by t_xrbindP=> _ -> /to_boolI ->. Qed.

Definition isem_cond (e : pexpr) (s : estate) : itree E bool :=
  iresult (sem_cond (p_globs p) e s).

Definition sem_bound (gd : glob_decls) (lo hi : pexpr) (s : estate) :
    exec (Z * Z) :=
  (Let vlo := sem_pexpr true gd s lo >>= to_int in
  Let vhi := sem_pexpr true gd s hi >>= to_int in
  ok (vlo, vhi))%result.

Definition isem_bound (lo hi : pexpr) (s : estate) : itree E (Z * Z) :=
  iresult (sem_bound (p_globs p) lo hi s).

Definition isem_assert (a: assertion) (s: estate) : itree E unit :=
  iresult (sem_assert (p_globs p) s a).

Definition sem_pre {dc: DirectCall} (P : prog) (fn:funname) (fs: fstate) :=
  if ~~assert_allowed then ok tt
  else if get_fundef (p_funcs P) fn is Some f then
    match f.(f_contract) with
    | Some ci =>
      Let vargs := mapM2 ErrType dc_truncate_val (map eval_atype f.(f_tyin)) fs.(fvals) in
      Let s := write_vars (~~direct_call) ci.(f_iparams) vargs (Estate fs.(fscs) fs.(fmem) Vm.init) in
      Let _ := mapM (sem_assert (p_globs P) s) ci.(f_pre) in
      ok tt
    | None => ok tt
    end
  else Error ErrType.

Definition isem_pre {dc : DirectCall} (fn : funname) (fs:fstate) : itree E unit :=
  iresult (sem_pre p fn fs).

Definition sem_post {dc: DirectCall} (P : prog) (fn:funname) (vargs' : values) (fs: fstate) :=
  if ~~assert_allowed then ok tt
  else if get_fundef (p_funcs P) fn is Some f then
    match f.(f_contract) with
    | Some ci =>
      Let vargs := mapM2 ErrType dc_truncate_val (map eval_atype f.(f_tyin)) vargs' in
      Let s := write_vars (~~direct_call) ci.(f_iparams) vargs (Estate fs.(fscs) fs.(fmem) Vm.init) in
      Let s :=  write_vars (~~direct_call) ci.(f_ires) fs.(fvals) s in
      Let _ := mapM (sem_assert (p_globs P) s) ci.(f_post) in
      ok tt
    | None => ok tt
    end
  else Error ErrType.

Definition isem_post {dc : DirectCall} (fn : funname) (vargs : values) (fr:fstate) : itree E unit :=
  iresult (sem_post p fn vargs fr).

End CORE.

End WSW.


*)

Lemma iter_rotate {E: Type -> Type} {A : Type}
    (D : A -> itree E A) (C : A -> itree E (A + A)) (a : A) :
  ITree.iter (fun a => D a >>= C) a
  ≈ D a >>= ITree.iter (fun a => C a >>= fun x =>
        match x with
        | inl a' => ITree.map inl (D a')
        | inr a' => Ret (inr a')
        end).
Proof.
  have -> :
    ITree.iter (fun a => D a >>= C) a
      ≈ ITree.iter (fun x =>
                      y <- ITree.map inl (D x) ;;
                      match y with
                      | inl a => C a
                      | inr b => Ret (inr b)
                      end) a.
  { apply: eutt_iter' => [?? -> | //].
    setoid_rewrite bind_map. reflexivity. }

  pose proof (iter_dinatural (C := Kleisli (itree E))
                (fun a => ITree.map inl (D a)) C a)
    as H.
  setoid_rewrite H.
  setoid_rewrite bind_map.
  reflexivity.
Qed.

Class AInstr (P S FS O FD CM: Type) : Type := mk_AInstr
  { AAssgn : P -> lval -> assgn_tag -> atype -> pexpr -> S -> exec S ;
    AOpn : P -> lvals -> assgn_tag -> O -> pexprs -> S -> exec S ;
    ASyscall : P -> syscall_t -> FS -> exec FS ;
    AAssert : P -> assertion -> S -> exec unit ;
    AEvalCond : P -> pexpr -> S -> exec bool ;
    AEvalBounds : P -> pexpr -> pexpr -> S -> exec (Z * Z) ;
    AWriteIndex : var_i -> Z -> S -> exec S ;
    AEvalArgs : P -> pexprs -> S -> exec values ;                
    AUpdateState : P -> lvals -> FS -> S -> exec S ;
    ASemPre : P -> funname -> FS -> exec unit ;
    ASemPost : P -> funname -> values -> FS -> exec unit ;
    AInitFuncall : P -> FD -> FS -> exec S ;
    AFinFuncall : FD -> S -> exec FS ;
    AGetFunDef : P -> funname -> FS -> exec FD ;
    AGetFunCode : FD -> CM ;
  }.


Section AUX_C.

Context {E: Type -> Type} {wE : exceptE error -< E}
        {S: Type} {wS : stateE S -< E}.

(* folding instruction semantics on commands (as there's no state,
   this could actually be simply map) *)
Definition isem_foldr {P A} (sem_i: P -> A -> itree E unit) (p: P)
  (c: list A) : itree E unit :=
  foldr (fun i k => sem_i p i ;; k) (Ret tt) c.

Definition itwrap (f: S -> itree E S) :
  itree E unit := s0 <- trigger (@Get S) ;; 
                  s1 <- f s0 ;; 
                  trigger (@Put S s1).              

Definition itlift (f: S -> exec S) :
  itree E unit := s0 <- trigger (@Get S) ;; 
                  s1 <- @iresult E wE S (f s0) ;; 
                  trigger (@Put S s1).              

Definition itliftG {A} (f: S -> exec A) :
  itree E A := s0 <- trigger (@Get S) ;; 
               @iresult E wE A (f s0).              

Definition itliftP (f: exec S) :
  itree E unit := s1 <- @iresult E wE S f ;; 
                  trigger (@Put S s1).              

End AUX_C.


Section WSW.

Context
  {asm_op: Type}
  {wsw: WithSubWord}
  {syscall_state : Type}
  {sip : SemInstrParams asm_op syscall_state}.    
Context {Mem FunDef Prog: Type}.

Record FState := mkFSt { FMem : Mem ; FVals : values }.

Record State := mkSt { EMem : Mem ; EVm : Vm.t }.

Notation StE := (stateE State).

Notation recCall := (callE (instr_info * funname * FState) FState).

(* Make global definition *)
Local Notation continue_loop := (ret (inl tt)).
Local Notation exit_loop := (ret (inr tt)).

Record xparams : Type := XParams {
  (* stack size limit *)                           
  xp_stack_sz : Z ;
  (* fresh allocation size limit *)                           
  xp_alloc_sz : Z ;
  (* output size limit *)                           
  xp_ret_sz : Z ;                           
  (* optional return address (output locations) *)                           
  xp_ret_loc : FState -> exec (option lvals) ;
  (* precondition on the size limits, output address and current memory *) 
  xp_pre : (option lvals) -> FState -> exec unit ;
  (* postcondition on validity of the return address, also comparing
     the fstates to check output and current memory size *) 
  xp_post : (option lvals) -> FState -> FState -> exec FState
}.                                                                       

Variant XCallEvent : Type -> Type :=
  | XCall : Z -> Z -> Z -> option lvals -> Mem -> XCallEvent FState.

Context (AI_Inst: AInstr Prog State FState sopn FunDef cmd). 

Notation interp_rec h := (interp (mrecursive h)).


Section SEM_C.

Context {E: Type -> Type} {wE : ErrEvent -< E}
        {wX : XCallEvent -< E} {wS : StE -< E}
        (sem_i: Prog -> instr -> itree E unit)
        (XPars : forall (p: Prog) (o: syscall_t), xparams)
        (p: Prog). 

Definition isem_for_round (i : var_i) (c : cmd) (w: Z) (k: itree E unit) :
  itree E unit :=
  itlift (AWriteIndex i w) ;; isem_foldr sem_i p c ;; k.

Definition isem_for_loop (i : var_i) (c : cmd) (ls : list Z) : itree E unit :=
  foldr (isem_for_round i c) (Ret tt) ls.

Definition isem_while_round (c1 : cmd) (e : pexpr) (c2 : cmd) :
  itree E (unit + unit) :=
  isem_foldr sem_i p c1 ;;
  b <- itliftG (AEvalCond p e) ;;
  if b then isem_foldr sem_i p c2 ;; continue_loop 
  else exit_loop.

Definition isem_while_loop (c1 : cmd) (e: pexpr) (c2: cmd) : itree E unit :=
  ITree.iter (fun _ => isem_while_round c1 e c2) tt.

Definition inner_fexec_xcall 
  (s_sz a_sz o_sz: Z) (xsp: option lvals)
  (o: syscall_t) (fs: FState) : itree E FState :=
  let m0 := FMem fs in
  trigger (XCall s_sz a_sz o_sz xsp m0).

Definition fexec_xcall (o : syscall_t) (fs: FState) :
  itree E FState :=
  let XP := XPars p o in  
  (* extract the output locations from the arguments *)
  xsp <- iresult (xp_ret_loc XP fs) ;; 
  iresult (xp_pre XP xsp fs) ;;
  (* executes the external function o in the fstate fs *)
  fs1 <- inner_fexec_xcall (xp_stack_sz XP) (xp_alloc_sz XP) (xp_ret_sz XP)
           xsp o fs ;;
  iresult (xp_post XP xsp fs fs1).

Definition sem_xcall (xs : lvals) (o : syscall_t) (es : pexprs)
    (s : State) : itree E State :=
  ves <- iresult (AEvalArgs p es s) ;;
  fs <- iresult (ASyscall p o (mkFSt (EMem s) ves)) ;;
(*  fs <- fexec_xcall p o (mkFSt (EMem s) ves) ;; *)
  iresult (AUpdateState p xs fs s).

Lemma interp_throw {D} (h: D ~> itree (D +' E)) T (e: error) :
  interp_rec h (throw (X:=T) e) ≈ throw e.
Proof. rewrite interp_vis bind_trigger; apply eqit_Vis => -[]. Qed.

End SEM_C.   

(*

Section With_program.

Context (p: Prog).  
Context {XPars : forall (o: syscall_t), xparams}.
Context {GetFunCode : FunDef -> cmd}.                                        


Section SEM_C.

Context {E: Type -> Type} {wE : ErrEvent -< E}
        {wX : XCallEvent -< E} {wS : StE -< E}.

(*
(* recCall trigger *)
Definition rec_call (ii : instr_info) (f : funname) (fs : FState) :
   itree (recCall +' E) FState := trigger_inl1 (Call (ii, f, fs)).
*)

Definition isem_for_round (sem_i: Prog -> instr -> itree E unit)
  (i : var_i) (c : cmd) (w: Z) (k: itree E unit) : itree E unit :=
  itlift (AWriteIndex i w) ;; isem_foldr sem_i c ;; k.

Definition isem_for_loop {sem_i: Prog -> instr -> itree E unit}
   (p: Prog) (i : var_i) (c : cmd) (ls : list Z) : itree E unit :=
  foldr (@isem_for_round sem_i p i c) (Ret tt) ls.

Definition isem_while_round {sem_i: Prog -> instr -> itree E unit}
   (p: Prog) (c1 : cmd) (e : pexpr) (c2 : cmd) : itree E (unit + unit) :=
  @isem_foldr sem_i p c1 ;;
  b <- itliftG (AEvalCond p e) ;;
  if b then @isem_foldr sem_i p c2 ;; continue_loop 
  else exit_loop.

Definition isem_while_loop {sem_i: Prog -> instr -> itree E unit}
   (p: Prog) (c1 : cmd) (e: pexpr) (c2: cmd) : itree E unit :=
  ITree.iter (fun _ => @isem_while_round sem_i p c1 e c2) tt.

Definition inner_fexec_xcall 
  (s_sz a_sz o_sz: Z) (xsp: option lvals)
  (o: syscall_t) (fs: FState) : itree E FState :=
  let m0 := FMem fs in
  trigger (XCall s_sz a_sz o_sz xsp m0).

Definition fexec_xcall (p: Prog) (o : syscall_t) (fs: FState) :
  itree E FState :=
  let XP := XPars p o in  
  (* extract the output locations from the arguments *)
  xsp <- iresult (xp_ret_loc XP fs) ;; 
  iresult (xp_pre XP xsp fs) ;;
  (* executes the external function o in the fstate fs *)
  fs1 <- inner_fexec_xcall (xp_stack_sz XP) (xp_alloc_sz XP) (xp_ret_sz XP)
           xsp o fs ;;
  iresult (xp_post XP xsp fs fs1).

Definition sem_xcall (p: Prog) (xs : lvals) (o : syscall_t) (es : pexprs)
    (s : State) : itree E State :=
  ves <- iresult (AEvalArgs p es s) ;;
  fs <- iresult (ASyscall p o (mkFSt (EMem s) ves)) ;;
(*  fs <- fexec_xcall p o (mkFSt (EMem s) ves) ;; *)
  iresult (AUpdateState p xs fs s).

End SEM_C.   

*)


(**** Abstract semantics **********************************************)
Section SEM_I.

Context {E: Type -> Type} {wE : ErrEvent -< E}
        {wX : XCallEvent -< E} {wS : StE -< E} 
        (XPars : forall (p: Prog) (o: syscall_t), xparams).

(* semantics of instructions, abstracting on function calls (through
   sem_fun) *)
Fixpoint isem_i_body (p : Prog) (i : instr) : itree (recCall +' E) unit :=
  let: (MkI ii i) := i in
  match i with
  | Cassgn x tg ty e => itlift (AAssgn p x tg ty e)

  | Copn xs tg o es => itlift (AOpn p xs tg o es)

  | Csyscall xs o es => itwrap (sem_xcall p xs o es)

  | Cassert a => itliftG (AAssert p a)

  | Cif e c1 c2 => b <- itliftG (AEvalCond p e) ;;
                   isem_foldr isem_i_body p (if b then c1 else c2) 

  | Cwhile a c1 e i c2 =>
    isem_while_loop isem_i_body p c1 e c2 

  | Cfor i (d, lo, hi) c =>     
    bounds <- itliftG (AEvalBounds p lo hi) ;;
    isem_for_loop isem_i_body p i c (wrange d bounds.1 bounds.2) 

  | Ccall xs fn args =>
    s0 <- trigger (@Get State) ;;  
    vargs <- iresult (AEvalArgs p args s0) ;;
    let fs0 := mkFSt (EMem s0) vargs in  
    iresult (ASemPre p fn fs0) ;; 
    fs1 <- trigger_inl1 (Call (ii, fn, fs0)) ;; 
    iresult (ASemPost p fn vargs fs1) ;;
    itliftP (AUpdateState p xs fs1 s0)
  end.
(* similar, for commands *)
Definition isem_cmd := isem_foldr isem_i_body.

Lemma fold_cmd (p : Prog) c:
  isem_cmd p c = isem_foldr isem_i_body p c.
Proof. by reflexivity. Qed. 

(* similar, for proper function calls *)
Definition isem_fun_body (p : Prog) (fn : funname) (fs0 : FState) :
  itree (recCall +' E) FState :=
   fd <- iresult (AGetFunDef p fn fs0) ;;
   let sinit := mkSt fs0.(FMem) Vm.init in
   iresult (ASemPre p fn fs0) ;;
   itliftP (AInitFuncall p fd fs0) ;;
   isem_cmd p (AGetFunCode fd) ;;
   fs1 <- itliftG (AFinFuncall fd) ;;
   iresult (ASemPost p fn fs1.(FVals) fs1) ;;
   Ret fs1.

(************************************************************)
(* full function semantics *)

(* handler of recCall events *)
Definition handle_recc (p: Prog) : recCall ~> itree (recCall +' E) :=
 fun T (rc : recCall T) =>
   match rc with
   | Call (ii, fn, fs) => isem_fun_body p fn fs
   end.

(* intepreter of recCall events *)
Definition interp_recc p T (t: itree (recCall +' E) T) : itree E T :=
  interp_mrec (handle_recc p) t.

(* recCall interpreter of instructions *)
Definition denote_instr p (i: instr) : itree E unit :=
  interp_recc p (isem_i_body p i).

(* recCall interpreter of commands *)
Definition denote_cmd p (c: cmd) : itree E unit :=
  interp_recc p (isem_cmd p c).

(* recCall interpreter of function calls (corresponds to: isem_fun) *)
Definition denote_fun p (fn : funname) (fs : FState) : itree E FState :=
  interp_recc p (isem_fun_body p fn fs).

(* function semantics, expressed with rec rather than interp_mrec *)
Definition denote_fun' p ii (fn : funname) (fs : FState) : itree E FState :=
  rec (fun x => isem_fun_body p (snd (fst x)) (snd x)) (ii, fn, fs). 

(* corresponds to: isem_fun_body with the sem_fun_full instance *) 
Definition denote_fcall p (fn : funname) (fs0 : FState) :
  itree E FState :=
   fd <- iresult (AGetFunDef p fn fs0) ;;
   let sinit := mkSt fs0.(FMem) Vm.init in
   iresult (ASemPre p fn fs0) ;;
   itliftP (AInitFuncall p fd fs0) ;;
   denote_cmd p (AGetFunCode fd) ;;
   fs1 <- itliftG (AFinFuncall fd) ;;
   iresult (ASemPost p fn fs1.(FVals) fs1) ;;
   Ret fs1.

(* recCall trigger *)
Definition rec_call (ii : instr_info) (f : funname) (fs : FState) :
   itree (recCall +' E) FState := trigger_inl1 (Call (ii, f, fs)).


(********************************************************************)
(* blank function semantics *)

Definition rec_call' ii (f : funname) (fs : FState) :
   itree (recCall +' E) FState := trigger_inl1 (Call (ii, f, fs)).

(* fully blank semantics (does nothing) *)
Definition denote_fun_blank' ii (fn : funname) (fs : FState) : itree E FState :=
  rec (fun x => rec_call' (fst (fst x)) (snd (fst x)) (snd x)) (ii, fn, fs). 

(* blank handler of recCall events *)
Definition handle_recc_blank : recCall ~> itree (recCall +' E) :=
 fun T (rc : recCall T) =>
   match rc with
   | Call (ii, fn, fs) => trigger_inl1 (Call (ii, fn, fs))
   end.

(* uninterpreted function semantics *)
Definition denote_fun_blank p (fn : funname) (fs : FState) : itree E FState :=
  interp_mrec handle_recc_blank (isem_fun_body p fn fs).

(**********************************************************************)

(*
Lemma denote_fun_eutt p ii (fn : funname) (fs : FState) :
  eutt eq (denote_fun' p ii fn fs) (denote_fun p fn fs).
Proof. by reflexivity. Qed.  
*)

Lemma isem_cmd_cons p i c :
  eutt eq (isem_cmd p (i :: c))
          (isem_i_body p i ;; isem_cmd p c).       
Proof. by reflexivity. Qed.

Lemma isem_cmd_cat p c1 c2 :
  eutt eq (isem_cmd p (c1 ++ c2))
          (isem_cmd p c1 ;; isem_cmd p c2).       
Proof.
  induction c1; simpl.
  - rewrite bind_ret_l; reflexivity.     
  - setoid_rewrite bind_bind.
    setoid_rewrite IHc1; reflexivity.
Qed.

Lemma denote_cmd_cons p i c :
  eutt eq (denote_cmd p (i :: c))
          (denote_instr p i ;; denote_cmd p c).       
Proof.
  setoid_rewrite interp_mrec_as_interp; simpl.
  setoid_rewrite interp_bind; reflexivity.
Qed.

Lemma denote_cmd_cat p c1 c2 :
  eutt eq (denote_cmd p (c1 ++ c2))
          (denote_cmd p c1 ;; denote_cmd p c2).       
Proof.
  unfold denote_cmd, interp_recc; simpl.
  setoid_rewrite interp_mrec_as_interp; simpl.
  setoid_rewrite isem_cmd_cat; simpl.
  setoid_rewrite interp_bind; reflexivity.
Qed.
  
Lemma denote_cmd_cat' p c1 c2 :
  eutt eq (denote_cmd p (c1 ++ c2))
          (denote_cmd p c1 ;; denote_cmd p c2).       
Proof.
  induction c1; simpl.
  - unfold denote_cmd at 2; simpl.
    setoid_rewrite interp_mrec_as_interp; simpl.
    setoid_rewrite interp_ret.
    setoid_rewrite bind_ret_l; reflexivity.
  - setoid_rewrite <- app_comm_cons; simpl.
    setoid_rewrite interp_mrec_as_interp; simpl.
    setoid_rewrite interp_bind.
    setoid_rewrite bind_bind.
    eapply eqit_bind; try reflexivity.
    unfold pointwise_relation; intros _.
    setoid_rewrite <- interp_mrec_as_interp; auto.
Qed.
  
Lemma isem_cmd_while p ii al c e inf c':
  isem_cmd p [:: MkI ii (Cwhile al c e inf c')] 
  ≈
  isem_cmd p (c ++ [:: MkI ii (Cif e (c' ++ [:: MkI ii (Cwhile al c e inf c')])
                               [::])]).
Proof.
  rewrite isem_cmd_cat. 
  unfold isem_cmd at 1; simpl.
  unfold isem_while_loop; simpl.
  setoid_rewrite bind_ret_r_unit.
  setoid_rewrite unfold_iter; simpl.
  unfold isem_while_round; simpl.
  setoid_rewrite bind_bind.
  eapply eqit_bind; try reflexivity.
  move=> []; simpl.
  unfold itliftG at 1; simpl.
  setoid_rewrite bind_bind.
  setoid_rewrite bind_bind.
  eapply eqit_bind; try reflexivity.
  move=> st.
  eapply eqit_bind; try reflexivity.
  move=> [|]; simpl.
  - setoid_rewrite bind_bind.    
    setoid_rewrite <- fold_cmd at 2.
    rewrite isem_cmd_cat.
    eapply eqit_bind; try reflexivity.
    move=> []; simpl.
    setoid_rewrite bind_ret_l.
    eapply eqit_Tau_l.
    setoid_rewrite bind_ret_r_unit; reflexivity.  
  - setoid_rewrite bind_ret_l; reflexivity.
Qed.    
   
Lemma denote_cmd_while p ii al c e inf c':
  denote_cmd p [:: MkI ii (Cwhile al c e inf c')] 
  ≈
  denote_cmd p (c ++
       [:: MkI ii (Cif e (c' ++ [:: MkI ii (Cwhile al c e inf c')]) [::])]).
Proof.
  unfold denote_cmd, interp_recc.
  setoid_rewrite interp_mrec_as_interp.
  setoid_rewrite isem_cmd_while; reflexivity.
Qed.  

(*
Notation interp_rec p := (interp (mrecursive (handle_recc p))).

Lemma interp_throw p T e : interp_rec p (throw (X:=T) e) ≈ throw e.
Proof. rewrite interp_vis bind_trigger; apply eqit_Vis => -[]. Qed.
*)

Lemma interp_ioget p Err T (o : option T) :
  eutt (E:=E) eq (interp_rec (handle_recc p) (ioget Err o)) (ioget Err o).
Proof.
  case o => /= [? | ].
  + rewrite interp_ret; reflexivity.
  apply interp_throw.
Qed.

Lemma interp_iresult p T (r : exec T) :
  eutt (E:=E) eq (interp (mrecursive (handle_recc p)) (iresult r)) (iresult r).
Proof.
  case r => /= [? | ?].
  + rewrite interp_ret; reflexivity.
  apply interp_throw.
 Qed.

Lemma interp_itliftP p (r : exec State) :
  eutt (E:=E) eq (interp (mrecursive (handle_recc p)) (itliftP r)) 
                 (itliftP r).
Proof.
  unfold itliftP; rewrite interp_bind.
  eapply eqit_bind.
  eapply interp_iresult.
  move=> st; setoid_rewrite interp_trigger; simpl; reflexivity.
Qed.

Lemma interp_itliftG p T (r : State -> exec T) :
  eutt (E:=E) eq (interp (mrecursive (handle_recc p)) (itliftG r)) 
                 (itliftG r).
Proof.
  unfold itliftG; rewrite interp_bind.
  eapply eqit_bind.
  setoid_rewrite interp_trigger; simpl; reflexivity.
  move=> st.
  eapply interp_iresult.
Qed.

Lemma isem_while_rotate p cdo cwh e :
  isem_while_loop isem_i_body p cdo e cwh
  ≈ isem_foldr isem_i_body p cdo ;; isem_while_loop isem_i_body p [::] e (cwh ++ cdo).
Proof.
  rewrite /isem_while_loop.
  etransitivity.
  + by apply iter_rotate.

  apply eutt_eq_bind => [].
  move=> [].
  apply: eutt_iter'; last reflexivity.
  move=> [] [] _.
  rewrite /isem_while_round /= bind_ret_l bind_bind.
  eapply eutt_eq_bind => -[]; last by rewrite bind_ret_l; reflexivity.
  setoid_rewrite isem_cmd_cat.
  rewrite bind_bind.
  setoid_rewrite bind_ret_l.
  rewrite -/isem_cmd bind_bind.
  eapply eutt_eq_bind.
  move=> []; unfold ITree.map.
  eapply eutt_eq_bind.
  move=> []; reflexivity.
Qed.
  
Lemma isem_cmd_while_rotate p ii al c e inf c':
  isem_cmd p [:: MkI ii (Cwhile al c e inf c')] 
    ≈
    isem_cmd p (c ++ [:: MkI ii (Cwhile al [::] e inf (c' ++ c))]).
Proof.
  rewrite isem_cmd_cat /= isem_while_rotate /= bind_bind.
  apply eutt_eq_bind.
  reflexivity.
Qed.

Lemma interp_isem_cmd (p: Prog) c :
  eutt (E:=E) eq (interp_recc p (isem_cmd p c))
    (isem_foldr denote_instr p c).
Proof.
   set (Pr := fun ir => forall ii,
       eutt (E:=E) eq (interp_recc p (isem_i_body p (MkI ii ir)))
         (denote_instr p (MkI ii ir))).
    set (Pi := fun i => 
       eutt (E:=E) eq (interp_recc p (isem_i_body p i))
                      (denote_instr p i)).
    set (Pc := fun c => 
       eutt (E:=E) eq (interp_recc p (isem_cmd p c))
                      (isem_foldr denote_instr p c)).
    apply: (cmd_rect (Pr:=Pr) (Pi:=Pi) (Pc:=Pc));
    clear c; subst Pr Pi Pc; simpl; try (intros; reflexivity).
  - setoid_rewrite interp_mrec_as_interp.
    setoid_rewrite interp_ret; reflexivity.
  - intros i c H H0.
    setoid_rewrite interp_mrec_as_interp; simpl.
    setoid_rewrite interp_bind.
    eapply eqit_bind.
    setoid_rewrite <- interp_mrec_as_interp; reflexivity.
    unfold pointwise_relation; intro u; destruct u.
    rewrite <- H0.
    setoid_rewrite <- interp_mrec_as_interp; reflexivity.
Qed.    

Lemma isem_call_unfold p (fn : funname) (fs : FState) :
  denote_fun p fn fs ≈ denote_fcall p fn fs.
Proof.
  unfold denote_fun, interp_recc, denote_fcall.
  setoid_rewrite interp_mrec_as_interp.
  unfold isem_fun_body.
  rewrite interp_bind.
  eapply eqit_bind; first by eapply interp_iresult.
  move=> fd; setoid_rewrite interp_bind.
  eapply eqit_bind; first by eapply interp_iresult.
  move=> [].
  rewrite interp_bind.
  eapply eqit_bind.
  eapply interp_itliftP.
  move=> [].
  rewrite interp_bind.
  eapply eqit_bind; try reflexivity.
  move=> [].
  rewrite interp_bind.
  eapply eqit_bind.
  eapply interp_itliftG.
  move=> fs1.
  rewrite interp_bind.
  eapply eqit_bind; first by eapply interp_iresult.
  move=> [].
  rewrite interp_ret; reflexivity.
Qed.  
  

Section Inline.

(* inline info is included in FState *)  
Context {do_inline : funname (* caller *) ->
    instr_info -> funname (* callee *) -> FState -> bool}.

(* conditional inliner action *)
Definition inliner
 (ctx : forall T : Type, recCall T -> itree (recCall +' E) T)
 (caller: funname) ii (callee: funname) (fs: FState) :
  itree (recCall +' E) FState :=
  if do_inline caller ii callee fs then ctx FState (Call (ii, callee, fs))
(* Interpret the top call but not the inner ones *)
     else trigger_inl1 (E:=E) (Call (ii, callee, fs)).
(* Do not interpret the call, simply retrigger the event *)

(* given the caller Name and the callee Event, lifts inliner to a
   handler with polymorphic return type *)
Definition inline_handleNE
  (ctx : forall T : Type, recCall T -> itree (recCall +' E) T)
  (caller: funname) T (cle: recCall T) : itree (recCall +' E) T :=
  match cle with
  | Call (ii, fn, fs) => inliner ctx caller ii fn fs end. 

(* similar, given caller Event and callee Event *)
Definition inline_handleEE
  (ctx : forall T : Type, recCall T -> itree (recCall +' E) T)
  T1 (clr: recCall T1) T2 (cle: recCall T2) : itree (recCall +' E) T2 :=
  match clr with
  | Call (_, caller, _) => inline_handleNE ctx caller cle end. 

(* folds the inliner on an itree *)
Definition inline_handleE 
        (ctx : forall T : Type, recCall T -> itree (recCall +' E) T)
        (T1 : Type) (d1 : recCall T1) :
  itree (recCall +' E) ~> itree (recCall +' E) := 
  interp (ext_r_handler (inline_handleEE ctx d1)).

(* the proper inline handler: given a caller, it inteprets its body
   with the inliner *) 
Definition inline_handle 
        (ctx : forall T : Type, recCall T -> itree (recCall +' E) T)
        (T1 : Type) (d1 : recCall T1) : itree (recCall +' E) T1 := 
  (inline_handleE ctx d1) T1 (ctx T1 d1).

(* makes the definition concrete *)
Definition inline_handle_recc p : forall (T1 : Type) (d1 : recCall T1),
  itree (recCall +' E) T1 := inline_handle (handle_recc p).

Lemma isem_call_inline p T (e: recCall T) :
  mrec (handle_recc p) e ≈ mrec (inline_handle_recc p) e.
Proof.
  unfold handle_recc, inline_handle_recc.  
  set cond := fun  T1 (d1: recCall T1) T2 (d2: recCall T2) =>
    match d1, d2 with
    | Call (_, caller, _), Call (ii, callee, fs) =>
        do_inline caller ii callee fs
    end.
  rewrite (mrec_loop2 cond).
  set F := (X in ctx2_cond _ X).  
  set G := (inline_handle _).
  assert (forall T0 (e0: recCall T0),
             eutt eq (ctx2_cond cond F e0) (G _ e0)) as H1.
  { intros T0 [[fn0 fs0]]; subst F G cond.
    unfold ctx2_cond, Handler.cat, ctx_cond, Handler.case_,
      inline_handle, inline_handleE, ext_r_handler,
      inline_handleEE, inline_handleNE, handle_recc, inliner; simpl.
    eapply eutt_interp; try reflexivity.
    unfold eq2, Eq2_Handler, eutt_Handler, Relation.i_pointwise.
    intros T1 [[[fn1 fs1]] | e1]; simpl; try reflexivity.
    destruct fn0; destruct fn1; simpl. reflexivity.
  }
  unfold mrec; eapply Proper_interp_mrec; eauto.
Qed.
    
End Inline.  

End SEM_I.

End WSW.


