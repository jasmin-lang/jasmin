From ITree Require Import
     ITree 
     ITreeFacts 
     Events.Exception
     Interp.Recursion.

From mathcomp Require Import ssreflect ssrbool. 

From Jasmin Require Import expr psem_defs psem. 
From Jasmin Require Import it_gen_lib it_exec.

Import MonadNotation. 
Local Open Scope monad_scope. 

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(**** This files contains semantic models for Jasmin, distinguished by
use of either event-based or fixpoint-based recursion *)

(**** ERROR SEMANTICS *******************************************)
Section Errors.

(* error events, based on error_data errors *)
Definition ErrEvent : Type -> Type := exceptE error_data.

(* maps ErrEvent events to the execS datatype *)
(* execT (itree E) R = itree E (execS R) *)
Definition handle_Err {E} : ErrEvent ~> execT (itree E) :=
  fun _ e =>
    match e with
    | Throw e' => Ret (ESerror _ e')
    end.

(* ErrEvent handler *)
Definition ext_handle_Err {E: Type -> Type} :
  ErrEvent +' E ~> execT (itree E) :=
  fun _ e =>
  match e with
  | inl1 e' => handle_Err e'
  | inr1 e' => Vis e' (pure (fun x => ESok x)) end.

(* ErrEvent interpreter *)
Definition interp_Err {E: Type -> Type} {A}
  (t: itree (ErrEvent +' E) A) : execT (itree E) A :=
  interp_exec ext_handle_Err t.

(*** auxiliary error functions *)

Definition ioget {E: Type -> Type} `{ErrEvent -< E} {V}
  (err: error_data) (o: option V) : itree E V :=
  match o with
  | Some v => Ret v
  | None => throw err
  end.

Definition err_result {E: Type -> Type} `{ErrEvent -< E}
  (Err : error -> error_data) : result error ~> itree E :=
  fun _ t => match t with
             | Ok v => Ret v
             | Error e => throw (Err e) end.

End Errors.


(**** JASMIN SEMANTICS *******************************************)
Section WSW.
Context
  {asm_op: Type}
  {asmop: asmOp asm_op}
  {wsw: WithSubWord}
  {dc: DirectCall}
  {syscall_state : Type}
  {ep : EstateParams syscall_state}
  {spp : SemPexprParams}
  {sip : SemInstrParams asm_op syscall_state}
  {pT : progT}
  {scP : semCallParams}
  (pr : prog)
  (ev : extra_val_t).

Local Notation pglobs := (p_globs pr).

(*** jasmin abbreviations *)

Definition eval_assgn
   (x: lval) (tg: assgn_tag) (ty: stype) (e: pexpr)
   (st1: estate) : exec estate :=
  (Let v := sem_pexpr true (p_globs pr) st1 e in
   Let v' := truncate_val ty v in
   write_lval true (p_globs pr) x v' st1).

Definition eval_syscall
   (xs: lvals) (o: syscall_t)
   (es: pexprs) (s: estate) : exec estate :=
  Let ves := sem_pexprs true (p_globs pr) s es in
  Let: (scs, m, vs) := exec_syscall s.(escs) s.(emem) o ves in
  write_lvals true (p_globs pr)
     (with_scs (with_mem s m) scs) xs vs.

(* dummy definition to match error_data (the state is not used yet) *)
Definition mk_error_data (s:estate) (e:error) : error_data := (e, tt).

(* build our state-sensitive errors *)
Definition mk_errtype : estate -> error_data :=
  fun s => mk_error_data s ErrType.

(*** lifting instruction to itrees *)

Definition iresult {E} `{ErrEvent -< E} {T} (s:estate) (F : exec T) :
    itree E T :=
  err_result (mk_error_data s) F.

Definition iget_fundef {E} `{ErrEvent -< E}
    (fn: funname) (s:estate) : itree E fundef :=
  ioget (mk_errtype s) (get_fundef (p_funcs pr) fn).

Definition iwrite_var {E} `{ErrEvent -< E}
    (wdb : bool) (x : var_i) (v : value) (s : estate) : itree E estate :=
  iresult s (write_var wdb x v s).

Definition iwrite_lval {E} `{ErrEvent -< E}
    (wdb : bool) (gd : glob_decls) (x : lval) (v : value) (s : estate) :
    itree E estate :=
  iresult s (write_lval wdb gd x v s).

Definition iwrite_lvals {E} `{ErrEvent -< E}
    (wdb : bool) (gd : glob_decls) (s : estate) (xs : lvals) (vs : values) :
    itree E estate :=
  iresult s (write_lvals wdb gd s xs vs).

Definition isem_pexpr {E} `{ErrEvent -< E}
    (wdb : bool) (gd : glob_decls) (s : estate) (e: pexpr) : itree E value :=
  iresult s (sem_pexpr wdb gd s e).

Definition isem_pexprs {E} `{ErrEvent -< E}
    (wdb : bool) (gd : glob_decls) (s : estate) (es: pexprs) : itree E values :=
  iresult s (sem_pexprs wdb gd s es).

(* Auxiliary functions for recursion on list (seq) *)
Fixpoint isem_ir_map {E} (R: instr_r -> estate -> itree E estate)
   (c: cmd) (st: estate) : itree E estate :=
  match c with
  | nil => Ret st
  | (MkI _ i) :: c' => st' <- R i st ;; isem_ir_map R c' st'
  end.

Fixpoint isem_i_map {E} (R: instr -> estate -> itree E estate)
   (c: cmd) (st: estate) : itree E estate :=
  match c with
  | nil => Ret st
  | i :: c' => st' <- R i st ;; isem_i_map R c' st'
  end.

(* function call info record *)
Record fstate := mk_fstate
      { fscs : syscall_state_t; fmem : mem; fvals : values }.

(**********************************************************************)
(*** error-aware interpreter with mutual recursion *)


Notation it_continue_loop st := (ret (inl st)).
Notation it_exit_loop st := (ret (inr st)).
Notation it_rec_call := (trigger_inl1).

Definition isem_cond {E} `{ErrEvent -< E} (e:pexpr) (s: estate) :
    itree E bool :=
  iresult s (sem_pexpr true pglobs s e >>r= to_bool).

Definition isem_bound {E} `{ErrEvent -< E} (e:pexpr) (s: estate) :
    itree E Z :=
  iresult s (sem_pexpr true pglobs s e >>r= to_int).

Section REC_sem.

Fixpoint isem_for_body {E} `{ErrEvent -< E}
   (RL : instr -> estate -> itree E estate)
   (i: var_i) (c: cmd)
   (ls: list Z) (s: estate) : itree E estate :=
  match ls with
  | nil => ret s
  | (w :: ws) =>
    s <- iwrite_var true i (Vint w) s;;
    s <- isem_i_map RL c s;;
    isem_for_body RL i c ws s
  end.
  
Definition isem_while_body {E} `{ErrEvent -< E}
   (RC : instr -> estate -> itree E estate)
   (c1 : cmd) (e:pexpr) (c2: cmd) (s1 : estate) : itree E (estate + estate) :=
   s2 <- isem_i_map RC c1 s1 ;;
   b <- isem_cond e s2 ;;
   if b then s3 <- isem_i_map RC c2 s2 ;; it_continue_loop s3
   else it_exit_loop s2.

Definition isem_while {E} `{ErrEvent -< E}
   (RC : instr -> estate -> itree E estate)
   (c1 : cmd) (e:pexpr) (c2: cmd) (s1 : estate) : itree E estate :=
  ITree.iter (isem_while_body RC c1 e c2) s1.

Definition isem_call {E} `{ErrEvent -< E}
    (RC: funname -> fstate -> itree E fstate)                  
    (xs: lvals) (fn: funname) (args: pexprs) (s1: estate) :
    itree E estate :=
  vargs <- isem_pexprs  (~~direct_call) pglobs s1 args ;;
  r <- RC fn (mk_fstate (escs s1) (emem s1) vargs) ;;
  iwrite_lvals (~~direct_call) pglobs
       (with_scs (with_mem s1 r.(fmem)) r.(fscs)) xs r.(fvals).

(* isem_i_body *)
Fixpoint isem_instrF {E} `{ErrEvent -< E}
   (RC : funname -> fstate -> itree E fstate)
   (i: instr) (s1: estate) : itree E estate :=
  let sem_i := isem_instrF RC in
  let sem_cmd := isem_i_map sem_i in
  let: (MkI _ i) := i in
  match i with
  | Cassgn x tg ty e => iresult s1 (eval_assgn x tg ty e s1)
  | Copn xs tg o es => iresult s1 (sem_sopn pglobs o s1 xs es)
  | Csyscall xs o es => iresult s1 (eval_syscall xs o es s1)

  | Cif e c1 c2 =>
    b <- isem_cond e s1;;
    sem_cmd (if b then c1 else c2) s1

  | Cwhile a c1 e c2 =>
    isem_while sem_i c1 e c2 s1

  | Cfor i (d, lo, hi) c =>
    vlo <- isem_bound lo s1 ;;
    vhi <- isem_bound hi s1 ;;
    isem_for_body sem_i i c (wrange d vlo vhi) s1

  | Ccall xs fn args => isem_call RC xs fn args s1
  end.                                

Definition estate0 (fs : fstate) :=
  Estate fs.(fscs) fs.(fmem) Vm.init.

Definition initialize_fcall (fd:fundef) (fs:fstate) : exec estate :=
  let sinit := estate0 fs in
  Let vargs' := mapM2 ErrType dc_truncate_val fd.(f_tyin) fs.(fvals) in
  Let s0 := init_state fd.(f_extra) (p_extra pr) ev sinit in
  write_vars (~~direct_call) fd.(f_params) vargs' s0.

Definition finalize_fcall (fd : fundef) (s:estate) :=
  Let vres := get_var_is (~~ direct_call) s.(evm) fd.(f_res) in
  Let vres' := mapM2 ErrType dc_truncate_val fd.(f_tyout) vres in
  let scs := s.(escs) in
  let m := finalize fd.(f_extra) s.(emem) in
  ok {| fscs := scs; fmem := m; fvals := vres' |}.

Definition isem_fcall_bodyF {E} `{ErrEvent -< E}
   (RC : funname -> fstate -> itree E fstate)
   (fn : funname) (fs:fstate) : itree E fstate :=
  (* FIXME: this is durty : sinit*)
  let sinit := estate0 fs in
  fd <- iget_fundef fn sinit;;
  s1 <- iresult sinit (initialize_fcall fd fs);;
  s2 <- isem_i_map (isem_instrF RC) fd.(f_body) s1;;
  iresult s2 (finalize_fcall fd s2).

Notation CALL := (callE (funname * fstate) fstate).

(* rec_call *)
Definition trigger_call {E}
    (fn: funname) (fc: fstate) : itree (CALL +' E) fstate :=
  trigger (Call (fn, fc)).

(* isem_i_rec *)
Definition isem_instr {E} `{ErrEvent -< E} (i : instr) (s1: estate) : itree (CALL +' E) estate :=
  isem_instrF trigger_call i s1.

Definition isem_cmd {E} `{ErrEvent -< E} (c : cmd) (s : estate) :
  itree (CALL +' E) estate :=
  isem_i_map isem_instr c s.

(* isem_call_rec *)
Definition isem_fcall_body {E} `{ErrEvent -< E} :                       
   funname -> fstate -> itree (CALL +' E) fstate :=
  isem_fcall_bodyF trigger_call .

Definition isem_fcall_body' {E} `{ErrEvent -< E} (x: funname * fstate) : itree (CALL +' E) fstate :=
  isem_fcall_body (fst x) (snd x).

(* interp_recCall *)
Definition handle_fcall {E} `{ErrEvent -< E} : CALL ~> itree (CALL +' E) :=
  calling' isem_fcall_body'.

(* isem_call *)
Definition isem_fcall {E} `{ErrEvent -< E}
   (fn : funname) (fs : fstate) : itree E fstate :=
  rec isem_fcall_body' (fn, fs).

(* isem_i *)
Definition isem_flat_instr {E} `{ErrEvent -< E} (i : instr) (s : estate) :
  itree E estate :=
  isem_instrF isem_fcall i s.

(* isem_cmd *)
Definition isem_flat_cmd {E} `{ErrEvent -< E} (c : cmd) (s : estate) :
  itree E estate :=
  isem_i_map isem_flat_instr c s.

(* sem_call *)
Definition final_isem_call (fn : funname) (fs : fstate) :
  execT (itree void1) (fstate) :=
  interp_Err (isem_fcall fn fs).

Lemma interp_ioget {E : Type -> Type} `{ErrEvent -< E} Err T (o : option T) :
  eutt (E:=E) eq (interp (mrecursive (D:=CALL) handle_fcall) (ioget Err o))
                 (ioget Err o).
Proof.
  case o => /=.
  + move=> ?; rewrite interp_ret; reflexivity.
  rewrite interp_vis bind_trigger.
  by apply eqit_Vis => -[].
Qed.

Lemma interp_iresult {E : Type -> Type} `{ErrEvent -< E} s T (r : exec T) :
  eutt (E:=E) eq (interp (mrecursive (D:=CALL) handle_fcall) (iresult s r)) (iresult s r).
Proof.
  case r => /=.
  + move=> ?; rewrite interp_ret; reflexivity.
  move=> e; rewrite interp_vis bind_trigger.
  by apply eqit_Vis => -[].
Qed.

Lemma interp_isem_cmd {E} `{ErrEvent -< E} c s :
  eutt (E:=E) eq
    (interp (mrecursive handle_fcall) (isem_cmd c s))
    (isem_flat_cmd c s).
Proof.
  apply: (cmd_rect
    (Pr := fun ir => forall ii s,
               eutt (E:=E) eq (interp (mrecursive handle_fcall) (isem_instr (MkI ii ir) s))
                              (isem_flat_instr (MkI ii ir) s))
    (Pi := fun i => forall s,
       eutt (E:=E) eq (interp (mrecursive handle_fcall) (isem_instr i s))
                      (isem_flat_instr i s))
    (Pc := fun c => forall s,
       eutt (E:=E) eq (interp (mrecursive handle_fcall) (isem_cmd c s))
                      (isem_flat_cmd c s))) c s => //=.
  + move=> s; rewrite interp_ret; reflexivity.
  + move=> i c hi hc s; rewrite interp_bind;apply eqit_bind; first by apply hi.
    by move=> s'; apply hc.
  + intros.
    by move=> >; apply interp_iresult.
  + by move=> >; apply interp_iresult.
  + by move=> >; apply interp_iresult.
  + move=> e c1 c2 hc1 hc2 ii s; rewrite /isem_instr /isem_flat_instr /=.
    rewrite interp_bind; apply eqit_bind.
    + by apply interp_iresult.
    by move=> []; [apply hc1 | apply hc2].
  + move=> v dir lo hi c hc ii s; rewrite /isem_instr /isem_flat_instr /=.
    rewrite interp_bind; apply eqit_bind; first by apply interp_iresult.
    move=> vlo.
    rewrite interp_bind; apply eqit_bind; first by apply interp_iresult.
    move=> vhi; elim: wrange s => {vlo vhi ii} //=.
    + move=> >; rewrite interp_ret; reflexivity.
    move=> j js hrec s.
    rewrite interp_bind; apply eqit_bind; first by apply interp_iresult.
    move=> s'; rewrite interp_bind.
    rewrite hc; setoid_rewrite hrec; reflexivity.
  + move=> al c1 e c2 hc1 hc2 ii s; rewrite /isem_instr /isem_flat_instr /= /isem_while.
    rewrite interp_iter; apply eutt_iter => {}s.
    rewrite /isem_while_body.
    rewrite interp_bind; apply eqit_bind; first by apply hc1.
    move=> s1; rewrite interp_bind; apply eqit_bind; first by apply interp_iresult.
    move=> [].
    + rewrite interp_bind; apply eqit_bind; first by apply hc2.
      move=> s2; rewrite interp_ret; reflexivity.
    rewrite interp_ret; reflexivity.
  move=> xs f es ii s; rewrite /isem_instr /isem_flat_instr /=.
  rewrite interp_bind; apply eqit_bind; first by apply interp_iresult.
  move=> vs.
  rewrite interp_bind; apply eqit_bind; last by move=> >; apply interp_iresult.
  rewrite interp_mrecursive; reflexivity.
Qed.
  
End REC_sem.


Section MREC_sem.

(*
Definition jsem_while_body {E} `{ErrEvent -< E}
   (RL : instr_r -> estate -> itree E estate)
   (c1 : cmd) (e:pexpr) (c2: cmd) (s1 : estate) : itree E (estate + estate) :=
   s2 <- isem_ir_map RL c1 s1 ;;
   b <- isem_cond e s2 ;;
   if b then s3 <- isem_ir_map RL c2 s2 ;; it_continue_loop s3
   else it_exit_loop s2.

Definition jsem_while {E} `{ErrEvent -< E}
   (RL : instr_r -> estate -> itree E estate)
   (c1 : cmd) (e:pexpr) (c2: cmd) (s1 : estate) : itree E estate :=
  ITree.iter (jsem_while_body RL c1 e c2) s1.
*)  

(* mutual recursion events *)
Variant MREvent : Type -> Type :=
 | LCode (c: cmd) (st: estate) : MREvent estate
 | FCall (f: funname) (fc: fstate) : MREvent fstate.

Fixpoint jsem_for_body {E} `{ErrEvent -< E}
   (RL : cmd -> estate -> itree E estate)
   (i: var_i) (c: cmd) (ls: list Z) (s: estate) : itree E estate :=
  match ls with
  | nil => ret s
  | (w :: ws) =>
    s <- iwrite_var true i (Vint w) s;;
    s <- RL c s;;
    jsem_for_body RL i c ws s
  end.

Definition jsem_while_body {E} `{ErrEvent -< E}
    (RL : cmd -> estate -> itree E estate)
    (c1 c2: cmd) (e: pexpr) (s1: estate) :
    itree E (estate + estate) :=
  s2 <- RL c1 s1 ;; 
  b <- isem_cond e s2 ;; 
  if b then s3 <- RL c2 s2 ;; it_continue_loop s3 
  else it_exit_loop s2. 


(* instruction semantic functor *)
Definition jsem_instrF {E} `{ErrEvent -< E}
  (RL : cmd -> estate -> itree (MREvent +' E) estate)
  (RC: funname -> fstate -> itree  (MREvent +' E) fstate)
    (i : instr_r) (s1: estate) :
    itree (MREvent +' E) estate :=
  match i with
  | Cassgn x tg ty e => iresult s1 (eval_assgn x tg ty e s1)
  | Copn xs tg o es => iresult s1 (sem_sopn pglobs o s1 xs es)
  | Csyscall xs o es => iresult s1 (eval_syscall xs o es s1)
  | Cif e c1 c2 =>
      b <- isem_cond e s1;;
      RL (if b then c1 else c2) s1
  | Cwhile a c1 e c2 =>
      ITree.iter (jsem_while_body RL c1 c2 e) s1
  | Cfor i (d, lo, hi) c =>
     vlo <- isem_bound lo s1 ;;
     vhi <- isem_bound hi s1 ;;
     jsem_for_body RL i c (wrange d vlo vhi) s1
  | Ccall xs fn args => isem_call RC xs fn args s1 
end.

Definition jsem_fcall {E} `{ErrEvent -< E} 
    (fn: funname) (fc: fstate) : itree (MREvent +' E) fstate :=
  it_rec_call (FCall fn fc).

(* event-based recursion *)
Definition msem_instr {E} `{ErrEvent -< E}
    (i : instr_r) (s1: estate) : itree (MREvent +' E) estate :=
  jsem_instrF (fun c s => it_rec_call (LCode c s)) isem_fcall i s1.

(* fixpoint-based recursion *)
Fixpoint rsem_instr {E} `{ErrEvent -< E}
    (i : instr_r) (s1: estate) : itree (MREvent +' E) estate :=
  jsem_instrF (isem_ir_map rsem_instr) isem_fcall i s1.

Definition initialize_call (scs1 : syscall_state_t) (m1 : mem)
    (fd : fundef) (vargs : values) : exec estate :=
  let sinit := (Estate scs1 m1 Vm.init) in
  Let vargs' := mapM2 ErrType dc_truncate_val fd.(f_tyin) vargs in
  Let s0 := init_state fd.(f_extra) (p_extra pr) ev sinit in
  write_vars (~~direct_call) fd.(f_params) vargs' s0.

Definition finalize_call (fd : fundef) (s:estate) :=
  Let vres := get_var_is (~~ direct_call) s.(evm) fd.(f_res) in
  Let vres' := mapM2 ErrType dc_truncate_val fd.(f_tyout) vres in
  let scs := s.(escs) in
  let m := finalize fd.(f_extra) s.(emem) in
  ok (mk_fstate scs m vres').

Definition jsem_call_body {E} `{ErrEvent -< E}
   (fn : funname) (fs: fstate) : itree (MREvent +' E) fstate :=
  (* FIXME: this is durty : sinit*)
  let sinit := estate0 fs in
  fd <- iget_fundef fn sinit;;
  s1 <- iresult sinit (initialize_fcall fd fs);;
  s2 <- it_rec_call (LCode fd.(f_body) s1);;
  iresult s2 (finalize_fcall fd s2).

Definition sem_mreventF {E} `{ErrEvent -< E}
   (R : instr_r -> estate -> itree (MREvent +' E) estate) :
   MREvent ~> itree (MREvent +' E) :=
 fun _ fs =>
   match fs with
   | LCode c st => isem_ir_map R c st
   | FCall fn fc => jsem_call_body fn fc
   end.

Definition sem_callF {E} `{ErrEvent -< E}
   (R : instr_r -> estate -> itree (MREvent +' E) estate)                      
   (fn : funname) (fc: fstate) : itree E fstate :=
  mrec (sem_mreventF R) (FCall fn fc).

(*** the error-aware semantics *)

(* event-based recursion *)
Definition msem_call {E} `{ErrEvent -< E} :
    funname -> fstate -> itree E fstate :=
  sem_callF msem_instr.

(* fixpoint-based recursion *)
Definition rsem_call {E} `{ErrEvent -< E} :
    funname -> fstate -> itree E fstate :=
  sem_callF rsem_instr.

(*** the final semantics *)

Definition final_msem_call (fn : funname) (fc : fstate) :
    execT (itree void1) fstate :=
  interp_Err (msem_call fn fc).

Definition final_rsem_call (fn : funname) (fc: fstate) :
    execT (itree void1) fstate :=
  interp_Err (rsem_call fn fc).

End MREC_sem.

End WSW.



