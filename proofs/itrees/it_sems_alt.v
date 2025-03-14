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
Definition mk_errtype := fun s => mk_error_data s ErrType.

(*** lifting instruction to itrees *)

Definition iget_fundef {E} `{ErrEvent -< E}
    (fn: funname) (s:estate) : itree E fundef :=
  ioget (mk_errtype s) (get_fundef (p_funcs pr) fn).

Definition iresult {E} `{ErrEvent -< E} {T} (s:estate) (F : exec T) :
    itree E T :=
  err_result (mk_error_data s) F.

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
Fixpoint isem_map {E} (sem_i: instr_r -> estate -> itree E estate)
   (c: cmd) (st: estate) : itree E estate :=
  match c with
  | nil => Ret st
  | (MkI _ i) :: c' => st' <- sem_i i st ;; isem_map sem_i c' st'
  end.


(**********************************************************************)
(*** error-aware interpreter with mutual recursion *)

(* function call info record *)
Record fstate := mk_fstate
      { fscs : syscall_state_t; fmem : mem; fvals : values }.
(*
Record fc_info : Type := mk_fc_info {
  fc_scs : syscall_state_t ;
  fc_m : mem ;
  fc_vs : values }.                           
*)

(* mutual recursion events *)
Variant MREvent : Type -> Type :=
 | LCode (c: cmd) (st: estate) : MREvent estate
 | FCall (f: funname) (fc: fstate) : MREvent fstate.

Notation it_continue_loop st := (ret (inl st)).
Notation it_exit_loop st := (ret (inr st)).
Notation it_rec_call := (trigger_inl1).

Definition isem_cond {E} `{ErrEvent -< E} (e:pexpr) (s: estate) :
    itree E bool :=
  iresult s (sem_pexpr true pglobs s e >>r= to_bool).

Definition isem_bound {E} `{ErrEvent -< E} (e:pexpr) (s: estate) :
    itree E Z :=
  iresult s (sem_pexpr true pglobs s e >>r= to_int).

Fixpoint isem_for_body {E} `{ErrEvent -< E}
   (RL : cmd -> estate -> itree E estate)
   (i: var_i) (c: cmd) (ls: list Z) (s: estate) : itree E estate :=
  match ls with
  | nil => ret s
  | (w :: ws) =>
    s <- iwrite_var true i (Vint w) s;;
    s <- RL c s;;
    isem_for_body RL i c ws s
  end.

Definition isem_while_body {E} `{ErrEvent -< E}
    (RL : cmd -> estate -> itree (MREvent +' E) estate)
    (c1 c2: cmd) (e: pexpr) (s1: estate) :
    itree (MREvent +' E) (estate + estate) :=
  s2 <- RL c1 s1 ;; 
  b <- isem_cond e s2 ;; 
  if b then s3 <- RL c2 s2 ;; it_continue_loop s3 
  else it_exit_loop s2. 

Definition isem_call {E} `{ErrEvent -< E}
    (RC: funname -> fstate -> itree  (MREvent +' E) fstate)                  
    (xs: lvals) (fn: funname) (args: pexprs) (s1: estate) :
    itree (MREvent +' E) estate :=
  vargs <- isem_pexprs  (~~direct_call) pglobs s1 args ;;
  res <- it_rec_call (FCall fn (mk_fstate (escs s1) (emem s1) vargs)) ;;
  iwrite_lvals (~~direct_call) pglobs
       (with_scs (with_mem s1 res.(fmem)) res.(fscs)) xs res.(fvals).
  
(* instruction semantic functor *)
Definition isem_instrF {E} `{ErrEvent -< E}
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
      ITree.iter (isem_while_body RL c1 c2 e) s1
  | Cfor i (d, lo, hi) c =>
     vlo <- isem_bound lo s1 ;;
     vhi <- isem_bound hi s1 ;;
     isem_for_body RL i c (wrange d vlo vhi) s1
  | Ccall xs fn args => isem_call RC xs fn args s1 
end.

Definition isem_fcall {E} `{ErrEvent -< E} 
    (fn: funname) (fc: fstate) : itree (MREvent +' E) fstate :=
  it_rec_call (FCall fn fc).

(* event-based recursion *)
Definition msem_instr {E} `{ErrEvent -< E}
    (i : instr_r) (s1: estate) : itree (MREvent +' E) estate :=
  isem_instrF (fun c s => it_rec_call (LCode c s)) isem_fcall i s1.

(* fixpoint-based recursion *)
Fixpoint rsem_instr {E} `{ErrEvent -< E}
    (i : instr_r) (s1: estate) : itree (MREvent +' E) estate :=
  isem_instrF (isem_map rsem_instr) isem_fcall i s1.

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

Definition sem_call_body {E} `{ErrEvent -< E}
   (fn : funname) (fc: fstate) : itree (MREvent +' E) fstate :=
  (* FIXME: this is durty : sinit*)
  let sinit := (Estate fc.(fscs) fc.(fmem) Vm.init) in
  fd <- iget_fundef fn sinit;;
  s1 <- iresult sinit (initialize_call fc.(fscs) fc.(fmem) fd fc.(fvals));;
  s2 <- it_rec_call (LCode fd.(f_body) s1);;
  iresult s2 (finalize_call fd s2).

Definition sem_mreventF {E} `{ErrEvent -< E}
   (R : instr_r -> estate -> itree (MREvent +' E) estate) :
   MREvent ~> itree (MREvent +' E) :=
 fun _ fs =>
   match fs with
   | LCode c st => isem_map R c st
   | FCall fn fc => sem_call_body fn fc
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

(******************************************************************)

Variant RecCode : Type -> Type :=
 | RECCode (c: cmd) (st: estate) : RecCode estate.

Variant RecCall : Type -> Type :=
  | RECCall (fn: funname) (fc: fstate) : RecCall fstate.

Definition FCState : Type -> Type := (RecCode +' RecCall).

End WSW.



