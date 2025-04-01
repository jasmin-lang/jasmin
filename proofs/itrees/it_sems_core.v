From ITree Require Import
     Basics
     ITree
     ITreeFacts
     Events.Exception
     Interp.Recursion
     MonadState.
Import Basics.Monads.

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.

Require Import expr psem_defs it_exec.

Import MonadNotation.
(* FIXME : This can be removed using %monad *)
Local Open Scope monad_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(**** ERROR SEMANTICS *******************************************)
Section Errors.

(* error events *)
Definition ErrEvent : Type -> Type := exceptE error_data.

(* failT (itree E) R = itree E (option R) *)
Definition handle_Err {E} : ErrEvent ~> execT (itree E) :=
  fun _ e =>
    match e with
    | Throw e' => Ret (ESerror _ e')
    end.

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

Definition ioget {E: Type -> Type} `{ErrEvent -< E} {V} (err: error_data) (o: option V) : itree E V :=
  match o with
  | Some v => Ret v
  | None => throw err
  end.

Definition err_result {E: Type -> Type} `{ErrEvent -< E} (Err : error -> error_data) :
  result error ~> itree E :=
  fun _ t => match t with
             | Ok v => Ret v
             | Error e => throw (Err e) end.

End Errors.

(** Type function isomorphism class *)
Class FIso (E1 E2: Type -> Type) : Type := FI {
    mfun1 : E1 -< E2 ;
    mfun2 : E2 -< E1 ;
    mid12 : forall T (x : E2 T), mfun1 (mfun2 x) = x ;
    mid21 : forall T (x : E1 T), mfun2 (mfun1 x) = x ;
}.

Notation with_Error E E0 := (FIso E (ErrEvent +' E0)).

#[global] Instance fromErr E E0 {wE : with_Error E E0} : ErrEvent -< E :=
  fun T (e:ErrEvent T) => mfun2 (inl1 e).

Definition is_error {E E0 : Type -> Type} (wE : with_Error E E0) (T : Type) (e : E T) :=
  match mfun1 e with
  | inl1 _ => true
  | inr1 _ => false
  end.

(* with_Error (ErrEvent +' void1) void1 *)
#[global]
Instance FIsoId E : FIso E E :=
  {| mfun1 := fun T x => x
   ; mfun2 := fun T x => x
   ; mid12 := fun T x => erefl
   ; mid21 := fun T x => erefl |}.

(* with_Error E E0 -> with_Error (E1 +' E) (E1 +' E0) *)
Section FIso_suml.
Context (E1 E E0 Err : Type -> Type) {FI : FIso E (Err +' E0)}.

Definition mfun1_suml T (e : (E1 +' E) T) : (Err +' (E1 +' E0)) T :=
  match e with
  | inl1 e1 => inr1 (inl1 e1)
  | inr1 e =>
    match mfun1 e with
    | inl1 err => inl1 err
    | inr1 e0  => inr1 (inr1 e0)
    end
  end.

Definition mfun2_suml T (e : (Err +' (E1 +' E0)) T) : (E1 +' E) T :=
  match e with
  | inl1 err => inr1 (mfun2 (inl1 err))
  | inr1 e10 =>
    match e10 with
    | inl1 e1 => inl1 e1
    | inr1 e0  => inr1 (mfun2 (inr1 e0))
    end
  end.

Lemma mfun_suml_12 T (x : (Err +' (E1 +' E0)) T) :
  mfun1_suml (mfun2_suml x) = x.
Proof. by case: x => [err | [e1 | e0]] //=; rewrite ?(mid12, mid21). Qed.

Lemma mfun_suml_21 T (x : (E1 +' E) T) :
  mfun2_suml (mfun1_suml x) = x.
Proof.
  case: x => [e1 | e] //=.
  by case heq : (mfun1 e) => [err | e0] /=; rewrite -heq ?(mid12, mid21).
Qed.

#[global]
Instance FIso_suml : FIso (E1 +' E) (Err +' (E1 +' E0)) :=
  {| mfun1 := mfun1_suml
   ; mfun2 := mfun2_suml
   ; mid12 := mfun_suml_12
   ; mid21 := mfun_suml_21 |}.

End FIso_suml.

Section WSW.
Context
  {asm_op: Type}
  {wsw: WithSubWord}
  {dc: DirectCall}
  {syscall_state : Type}
  {ep : EstateParams syscall_state}
  {spp : SemPexprParams}
  {sip : SemInstrParams asm_op syscall_state}
  {pT : progT}
  {scP : semCallParams}.

Record fstate := { fscs : syscall_state_t; fmem : mem; fvals : values }.

Variant recCall : Type -> Type :=
 | RecCall (f:funname) (fs:fstate) : recCall fstate.

Definition mk_error_data (s:estate) (e:error)  := (e, tt).

Definition mk_errtype := fun s => mk_error_data s ErrType.

Section CORE.

Context {E E0} {wE : with_Error E E0} (p : prog) (ev : extra_val_t).

Definition kget_fundef (funcs: fun_decls) (fn: funname) : ktree E fstate fundef :=
  fun _ => ioget (ErrType, tt) (get_fundef funcs fn).

Definition iresult {T} (s:estate) (F : exec T)  : itree E T :=
  err_result (mk_error_data s) F.

Definition iwrite_var (wdb : bool) (x : var_i) (v : value) (s : estate) : itree E estate :=
  iresult s (write_var wdb x v s).

Definition iwrite_lval (wdb : bool) (gd : glob_decls) (x : lval) (v : value) (s : estate)
  : itree E estate :=
  iresult s (write_lval wdb gd x v s).

Definition iwrite_lvals (wdb : bool) (gd : glob_decls) (xs : lvals) (vs : values) (s : estate)
  : itree E estate :=
  iresult s (write_lvals wdb gd s xs vs).

Definition isem_pexprs (wdb : bool) (gd : glob_decls) (es: pexprs) (s : estate) : itree E values :=
  iresult s (sem_pexprs wdb gd s es).

Definition sem_assgn  (x : lval) (tg : assgn_tag) (ty : stype) (e : pexpr) (s : estate) : exec estate :=
  Let v := sem_pexpr true (p_globs p) s e in
  Let v' := truncate_val ty v in
  write_lval true (p_globs p) x v' s.

Definition fexec_syscall (o : syscall_t) (fs:fstate) : exec fstate :=
  Let: (scs, m, vs) := exec_syscall fs.(fscs) fs.(fmem) o fs.(fvals) in
  ok {| fscs := scs; fmem := m; fvals := vs |}.

Definition mk_fstate (vs:values) (s:estate) := {| fscs := escs s; fmem:= emem s; fvals := vs |}.

Definition upd_estate wdb (gd : glob_decls) (xs:lvals) (fs : fstate) (s:estate) :=
  write_lvals wdb gd (with_scs (with_mem s fs.(fmem)) fs.(fscs)) xs fs.(fvals).

Definition sem_syscall (xs : lvals) (o : syscall_t) (es : pexprs) (s : estate) : exec estate :=
  Let ves := sem_pexprs true (p_globs p) s es in
  Let fs := fexec_syscall o (mk_fstate ves s) in
  upd_estate true (p_globs p) xs fs s.

Definition sem_cond (gd : glob_decls) (e : pexpr) (s : estate) : exec bool :=
  (sem_pexpr true gd s e >>= to_bool)%result.

Definition isem_cond (e : pexpr) (s : estate) : itree E bool :=
  iresult s (sem_cond (p_globs p) e s).

Definition sem_bound (gd : glob_decls) (lo hi : pexpr) (s : estate) : exec (Z * Z) :=
  (Let vlo := sem_pexpr true gd s lo >>= to_int in
  Let vhi := sem_pexpr true gd s hi >>= to_int in
  ok (vlo, vhi))%result.

Definition isem_bound (lo hi : pexpr) (s : estate) : itree E (Z * Z) :=
  iresult s (sem_bound (p_globs p) lo hi s).

Definition rec_call (f : funname) (fs : fstate) : itree (recCall +' E) fstate :=
  trigger_inl1 (RecCall f fs).

End CORE.

Section SEM_C.

Context {E E0} {wE : with_Error E E0}
        (sem_i: prog -> extra_val_t -> instr -> estate -> itree E estate)
        (p : prog) (ev : extra_val_t).

Fixpoint isem_cmd_body (c: cmd) (s: estate) : itree E estate :=
  match c with
  | nil => Ret s
  | i :: c' => s <- sem_i p ev i s;; isem_cmd_body c' s
  end.

Fixpoint isem_for_body (i : var_i) (c : cmd) (ls : list Z) (s: estate) : itree E estate :=
  match ls with
  | nil => Ret s
  | (w :: ws) =>
    s <- iwrite_var true i (Vint w) s;;
    s <- isem_cmd_body c s;;
    isem_for_body i c ws s
  end.

(* Make global definition *)
Local Notation continue_loop s := (ret (inl s)).
Local Notation exit_loop s := (ret (inr s)).

Definition isem_while_loop (c1 : cmd) (e : pexpr) (c2 : cmd) (s : estate) : itree E (estate + estate) :=
  s <- isem_cmd_body c1 s;;
  b <- isem_cond p e s;;
  if b then s <- isem_cmd_body c2 s;; continue_loop s
  else exit_loop s.

Definition isem_while_body (c1 : cmd) (e:pexpr) (c2: cmd) (s : estate) : itree E estate :=
  ITree.iter (isem_while_loop c1 e c2) s.

End SEM_C.

Class sem_Fun (E : Type -> Type) :=
  { sem_fun : prog -> extra_val_t -> funname -> fstate -> itree E fstate }.

#[global]
Instance sem_fun_rec (E : Type -> Type) : sem_Fun (recCall +' E) | 0 :=
  {| sem_fun := fun _ _ => rec_call (E:=E) |}.

Section SEM_I.

Context {E E0} {wE : with_Error E E0} {sem_F : sem_Fun E }.

Fixpoint isem_i_body (p : prog) (ev : extra_val_t) (i : instr) (s : estate) : itree E estate :=
  let: (MkI _ i) := i in
  match i with
  | Cassgn x tg ty e => iresult s (sem_assgn p x tg ty e s)

  | Copn xs tg o es => iresult s (sem_sopn (p_globs p) o s xs es)

  | Csyscall xs o es => iresult s (sem_syscall p xs o es s)

  | Cif e c1 c2 =>
    b <- isem_cond p e s;;
    isem_cmd_body isem_i_body p ev (if b then c1 else c2) s

  | Cwhile a c1 e i c2 =>
    isem_while_body isem_i_body p ev c1 e c2 s

  | Cfor i (d, lo, hi) c =>
    bounds <- isem_bound p lo hi s;;
    isem_for_body isem_i_body p ev i c (wrange d bounds.1 bounds.2) s

  | Ccall xs fn args =>
    vargs <- isem_pexprs  (~~direct_call) (p_globs p) args s;;
    fs <- sem_fun p ev fn (mk_fstate vargs s) ;;
    iresult s (upd_estate (~~direct_call) (p_globs p) xs fs s)
  end.

Definition isem_cmd_ := isem_cmd_body isem_i_body.

Lemma isem_cmd_cat p ev c c' s :
  isem_cmd_ p ev (c ++ c') s ≈ (s <- isem_cmd_ p ev c s;; isem_cmd_ p ev c' s).
Proof.
  rewrite /isem_cmd_; elim: c s => [ | i c hc] /= s.
  + rewrite bind_ret_l; reflexivity.
  rewrite bind_bind; setoid_rewrite hc; reflexivity.
Qed.

(**********************************************************************)
(** error-aware interpreter with mutual recursion *)

Definition estate0 (fs : fstate) :=
  Estate fs.(fscs) fs.(fmem) Vm.init.

Definition initialize_funcall (p : prog) (ev : extra_val_t) (fd : fundef) (fs : fstate) : exec estate :=
  let sinit := estate0 fs in
  Let vargs' := mapM2 ErrType dc_truncate_val fd.(f_tyin) fs.(fvals) in
  Let s0 := init_state fd.(f_extra) (p_extra p) ev sinit in
  write_vars (~~direct_call) fd.(f_params) vargs' s0.

Definition finalize_funcall (fd : fundef) (s:estate) : exec fstate :=
  Let vres := get_var_is (~~ direct_call) s.(evm) fd.(f_res) in
  Let vres' := mapM2 ErrType dc_truncate_val fd.(f_tyout) vres in
  let scs := s.(escs) in
  let m := finalize fd.(f_extra) s.(emem) in
  ok {| fscs := scs; fmem := m; fvals := vres' |}.

Definition ifinalize_funcall (fd : fundef) (s:estate) : itree E fstate :=
  err_result (fun e => (e, tt)) (finalize_funcall fd s).

Definition isem_fun_body (p : prog) (ev : extra_val_t)
   (fn : funname) (fs : fstate) :=
   fd <- kget_fundef (p_funcs p) fn fs;;
   let sinit := estate0 fs in
   s1 <- iresult sinit (initialize_funcall p ev fd fs);;
   s2 <- isem_cmd_ p ev fd.(f_body) s1;;
   iresult s2 (finalize_funcall fd s2).

End SEM_I.

Section SEM_F.

Context {E E0} {wE : with_Error E E0}.

Definition isem_i_rec (p : prog) (ev : extra_val_t) (i : instr) (s : estate)
  : itree (recCall +' E) estate :=
  isem_i_body p ev i s.

Definition isem_cmd_rec (p : prog) (ev : extra_val_t) (c : cmd) (s : estate)
  : itree (recCall +' E) estate :=
  isem_cmd_ p ev c s.

Definition isem_fun_rec (p : prog) (ev : extra_val_t)
   (fn : funname) (fs : fstate) : itree (recCall +' E) fstate :=
  isem_fun_body p ev fn fs.

Definition interp_recCall (p : prog) (ev : extra_val_t) : recCall ~> itree (recCall +' E) :=
 fun T (rc : recCall T) =>
   match rc with
   | RecCall fn fs => isem_fun_rec p ev fn fs
   end.

Definition isem_fun (p : prog) (ev : extra_val_t) (fn : funname) (fs : fstate) : itree E fstate :=
  mrec (interp_recCall p ev) (RecCall fn fs).

#[global]
Instance sem_fun_full : sem_Fun E | 100 :=
  {| sem_fun := isem_fun |}.

Definition isem_i (p : prog) (ev : extra_val_t) (i : instr) (s : estate) : itree E estate :=
  isem_i_body p ev i s.

Definition isem_cmd (p : prog) (ev : extra_val_t) (c : cmd) (s : estate) : itree E estate :=
  isem_cmd_ p ev c s.

End SEM_F.

Definition err_sem_fun (p : prog) (ev : extra_val_t) (fn : funname) (fs : fstate) :
  execT (itree void1) fstate :=
  interp_Err (isem_fun p ev fn fs).

(* Core lemmas about the definition *)

Section Section.

Context {E E0: Type -> Type} {wE : with_Error E E0}.
Context (p : prog) (ev : extra_val_t).

Notation interp_rec := (interp (mrecursive (interp_recCall p ev))).

Lemma interp_throw T e : interp_rec (throw (X:=T) e) ≈ throw e.
Proof. rewrite interp_vis bind_trigger; apply eqit_Vis => -[]. Qed.

Lemma interp_err_result e T (r : result error T) :
  eutt (E:=E) eq (interp_rec (err_result e r)) (err_result e r).
Proof.
  case: r => /= [t | err].
  + rewrite interp_ret; reflexivity.
  apply interp_throw.
Qed.

Lemma interp_ioget Err T (o : option T) :
  eutt (E:=E) eq (interp_rec (ioget Err o)) (ioget Err o).
Proof.
  case o => /= [? | ].
  + rewrite interp_ret; reflexivity.
  apply interp_throw.
Qed.

Lemma interp_iresult s T (r : exec T) :
  eutt (E:=E) eq (interp (mrecursive (interp_recCall p ev)) (iresult s r)) (iresult s r).
Proof.
  case r => /= [? | ?].
  + rewrite interp_ret; reflexivity.
  apply interp_throw.
 Qed.

Lemma interp_isem_cmd c s :
  eutt (E:=E) eq (interp_rec (isem_cmd_body isem_i_rec p ev c s))
         (isem_cmd_body isem_i_body p ev c s).
Proof.
  apply:
   (cmd_rect
    (Pr := fun ir => forall ii s,
       eutt (E:=E) eq (interp_rec (isem_i_rec p ev (MkI ii ir) s))
                      (isem_i p ev (MkI ii ir) s))
    (Pi := fun i => forall s,
       eutt (E:=E) eq (interp_rec (isem_i_rec p ev i s))
                      (isem_i p ev i s))
    (Pc := fun c => forall s,
       eutt (E:=E) eq (interp_rec (isem_cmd_body isem_i_rec p ev c s))
                      (isem_cmd p ev c s))) => // {c s}.
  + move=> s /=; rewrite interp_ret; reflexivity.
  + move=> i c hi hc s; rewrite interp_bind;apply eqit_bind; first by apply hi.
    by move=> s'; apply hc.
  1-3: by move=> >; apply interp_iresult.
  + move=> e c1 c2 hc1 hc2 ii s; rewrite /isem_i /isem_i_rec /=.
    rewrite interp_bind; apply eqit_bind.
    + by apply interp_iresult.
    by move=> []; [apply hc1 | apply hc2].
  + move=> v dir lo hi c hc ii s; rewrite /isem_i /isem_i_rec /=.
    rewrite interp_bind; apply eqit_bind; first by apply interp_iresult.
    move=> bounds /=. elim: wrange s => {bounds ii} //=.
    + move=> >; rewrite interp_ret; reflexivity.
    move=> j js hrec s.
    rewrite interp_bind; apply eqit_bind; first by apply interp_iresult.
    move=> s'; rewrite interp_bind.
    rewrite hc; setoid_rewrite hrec; reflexivity.
  + move=> al c1 e inf c2 hc1 hc2 ii s; rewrite /isem_i /isem_i_rec /= /isem_while_body.
    rewrite interp_iter; apply eutt_iter=> {}s.
    rewrite /isem_while_loop.
    rewrite interp_bind; apply eqit_bind; first by apply hc1.
    move=> s1; rewrite interp_bind; apply eqit_bind; first by apply interp_iresult.
    move=> [].
    + rewrite interp_bind; apply eqit_bind; first by apply hc2.
      move=> s2; rewrite interp_ret; reflexivity.
    rewrite interp_ret; reflexivity.
  move=> xs f es ii s; rewrite /isem_i /isem_i_rec /=.
  rewrite interp_bind; apply eqit_bind; first by apply interp_iresult.
  move=> vs.
  rewrite interp_bind; apply eqit_bind; last by move=> >; apply interp_iresult.
  rewrite interp_mrecursive; reflexivity.
Qed.

Lemma isem_call_unfold (fn : funname) (fs : fstate) :
  isem_fun p ev fn fs ≈ isem_fun_body p ev fn fs.
Proof.
  rewrite {1}/isem_fun.
  rewrite mrec_as_interp.
  rewrite {2}/interp_recCall /isem_fun_rec /isem_fun_body.
  rewrite interp_bind; apply eqit_bind.
  + by apply interp_ioget.
  move=> fd; rewrite interp_bind; apply eqit_bind.
  + by apply interp_iresult.
  move=> s1; rewrite interp_bind; apply eqit_bind.
  + apply interp_isem_cmd.
  move=> s2; apply interp_iresult.
Qed.

End Section.

End WSW.
