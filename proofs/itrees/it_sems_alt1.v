From ITree Require Import
     ITree
     ITreeFacts
     Events.Exception
     Interp.Recursion.

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.

Require Import expr psem_defs psem it_gen_lib it_exec.

Import MonadNotation.
Local Open Scope monad_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(**** ERROR SEMANTICS *******************************************)
Section Errors.

(* error events *)
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

Definition mk_error_data (s:estate) (e:error)  := (e, tt).

Definition mk_errtype := fun s => mk_error_data s ErrType.

Section CORE.

Context {E} `{ErrEvent -< E} (p : prog) (ev : extra_val_t).

Definition iget_fundef (funcs: fun_decls) (fn: funname) (s:estate) : itree E fundef :=
  ioget (mk_errtype s) (get_fundef funcs fn).

Definition iresult {T} (s:estate) (F : exec T)  : itree E T :=
  err_result (mk_error_data s) F.

Definition iwrite_var (wdb : bool) (x : var_i) (v : value) (s : estate) : itree E estate :=
  iresult s (write_var wdb x v s).

Definition iwrite_lval (wdb : bool) (gd : glob_decls) (x : lval) (v : value) (s : estate) : itree E estate :=
  iresult s (write_lval wdb gd x v s).

Definition iwrite_lvals (wdb : bool) (gd : glob_decls) (s : estate) (xs : lvals) (vs : values) : itree E estate :=
  iresult s (write_lvals wdb gd s xs vs).

Definition isem_pexpr (wdb : bool) (gd : glob_decls) (s : estate) (e: pexpr) : itree E value :=
  iresult s (sem_pexpr wdb gd s e).

Definition isem_pexprs (wdb : bool) (gd : glob_decls) (s : estate) (es: pexprs) : itree E values :=
  iresult s (sem_pexprs wdb gd s es).

Definition sem_assgn  (x : lval) (tg : assgn_tag) (ty : stype) (e : pexpr) (s : estate) : exec estate :=
   (Let v := sem_pexpr true (p_globs p) s e in
    Let v' := truncate_val ty v in
    write_lval true (p_globs p) x v' s).

Record fstate := { fscs : syscall_state_t; fmem : mem; fvals : values }.

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
  sem_pexpr true gd s e >>r= to_bool.

Definition isem_cond (e : pexpr) (s : estate) : itree E bool :=
  iresult s (sem_cond (p_globs p) e s).

Definition sem_bound (gd : glob_decls) (lo hi : pexpr) (s : estate) : exec (Z * Z) :=
  Let vlo := sem_pexpr true gd s lo >>r= to_int in
  Let vhi := sem_pexpr true gd s hi >>r= to_int in
  ok (vlo, vhi).

Definition isem_bound (lo hi : pexpr) (s : estate) : itree E (Z * Z) :=
  iresult s (sem_bound (p_globs p) lo hi s).

End CORE.

Section SEM_C.

Context {E} `{ErrEvent -< E}
        (sem_i: prog -> extra_val_t -> instr -> estate -> itree E estate)
        (p : prog) (ev : extra_val_t).

(* isem_cmd_body *)
Fixpoint isem_map (c: cmd) (s: estate) : itree E estate :=
  match c with
  | nil => Ret s
  | i :: c' => s' <- sem_i p ev i s ;; isem_map c' s'
  end.

Fixpoint isem_for_body (i : var_i) (c : cmd) (ls : list Z) (s : estate) : itree E estate :=
  match ls with
  | nil => ret s
  | (w :: ws) =>
    s <- iwrite_var true i (Vint w) s;;
    s <- isem_map c s;;
    isem_for_body i c ws s
  end.

(* Make global definition *)
Local Notation continue_loop st := (ret (inl st)).
Local Notation exit_loop st := (ret (inr st)).

Definition isem_while_loop (c1 : cmd) (e : pexpr) (c2 : cmd) (s1 : estate) : itree E (estate + estate) :=
   s2 <- isem_map c1 s1 ;;
   b <- isem_cond p e s2 ;;
   if b then s3 <- isem_map c2 s2 ;; continue_loop s3
   else exit_loop s2.

Definition isem_while (c1 : cmd) (e:pexpr) (c2: cmd) (s1 : estate) : itree E estate :=
  ITree.iter (isem_while_loop c1 e c2) s1.

End SEM_C.

Section SEM_I.

Context {E} `{ErrEvent -< E} 
  (sem_fun : prog -> extra_val_t -> funname -> fstate -> itree E fstate).

Fixpoint isem_i_body (p : prog) (ev : extra_val_t)
  (i : instr) (s1 : estate) : itree E estate :=
  let: (MkI _ i) := i in
  match i with
  | Cassgn x tg ty e => iresult s1 (sem_assgn p x tg ty e s1)
  | Copn xs tg o es => iresult s1 (sem_sopn (p_globs p) o s1 xs es)
  | Csyscall xs o es => iresult s1 (sem_syscall p xs o es s1)

  | Cif e c1 c2 =>
    b <- isem_cond p e s1;;
    isem_map isem_i_body p ev (if b then c1 else c2) s1

  | Cwhile a c1 e c2 =>
    isem_while isem_i_body p ev c1 e c2 s1

  | Cfor i (d, lo, hi) c =>
    bounds <- isem_bound p lo hi s1 ;;
    isem_for_body isem_i_body p ev i c (wrange d bounds.1 bounds.2) s1

  | Ccall xs fn args =>
    vargs <- isem_pexprs  (~~direct_call) (p_globs p) s1 args;;
    fs <- sem_fun p ev fn (mk_fstate vargs s1) ;;
    iresult s1 (upd_estate (~~direct_call) (p_globs p) xs fs s1)
  end.

Definition isem_cmd_ := isem_map isem_i_body.

Lemma isem_cmd_cat p ev c c' s :
  isem_cmd_ p ev (c ++ c') s ≈ (s' <- isem_cmd_ p ev c s;; isem_cmd_ p ev c' s').
Proof.
  rewrite /isem_cmd_; elim: c s => [ | i c hc] /= s.
  + rewrite bind_ret_l; reflexivity.
  rewrite bind_bind; setoid_rewrite hc; reflexivity.
Qed.

End SEM_I.

(**********************************************************************)
(** error-aware interpreter with mutual recursion *)

Definition estate0 (fs : fstate) :=
  Estate fs.(fscs) fs.(fmem) Vm.init.

Definition initialize_funcall (p : prog) (ev : extra_val_t) (fd : fundef) (fs : fstate) : exec estate :=
  let sinit := estate0 fs in
  Let vargs' := mapM2 ErrType dc_truncate_val fd.(f_tyin) fs.(fvals) in
  Let s0 := init_state fd.(f_extra) (p_extra p) ev sinit in
  write_vars (~~direct_call) fd.(f_params) vargs' s0.

Definition finalize_funcall (fd : fundef) (s:estate) :=
  Let vres := get_var_is (~~ direct_call) s.(evm) fd.(f_res) in
  Let vres' := mapM2 ErrType dc_truncate_val fd.(f_tyout) vres in
  let scs := s.(escs) in
  let m := finalize fd.(f_extra) s.(emem) in
  ok {| fscs := scs; fmem := m; fvals := vres' |}.

Definition isem_funcall {E} `{ErrEvent -< E}
   (rec_call : prog -> extra_val_t -> funname -> fstate -> itree E fstate)
   (p : prog) (ev : extra_val_t)
   (fn : funname) (fs : fstate) : itree E fstate :=
  (* FIXME: this is durty : sinit*)
  let sinit := estate0 fs in
  fd <- iget_fundef (p_funcs p) fn sinit;;
  s1 <- iresult sinit (initialize_funcall p ev fd fs);;
  s2 <- isem_cmd_ rec_call p ev fd.(f_body) s1;;
  iresult s2 (finalize_funcall fd s2).


Section SEM_F.

Context {E} `{ErrEvent -< E}.

Notation recCall := (callE (funname * fstate) fstate).

Definition rec_call (p : prog) (ev : extra_val_t) (fn: funname) (fc: fstate) :
  itree (recCall +' E) fstate := trigger (Call (fn, fc)).

Definition isem_i_rec (p : prog) (ev : extra_val_t) (i : instr) (s1 : estate) : itree (recCall +' E) estate :=
  isem_i_body rec_call p ev i s1.

Definition isem_cmd_rec (p : prog) (ev : extra_val_t) (c : cmd) (s1 : estate) : itree (recCall +' E) estate :=
  isem_cmd_ rec_call p ev c s1.

Definition isem_fun_rec (p : prog) (ev : extra_val_t)
   (fn : funname) (fs : fstate) : itree (recCall +' E) fstate :=
  isem_funcall rec_call p ev fn fs.

Definition handle_recCall 
  (p : prog) (ev : extra_val_t) (x: funname * fstate) :
  itree (recCall +' E) fstate :=
  isem_fun_rec p ev (fst x) (snd x).

Definition isem_fun (p : prog) (ev : extra_val_t) (fn : funname) (fs : fstate) : itree E fstate :=
  rec (handle_recCall p ev) (fn, fs).

Definition isem_i (p : prog) (ev : extra_val_t) (i : instr) (s : estate) : itree E estate :=
  isem_i_body isem_fun p ev i s.

Definition isem_cmd (p : prog) (ev : extra_val_t) (c : cmd) (s : estate) : itree E estate :=
  isem_cmd_ isem_fun p ev c s.

End SEM_F.

Definition sem_fun (p : prog) (ev : extra_val_t) (fn : funname) (fs : fstate) : execT (itree void1) (fstate) :=
  interp_Err (isem_fun p ev fn fs).

(* Core lemmas about the definition *)

Lemma interp_ioget {E : Type -> Type} `{ErrEvent -< E} (p : prog) (ev : extra_val_t) Err T (o : option T) :
  eutt (E:=E) eq (interp (recursive (handle_recCall p ev)) (ioget Err o)) (ioget Err o).
Proof.
  case o => /=.
  + move=> ?; rewrite interp_ret; reflexivity.
  rewrite interp_vis bind_trigger.
  by apply eqit_Vis => -[].
Qed.

Lemma interp_iresult {E : Type -> Type} `{ErrEvent -< E} (p : prog) (ev : extra_val_t) s T (r : exec T) :
  eutt (E:=E) eq (interp (recursive (handle_recCall p ev)) (iresult s r)) (iresult s r).
Proof.
  case r => /=.
  + move=> ?; rewrite interp_ret; reflexivity.
  move=> e; rewrite interp_vis bind_trigger.
  by apply eqit_Vis => -[].
Qed.

Lemma interp_isem_cmd {E} `{ErrEvent -< E} (p : prog) (ev : extra_val_t) c s :
  eutt (E:=E) eq (interp (recursive (handle_recCall p ev)) (isem_map isem_i_rec p ev c s))
         (isem_map (isem_i_body isem_fun) p ev c s).
Proof.
  apply:
   (cmd_rect
    (Pr := fun ir => forall ii s,
       eutt (E:=E) eq (interp (recursive (handle_recCall p ev)) (isem_i_rec p ev (MkI ii ir) s))
                      (isem_i p ev (MkI ii ir) s))
    (Pi := fun i => forall s,
       eutt (E:=E) eq (interp (recursive (handle_recCall p ev)) (isem_i_rec p ev i s))
                      (isem_i p ev i s))
    (Pc := fun c => forall s,
       eutt (E:=E) eq (interp (recursive (handle_recCall p ev)) (isem_map isem_i_rec p ev c s))
                      (isem_cmd p ev c s))) => // {c s}.
  + move=> s /=; rewrite interp_ret; reflexivity.
  + move=> i c hi hc s; rewrite interp_bind;apply eqit_bind; first by apply hi.
    by move=> s'; apply hc.
  + by move=> >; apply interp_iresult.
  + by move=> >; apply interp_iresult.
  + by move=> >; apply interp_iresult.
  + move=> e c1 c2 hc1 hc2 ii s; rewrite /isem_i /isem_i_rec /=.
    rewrite interp_bind; apply eqit_bind.
    + by apply interp_iresult.
    by move=> []; [apply hc1 | apply hc2].
  + move=> v dir lo hi c hc ii s; rewrite /isem_i /isem_i_rec /=.
    rewrite interp_bind; apply eqit_bind; first by apply interp_iresult.
    move=> bounds; elim: wrange s => {bounds ii} //=.
    + move=> >; rewrite interp_ret; reflexivity.
    move=> j js hrec s.
    rewrite interp_bind; apply eqit_bind; first by apply interp_iresult.
    move=> s'; rewrite interp_bind.
    rewrite hc; setoid_rewrite hrec; reflexivity.
  + move=> al c1 e c2 hc1 hc2 ii s; rewrite /isem_i /isem_i_rec /= /isem_while.
    rewrite interp_iter; apply eutt_iter => {}s.
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
  rewrite interp_recursive_call; reflexivity.
Qed.

Lemma isem_call_unfold {E} `{ErrEvent -< E} (p : prog) (ev : extra_val_t) (fn : funname) (fs : fstate) :
  isem_fun (E:=E) p ev fn fs ≈ isem_funcall isem_fun p ev fn fs.
Proof.
  rewrite {1}/isem_fun.
  rewrite rec_as_interp.
  rewrite {2}/handle_recCall /isem_fun_rec /isem_funcall.
  rewrite interp_bind; apply eqit_bind.
  + by apply interp_ioget.
  move=> fd; rewrite interp_bind; apply eqit_bind.
  + by apply interp_iresult.
  move=> s1; rewrite interp_bind; apply eqit_bind.
  + apply interp_isem_cmd.
  move=> s2; apply interp_iresult.
Qed.

End WSW.
