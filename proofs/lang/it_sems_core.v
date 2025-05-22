From ITree Require Import
     Basics
     ITree
     ITreeFacts
     Events.Exception
     Interp.Recursion
     MonadState.
Import Basics.Monads.

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.

Require Import expr psem_defs psem_core it_exec rec_facts.

Import MonadNotation.
Local Open Scope monad_scope.

(**** Error semantics ******************************************)
Section Errors.

(* error events *)
Definition ErrEvent : Type -> Type := exceptE error_data.

(* execT (itree E) R = itree E (execS R) *)
Definition handle_Err {E} : ErrEvent ~> execT (itree E) :=
  fun _ e =>
    match e with
    | Throw e' => Ret (ESerror _ e')
    end.

(* ErrEvnt handler *)
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
  {wc : WithCatch }
  {wa : WithAssert}
  {sip : SemInstrParams asm_op syscall_state}
  {pT : progT}
  {scP : semCallParams}.

(* Recursion events (curried version of Call in ITree) *)
Variant recCall : Type -> Type :=
 | RecCall (ii:instr_info) (f:funname) (fs:fstate) : recCall fstate.

Definition mk_error_data (s:estate) (e:error)  := (e, tt).

Definition mk_errtype := fun s => mk_error_data s ErrType.

(**** Auxiliary definitions ******************************************)
Section CORE.

Context {E E0} {wE : with_Error E E0} (p : prog) (ev : extra_val_t).

Definition kget_fundef (funcs: fun_decls) (fn: funname) :
    ktree E fstate fundef :=
  fun _ => ioget (ErrType, tt) (get_fundef funcs fn).

Definition iresult {T} (s:estate) (F : exec T)  : itree E T :=
  err_result (mk_error_data s) F.

Definition iwrite_var (wdb : bool) (x : var_i) (v : value) (s : estate) :
    itree E estate :=
  iresult s (write_var wdb x v s).

Definition iwrite_lval (wdb : bool) (gd : glob_decls) (x : lval)
    (v : value) (s : estate) : itree E estate :=
  iresult s (write_lval wdb gd x v s).

Definition iwrite_lvals (wdb : bool) (gd : glob_decls) (xs : lvals)
    (vs : values) (s : estate) : itree E estate :=
  iresult s (write_lvals wdb gd s xs vs).

Definition isem_pexprs (wdb : bool) (gd : glob_decls) (es: pexprs)
    (s : estate) : itree E values :=
  iresult s (sem_pexprs wdb gd s es).

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

Definition sem_syscall (xs : lvals) (o : syscall_t) (es : pexprs)
    (s : estate) : exec estate :=
  Let ves := sem_pexprs true (p_globs p) s es in
  Let fs := fexec_syscall o (mk_fstate ves s) in
  upd_estate true (p_globs p) xs fs s.

Lemma sem_cond_sem_pexpr gd e s b :
  sem_cond gd e s = ok b -> sem_pexpr true gd s e = ok (Vbool b).
Proof. rewrite /sem_cond /=; by t_xrbindP=> _ -> /to_boolI ->. Qed.

Definition isem_cond (e : pexpr) (s : estate) : itree E bool :=
  iresult s (sem_cond (p_globs p) e s).

Definition sem_bound (gd : glob_decls) (lo hi : pexpr) (s : estate) :
    exec (Z * Z) :=
  (Let vlo := sem_pexpr true gd s lo >>= to_int in
  Let vhi := sem_pexpr true gd s hi >>= to_int in
  ok (vlo, vhi))%result.

Definition isem_bound (lo hi : pexpr) (s : estate) : itree E (Z * Z) :=
  iresult s (sem_bound (p_globs p) lo hi s).

Definition isem_assert (a: assertion) (s: estate) : itree E unit :=
  iresult s (sem_assert (p_globs p) s a).

Definition isem_pre {dc : DirectCall} s (fn : funname) (fs:fstate) : itree E unit :=
  iresult s (sem_pre p fn fs).

Definition isem_post {dc : DirectCall} s (fn : funname) (vargs : values) (fr:fstate) : itree E unit :=
  iresult s (sem_post p fn vargs fr).

(* recCall trigger *)
Definition rec_call (ii:instr_info) (f : funname) (fs : fstate) :
   itree (recCall +' E) fstate :=
  trigger_inl1 (RecCall ii f fs).

End CORE.

(**** Abstract semantics **********************************************)
Section SEM_C.

Context {E E0} {wE : with_Error E E0}
        (sem_i: prog -> extra_val_t -> instr -> estate -> itree E estate)
        (p : prog) (ev : extra_val_t).

(* folding instruction semantics on commands *)
Definition isem_foldr (c: cmd) : estate -> itree E estate :=
  foldr (fun i k s => s' <- sem_i p ev i s ;; k s')
        (fun s: estate => Ret s) c.

(* Make global definition *)
Local Notation continue_loop s := (ret (inl s)).
Local Notation exit_loop s := (ret (inr s)).

Definition isem_for_round (i : var_i) (c : cmd)
  (w: Z) (k: estate -> itree E estate) (s: estate) :
    itree E estate :=
  s <- iwrite_var true i (Vint w) s ;;
  s <- isem_foldr c s ;; k s.

Definition isem_for_loop (i : var_i) (c : cmd) (ls : list Z)
  : estate -> itree E estate :=
  foldr (isem_for_round i c) (fun s: estate => Ret s) ls.

Definition isem_while_round (c1 : cmd) (e : pexpr) (c2 : cmd) (s : estate) :
    itree E (estate + estate) :=
  s <- isem_foldr c1 s;;
  b <- isem_cond p e s;;
  if b then s <- isem_foldr c2 s;; continue_loop s
  else exit_loop s.

Definition isem_while_loop (c1 : cmd) (e:pexpr) (c2: cmd) (s : estate) :
    itree E estate :=
  ITree.iter (isem_while_round c1 e c2) s.

End SEM_C.

Class sem_Fun (E : Type -> Type) :=
  { sem_fun : prog -> extra_val_t -> instr_info -> funname -> fstate -> itree E fstate }.

#[global]
Instance sem_fun_rec (E : Type -> Type) : sem_Fun (recCall +' E) | 0 :=
  {| sem_fun := fun _ _ => rec_call (E:=E) |}.

Section SEM_I.

Context {E E0} {wE : with_Error E E0} {sem_F : sem_Fun E }.


(* semantics of instructions, abstracting on function calls (through
   sem_fun) *)
Fixpoint isem_i_body (p : prog) (ev : extra_val_t) (i : instr) (s : estate) :
    itree E estate :=
  let: (MkI ii i) := i in
  match i with
  | Cassgn x tg ty e => iresult s (sem_assgn p x tg ty e s)

  | Copn xs tg o es => iresult s (sem_sopn (p_globs p) o s xs es)

  | Csyscall xs o es => iresult s (sem_syscall p xs o es s)

  | Cassert a => isem_assert p a s;; Ret s

  | Cif e c1 c2 =>
    b <- isem_cond p e s;;
    isem_foldr isem_i_body p ev (if b then c1 else c2) s

  | Cwhile a c1 e i c2 =>
    isem_while_loop isem_i_body p ev c1 e c2 s

  | Cfor i (d, lo, hi) c =>
    bounds <- isem_bound p lo hi s;;
    isem_for_loop isem_i_body p ev i c (wrange d bounds.1 bounds.2) s

  | Ccall xs fn args =>
    vargs <- isem_pexprs  (~~direct_call) (p_globs p) args s;;
    let fi := mk_fstate vargs s in
    isem_pre p s fn fi;; 
    fs <- sem_fun p ev ii fn fi ;;
    isem_post p s fn vargs fs;;
    iresult s (upd_estate (~~direct_call) (p_globs p) xs fs s)
  end.

(* similar, for commands *)
Definition isem_cmd_ := isem_foldr isem_i_body.

Lemma isem_cmd_cat p ev c c' s :
  isem_cmd_ p ev (c ++ c') s ≈ (s <- isem_cmd_ p ev c s;; isem_cmd_ p ev c' s).
Proof.
  rewrite /isem_cmd_; elim: c s => [ | i c hc] /= s.
  + rewrite bind_ret_l; reflexivity.
  rewrite bind_bind; setoid_rewrite hc; reflexivity.
Qed.

Lemma isem_cmd_while p ev ii al c e inf c' s:
  isem_cmd_ p ev [:: MkI ii (Cwhile al c e inf c')] s
  ≈
 isem_cmd_ p ev (c ++ [:: MkI ii (Cif e (c' ++ [:: MkI ii (Cwhile al c e inf c')]) [::])]) s.
Proof.
  rewrite /= isem_cmd_cat.
  rewrite /isem_while_loop unfold_iter bind_ret_r.
  rewrite /isem_while_round bind_bind /isem_cmd_.
  apply eutt_eq_bind => {}s /=; rewrite !bind_bind.
  apply eutt_eq_bind => -[] /=; last by rewrite !bind_ret_l; reflexivity.
  rewrite -/isem_cmd_ isem_cmd_cat; rewrite !bind_bind.
  apply eutt_eq_bind => {}s /= ; rewrite bind_ret_l !bind_ret_r tau_eutt; reflexivity.
Qed.

Definition estate0 (fs : fstate) :=
  Estate fs.(fscs) fs.(fmem) Vm.init.

Definition initialize_funcall (p : prog) (ev : extra_val_t) (fd : fundef) (fs : fstate) : exec estate :=
  let sinit := estate0 fs in
  Let vargs' := mapM2 ErrType dc_truncate_val (map eval_atype fd.(f_tyin)) fs.(fvals) in
  Let s0 := init_state fd.(f_extra) (p_extra p) ev sinit in
  write_vars (~~direct_call) fd.(f_params) vargs' s0.

Definition finalize_funcall (fd : fundef) (s:estate) : exec fstate :=
  Let vres := get_var_is (~~ direct_call) s.(evm) fd.(f_res) in
  Let vres' := mapM2 ErrType dc_truncate_val (map eval_atype fd.(f_tyout)) vres in
  let scs := s.(escs) in
  let m := finalize fd.(f_extra) s.(emem) in
  ok {| fscs := scs; fmem := m; fvals := vres' |}.

Definition ifinalize_funcall (fd : fundef) (s:estate) : itree E fstate :=
  err_result (fun e => (e, tt)) (finalize_funcall fd s).

(* similar, for proper function calls *)
Definition isem_fun_body (p : prog) (ev : extra_val_t)
   (fn : funname) (fs : fstate) :=
   fd <- kget_fundef (p_funcs p) fn fs;;
   let sinit := estate0 fs in
   isem_pre p sinit fn fs;;
   s1 <- iresult sinit (initialize_funcall p ev fd fs);;
   s2 <- isem_cmd_ p ev fd.(f_body) s1;;
   fr <- iresult s2 (finalize_funcall fd s2);;
   isem_post p s2 fn fs.(fvals) fr;;
   Ret fr.

(* A variant of the semantic based on exec, usefull for the proofs *)
Fixpoint esem_i (p : prog) (ev : extra_val_t) (i : instr) (s : estate) :
    exec estate :=
  let: (MkI ii i) := i in
  match i with
  | Cassgn x tg ty e => sem_assgn p x tg ty e s

  | Copn xs tg o es => sem_sopn (p_globs p) o s xs es

  | Csyscall xs o es => sem_syscall p xs o es s

  | Cassert a => Let _ := sem_assert (p_globs p) s a in ok s
  | Cif e c1 c2 =>
    Let b := sem_cond (p_globs p) e s in
    foldM (esem_i p ev) s (if b then c1 else c2)

  | Cwhile a c1 e i c2 => Error ErrSemUndef

  | Cfor i (d, lo, hi) c =>
    Let bounds := sem_bound (p_globs p) lo hi s in
    foldM (fun j s =>
      Let s := write_var true i (Vint j) s in
      foldM (esem_i p ev) s c)
     s (wrange d bounds.1 bounds.2)

  | Ccall xs fn args => Error ErrSemUndef
  end.

Definition esem (p : prog) (ev : extra_val_t) (c : cmd) (s : estate) :=
  foldM (esem_i p ev) s c.

Definition esem_for p ev i c :=
  foldM (fun j s =>
      Let s := write_var true i (Vint j) s in
      foldM (esem_i p ev) s c).

Lemma esem_i_bodyP p ev c s s' :
  esem p ev c s = ok s' -> isem_cmd_ p ev c s ≈ iresult s (ok s').
Proof.
  set Pi := fun i => forall s s', esem_i p ev i s = ok s' -> isem_i_body p ev i s ≈ iresult s (ok s').
  set Pi_r := fun i => forall ii, Pi (MkI ii i).
  set Pc := fun c => forall s s', foldM (esem_i p ev) s c = ok s' -> isem_cmd_ p ev c s ≈ iresult s (ok s').
  apply (cmd_rect (Pr := Pi_r) (Pi := Pi) (Pc := Pc)) => {s s' c} //.
  + move=> > /= [<-]; reflexivity.
  + by move=> i c hi hc s s' /=; t_xrbindP => s1 /hi ->; rewrite bind_ret_l; apply hc.
  1-3: move=> > /= -> /=; reflexivity.
  + move=> > /=; t_xrbindP; rewrite /isem_assert => -> ->; rewrite bind_ret_l; reflexivity.
  + move=> > hc1 hc2 ii s s' /=.
    rewrite /isem_cond; t_xrbindP => b -> /=.
    by rewrite bind_ret_l; case: b; [apply hc1 | apply hc2].
  move=> i d lo hi c hc ii s s' /=.
  rewrite /isem_bound; t_xrbindP => bound -> /=.
  rewrite bind_ret_l.
  elim: wrange s => {bound} => /= [ | j js hrec] s.
  + move=> [<-]; reflexivity.
  t_xrbindP => s1 s2 hw /hc{}hc /hrec{}hrec.
  rewrite /isem_for_round /= /iwrite_var hw /= bind_ret_l.
  by move: hc; rewrite /isem_cmd_ => -> /=; rewrite bind_ret_l.
Qed.

Lemma esem_cat p ev c1 c2 s : esem p ev (c1 ++ c2) s = Let s1 := esem p ev c1 s in esem p ev c2 s1.
Proof. by rewrite /esem foldM_cat. Qed.

Lemma esem_cons p ev i c s : esem p ev (i :: c) s = Let s1 := esem_i p ev i s in esem p ev c s1.
Proof. done. Qed.

Lemma esem_c_nil p ev s : esem p ev [::] s = ok s.
Proof. done. Qed.

Lemma esem1 p ev s i : esem p ev [::i] s = esem_i p ev i s.
Proof. by rewrite esem_cons; case: esem_i. Qed.

Lemma eEForOne p ev s1 s1' s2 s3 i w ws c :
  write_var true i (Vint w) s1 = ok s1' ->
  esem p ev c s1' = ok s2 ->
  esem_for p ev i c s2 ws = ok s3 ->
  esem_for p ev i c s1 (w :: ws) = ok s3.
Proof. by rewrite /esem => /= -> /= -> /=. Qed.

End SEM_I.

(*** error-aware interpreter with recursion ***************************)
Section SEM_F.

Context {E E0} {wE : with_Error E E0}.

Section EXTEQ.
Context (sem_F1 sem_F2: sem_Fun E) (p:prog) (ev:extra_val_t) .
Hypothesis sem_F_ext : forall ii fn fs,
  sem_fun (sem_Fun := sem_F1) p ev ii fn fs ≈ sem_fun (sem_Fun := sem_F2) p ev ii fn fs.

Lemma isem_cmd_ext c s :
  isem_cmd_ (sem_F := sem_F1) p ev c s ≈ isem_cmd_ (sem_F := sem_F2) p ev c s.
Proof.
  apply (cmd_rect
    (Pr := fun ir => forall ii s,
       isem_i_body (sem_F:=sem_F1) p ev (MkI ii ir) s ≈ isem_i_body (sem_F:=sem_F2) p ev (MkI ii ir) s)
    (Pi := fun i => forall s,
       isem_i_body (sem_F:=sem_F1) p ev i s ≈ isem_i_body (sem_F:=sem_F2) p ev i s)
    (Pc := fun c => forall s,
       isem_cmd_ (sem_F := sem_F1) p ev c s ≈ isem_cmd_ (sem_F := sem_F2) p ev c s)) => //{c s};
    try by move=> *; reflexivity.
  + move=> i c hi hc s /=; rewrite hi.
    apply eqit_bind; first reflexivity.
    by move=> s'; apply hc.
  + move=> e c1 c2 hc1 hc2 /= _ s.
    apply eqit_bind; first reflexivity.
    by move=> []; [apply hc1 | apply hc2].
  + move=> x dir lo hi c hc ii s /=.
    apply eqit_bind; first reflexivity.
    move=> bound; elim:wrange s => /=; first reflexivity.
    move=> j js hrec s; rewrite /isem_for_round.
    apply eqit_bind; first reflexivity.
    move=> ?; apply eqit_bind; first apply hc.
    move=> ?; apply hrec.
  + move=> al c e ii' c' hc hc' ii s /=.
    rewrite /isem_while_loop.
    apply eutt_iter=> {}s.
    rewrite /isem_while_round.
    apply eqit_bind; first apply hc.
    move=> ?; apply eqit_bind; first reflexivity.
    move=> []; last by reflexivity.
    by apply eqit_bind; [apply hc' | reflexivity].
  move=> xs f es ii s /=.
  apply eqit_bind; first reflexivity.
  move=> ?; apply eqit_bind; first reflexivity.
  move=> ?; apply eqit_bind; first by apply sem_F_ext.
  move=> ?; apply eqit_bind; first reflexivity.
  move=> ?; reflexivity.
Qed.

End EXTEQ.

(* semantics of instructions parametrized by recCall events *)
Definition isem_i_rec (p : prog) (ev : extra_val_t) (i : instr) (s : estate)
  : itree (recCall +' E) estate :=
  isem_i_body (sem_F := sem_fun_rec E) p ev i s.

(* similar, for commands *)
Definition isem_cmd_rec (p : prog) (ev : extra_val_t) (c : cmd) (s : estate)
  : itree (recCall +' E) estate :=
  isem_cmd_ (sem_F := sem_fun_rec E) p ev c s.

(* similar, for function calls *)
Definition isem_fun_rec (p : prog) (ev : extra_val_t)
   (fn : funname) (fs : fstate) : itree (recCall +' E) fstate :=
  isem_fun_body (sem_F := sem_fun_rec E) p ev fn fs.

(* handler of recCall events *)
Definition handle_recCall {sem_F : funname -> sem_Fun (recCall +' E)} (p : prog) (ev : extra_val_t) :
   recCall ~> itree (recCall +' E) :=
 fun T (rc : recCall T) =>
   match rc with
   | RecCall _ fn fs => isem_fun_body (sem_F:=sem_F fn) p ev fn fs
   end.

(* intepreter of recCall events for functions, giving us the recursive
   semantics of functions *)
Definition isem_fun_def {sem_F : funname -> sem_Fun (recCall +' E)} (p : prog) (ev : extra_val_t) (fn : funname) (fs : fstate) : itree E fstate :=
  mrec (handle_recCall (sem_F := sem_F) p ev) (RecCall dummy_instr_info fn fs).

Definition isem_fun := isem_fun_def (sem_F := fun _ => sem_fun_rec E).

#[global]
Instance sem_fun_full : sem_Fun E | 100 :=
  {| sem_fun := fun p ev ii => isem_fun p ev |}.

(* recursive semantics of instructions *)
Definition isem_i (p : prog) (ev : extra_val_t) (i : instr) (s : estate) : itree E estate :=
  isem_i_body (sem_F := sem_fun_full) p ev i s.

(* similar, for commands *)
Definition isem_cmd (p : prog) (ev : extra_val_t) (c : cmd) (s : estate) : itree E estate :=
  isem_cmd_ (sem_F := sem_fun_full) p ev c s.

(* Definition of a semantic allowing to immediately interprete call, this is used
   for inlining *)

Definition sem_fun_inline
   (do_inline :  funname (* caller *) -> instr_info -> funname (* callee *) -> bool)
   (caller : funname) :=
 {| sem_fun := fun (p : prog) (ev : extra_val_t) (ii:instr_info) (callee : funname) (fs : fstate) =>
     if do_inline caller ii callee then 
       isem_fun_rec p ev callee fs (* Interprete the call but not the internal ones *)
     else rec_call (E:=E) ii callee fs (* Do not interprete the call, simply emmit an event *)
 |}.

Definition isem_fun_inline
  (do_inline :  funname (* caller *) -> instr_info -> funname (* callee *) -> bool) :=
  isem_fun_def (sem_F := sem_fun_inline do_inline).

End SEM_F.

(* interpreter of error events, giving us the fully interpreted
   semantics of functions *)
Definition err_sem_fun (p : prog) (ev : extra_val_t) (fn : funname)
    (fs : fstate) : execT (itree void1) fstate :=
  interp_Err (isem_fun p ev fn fs).

(*** Core lemmas about the definition ********************************)
Section CoreLemmas.

Context {E E0: Type -> Type} {wE : with_Error E E0}.
Context (p : prog) (ev : extra_val_t).

Notation interp_rec := (interp (mrecursive (handle_recCall p ev))).

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
  eutt (E:=E) eq (interp (mrecursive (handle_recCall p ev)) (iresult s r)) (iresult s r).
Proof.
  case r => /= [? | ?].
  + rewrite interp_ret; reflexivity.
  apply interp_throw.
 Qed.

Lemma interp_isem_cmd c s :
  eutt (E:=E) eq (interp_rec (isem_foldr isem_i_rec p ev c s))
         (isem_foldr isem_i_body p ev c s).
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
       eutt (E:=E) eq (interp_rec (isem_foldr isem_i_rec p ev c s))
                      (isem_cmd p ev c s))) => // {c s}.
  + move=> s /=; rewrite interp_ret; reflexivity.
  + move=> i c hi hc s; rewrite interp_bind;apply eqit_bind; first by apply hi.
    by move=> s'; apply hc.
  1-3: by move=> >; apply interp_iresult.
  + move => a ii s /=.
    rewrite interp_bind; apply eqit_bind.
    + by apply interp_iresult.
    move => ?; rewrite interp_ret; reflexivity.
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
  + move=> al c1 e inf c2 hc1 hc2 ii s; rewrite /isem_i /isem_i_rec /= /isem_while_loop.
    rewrite interp_iter; apply eutt_iter=> {}s.
    rewrite /isem_while_round.
    rewrite interp_bind; apply eqit_bind; first by apply hc1.
    move=> s1; rewrite interp_bind; apply eqit_bind; first by apply interp_iresult.
    move=> [].
    + rewrite interp_bind; apply eqit_bind; first by apply hc2.
      move=> s2; rewrite interp_ret; reflexivity.
    rewrite interp_ret; reflexivity.
  move=> xs f es ii s; rewrite /isem_i /isem_i_rec /=.
  rewrite interp_bind; apply eqit_bind; first by apply interp_iresult.
  move=> vs; rewrite interp_bind; apply eqit_bind.
  + by apply interp_iresult.
  move => ?;rewrite interp_bind;apply eqit_bind.
  + rewrite interp_mrecursive; reflexivity.
  move => ?;rewrite interp_bind;apply eqit_bind.
  + by apply interp_iresult.
  move=> ?; exact: interp_iresult.
Qed.

Lemma isem_call_unfold (fn : funname) (fs : fstate) :
  isem_fun p ev fn fs ≈ isem_fun_body p ev fn fs.
Proof.
  rewrite {1}/isem_fun {1}/isem_fun_def.
  rewrite mrec_as_interp.
  rewrite {2}/handle_recCall /isem_fun_rec /isem_fun_body.
  rewrite interp_bind; apply eqit_bind.
  + by apply interp_ioget.
  move=> fd; rewrite interp_bind; apply eqit_bind.
  + by apply interp_iresult.
  move=> _; rewrite interp_bind; apply eqit_bind.
  + by apply interp_iresult.
  move=> s1; rewrite interp_bind; apply eqit_bind.
  + apply interp_isem_cmd.
  move=> s2; rewrite interp_bind; apply eqit_bind.
  + by apply interp_iresult.
  move=> fr; rewrite interp_bind; apply eqit_bind.
  + by apply interp_iresult.
  move=> _; rewrite interp_ret; reflexivity.
Qed.

Lemma interp_cond_throw  (cond : forall T, recCall T -> bool) (ctx : forall T, recCall T -> itree (recCall +' E) T) (e: error * unit) T :
  interp (ctx_cond cond ctx) (throw e) ≈ throw (X := T) e.
Proof.
  rewrite /throw interp_vis /= /inr_ /Inr_sum1_Handler /Handler.inr_ /Handler.htrigger.
  rewrite bind_trigger.
  by apply eqit_Vis => -[].
Qed.

Lemma interp_cond_iresult
  (cond : forall T, recCall T -> bool) (ctx : forall T, recCall T -> itree (recCall +' E) T) T (ex : exec T) (s : estate) :
   interp (ctx_cond cond ctx) (iresult s ex) ≈ iresult s ex.
Proof.
  rewrite /iresult; case ex => [t | e] /=.
  + rewrite interp_ret; reflexivity.
  by apply interp_cond_throw.
Qed.

Lemma isem_call_inline do_inline (fn : funname) (fs : fstate) :
  isem_fun p ev fn fs ≈ isem_fun_inline do_inline p ev fn fs.
Proof.
  rewrite /isem_fun /isem_fun_inline /isem_fun_def /handle_recCall /=.
  rewrite /isem_fun_body.
  set cond := fun  T1 (d1: recCall T1) T2 (d2: recCall T2) =>
    match d1, d2 with
    | RecCall _ caller _, RecCall ii callee _ => do_inline caller ii callee
    end.
  rewrite (mrec_loop2 cond).
  rewrite /mrec.
  set F := (X in ctx2_cond _ X).
  have haux : forall (ii1 : instr_info) (fn1 : funname) (fs1 : fstate),
    ctx2_cond cond F (RecCall ii1 fn1 fs1)
    ≈ fd <- kget_fundef (p_funcs p) fn1 fs1;;
      _ <- isem_pre p (estate0 fs1) fn1 fs1;;
      s1 <- iresult (estate0 fs1) (initialize_funcall p ev fd fs1);;
      s2 <- isem_cmd_ (sem_F:= sem_fun_inline do_inline fn1) p ev (f_body fd) s1;;
      fr <- iresult s2 (finalize_funcall fd s2) ;;
      _ <- isem_post p s2 fn1 (fvals fs1) fr;;
      Ret fr.
  + move=> ii1 fn1 fs1.
    rewrite /ctx2_cond /Handler.cat interp_bind.
    apply eutt_eq_bind'.
    + rewrite /kget_fundef; case: get_fundef => [fd | ] /=.
      + rewrite interp_ret; reflexivity.
      by apply interp_cond_throw.
    move=> fd.
    rewrite interp_bind. 
    apply eutt_eq_bind'.
    + rewrite interp_cond_iresult; reflexivity.
    move=> ?.
    rewrite interp_bind.
    apply eutt_eq_bind'.
    + by apply interp_cond_iresult.
    move=> s; rewrite interp_bind.
    apply eutt_eq_bind'; last first.
    + move=> ?; rewrite interp_bind; apply eutt_eq_bind'.
      + by apply interp_cond_iresult.
      move=> ?; rewrite interp_bind; apply eutt_eq_bind'.
      + by apply interp_cond_iresult.
      move=> ?; rewrite interp_ret; reflexivity.
    set Pi := fun i =>
      forall s,
       interp (ctx_cond (cond fstate (RecCall dummy_instr_info fn1 fs1)) F)
          (isem_i_body (sem_F := sem_fun_rec E) p ev i s) ≈
       isem_i_body (sem_F:= sem_fun_inline do_inline fn1) p ev i s.
    set Pr := fun i => forall ii, Pi (MkI ii i).
    set Pc := fun c =>
      forall s,
        interp (ctx_cond (cond fstate (RecCall dummy_instr_info fn1 fs1)) F)
          (isem_cmd_rec p ev c s) ≈
        isem_cmd_ (sem_F:= sem_fun_inline do_inline fn1) p ev c s.
    move: (f_body fd) s.
    apply (cmd_rect (Pr:=Pr) (Pi:=Pi) (Pc:=Pc)) => //=; subst Pi Pr Pc => /=.
    + move=> s; rewrite interp_ret; reflexivity.
    + by move=> i c hi hc s; rewrite interp_bind hi; apply/eutt_eq_bind/hc.
    + by move=> > ? >; apply interp_cond_iresult.
    + by move=> > ? > ? > ; apply interp_cond_iresult.
    + by move=> > ? >; apply interp_cond_iresult.
    + move=> a ii s; rewrite interp_bind; apply eutt_eq_bind'.
      + by apply interp_cond_iresult.
      move=> ?; rewrite interp_ret; reflexivity.
    + move=> e c1 c2 hc1 hc2 ii s; rewrite interp_bind.
      rewrite /isem_cond interp_cond_iresult.
      by apply/eutt_eq_bind; case; [apply hc1 | apply hc2].
    + move=> x dir lo hi c hc ii s; rewrite interp_bind.
      rewrite /isem_bound interp_cond_iresult.
      apply eutt_eq_bind => ? /=.
      elim: (wrange _ _) s => //= [ | j js hrec] s.
      + rewrite interp_ret; reflexivity.
      rewrite /isem_for_round interp_bind /iwrite_var interp_cond_iresult.
      apply eutt_eq_bind => ? /=.
      by rewrite interp_bind hc; apply eutt_eq_bind => ? /=; apply hrec.
    + move=> al c e ii' c' hc hc' ii s.
      rewrite /isem_while_loop interp_iter.
      apply eutt_iter => s'.
      rewrite /isem_while_round interp_bind hc.
      apply eutt_eq_bind => ?; rewrite interp_bind /isem_cond interp_cond_iresult.
      apply eutt_eq_bind => -[]; last first.
      + rewrite interp_ret; reflexivity.
      rewrite interp_bind hc'.
      apply eutt_eq_bind => ?.
      rewrite interp_ret; reflexivity.
    move=> xs f es ii s; rewrite interp_bind.
    rewrite /isem_pexprs interp_cond_iresult; apply eutt_eq_bind => ?.
    rewrite interp_bind; apply eutt_eq_bind'.
    + by apply interp_cond_iresult.
    move=> _; rewrite interp_bind; apply eutt_eq_bind'.
    + rewrite /ctx_cond /cond /Handler.case_ /rec_call /F.
      setoid_rewrite interp_trigger; reflexivity.
    move=> ?; rewrite interp_bind; apply eutt_eq_bind'.
    + by apply interp_cond_iresult. 
    by move=> ?; apply interp_cond_iresult.
  apply Proper_interp_mrec => //.
  by move=> T [].
Qed.

End CoreLemmas.

End WSW.
