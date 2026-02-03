(* * Jasmin semantics with “partial values”. *)

(* ** Imports and settings *)
From mathcomp Require Import ssreflect ssrfun ssrbool seq ssralg.
From Coq Require Import ZArith.
Require Export utils syscall wsize word type low_memory sem_type values.
Import Utf8.

Local Open Scope Z_scope.




Section SourceSysCall.

Context
  {pd: PointerData}
  {syscall_state : Type}
  {sc_sem : syscall_sem syscall_state} .

Definition exec_getrandom_u (scs : syscall_state) len vs :=
  Let: (a, n) :=
    match vs with
    | [:: va; vn] =>
      Let a := to_arr len va in
      Let n := to_word Uptr vn in
      ok (a, n)
    | _ => type_error
    end in
  let sd := get_random scs (wunsigned n) in
  Let t := WArray.fill len sd.2 in
  Let a' := WArray.set_sub AAscale (ws:=U8) a 0 t in
  ok (sd.1, [::Varr a']).

Definition exec_syscall_u
  {pd : PointerData}
  (env : length_var -> positive)
  (scs : syscall_state_t)
  (m : mem)
  (o : syscall_t)
  (al : seq array_length)
  (vs : values) :
  exec (syscall_state_t * mem * values) :=
  match o with
  | RandomBytes ws =>
    Let al :=
      match al with
      | [:: al] => ok al
      | _ => Error ErrType
      end
    in
    let len := Z.to_pos (arr_size ws (eval env al)) in
    Let sv := exec_getrandom_u scs len vs in
    ok (sv.1, m, sv.2)
  end.

Lemma exec_syscallPu env scs m o al vargs vargs' rscs rm vres :
  exec_syscall_u env scs m o al vargs = ok (rscs, rm, vres) →
  List.Forall2 value_uincl vargs vargs' →
  exists2 vres' : values,
    exec_syscall_u env scs m o al vargs' = ok (rscs, rm, vres') & List.Forall2 value_uincl vres vres'.
Proof.
Local Opaque arr_size.
  rewrite /exec_syscall_u; case: o => [ ws ].
  case: al => // al [] //=.
  t_xrbindP => -[scs' v'] /= h ??? hu; subst scs' m v'.
  move: h; rewrite /exec_getrandom_u.
  case: hu => // va va' _ _ /of_value_uincl_te ha [] // vn vn' _ _ /of_value_uincl_te hn [] //=.
  t_xrbindP => -[_ _] a /(ha (carr _)) {ha} [/= a' -> hincl] n /(hn (cword _)) /= -> [<- <-].
  t_xrbindP => t ht ra hra ??; subst rscs vres.
  have [ra' hra' hincl'] := WArray.uincl_set_sub hincl (WArray.uincl_refl _) hra.
  by rewrite /= ht /= hra' /=; eexists; eauto.
Local Transparent arr_size.
Qed.

Definition mem_equiv m1 m2 := stack_stable m1 m2 /\ validw m1 =3 validw m2.

Lemma exec_syscallSu env scs m o al vargs rscs rm vres :
  exec_syscall_u env scs m o al vargs = ok (rscs, rm, vres) →
  mem_equiv m rm.
Proof.
Local Opaque arr_size.
  rewrite /exec_syscall_u; case: o => [ ws ].
  case: al => // al [] //=.
  by t_xrbindP => -[scs' v'] /= _ _ <- _.
Local Transparent arr_size.
Qed.

End SourceSysCall.

Section Section.

Context {pd: PointerData} {syscall_state : Type} {sc_sem : syscall_sem syscall_state}.

Definition exec_getrandom_s_core (scs : syscall_state_t) (m : mem) (p:pointer) (len:pointer) : exec (syscall_state_t * mem * pointer) := 
  let len := wunsigned len in
  let sd := syscall.get_random scs len in
  Let m := fill_mem m p sd.2 in
  ok (sd.1, m, p).

Lemma exec_getrandom_s_core_stable scs m p len rscs rm rp :
  exec_getrandom_s_core scs m p len = ok (rscs, rm, rp) →
  stack_stable m rm.
Proof. by rewrite /exec_getrandom_s_core; t_xrbindP => rm' /fill_mem_stack_stable hf ? <- ?. Qed.

Lemma exec_getrandom_s_core_validw scs m p len rscs rm rp : 
  exec_getrandom_s_core scs m p len = ok (rscs, rm, rp) →
  validw m =3 validw rm.
Proof. by rewrite /exec_getrandom_s_core; t_xrbindP => rm' /fill_mem_validw_eq hf ? <- ?. Qed.

Definition sem_syscall (o:syscall_t) :
     forall env, syscall_state_t -> mem -> sem_prod (map (eval_atype env) (syscall_sig_s o).(scs_tin)) (exec (syscall_state_t * mem * sem_tuple (map (eval_atype env) (syscall_sig_s o).(scs_tout)))) := 
  match o with
  | RandomBytes _ => fun _ => exec_getrandom_s_core
  end.

Definition exec_syscall_s env (scs : syscall_state_t) (m : mem) (o:syscall_t) vs : exec (syscall_state_t * mem * values) :=
  let semi := sem_syscall o env in
  Let: (scs', m', t) := app_sopn _ (semi scs m) vs in
  ok (scs', m', list_ltuple t).

Lemma syscall_sig_s_noarr o env : all is_not_carr (map (eval_atype env) (syscall_sig_s o).(scs_tin)).
Proof. by case: o. Qed.

Lemma exec_syscallPs_eq env scs m o vargs vargs' rscs rm vres :
  exec_syscall_s env scs m o vargs = ok (rscs, rm, vres) → 
  List.Forall2 value_uincl vargs vargs' → 
  exec_syscall_s env scs m o vargs' = ok (rscs, rm, vres).
Proof.
  rewrite /exec_syscall_s; t_xrbindP => -[[scs' m'] t] happ [<- <- <-] hu.
  by have -> := vuincl_sopn (syscall_sig_s_noarr o env) hu happ.
Qed.

Lemma exec_syscallPs env scs m o vargs vargs' rscs rm vres :
  exec_syscall_s env scs m o vargs = ok (rscs, rm, vres) → 
  List.Forall2 value_uincl vargs vargs' → 
  exists2 vres' : values,
    exec_syscall_s env scs m o vargs' = ok (rscs, rm, vres') & List.Forall2 value_uincl vres vres'.
Proof.
  move=> h1 h2; rewrite (exec_syscallPs_eq h1 h2).
  by exists vres=> //; apply List_Forall2_refl.
Qed.

Lemma sem_syscall_equiv o env scs m :
  mk_forall (fun (rm: (syscall_state_t * mem * _)) => mem_equiv m rm.1.2)
            (sem_syscall o env scs m).
Proof.
  case: o => _ws p len [[scs' rm] t] /= hex; split.
  + by apply: exec_getrandom_s_core_stable hex.
  by apply: exec_getrandom_s_core_validw hex.
Qed.

Lemma exec_syscallSs env scs m o vargs rscs rm vres :
  exec_syscall_s env scs m o vargs = ok (rscs, rm, vres) → 
  mem_equiv m rm.
Proof.
  rewrite /exec_syscall_s; t_xrbindP => -[[scs' m'] t] happ [_ <- _].
  apply (mk_forallP (sem_syscall_equiv o env scs m) happ).
Qed.

End Section.
