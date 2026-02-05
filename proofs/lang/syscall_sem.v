(* * Jasmin semantics with “partial values”. *)

(* ** Imports and settings *)
From mathcomp Require Import ssreflect ssrfun ssrbool seq ssralg.
From Coq Require Import ZArith.
Require Export utils syscall wsize word type low_memory sem_type values.
Import Utf8.

Local Open Scope Z_scope.



(* Unset Universe Checking. *)

Section SourceSysCall.

Context
  {pd: PointerData}
  {syscall_state : Type}
  {sc_sem : syscall_sem syscall_state} .
(*
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
  end. *)

Definition exec_getrandom_u_core ws (scs : syscall_state_t) (m : mem) N (a : WArray.array (Z.to_pos (arr_size ws N))) (n:pointer) :=
  let len := arr_size ws (Z.to_pos (wunsigned n)) in
  let sd := get_random scs len in
  Let t := WArray.fill (Z.to_pos len) sd.2 in
  Let a' := WArray.set_sub AAscale a 0 t in
  ok (sd.1, m, a').

Fixpoint dep_type (n : nat) (A : Type) (B : seq A -> Type) : Type :=
  match n with
  | 0%nat => B [::]
  | S n => forall (a : A), dep_type n (fun l => B (a :: l))
  end.

Fixpoint app_dep n A (B : seq A -> Type) : dep_type n B -> forall l : seq A, exec (B l) :=
  match n with
  | 0%nat => fun (b : B [::]) (l : seq A) => if l is [::] then ok b else type_error
  | S n => fun (f : forall (a : A), _) (l : seq A) =>
    if l is a :: l then app_dep (f a) l else type_error
  end.

Definition sem_syscall_u (N : length_var) (o : syscall_t) :
  syscall_state_t -> mem ->
  dep_type (size (syscall_sig_u N o).(scs_al))
    (fun l =>
      let env : length_var -> positive :=
        let als := zip (syscall_sig_u N o).(scs_al) l in
        fun x =>
        odflt 1%positive (xseq.assoc als x) (* should we fail instead of this default value? *)
       in
    (sem_prod (map (eval_atype env) (syscall_sig_u N o).(scs_tin))
         (exec (syscall_state_t * mem * sem_tuple (map (eval_atype env) (syscall_sig_u N o).(scs_tout)))))) :=
  match o with
  | RandomBytes ws =>
    ecast b (_ -> _ -> forall a,
      sem_prod [:: carr (Z.to_pos (arr_size ws (odflt 1%positive (if b then Some a else None)))); cword Uptr]
        (exec (_ * _ * sem_tuple [:: carr (Z.to_pos (arr_size ws (odflt 1%positive (if b then Some a else None))))])))
      (esym (eqtype.eq_refl N))
      (@exec_getrandom_u_core ws)
  end.

Definition exec_syscall_u (N:length_var) (scs : syscall_state_t) (m : mem) (o:syscall_t) (alargs: seq positive) (vs:values) : exec (syscall_state_t * mem * values) :=
  let semi := sem_syscall_u N o in
  Let semi := app_dep (semi scs m) alargs in
  Let: (scs', m', t) := app_sopn _ semi vs in
  ok (scs', m', list_ltuple t).

(*
Fixpoint dep_type (A : Type) n : lprod (nseq n A) Type -> Type :=
  match n with
  | 0 => fun B => B
  | S n => fun B => forall x : A, dep_type (B x)
  end.
Definition dep_type' A n (f:seq A -> Type) := dep_type (curry n f).

Definition split_tuple A n : ltuple (nseq (S n) A) -> A * ltuple (nseq n A) :=
  match n with
  | 0 => fun a => (a, tt)
  | S n => fun a => a
  end.

Fixpoint app (A : Type) n : lprod (nseq n A) Type -> ltuple (nseq n A) -> Type :=
  match n with
  | 0 => fun B _ => B
  | S n => fun B l => let (a, l) := split_tuple l in app (B a) l
  end.

Fixpoint app_dep A n (B : lprod (nseq n A) Type) : dep_type B -> forall l : ltuple (nseq n A), app B l.
case: n B.
simpl. move=> B b _. apply b.
move=> n B f l /=.
case: split_tuple => a l'.
have := app_dep A n (B a) (f a) l'. apply: id.
Defined.

Definition test o N : lprod (nseq (size (syscall_sig_u N o).(scs_al)) positive) Type. apply curry.
simpl. refine (fun l =>
  let env : length_var -> positive :=
        let als := zip (syscall_sig_u N o).(scs_al) l in
        fun x =>
        odflt 1%positive (xseq.assoc als x)
       in
       sem_prod (map (eval_atype env) (syscall_sig_u N o).(scs_tin))
         (exec (syscall_state_t * mem * sem_tuple (map (eval_atype env) (syscall_sig_u N o).(scs_tout))))).
Defined.

Definition sem_syscall_u (o:syscall_t) (N : length_var) :
     syscall_state_t -> mem -> dep_type (test o N).
     case: o => ws.
     rewrite /test /curry /= /sem_prod /=.
     move=> scs m len. rewrite eqtype.eq_refl /=. move=> ??. apply: exec_getrandom_u_core => //.
Defined.
*)

Lemma exec_syscallPu N scs m o alargs vargs vargs' rscs rm vres :
  exec_syscall_u N scs m o alargs vargs = ok (rscs, rm, vres) →
  List.Forall2 value_uincl vargs vargs' →
  exists2 vres' : values,
    exec_syscall_u N scs m o alargs vargs' = ok (rscs, rm, vres') & List.Forall2 value_uincl vres vres'.
Proof.
Local Opaque arr_size.
  rewrite /exec_syscall_u; case: o => [ ws ].
  case: alargs => // al [] //=.
  rewrite -> eqtype.eq_refl; move=> /=.
  move=> + hu.
  case: hu => // va va' {}vargs {}vargs' /of_value_uincl_te ha.
  case; first by t_xrbindP.
  move=> vn vn' {}vargs {}vargs' /of_value_uincl_te hn.
  case; last by t_xrbindP.
  t_xrbindP=> -[[{}scs' {}m'] ra] a /(ha (carr _)) {ha} [/= a' -> hincl] n /(hn (cword _)) /= -> hexec [<- <- <-].
  move: hexec; rewrite /exec_getrandom_u_core.
  t_xrbindP=> t ht {}ra hra <- <- <-.
  have [ra' hra' hincl'] := WArray.uincl_set_sub hincl (WArray.uincl_refl _) hra.
  by rewrite /= ht /= hra' /=; eexists; eauto.
Qed.

Definition mem_equiv m1 m2 := stack_stable m1 m2 /\ validw m1 =3 validw m2.

Lemma exec_syscallSu N scs m o alargs vargs rscs rm vres :
  exec_syscall_u N scs m o alargs vargs = ok (rscs, rm, vres) →
  mem_equiv m rm.
Proof.
  rewrite /exec_syscall_u; case: o => [ ws ].
  case: alargs => // al [] //=.
  rewrite -> eqtype.eq_refl; move=> /=.
  case: vargs => // va.
  case; first by t_xrbindP.
  move=> vn.
  case; last by t_xrbindP.
  t_xrbindP=> -[[scs' m'] v'] /= ? _ ? _.
  rewrite /exec_getrandom_u_core.
  by t_xrbindP=> _ _ _ _ _ <- _ _ <- _.
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

Definition sem_syscall_s (o : syscall_t) :
  syscall_state_t -> mem ->
  dep_type (size (syscall_sig_s o).(scs_al))
    (fun l =>
      let env : length_var -> positive :=
        let als := zip (syscall_sig_s o).(scs_al) l in
        fun x =>
        odflt 1%positive (xseq.assoc als x) (* should we fail instead of this default value? *)
       in
    (sem_prod (map (eval_atype env) (syscall_sig_s o).(scs_tin))
         (exec (syscall_state_t * mem * sem_tuple (map (eval_atype env) (syscall_sig_s o).(scs_tout)))))) :=
  match o with
  | RandomBytes _ => exec_getrandom_s_core
  end.

Definition exec_syscall_s (scs : syscall_state_t) (m : mem) (o:syscall_t) alargs vs : exec (syscall_state_t * mem * values) :=
  let semi := sem_syscall_s o in
  Let semi := app_dep (semi scs m) alargs in
  Let: (scs', m', t) := app_sopn _ semi vs in
  ok (scs', m', list_ltuple t).

Lemma syscall_sig_s_noarr o env : all is_not_carr (map (eval_atype env) (syscall_sig_s o).(scs_tin)).
Proof. by case: o. Qed.

Lemma exec_syscallPs_eq scs m o alargs vargs vargs' rscs rm vres :
  exec_syscall_s scs m o alargs vargs = ok (rscs, rm, vres) → 
  List.Forall2 value_uincl vargs vargs' → 
  exec_syscall_s scs m o alargs vargs' = ok (rscs, rm, vres).
Proof.
  rewrite /exec_syscall_s.
  t_xrbindP=> ? -> -[[scs' m'] vres'] happ [<- <- <-] hu /=.
  by have -> := vuincl_sopn (syscall_sig_s_noarr o _) hu happ.
Qed.

Lemma exec_syscallPs scs m o alargs vargs vargs' rscs rm vres :
  exec_syscall_s scs m o alargs vargs = ok (rscs, rm, vres) → 
  List.Forall2 value_uincl vargs vargs' → 
  exists2 vres' : values,
    exec_syscall_s scs m o alargs vargs' = ok (rscs, rm, vres') & List.Forall2 value_uincl vres vres'.
Proof.
  move=> h1 h2; rewrite (exec_syscallPs_eq h1 h2).
  by exists vres=> //; apply List_Forall2_refl.
Qed.

Lemma sem_syscall_s_equiv o scs m alargs semi :
  app_dep (sem_syscall_s o scs m) alargs = ok semi ->
  mk_forall (fun (rm: (syscall_state_t * mem * _)) => mem_equiv m rm.1.2) semi.
Proof.
  case: o semi => _ws /=.
  case: alargs => // _ [<-] /= p n [[scs' rm] t] hex; split.
  + by apply: exec_getrandom_s_core_stable hex.
  by apply: exec_getrandom_s_core_validw hex.
Qed.

Lemma exec_syscallSs scs m o alargs vargs rscs rm vres :
  exec_syscall_s scs m o alargs vargs = ok (rscs, rm, vres) → 
  mem_equiv m rm.
Proof.
  rewrite /exec_syscall_s.
  t_xrbindP=> semi hsemi -[[scs' m'] vres'] happ [_ <- _].
  apply (mk_forallP (sem_syscall_s_equiv hsemi) happ).
Qed.

End Section.
