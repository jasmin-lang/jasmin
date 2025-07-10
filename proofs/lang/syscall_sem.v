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
  {syscall_state : Type}.

Definition exec_getrandom_arg_u len vs :=
  Let _ :=
    match vs with
    | [:: v] => to_arr len v
    | _ => type_error
    end in
  ok (Zpos len).

Definition exec_syscall_arg_u (o : syscall_t) vs :=
  match o with
  | RandomBytes _ len => exec_getrandom_arg_u len vs
  end.

Definition exec_getrandom_store_u len (bytes: seq u8) :=
  WArray.fill len bytes.

Definition exec_syscall_store_u (o: syscall_t) (scs: syscall_state) (m:mem) (vs:values) (bytes : seq u8) :=
  match o with
  | RandomBytes _ len =>
    Let t :=  exec_getrandom_store_u len bytes in
    ok (scs, m, [::Varr t])
  end.

Lemma exec_syscall_argPu o vargs vargs' len :
  List.Forall2 value_uincl vargs vargs' ->
  exec_syscall_arg_u o vargs = ok len ->
  exec_syscall_arg_u o vargs' = ok len.
Proof.
  case: o => _ len' /=.
  rewrite /exec_getrandom_arg_u.
  case: vargs => // v1 [] // /List_Forall2_inv_l [v2] [l] [?] [hu] /List_Forall2_inv_l ?; subst vargs' l.
  by t_xrbindP => t /(val_uincl_of_val (ty := carr len') hu) [? /= ->] _ /= ->.
Qed.

Lemma exec_syscall_storePu o vargs vargs' scs scs' m m' bytes vres :
  List.Forall2 value_uincl vargs vargs' ->
  exec_syscall_store_u o scs m vargs bytes = ok (scs', m', vres) ->
  exec_syscall_store_u o scs m vargs' bytes = ok (scs', m', vres).
Proof. by case: o => _ len' /=. Qed.

Definition mem_equiv m1 m2 := stack_stable m1 m2 /\ validw m1 =3 validw m2.

Lemma exec_syscall_storeSu o scs m vargs bytes scs' m' vres :
  exec_syscall_store_u o scs m vargs bytes = ok (scs', m', vres) ->
  mem_equiv m m'.
Proof.
  case: o => ws len'; rewrite /exec_syscall_store_u /= /exec_getrandom_store_u.
  by t_xrbindP => ? _ _ -> _.
Qed.

Definition exec_syscall_u {sc_sem : syscall_sem syscall_state} (scs : syscall_state_t) (m : mem) (o:syscall_t) vs : exec (syscall_state_t * mem * values) :=
  Let len := exec_syscall_arg_u o vs in
  let (scs', bytes) := get_random scs len in
  exec_syscall_store_u o scs' m vs bytes.

End SourceSysCall.

Section StackSysCall.

Context {pd: PointerData} {syscall_state : Type} {sc_sem : syscall_sem syscall_state}.

Definition exec_getrandom_arg_s vs :=
  Let len :=
    match vs with
    | [:: v1; v2] => to_word Uptr v2
    | _ => type_error
    end in
  ok (wunsigned len).

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
     syscall_state_t -> mem -> sem_prod (map eval_atype (syscall_sig_s o).(scs_tin)) (exec (syscall_state_t * mem * sem_tuple (map eval_atype (syscall_sig_s o).(scs_tout)))) :=
  match o with
  | RandomBytes _ _ => exec_getrandom_s_core
  end.

Definition exec_syscall_arg_s (o : syscall_t) vs :=
  match o with
  | RandomBytes _ _ => exec_getrandom_arg_s vs
  end.

Definition exec_getrandom_store_s (vs : values) (m:mem) (bytes: seq u8) :=
  Let p :=
    match vs with
    | [:: v1; v2] => to_word Uptr v1
    | _ => type_error
    end in
  Let m := fill_mem m p bytes in
  ok (m, p).

Definition exec_syscall_store_s (o: syscall_t) (scs: syscall_state) (m:mem) (vs:values) (bytes : seq u8) :=
  match o with
  | RandomBytes _ _ =>
    Let mp := exec_getrandom_store_s vs m bytes in
    ok (scs, mp.1, [::Vword mp.2])
  end.

Lemma exec_syscall_argPs o vargs vargs' len :
  List.Forall2 value_uincl vargs vargs' ->
  exec_syscall_arg_s o vargs = ok len ->
  exec_syscall_arg_s o vargs' = ok len.
Proof.
  case: o => _ len' /=.
  rewrite /exec_getrandom_arg_s.
  case: vargs => // v1 [] // v2 [] // /List_Forall2_inv_l [v1'] [l] [?]
    [hu1] /List_Forall2_inv_l [v2'] [l'] [? [hu2 /List_Forall2_inv_l ?]].
  subst l l' vargs'.
  t_xrbindP => w /(val_uincl_of_val (ty := cword Uptr) hu2) /=.
  move=> [vt] -> /= /value_uinclE /=.
  by move=> [sz [w']] [] /Vword_inj [h] ?; subst => /= /word_uincl_eq -> ->.
Qed.

Lemma exec_syscall_storePs o vargs vargs' scs scs' m m' bytes vres :
  List.Forall2 value_uincl vargs vargs' ->
  exec_syscall_store_s o scs m vargs bytes = ok (scs', m', vres) ->
  exec_syscall_store_s o scs m vargs' bytes = ok (scs', m', vres).
Proof.
  case: o => _ len' /=.
  rewrite /exec_getrandom_store_s.
  case: vargs => // v1 [] // v2 [] // /List_Forall2_inv_l [v1'] [l] [?]
    [hu1] /List_Forall2_inv_l [v2'] [l'] [? [hu2 /List_Forall2_inv_l ?]].
  subst l l' vargs'.
  t_xrbindP => -[m_ w2] w1 /(val_uincl_of_val (ty := cword Uptr) hu1) /=.
  move=> [vt] -> /= /value_uinclE /=.
  move=> [sz [w']] [] /Vword_inj [h] ?; subst => /= /word_uincl_eq ->.
  by move=> m'' -> [-> ->] -> -> <- /=.
Qed.

Lemma exec_syscall_storeSs o scs m vargs bytes scs' m' vres :
  exec_syscall_store_s o scs m vargs bytes = ok (scs', m', vres) ->
  mem_equiv m m'.
Proof.
  case: o => _ len' /=.
  rewrite /exec_getrandom_store_s.
  case: vargs => // v1 [] // v2 [] //.
  t_xrbindP => -[m_ w2] w1 ? m'' hfill [<- _] _ <- /= _.
  split.
  + by apply: fill_mem_stack_stable hfill.
  by apply: fill_mem_validw_eq hfill.
Qed.

Definition exec_syscall_s (scs : syscall_state_t) (m : mem) (o:syscall_t) vs : exec (syscall_state_t * mem * values) :=
  Let len := exec_syscall_arg_s o vs in
  let (scs', bytes) := get_random scs len in
  exec_syscall_store_s o scs' m vs bytes.

Lemma syscall_sig_s_noarr o : all is_not_carr (map eval_atype (syscall_sig_s o).(scs_tin)).
Proof. by case: o. Qed.

Lemma sem_syscall_equiv o scs m :
  mk_forall (fun (rm: (syscall_state_t * mem * _)) => mem_equiv m rm.1.2)
            (sem_syscall o scs m).
Proof.
  case: o => _ws _len /= p len [[scs' rm] t] /= hex; split.
  + by apply: exec_getrandom_s_core_stable hex.
  by apply: exec_getrandom_s_core_validw hex.
Qed.

Lemma exec_syscallSs scs m o vargs rscs rm vres :
  exec_syscall_s scs m o vargs = ok (rscs, rm, vres) →
  mem_equiv m rm.
Proof.
  rewrite /exec_syscall_s; t_xrbindP => len ?;
  case: get_random => [scs' bytes].
  apply exec_syscall_storeSs.
Qed.

Lemma exec_syscallPs_eq scs m o vargs vargs' rscs rm vres :
  exec_syscall_s scs m o vargs = ok (rscs, rm, vres) →
  List.Forall2 value_uincl vargs vargs' →
  exec_syscall_s scs m o vargs' = ok (rscs, rm, vres).
Proof.
  rewrite /exec_syscall_s; t_xrbindP => len hexa.
  case heq: get_random => [scs' bytes] hexs hu.
  have -> /= := exec_syscall_argPs hu hexa.
  by rewrite heq (exec_syscall_storePs hu hexs).
Qed.

End StackSysCall.
