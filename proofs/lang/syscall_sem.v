(* * Jasmin semantics with “partial values”. *)

(* ** Imports and settings *)
From mathcomp Require Import all_ssreflect all_algebra.
Require Import ZArith Psatz.
Require Export utils syscall wsize word type low_memory sem_type values.
Import Utf8.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope Z_scope.




Section SourceSysCall.

Context
  {pd: PointerData}
  {syscall_state : Type}
  {sc_sem : syscall_sem syscall_state} .

Definition exec_getrandom_u (scs : syscall_state) len vs :=
  Let _ :=
    match vs with
    | [:: v] => to_arr len v
    | _ => type_error
    end in
  let sd := get_random scs (Zpos len) in
  Let t := WArray.fill len sd.2 in
  ok (sd.1, [::Varr t]).

Definition data_of_array (len: positive) (a: WArray.array len) : seq u8 :=
  map snd (Mz.elements (WArray.arr_data a)).

Definition exec_open_u (scs : syscall_state) (len: positive) (vs : seq value) : exec (syscall_state * seq value) :=
  Let a :=
    match vs with
    | [:: v] => to_arr len v
    | _ => type_error
    end in
  let '(st, fd) := open_file scs (data_of_array a) in
  ok (st, [::Vword fd]).

Definition exec_close_u (scs : syscall_state) (vs : seq value) := 
  Let a :=
    match vs with
    | [:: v] => to_word U64 v
    | _ => type_error
    end in
  let '(st, success) := close_file scs a in
  ok (st, [::Vword success]).

Definition exec_write_u (scs : syscall_state) (len: positive) (vs : seq value) : exec (syscall_state * seq value) :=
  Let a :=
    match vs with
    | [:: v; fd] => (to_arr len v, to_word U64 fd)
    | _ => type_error
    end in
  let '(st, ret) := write_to_file scs (data_of_array a.1) a.2 in
  Let t := WArray.fill len ret in
  ok (st, [:: Varr t]).

Definition exec_syscall_u
  (scs : syscall_state_t)
  (m : mem)
  (o : syscall_t)
  (vs : values) :
  exec (syscall_state_t * mem * values) :=
  match o with
  | RandomBytes len =>
      Let sv := exec_getrandom_u scs len vs in
      ok (sv.1, m, sv.2)
  | Open len => 
      Let: (st, fd) := exec_open_u scs len vs in
      ok (st, m, fd)
  | Close =>
      Let: (st, ret) := exec_close_u scs vs in
      ok (st, m, ret)
  end.

Lemma exec_syscallPu scs m o vargs vargs' rscs rm vres :
  exec_syscall_u scs m o vargs = ok (rscs, rm, vres) →
  List.Forall2 value_uincl vargs vargs' →
  exists2 vres' : values,
    exec_syscall_u scs m o vargs' = ok (rscs, rm, vres') & List.Forall2 value_uincl vres vres'.
Proof.
  rewrite /exec_syscall_u; case: o => [ p | p | p ].
  t_xrbindP => -[scs' v'] /= h ??? hu; subst scs' m v'.
  move: h; rewrite /exec_getrandom_u.
  case: hu => // va va' ?? /of_value_uincl_te h [] //.
  t_xrbindP => a /h{h}[? /= -> ?] ra hra ??; subst rscs vres.
  by rewrite hra /=; eexists; eauto.
Admitted.

Definition mem_equiv m1 m2 := stack_stable m1 m2 /\ validw m1 =2 validw m2.

Lemma exec_syscallSu scs m o vargs rscs rm vres :
  exec_syscall_u scs m o vargs = ok (rscs, rm, vres) →
  mem_equiv m rm.
Proof.
  rewrite /exec_syscall_u; case: o => [ p | | ].
  by t_xrbindP => -[scs' v'] /= _ _ <- _.
Admitted.

End SourceSysCall.

Section Section.

Context {pd: PointerData} {syscall_state : Type} {sc_sem : syscall_sem syscall_state}.

Definition exec_getrandom_s_core (scs : syscall_state_t) (m : mem) (p:pointer) (len:pointer) : exec (syscall_state_t * mem * pointer) := 
  let len := wunsigned len in
  let sd := syscall.get_random scs len in
  Let m := fill_mem m p sd.2 in
  ok (sd.1, m, p).

Definition exec_open_file_s_core (scs : syscall_state_t) (m : mem) (p:pointer) (len:pointer) : exec (syscall_state_t * mem * word U64) := 
  let len := wunsigned len in
  let '(st, fd) := syscall.open_file scs [::] in (** FIXME: ??? *)
  ok (st, m, fd).

Definition exec_close_file_s_core (scs : syscall_state_t) (m : mem) (p:word U64) : exec (syscall_state_t * mem * word U8) :=
  let '(st, success) := syscall.close_file scs p in
  ok (st, m, success). (** FIXME: ??? *)

Lemma exec_getrandom_s_core_stable scs m p len rscs rm rp : 
  exec_getrandom_s_core scs m p len = ok (rscs, rm, rp) →
  stack_stable m rm.
Proof. by rewrite /exec_getrandom_s_core; t_xrbindP => rm' /fill_mem_stack_stable hf ? <- ?. Qed.

Lemma exec_getrandom_s_core_validw scs m p len rscs rm rp : 
  exec_getrandom_s_core scs m p len = ok (rscs, rm, rp) →
  validw m =2 validw rm.
Proof. by rewrite /exec_getrandom_s_core; t_xrbindP => rm' /fill_mem_validw_eq hf ? <- ?. Qed.

Definition sem_syscall (o:syscall_t) : 
     syscall_state_t -> mem -> sem_prod (syscall_sig_s o).(scs_tin) (exec (syscall_state_t * mem * sem_tuple (syscall_sig_s o).(scs_tout))) := 
  match o with
  | RandomBytes _ => exec_getrandom_s_core
  | Open _ => exec_open_file_s_core
  | Close => exec_close_file_s_core
  end.

Definition exec_syscall_s (scs : syscall_state_t) (m : mem) (o:syscall_t) vs : exec (syscall_state_t * mem * values) :=
  let semi := sem_syscall o in
  Let: (scs', m', t) := app_sopn _ (semi scs m) vs in
  ok (scs', m', list_ltuple t).
  
Lemma syscall_sig_s_noarr o : all is_not_sarr (syscall_sig_s o).(scs_tin).
Proof. by case: o. Qed.

Lemma exec_syscallPs_eq scs m o vargs vargs' rscs rm vres :
  exec_syscall_s scs m o vargs = ok (rscs, rm, vres) → 
  List.Forall2 value_uincl vargs vargs' → 
  exec_syscall_s scs m o vargs' = ok (rscs, rm, vres).
Proof.
  rewrite /exec_syscall_s; t_xrbindP => -[[scs' m'] t] happ [<- <- <-] hu.
  by have -> := vuincl_sopn (syscall_sig_s_noarr o ) hu happ.
Qed.
 
Lemma exec_syscallPs scs m o vargs vargs' rscs rm vres :
  exec_syscall_s scs m o vargs = ok (rscs, rm, vres) → 
  List.Forall2 value_uincl vargs vargs' → 
  exists2 vres' : values,
    exec_syscall_s scs m o vargs' = ok (rscs, rm, vres') & List.Forall2 value_uincl vres vres'.
Proof.
  move=> h1 h2; rewrite (exec_syscallPs_eq h1 h2).
  by exists vres=> //; apply List_Forall2_refl.
Qed.

Lemma sem_syscall_equiv o scs m : 
  mk_forall (fun (rm: (syscall_state_t * mem * _)) => mem_equiv m rm.1.2)
            (sem_syscall o scs m).
Proof.
Admitted.
(**  case: o => _len /= p len [[scs' rm] t] /= hex; split.
  + by apply: exec_getrandom_s_core_stable hex. 
  by apply: exec_getrandom_s_core_validw hex.
Admitted. **)

Lemma exec_syscallSs scs m o vargs rscs rm vres :
  exec_syscall_s scs m o vargs = ok (rscs, rm, vres) → 
  mem_equiv m rm.
Proof.
  rewrite /exec_syscall_s; t_xrbindP => -[[scs' m'] t] happ [_ <- _].
  apply (mk_forallP (sem_syscall_equiv o scs m) happ).
Qed.

End Section.
