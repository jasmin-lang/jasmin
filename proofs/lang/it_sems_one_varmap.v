(** Semantics of the “one-varmap” intermediate language.
*)
From ITree Require Import
     Basics
     ITree
     ITreeFacts
     Events.Exception
     Interp.Handler
     Interp.Interp
     Interp.InterpFacts
     Interp.Recursion
     Interp.RecursionFacts
     MonadState.
Import Basics.Monads.

Require psem one_varmap sem_one_varmap it_sems_core.
Import Utf8.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.
Export one_varmap sem_one_varmap.
Import psem it_sems_core var.
Import low_memory.

Local Unset Elimination Schemes.

Import MonadNotation.
Local Open Scope monad_scope.

(** Semantics of programs in which there is a single scope for local variables.
Function arguments and returns are passed by name:
the caller puts the arguments in the right variables and read them from the right variables.

Also the instructions may be annotated with variables that are known to be free:
this semantics explicitly kills these variables before executing the corresponding instruction.

The semantics also ensures some properties:

 - No for loop
 - Calls to “rastack” functions are annotated with free variables
 - The sp_rsp local variable always hold the pointer to the top of the stack
 - The sp_rip local variable is assumed to hold the pointer to the static global data
 - The var_tmp a set of local variables free at the beginning of export functions

The semantic predicates are indexed by a set of variables which is *precisely* the set of variables that are written during the execution.
 *)

#[local] Existing Instance withsubword.
#[local] Existing Instance progStack.
#[local] Existing Instance noassert.

Section SEM.

Context
  {asm_op syscall_state : Type}
  {ep : EstateParams syscall_state}
  {spp : SemPexprParams}
  {sip : SemInstrParams asm_op syscall_state}
  {ovm_i : one_varmap_info}
.

Section SEM_C.

  Context
    {E E0}
      {wE : with_Error E E0}
      (sem_i: sprog -> instr -> estate -> itree E (Sv.t * estate))
      (p : prog).

(* folding instruction semantics on commands *)

(*
Definition isem_foldr (c: cmd) : estate -> itree E (Sv.t * estate) :=
  foldr (fun i k s => s' <- sem_i p ev i s.2 ;; k (Sv.union s.1 s'.1, s'.2))
        (fun s => Ret (Sv.empty, s)) c.
*)
(*
Fixpoint isem_cmd_ (c: cmd) : estate -> itree E (Sv.t * estate) :=
  fun s =>
   match c with
   | [::] => Ret (Sv.empty, s)
   | i :: c => ks <- sem_i p ev i s;; ks' <- isem_cmd_ c ks.2;; Ret (Sv.union ks.1 ks'.1, ks'.2)
   end.
*)

Fixpoint isem_cmd_ (c: cmd) : Sv.t * estate -> itree E (Sv.t * estate) :=
  fun ks =>
   match c with
   | [::] => Ret ks
   | i :: c => ks' <- sem_i p i ks.2;; isem_cmd_ c (Sv.union ks.1 ks'.1, ks'.2)
   end.

(* Make global definition *)
Local Notation continue_loop s := (ret (inl s)).
Local Notation exit_loop s := (ret (inr s)).

Definition isem_while_round (c1 : cmd) (e : pexpr) (c2 : cmd) (s : Sv.t * estate) :
    itree E (Sv.t * estate + Sv.t * estate) :=
  s <- isem_cmd_ c1 s;;
  b <- isem_cond p e s.2;;
  if b then s <- isem_cmd_ c2 s;; continue_loop s
  else exit_loop s.

Definition isem_while_loop (c1 : cmd) (e:pexpr) (c2: cmd) (s : Sv.t * estate) :
    itree E (Sv.t * estate) :=
  ITree.iter (isem_while_round c1 e c2) s.

End SEM_C.

Notation add_fv fv :=
  (Result.map (aT:=estate) (rT:=Sv.t * estate) (fun (s:estate) => (fv, s))).

(* semantics of instructions, abstracting on function calls (through
   sem_fun) *)

Variant recCallK : Type -> Type :=
 | RecCallK (f:funname) (fs: estate) : recCallK (Sv.t * estate).

Class sem_FunK (E : Type -> Type) :=
  { sem_funK : sprog -> funname -> estate -> itree E (Sv.t * estate) }.

(* recCall trigger *)
Definition rec_callK {E : Type -> Type} (f : funname) (fs : estate) :
   itree (recCallK +' E) (Sv.t * estate) :=
  trigger_inl1 (RecCallK f fs).

#[global]
Instance sem_funK_rec (E : Type -> Type) : sem_FunK (recCallK +' E) | 0 :=
  {| sem_funK := fun _ => rec_callK (E:=E) |}.

Context (var_tmp : Sv.t).

Section SEM_I.

  Context
    {E E0}
      {wE : with_Error E E0}
      {rndE0 : RndEvent syscall_state -< E}
      {sem_F : sem_FunK E}.

Let vrsp (p:sprog) : var := vid p.(p_extra).(sp_rsp).
Let vgd (p:sprog) : var := vid p.(p_extra).(sp_rip).

Definition valid_RSP p m vm :=
  value_eqb vm.[vrsp p] (Vword (top_stack m)).

Definition saved_stack_valid_init (p:sprog) fd :=
  match sf_save_stack (f_extra fd) with
  | SavedStackReg r => [&& r != vgd p & r != vrsp p]
  | _ => true
  end.

Definition saved_stack_valid_final (p:sprog) fd (k:Sv.t) :=
  match sf_save_stack (f_extra fd) with
  | SavedStackReg r => ~~ Sv.mem r k
  | _ => true
  end.

Definition initialize_funcall (p:sprog) f (fs:estate) :=
 Let _ := assert [&& top_stack_aligned f fs.(emem)
                   & valid_RSP p fs.(emem) fs.(evm)] ErrSemUndef in
 Let m1 :=
   Result.map_err (fun _ => ErrSemUndef)
      (alloc_stack fs.(emem)
      f.(f_extra).(sf_align)
      f.(f_extra).(sf_stk_sz)
      f.(f_extra).(sf_stk_ioff)
      f.(f_extra).(sf_stk_extra_sz)) in
 let vm1 := ra_undef_vm f fs.(evm) var_tmp in
 ok {| escs := fs.(escs); emem := m1; evm := set_RSP p m1 vm1; |}.

Definition is_disjoint_magic (p:sprog) fn :=
  match get_fundef (p_funcs p) fn with
  | Some fd =>
      assert (disjoint (ra_vm (f_extra fd) Sv.empty) (magic_variables p)) ErrSemUndef
  | None => Error ErrSemUndef
  end.

Definition is_init_state_ok (p:sprog) fn fs :=
  match get_fundef (p_funcs p) fn with
  | Some fd =>
      Let _ := Result.map_err (fun _ => ErrSemUndef) (initialize_funcall (p:sprog) fd fs) in ok tt
  | None => Error ErrSemUndef
  end.

Definition writefun_RA (p:sprog) (fn: funname) :=
  match get_fundef (p_funcs p) fn with
  | None => Sv.empty
  | Some fd => Sv.union (ra_undef fd var_tmp) (ra_vm_return fd.(f_extra))
  end.

Fixpoint isem_i(p : sprog) (i : instr) (s : estate) :
    itree E (Sv.t * estate) :=
  let: (MkI ii i) := i in
  ks <- isem_ir p i s;;
  _ <- iresult (ks.2)
         (assert ([&& is_stack_stable (emem s) (emem ks.2)
                    , valid_RSP p (emem ks.2) (evm ks.2)
                    & disjoint ks.1 (magic_variables p)]) ErrSemUndef);;
  Ret ks
with isem_ir (p : sprog) (i : instr_r) (s : estate) : itree E (Sv.t * estate) :=
  match i with
  | Cassgn x tg ty e => iresult s (add_fv (vrv x) (sem_assgn p x tg ty e s))

  | Copn xs tg o es => iresult s (add_fv (vrvs xs) (sem_sopn (p_globs p) o s xs es))

  | Csyscall xs o es =>
      let fv := Sv.union syscall_kill (vrvs (to_lvals (syscall_sig o).(scs_vout))) in
      vs <- @isem_pexprs withsubword syscall_state ep spp E E0 wE true (p_globs p) es s;;
      fs <- fexec_syscall s o (mk_fstate vs s);;
      iresult s (add_fv fv  (upd_estate true (p_globs p) xs fs s))

  | Cif e c1 c2 =>
    b <- isem_cond p e s;;
    isem_cmd_ isem_i p (if b then c1 else c2) (Sv.empty, s)

  | Cwhile a c1 e i c2 =>
    isem_while_loop isem_i p c1 e c2 (Sv.empty, s)

  | Ccall xs fn args =>
    let fi := kill_tmp_call p fn s in
    iresult s (is_disjoint_magic p fn);;
    fs <- sem_funK p fn fi;;
    iresult s (assert (valid_RSP p (emem fi) (evm fs.2) && Sv.subset (writefun_RA p fn) fs.1) ErrSemUndef);;
    Ret (Sv.union fs.1 (fd_tmp_call p fn), kill_tmp_call p fn fs.2)

  | Cassert _ => Exception.throw (ErrSemUndef, tt)
  | Cfor _ _ _ => Exception.throw (ErrSemUndef, tt)
  end.

Definition isem_cmd (p:sprog) c s :=
  isem_cmd_ isem_i p c (Sv.empty, s).

Definition finalize_funcall p f ks2 :=
  let (k, s2') := (ks2.1, ks2.2) in
  Let _ := assert [&& ra_valid p f k
                    , saved_stack_valid_final p f k
                    & valid_RSP p s2'.(emem) s2'.(evm)] ErrSemUndef in
  let m2 := free_stack s2'.(emem) in
  let vm2 := kill_vars (ra_vm_return f.(f_extra)) s2'.(evm) in
  let s2 := {| escs := s2'.(escs); emem := m2 ; evm := set_RSP p m2 vm2 |} in
  let k' := Sv.union (ra_undef f var_tmp) (ra_vm_return f.(f_extra)) in
  ok (Sv.union k k', s2).

Definition isem_fun_body (p : prog)
   (fn : funname) (fs : estate) :=
   fd <- ioget (ErrSemUndef, tt) (get_fundef (p_funcs p) fn);;
   iresult fs (assert (saved_stack_valid_init p fd) ErrSemUndef);;
   s1 <- iresult fs (Result.map_err (fun _ => ErrSemUndef) (initialize_funcall p fd fs));;
   ks2 <- isem_cmd p fd.(f_body) s1;;
   ks3 <- iresult ks2.2 (finalize_funcall p fd ks2);;
   _ <- iresult ks3.2 (assert (is_stack_stable (emem fs) (emem ks3.2)) ErrSemUndef);;
   Ret ks3.

End SEM_I.

(* semantics of instructions parametrized by recCall events *)

Section REC.
Context {E E0} {wE : with_Error E E0}  {rndE0 : RndEvent syscall_state -< E}
.

Definition isem_ir_rec (p : sprog) (i : instr_r) (s : estate)
  : itree (recCallK +' E) (Sv.t * estate) :=
  isem_ir (sem_F := sem_funK_rec E) p i s.

Definition isem_i_rec (p : sprog) (i : instr) (s : estate)
  : itree (recCallK +' E) (Sv.t * estate) :=
  isem_i (sem_F := sem_funK_rec E) p i s.


Definition isem_cmd_rec (p : sprog) (c : cmd) (s : estate)
  : itree (recCallK +' E) (Sv.t * estate) :=
  isem_cmd (sem_F := sem_funK_rec E) p c s.

Definition isem_fun_rec (p : sprog)
   (fn : funname) (fs : estate) : itree (recCallK +' E) (Sv.t * estate) :=
  isem_fun_body (sem_F := sem_funK_rec E) p fn fs.

(* handler of recCallK events *)
Definition handle_recCallK {sem_F : funname -> sem_FunK (recCallK +' E)}
  (p : sprog) :
   recCallK ~> itree (recCallK +' E) :=
 fun T (rc : recCallK T) =>
   match rc with
   | RecCallK fn fs => isem_fun_body (sem_F:=sem_F fn) p fn fs
   end.

Definition isem_fun_def {sem_F : funname -> sem_FunK (recCallK +' E)} (p : sprog) (fn : funname) (fs : estate) : itree E (Sv.t * estate) :=
  mrec (handle_recCallK (sem_F := sem_F) p) (RecCallK fn fs).

(* This is the semantics we want to use for the proof of merge_varmaps *)
Definition isem_fun := isem_fun_def (sem_F := fun _ => sem_funK_rec E).

(* We define an alternative semantics which is used for the proof of linearization,
   where we check that the stack can be allocate before emitting the call event
 *)
Instance sem_funK_rec_check  {E E0} {wE : with_Error E E0} : sem_FunK (recCallK +' E) | 0 :=
  {| sem_funK := fun (p:sprog) fn fs =>
     (_ <- iresult fs (Result.map_err (fun _ => ErrSemUndef) (is_init_state_ok p fn fs));;
      rec_callK (E:=E) fn fs)%itree |}.

Definition isem_fun_check := isem_fun_def (sem_F := fun _ => sem_funK_rec_check).

(* Equivalence between the two semantic, it is mostly the proof of rec_facts.CHECK.mrec_check,
   and some administrative stuff *)
Lemma isem_fun_isem_fun_check (p:sprog) fn s :
  isem_fun p fn s ≈ isem_fun_check p fn s.
Proof.
  rewrite /isem_fun /isem_fun_check /isem_fun_def.
  rewrite (rec_facts.CHECK.mrec_check
    (check:= fun T (rc : recCallK T) =>
       match rc with RecCallK fn fs => is_ok (is_init_state_ok p fn fs) end)
    (exn := (ErrSemUndef, tt))); last first.
  + move=> T [] {}fn {}s; rewrite /is_init_state_ok /handle_recCallK /isem_fun_body.
    case: (get_fundef (p_funcs p) fn) => [fd | ] /=; last first.
    + rewrite bind_throw; reflexivity.
    rewrite bind_ret_l.
    case: saved_stack_valid_init => /=; last first.
    + rewrite bind_throw; reflexivity.
    rewrite bind_ret_l; case: initialize_funcall => //=.
    move=> _ _; rewrite bind_throw; reflexivity.
  rewrite /mrec; apply Proper_interp_mrec.
  + move=> T [] {}fn {}s.
    rewrite /rec_facts.CHECK.ctx' /= /rec_facts.CHECK.ctx1 /=.
    set (F := case_ _ _).
    rewrite /isem_fun_body.
    have F_throw : forall e, interp F (throw e) ≈ throw e.
    + by move=> ??; rewrite interp_vis bind_vis; apply eqit_Vis => -[].
    have F_iresult : forall s T (r : exec T), interp F (iresult s r) ≈ iresult s r.
    + move=> s1 T1 [v | err] /=; first by rewrite interp_ret; reflexivity.
      rewrite F_throw; reflexivity.
    case: get_fundef => [fd | ] /=; last by rewrite !bind_throw F_throw; reflexivity.
    rewrite !bind_ret_l !interp_bind !F_iresult; apply eqit_bind; first reflexivity.
    move=> []; rewrite !interp_bind !F_iresult; apply eqit_bind; first reflexivity.
    move=> s1; rewrite !interp_bind; apply eqit_bind; last first.
    + move=> s2; rewrite !interp_bind !F_iresult; apply eqit_bind; first reflexivity.
      move=> s3; rewrite !interp_bind !F_iresult; apply eqit_bind; first reflexivity.
      move=> []; rewrite interp_ret; reflexivity.
    apply (cmd_rect
            (Pr := fun i => forall s,
              interp F (isem_ir (sem_F:= sem_funK_rec E) p i s) ≈
              isem_ir (sem_F:= sem_funK_rec_check) p i s)
            (Pi := fun i => forall s,
              interp F (isem_i (sem_F:= sem_funK_rec E) p i s) ≈
              isem_i (sem_F:= sem_funK_rec_check) p i s)
            (Pc := fun c => forall s,
              interp F (isem_cmd_ (isem_i (sem_F:= sem_funK_rec E)) p c s) ≈
              isem_cmd_ (isem_i (sem_F:= sem_funK_rec_check)) p c s)) => {fd s s1} /=.
    + move=> i ii ih s; rewrite !interp_bind ih; apply eqit_bind; first reflexivity.
      move=> ?; rewrite interp_bind F_iresult; apply eqit_bind; first reflexivity.
      move=> ?; rewrite interp_ret; reflexivity.
    + move=> ?; rewrite interp_ret; reflexivity.
    + move=> i c hi hc s; rewrite !interp_bind hi; setoid_rewrite hc; reflexivity.
    1-2: by move=> *; apply F_iresult.
    + move => *.
      rewrite interp_bind //.
      rewrite /isem_pexprs F_iresult.
      apply eqit_bind; first reflexivity.
      move => ?. rewrite interp_bind.
      rewrite /fexec_syscall interp_bind F_iresult.
      apply eutt_eq_bind'.
      + apply eutt_eq_bind';first reflexivity .
        move=> ?; rewrite interp_bind.
        apply eutt_eq_bind'.
        setoid_rewrite interp_trigger; reflexivity.
        move=> ?; rewrite interp_bind.
        apply eutt_eq_bind'.
        rewrite  F_iresult; reflexivity.
        move => ?. rewrite interp_ret;reflexivity.
        move => ?. rewrite  F_iresult; reflexivity.
    + by move=> *; apply F_throw.
    + move=> e c1 c2 hc1 hc2 s; rewrite interp_bind F_iresult; apply eqit_bind; first reflexivity.
      by move=> []; [apply hc1 | apply hc2].
    + by move=> *; apply F_throw.
    + move=> al c e iiw c' hc hc' s.
      rewrite /isem_while_loop; apply interp_iter'_eutt => s1.
      rewrite /isem_while_round !interp_bind hc; apply eqit_bind; first reflexivity.
      move=> s2; rewrite interp_bind F_iresult; apply eqit_bind; first reflexivity.
      move=> [].
      + rewrite !interp_bind hc'; apply eqit_bind; first reflexivity.
        move=> s3; rewrite interp_ret; reflexivity.
      rewrite interp_ret; reflexivity.
    move=> *; rewrite !interp_bind F_iresult; apply eqit_bind; first reflexivity.
    move=> ?; rewrite /rec_callK /= interp_bind bind_bind.
    rewrite interp_vis /= bind_bind {1}/rec_facts.CHECK.dup.
    case: is_init_state_ok => /= [? | err]; last by rewrite !bind_throw; reflexivity.
    rewrite !bind_ret_l; apply eqit_bind; first reflexivity.
    move=> ?.
    rewrite interp_ret bind_tau bind_ret_l.
    setoid_rewrite tau_euttge.
    rewrite interp_bind F_iresult; apply eqit_bind; first reflexivity.
    move=> ?; rewrite interp_ret; reflexivity.
  rewrite /rec_facts.CHECK.ctx' /= /rec_facts.CHECK.ctx1 /=.
  set (F := case_ _ _).
  rewrite /isem_fun_body.
  have F_throw : forall e, interp F (throw e) ≈ throw e.
  + by move=> ??; rewrite interp_vis bind_vis; apply eqit_Vis => -[].
  have F_iresult : forall s T (r : exec T), interp F (iresult s r) ≈ iresult s r.
  + move=> s1 T1 [v | err] /=; first by rewrite interp_ret; reflexivity.
    rewrite F_throw; reflexivity.
  case: get_fundef => [fd | ] /=; last by rewrite !bind_throw F_throw; reflexivity.
  rewrite !bind_ret_l !interp_bind !F_iresult; apply eqit_bind; first reflexivity.
  move=> []; rewrite !interp_bind !F_iresult; apply eqit_bind; first reflexivity.
  move=> s1; rewrite !interp_bind; apply eqit_bind; last first.
  + move=> s2; rewrite !interp_bind !F_iresult; apply eqit_bind; first reflexivity.
    move=> s3; rewrite !interp_bind !F_iresult; apply eqit_bind; first reflexivity.
    move=> []; rewrite interp_ret; reflexivity.
  apply (cmd_rect
          (Pr := fun i => forall s,
            interp F (isem_ir (sem_F:= sem_funK_rec E) p i s) ≈
            isem_ir (sem_F:= sem_funK_rec_check) p i s)
          (Pi := fun i => forall s,
            interp F (isem_i (sem_F:= sem_funK_rec E) p i s) ≈
            isem_i (sem_F:= sem_funK_rec_check) p i s)
          (Pc := fun c => forall s,
            interp F (isem_cmd_ (isem_i (sem_F:= sem_funK_rec E)) p c s) ≈
            isem_cmd_ (isem_i (sem_F:= sem_funK_rec_check)) p c s)) => {fd s s1} /=.
  + move=> i ii ih s; rewrite !interp_bind ih; apply eqit_bind; first reflexivity.
    move=> ?; rewrite interp_bind F_iresult; apply eqit_bind; first reflexivity.
    move=> ?; rewrite interp_ret; reflexivity.
  + move=> ?; rewrite interp_ret; reflexivity.
  + move=> i c hi hc s; rewrite !interp_bind hi; setoid_rewrite hc; reflexivity.
    1-2: by move=> *; apply F_iresult.
        + move => *.
      rewrite interp_bind //.
      rewrite /isem_pexprs F_iresult.
      apply eqit_bind; first reflexivity.
      move => ?. rewrite interp_bind.
      rewrite /fexec_syscall interp_bind F_iresult.
      apply eutt_eq_bind'.
      + apply eutt_eq_bind';first reflexivity .
        move=> ?; rewrite interp_bind.
        apply eutt_eq_bind'.
        setoid_rewrite interp_trigger; reflexivity.
        move=> ?; rewrite interp_bind.
        apply eutt_eq_bind'.
        rewrite  F_iresult; reflexivity.
        move => ?. rewrite interp_ret;reflexivity.
        move => ?. rewrite  F_iresult; reflexivity.
  + by move=> *; apply F_throw.
  + move=> e c1 c2 hc1 hc2 s; rewrite interp_bind F_iresult; apply eqit_bind; first reflexivity.
    by move=> []; [apply hc1 | apply hc2].
  + by move=> *; apply F_throw.
  + move=> al c e iiw c' hc hc' s.
    rewrite /isem_while_loop; apply interp_iter'_eutt => s1.
    rewrite /isem_while_round !interp_bind hc; apply eqit_bind; first reflexivity.
    move=> s2; rewrite interp_bind F_iresult; apply eqit_bind; first reflexivity.
    move=> [].
    + rewrite !interp_bind hc'; apply eqit_bind; first reflexivity.
      move=> s3; rewrite interp_ret; reflexivity.
    rewrite interp_ret; reflexivity.
  move=> *; rewrite !interp_bind F_iresult; apply eqit_bind; first reflexivity.
  move=> ?; rewrite /rec_callK /= interp_bind bind_bind.
  rewrite interp_vis /= bind_bind {1}/rec_facts.CHECK.dup.
  case: is_init_state_ok => /= [? | err]; last by rewrite !bind_throw; reflexivity.
  rewrite !bind_ret_l; apply eqit_bind; first reflexivity.
  move=> ?.
  rewrite interp_ret bind_tau bind_ret_l.
  setoid_rewrite tau_euttge.
  rewrite interp_bind F_iresult; apply eqit_bind; first reflexivity.
  move=> ?; rewrite interp_ret; reflexivity.
Qed.

Definition isem_exportcall (p:sprog) (gd: @extra_val_t progStack) fn (s:estate) :=
  fd <-ioget (ErrType, tt) (get_fundef p.(p_funcs) fn);;
  let vrsp : var := vid p.(p_extra).(sp_rsp) in
  let vgd : var := vid p.(p_extra).(sp_rip) in
  let vm := s.(evm) in
  _ <- iresult s (assert [&& is_RAnone fd.(f_extra).(sf_return_address)
                           , disjoint (sv_of_list fst fd.(f_extra).(sf_to_save)) (sv_of_list v_var fd.(f_res))
                           , ~~ Sv.mem vrsp (sv_of_list v_var fd.(f_res))
                           & value_eqb vm.[vgd] (Vword gd)]
                          ErrSemUndef);;
  ks2 <- isem_fun p fn s;;
  let (k, s2) := (ks2.1, ks2.2) in
  _ <- iresult s2 (assert (Sv.subset (Sv.inter callee_saved (Sv.union k (ra_undef fd var_tmp)))
                                     (sv_of_list fst fd.(f_extra).(sf_to_save)))
                      ErrSemUndef);;
  Ret s2.

Definition isem_exportcall_check (p:sprog) (gd: @extra_val_t progStack) fn (s:estate) :=
  fd <-ioget (ErrType, tt) (get_fundef p.(p_funcs) fn);;
  let vrsp : var := vid p.(p_extra).(sp_rsp) in
  let vgd : var := vid p.(p_extra).(sp_rip) in
  let vm := s.(evm) in
  _ <- iresult s (assert [&& is_RAnone fd.(f_extra).(sf_return_address)
                           , disjoint (sv_of_list fst fd.(f_extra).(sf_to_save)) (sv_of_list v_var fd.(f_res))
                           , ~~ Sv.mem vrsp (sv_of_list v_var fd.(f_res))
                           & value_eqb vm.[vgd] (Vword gd)]
                          ErrSemUndef);;
 _ <- iresult s (Result.map_err (fun _ => ErrSemUndef)
        (alloc_stack s.(emem)
          fd.(f_extra).(sf_align)
          fd.(f_extra).(sf_stk_sz)
          fd.(f_extra).(sf_stk_ioff)
          fd.(f_extra).(sf_stk_extra_sz)));;
  ks2 <- isem_fun_check p fn s;;
  let (k, s2) := (ks2.1, ks2.2) in
  _ <- iresult s2 (assert (Sv.subset (Sv.inter callee_saved (Sv.union k (ra_undef fd var_tmp)))
                                     (sv_of_list fst fd.(f_extra).(sf_to_save)))
                      ErrSemUndef);;
  Ret s2.

End REC.

End SEM.
