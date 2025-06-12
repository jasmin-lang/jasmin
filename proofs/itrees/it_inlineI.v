(* ** Imports and settings *)
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrfun ssrbool.
Require Import expr compiler_util allocation.

Local Open Scope seq_scope.

Module Import E.

  Definition pass : string := "inlining".

  Definition inline_error msg := {|
    pel_msg := msg;
    pel_fn := None;
    pel_fi := None;
    pel_ii := None;
    pel_vi := None;
    pel_pass := Some pass;
    pel_internal := true
  |}.

End E.

(* ** inlining
 * -------------------------------------------------------------------- *)

Section INLINE.

Context
  {wsw : WithSubWord}
  {asm_op syscall_state : Type}
  {asmop: asmOp asm_op}
  (rename_fd : instr_info -> funname -> ufundef -> ufundef)
  (dead_vars_fd : ufun_decl -> instr_info -> Sv.t)
.

Definition get_flag (x:lval) flag :=
  match x with
  | Lvar x => if is_inline_var x then AT_inline else flag
  | _      => flag
  end.

Definition assgn_tuple iinfo (xs:lvals) flag (tys:seq stype) (es:pexprs) :=
  let assgn xe := MkI iinfo (Cassgn xe.1 (get_flag xe.1 flag) xe.2.1 xe.2.2) in
  map assgn (zip xs (zip tys es)).

Definition inline_c (inline_i: instr -> Sv.t -> cexec (Sv.t * cmd)) c s :=
  foldr (fun i r =>
    Let r := r in
    Let ri := inline_i i r.1 in
    ok (ri.1, ri.2 ++ r.2)) (ok (s,[::])) c.

Definition sparams (fd:ufundef) :=
  vrvs_rec Sv.empty (map Lvar fd.(f_params)).

Definition locals_p (fd:ufundef) :=
  let s := read_es (map Plvar fd.(f_res)) in
  let w := write_c_rec s fd.(f_body) in
  let r := read_c_rec w fd.(f_body) in
  vrvs_rec r (map Lvar fd.(f_params)).

Definition locals fd :=
  Sv.diff (locals_p fd) (sparams fd).

Definition check_rename f (fd1 fd2:ufundef) (s:Sv.t) :=
  Let _ := check_ufundef dead_vars_fd tt tt (f,fd1) (f,fd2) tt in
  let s2 := locals_p fd2 in
  if disjoint s s2 then ok tt
  else Error (inline_error (pp_s "invalid refreshing in function")).

Definition get_fun (p:ufun_decls) (f:funname) :=
  match get_fundef p f with
  | Some fd => ok fd
  | None    => Error (inline_error (pp_box [::pp_s "Unknown function"; PPEfunname f]))
  end.

Fixpoint inline_i (px: ufun_decls) (i:instr) (X:Sv.t) : cexec (Sv.t * cmd) :=
  let '(MkI iinfo ir) := i in
  match ir with
  | Cassgn _ _ _ _
  | Copn _ _ _ _
  | Csyscall _ _ _
    => ok (Sv.union (read_i ir) X, [::i])
  | Cif e c1 c2  =>
    Let c1 := inline_c (inline_i px) c1 X in
    Let c2 := inline_c (inline_i px) c2 X in
    ok (read_e_rec (Sv.union c1.1 c2.1) e, [::MkI iinfo (Cif e c1.2 c2.2)])
  | Cfor x (d,lo,hi) c =>
    let X := Sv.union (read_i ir) X in
    Let c := inline_c (inline_i px) c X in
    ok (X, [::MkI iinfo (Cfor x (d, lo, hi) c.2)])
  | Cwhile a c e info c' =>
    let X := Sv.union (read_i ir) X in
    Let c := inline_c (inline_i px) c X in
    Let c' := inline_c (inline_i px) c' X in
    ok (X, [::MkI iinfo (Cwhile a c.2 e info c'.2)])
  | Ccall xs f es =>
    let X := Sv.union (read_i ir) X in
    if ii_is_inline iinfo then
      Let fd := add_iinfo iinfo (get_fun px f) in
      let fd' := rename_fd iinfo f fd in
      Let _ := add_iinfo iinfo (check_rename f fd fd' (Sv.union (vrvs xs) X)) in
      let ii := ii_with_location iinfo in
      let rename_args :=
        assgn_tuple ii (map Lvar fd'.(f_params)) AT_rename fd'.(f_tyin) es
      in
      let rename_res :=
        assgn_tuple ii xs AT_rename fd'.(f_tyout) (map Plvar fd'.(f_res))
      in
      ok (X, rename_args ++ fd'.(f_body) ++ rename_res)
    else ok (X, [::i])
  end.

Definition inline_fd (p:ufun_decls) (fd:ufundef) :=
  match fd with
  | MkFun ii tyin params c tyout res ef =>
    let s := read_es (map Plvar res) in
    Let c := inline_c (inline_i p) c s in
    ok (MkFun ii tyin params c.2 tyout res ef)
  end.

Definition inline_fd_cons (ffd:funname * ufundef) (p:cexec ufun_decls) :=
  Let p := p in
  let f := ffd.1 in
  Let fd := add_funname f (add_finfo ffd.2.(f_info) (inline_fd p ffd.2)) in
  ok ((f,fd):: p).

Definition inline_prog (p:ufun_decls) :=
  foldr inline_fd_cons (ok [::]) p.

Definition inline_prog_err (p:uprog) :=
  if uniq [seq x.1 | x <- p_funcs p] then
    Let fds := inline_prog (p_funcs p) in
    ok {| p_extra := p_extra p; p_globs := p_globs p; p_funcs := fds |}
  else Error (inline_error (pp_s "two function declarations with the same name")).

End INLINE. 

(*******************************************************)

From Paco Require Import paco.

From ITree Require Import
     Basics
     ITree
     ITreeFacts
     Events.Exception
     Interp.Recursion
     MonadState
     Eq.Paco2.

Import Basics.Monads.

Require Import it_sems_coreP.

Require Import inline_lemmaI2.

Require Import expr psem_defs psem_core it_exec tfam_iso.

Section IT_section.

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

Context
  (rename_fd : instr_info -> funname -> ufundef -> ufundef)
  (dead_vars_fd : ufun_decl -> instr_info -> Sv.t).

Notation recCall := (callE (funname * fstate) fstate).

Section IT_section1.

Context {E E0} {wE : with_Error E E0} (* {sem_F : sem_Fun E } *)
  (p : prog) (ev : extra_val_t).

Definition flat_i_sem (i: instr) (s: estate) :
  itree (recCall +' E) estate :=
  isem_i_body p ev i s.

Definition flat_cmd_sem (c: cmd) (s: estate) :
  itree (recCall +' E) estate :=
  isem_cmd_rec p ev c s.

Definition flat_fun_sem (fn: funname) (fs: fstate) :
  itree (recCall +' E) fstate :=
  isem_fun_body p ev fn fs.

Definition flat_fundef_sem (fd: fundef) (fs: fstate) :
  itree (recCall +' E) fstate :=
  isem_fundef_body p ev fd fs.

Notation sem_inline it :=
  (interp (ext_handler (handle_recCall p ev)) it).

Notation RA_tr it :=
  (translate (@rassoc_tr recCall recCall E) it).

Definition handle_2recCall :
  (recCall +' recCall) ~> itree ((recCall +' recCall) +' E) :=
  joint_handler (handle_recCall p ev) (handle_recCall p ev). 

(* eutt eq is too strong, both for the eutt (there might be errors) and 
   for the eq (the two states are related, not necessarily equal) *)

(* T := (kt s) is the tagged itree

partial semantics of the source program: S := asem_i s

partial semantics of the abstract inlined program: 
AI := (sem_inline (RA_tr T))

partial semantics of the concretely inlined program: 
CI := (asem_c s)

By the high-level lemma, we know the full semantics of AI equals to
the full semantics of T.

So by 2, the full semantics of T equals the full semantics of
CI.

By 1, the full semantics of S equals the full semantics of forgetful T.

The semantics of T equals that of the forgetful T.

So the full semantics of S equals that of CI. 
*)
Definition inline_i_info (i: instr) (c: cmd) : Type :=
  let asem_i := flat_i_sem i in 
  let asem_c := flat_cmd_sem c in
  sig (fun (kt: estate -> itree ((recCall +' recCall) +' E) estate) =>
    (forall s, eutt eq (forget_tr (kt s)) (asem_i s)) /\ 
    (forall s, eutt eq (sem_inline (RA_tr (kt s))) (asem_c s))).

Definition inline_ir_info (ir: instr_r) (ii: instr_info) (c: cmd) : Type :=
  let asem_i := flat_i_sem (MkI ii ir) in 
  let asem_c := flat_cmd_sem c in
  sig (fun (kt: estate -> itree ((recCall +' recCall) +' E) estate) =>
    (forall s, eutt eq (forget_tr (kt s)) (asem_i s)) /\
    (forall s, eutt eq (sem_inline (RA_tr (kt s))) (asem_c s))).

Definition inline_cmd_info (c1 c2: cmd) : Type :=
  let asem_c1 := flat_cmd_sem c1 in 
  let asem_c2 := flat_cmd_sem c2 in
  sig (fun (kt: estate -> itree ((recCall +' recCall) +' E) estate) =>
    (forall s, eutt eq (forget_tr (kt s)) (asem_c1 s)) /\
    (forall s, eutt eq (sem_inline (RA_tr (kt s))) (asem_c2 s))).

Definition inl_ext {F1 F2} F3 (X: F1 -< F2) : F1 -< F2 +' F3 :=
  fun T y => inl1 (X T y).

Definition inr_ext {F1 F2} F3 (X: F1 -< F2) : F1 -< F3 +' F2 :=
  fun T y => inr1 (X T y).

Variant ResultSim T1 T2 (RR: T1 -> T2 -> Prop) :
    result error T1 -> result error T2 -> Type :=
  | ResultSim_error : forall e, ResultSim (Error e) (Error e)
  | ResultSim_ok : forall t1 t2, RR t1 t2 -> ResultSim (ok t1) (ok t2).            
Lemma err_result_forget_eqit b1 b2 (D1 E1: Type -> Type) (X: ErrEvent -< E1)
  (Err : error -> error_data) T1 T2 (RR: T1 -> T2 -> Prop)
  (t1: result error T1) (t2: result error T2) (H: ResultSim RR t1 t2) : 
  eqit RR b1 b2 (translate (@forget_f D1 E1)
             (@err_result ((D1 +' D1) +' E1) (inr_ext _ X) Err T1 t1))
          (@err_result (D1 +' E1) (inr_ext _ X) Err T2 t2).
Proof.
  destruct H; simpl.
  - pstep; red; simpl.
    econstructor; intro v. destruct v.
  - pstep; red; simpl.
    econstructor; auto.
Qed.    

Lemma err_result_rassoc_eqit b1 b2 (D1 E1: Type -> Type) (X: ErrEvent -< E1)
  (Err : error -> error_data) (hh: D1 ~> itree (D1 +' E1)) T1 T2 (RR: T1 -> T2 -> Prop)
  (t1: result error T1) (t2: result error T2) (H: ResultSim RR t1 t2) : 
  eqit RR b1 b2 (interp (ext_handler hh) (translate (@rassoc_tr D1 D1 E1)
          (@err_result ((D1 +' D1) +' E1) (inr_ext _ X) Err T1 t1)))
    (@err_result (D1 +' E1) (inr_ext _ X) Err T2 t2).
Proof.
  destruct H; simpl.
  - pstep; red; simpl.
    econstructor. intros v; destruct v.
  - pstep; red; simpl.
    econstructor; eauto.
Qed.    


Context (InputRel : fstate -> estate -> Prop)
        (CStateRel : estate -> estate -> Prop).
 (*       (FStateRel : fstate -> estate -> Prop). *)

Lemma inline_cmd_x (px: ufun_decls) (c1: cmd) :
  forall (X: Sv.t),
  option (Sv.t * sigT (fun c2: cmd => inline_cmd_info c1 c2)).
Proof.
  set (Pr := fun ir => forall (ii: instr_info) (sv: Sv.t),
               option (Sv.t * sigT (fun c2: cmd => inline_ir_info ir ii c2))).
  set (Pi := fun i => forall (sv: Sv.t),
                 option (Sv.t * sigT (fun c2: cmd => inline_i_info i c2))).
  set (Pc := fun c1 => forall (sv: Sv.t),
               option (Sv.t * sigT (fun c2: cmd => inline_cmd_info c1 c2))).  
  set (CR := cmd_rect (Pr := Pr) (Pi := Pi) (Pc := Pc)).       
  eapply CR.
  
  { intros ir ii H sv0; subst Pr Pi; simpl in *. 
    destruct (H ii sv0) as [[sv [c2 H0]] | ].       
    2: { exact None. }
    unfold inline_ir_info in H0.
    econstructor 1; split.
    exact sv.
    exists c2.
    unfold inline_i_info.
    exact H0.
  }
  
  { intros sv0.
    set C := inline_c (inline_i rename_fd dead_vars_fd px) [::] sv0.
    simpl in *.                  
    destruct C as [[sv c2] | ] eqn: was_C.
    2: { exact None. }
    inv was_C.
    subst Pc; simpl.
    econstructor 1; split.
    exact sv.
    exists [::].
    unfold inline_cmd_info.
    exists (fun s => Ret s); split; simpl; intro s.
    { unfold forget_tr.
      rewrite translate_ret; reflexivity.
    }
    { rewrite translate_ret.
      rewrite interp_ret; reflexivity.
    }
  }

  { intros i c Hi Hc sv0.
    destruct (Hi sv0) as [[sv_i [c2_i Hi1]] | ].
    2: { exact None. }
    destruct (Hc sv_i) as [[sv_c [c2_c Hc1]] | ]. 
    2: { exact None. }
    econstructor 1.
    split.
    exact sv_c.
    exists (c2_i ++ c2_c).
    unfold inline_i_info, inline_cmd_info in Hi1, Hc1.
    unfold inline_cmd_info. 
    destruct Hi1 as [kt1 [Hi1 Hi2]].
    destruct Hc1 as [kt2 [Hc1 Hc2]].

    set kt := (fun s => bind (kt1 s) kt2).
    exists kt; split; simpl; intro s; subst kt; unfold forget_tr.

    { rewrite translate_bind.
      eapply eqit_bind; eauto.
      eapply Hi1.
    }
    { rewrite translate_bind.
      setoid_rewrite isem_cmd_cat; simpl.
      rewrite interp_bind.
      eapply eqit_bind; eauto.
      eapply Hi2.
    }
  }

  { intros x tg ty e.
    subst Pr; simpl; intros ii sv0.
    econstructor 1; split.
    exact sv0.
    exists ( [:: (MkI ii (Cassgn x tg ty e))] ).
    unfold inline_ir_info.

    set kt := (fun s => @free_tr recCall recCall E _
                          (flat_i_sem (MkI ii (Cassgn x tg ty e)) s)).
    exists kt; split; subst kt; simpl; intro s.
    { rewrite <- forget_free_inv_lemma.
      reflexivity.
    }
    { setoid_rewrite <- rassoc_free_interp_lemma at 1.
      setoid_rewrite bind_ret_r.
      reflexivity.
    }
  }

  { intros xs t o es.
    subst Pr; simpl; intros ii sv0.
    econstructor 1; split.
    exact sv0.
    exists ( [:: (MkI ii (Copn xs t o es))] ).
    unfold inline_ir_info.

    set kt := (fun s => @free_tr recCall recCall E _
                          (flat_i_sem (MkI ii (Copn xs t o es)) s)).
    exists kt; split; subst kt; simpl; intro s.
    { rewrite <- forget_free_inv_lemma.
      reflexivity.
    }
    { setoid_rewrite <- rassoc_free_interp_lemma at 1.
      setoid_rewrite bind_ret_r.
      reflexivity.
    }
  }

  { intros xs o es.
    subst Pr; simpl; intros ii sv0.
    econstructor 1; split.
    exact sv0.
    exists ( [:: (MkI ii (Csyscall xs o es))] ).
    unfold inline_ir_info.

    set kt := (fun s => @free_tr recCall recCall E _
                          (flat_i_sem (MkI ii (Csyscall xs o es)) s)).
    exists kt; split; subst kt; simpl; intro s.
    { rewrite <- forget_free_inv_lemma.
      reflexivity.
    }
    { setoid_rewrite <- rassoc_free_interp_lemma at 1.
      setoid_rewrite bind_ret_r.
      reflexivity.
    }
  }

  { rename c1 into c0.
    intros e c1 c2 Hc1 Hc2.
    subst Pr; simpl; intros ii sv0.
    unfold Pc in Hc1, Hc2.
    
    destruct (Hc1 sv0) as [[sv1 [c1R [kt1 [Hc1A Hc1B]]]] | ].
    2: { exact None. }
    destruct (Hc2 sv0) as [[sv2 [c2R [kt2 [Hc2A Hc2B]]]] | ].
    2: { exact None. }

    set svR := (read_e_rec (Sv.union sv1 sv2) e).
    econstructor 1; split.
    exact svR.

    exists ([::MkI ii (Cif e c1R c2R)]).
    unfold inline_ir_info.

    set kt := (isem_ifP p e kt1 kt2).
    exists kt.

    subst kt; split; simpl; intro s.

    { unfold forget_tr, flat_i_sem, isem_ifP; simpl.
      repeat (rewrite translate_bind).
      eapply eqit_bind; eauto; try reflexivity.

      eapply err_result_forget_eqit; simpl.
      destruct (sem_cond (p_globs p) e s) eqn: was_t;
        econstructor; eauto.
      
      unfold pointwise_relation; intro b.
      destruct b; eauto.
      eapply Hc1A.
      eapply Hc2A.
    }
    
    { unfold isem_ifP; simpl.
      rewrite bind_bind.
      rewrite translate_bind.
      rewrite interp_bind.
      eapply eqit_bind; try reflexivity.

      eapply err_result_rassoc_eqit.
      destruct (sem_cond (p_globs p) e s) eqn: was_t;
        econstructor; eauto.
       
      unfold pointwise_relation; intro b.
      rewrite bind_ret_r.
      destruct b; eauto.
      eapply Hc1B.
      eapply Hc2B.
    } 
  }

  { rename c1 into c0.
    intros x dir lo hi c Hc.
    subst Pr; simpl; intros ii sv0.
    unfold Pc in Hc.
    
    destruct (Hc sv0) as [[sv1 [c1R [kt0 [Hc1A Hc1B]]]] | ].
    2: { exact None. }

    set ir := (Cfor x (dir, lo, hi) c0).
    
    set svR := Sv.union (read_i ir) sv0.
    econstructor 1; split.
    exact svR.

    exists ([::MkI ii (Cfor x (dir, lo, hi) c1R)]).
    unfold inline_ir_info.

    set kt := (isem_forP p x (dir, lo, hi) kt0).
    exists kt.

    subst kt; split; simpl; intro s.

    { unfold forget_tr, flat_i_sem. simpl.
      rewrite translate_bind.
      eapply eqit_bind.

      eapply err_result_forget_eqit.
      destruct (sem_bound (p_globs p) lo hi s) eqn: was_t;
        econstructor; eauto.
      
      unfold pointwise_relation; intros [z1 z2]; simpl.
      unfold isem_for_loopP; simpl.

      revert s.
      induction (wrange dir z1 z2); simpl.
      intro s.
      rewrite translate_ret. reflexivity.

      intros s; simpl.
      unfold isem_for_roundP; simpl.
      rewrite translate_bind.
      eapply eqit_bind.

      eapply err_result_forget_eqit.
      destruct (write_var true x a s) eqn: was_t;
        econstructor; eauto.
      
      unfold pointwise_relation; intro s1.
      rewrite translate_bind.
      eapply eqit_bind.

      eapply Hc1A.
      
      unfold pointwise_relation; intro s2.
      eapply IHl.
    }      
    
    { rewrite bind_ret_r.
      unfold isem_for_loopP, isem_for_roundP; simpl.
      rewrite translate_bind; simpl.
      unfold isem_for_loop, isem_for_round; simpl.
      rewrite interp_bind.
      eapply eqit_bind.

      eapply err_result_rassoc_eqit.
      destruct (sem_bound (p_globs p) lo hi s) eqn: was_t;
        econstructor; eauto.
      
      unfold pointwise_relation; intros [z1 z2]; simpl.
      revert s.

      induction (wrange dir z1 z2); simpl.

      intro s.
      rewrite translate_ret; simpl.
      unfold sem_inline; simpl.
      pstep; red. simpl. econstructor; auto.

      intro s.
      rewrite translate_bind.
      rewrite interp_bind.
      eapply eqit_bind.

      eapply err_result_rassoc_eqit.
      destruct (write_var true x a s) eqn: was_t;
        econstructor; eauto.
       
      intro s1.
      rewrite translate_bind.
      rewrite interp_bind.
      eapply eqit_bind.
      eapply Hc1B.

      intro s2; simpl.
      eapply IHl.
    }  
  }

  { rename c1 into c0.
    intros a c1 e ii2 c2 Hc1 Hc2.
    subst Pr; simpl; intros ii sv0.
    unfold Pc in Hc1, Hc2.
    
    destruct (Hc1 sv0) as [[sv1 [c1R [kt1 [Hc1A Hc1B]]]] | ].
    2: { exact None. }
    destruct (Hc2 sv0) as [[sv2 [c2R [kt2 [Hc2A Hc2B]]]] | ].
    2: { exact None. }

    econstructor 1; split.
    exact sv0.

    exists ([::MkI ii (Cwhile a c1R e ii2 c2R)]).
    unfold inline_ir_info.

    set kt := (isem_while_loopP p kt1 e kt2).
    exists kt.

    subst kt; split; simpl; intro s.

    { unfold forget_tr, flat_i_sem, isem_while_loopP; simpl.
      rewrite translate_iter.
      eapply eutt_iter'; eauto; try reflexivity.
      intros s1 s2 H.
      inv H.
      unfold isem_while_roundP, isem_while_round.
      rewrite translate_bind.
      
      eapply eqit_bind' with (RR := eq).
      eapply Hc1A.

      intros r1 r2 H.
      inv H; simpl.

      rewrite translate_bind.
      eapply eqit_bind' with (RR:= eq).

      eapply err_result_forget_eqit; simpl.
      destruct (sem_cond (p_globs p) e r2) eqn: was_t;
        econstructor; eauto.
      
      intros b1 b2 H.
      inv H; simpl.
      destruct b2; simpl.

      rewrite translate_bind.
      eapply eqit_bind' with (RR:= eq).
      eapply Hc2A.

      intros x1 x2 H.
      inv H; simpl.
      pstep; red; simpl. econstructor; auto.
      pstep; red; simpl. econstructor; auto.
    }      
      
    { rewrite bind_ret_r.
      unfold isem_while_loopP, isem_while_loop.
      unfold isem_while_roundP, isem_while_round; simpl.
      rewrite translate_iter.
      rewrite interp_iter.
      unfold CategoryOps.iter.
      unfold Iter_Kleisli.
      unfold Basics.iter.
      unfold MonadIter_itree.
      eapply eutt_iter.
      unfold pointwise_relation; intro s0.
      rewrite translate_bind.
      rewrite interp_bind.
      eapply eqit_bind.
      eapply Hc1B.
      unfold pointwise_relation; intro s1.
      rewrite translate_bind.
      rewrite interp_bind.
      eapply eqit_bind.

      eapply err_result_rassoc_eqit.
      destruct (sem_cond (p_globs p) e s1) eqn: was_t;
        econstructor; eauto.
      
      unfold pointwise_relation; intro b.
      destruct b; simpl.
      { rewrite translate_bind.
        rewrite interp_bind.
        eapply eqit_bind.
        eapply Hc2B.
        unfold RA_tr.
        setoid_rewrite interp_translate.
        unfold pointwise_relation; intro s2; simpl.
        rewrite interp_ret.
        pstep; red. econstructor; auto.
      }
      { setoid_rewrite interp_translate.
        rewrite interp_ret.
        pstep; red. econstructor; auto.
      }
    }  
  }

  { rename c1 into c0.
    intros xs fn es.
    subst Pr; simpl; intros ii sv0.

    set ir := (Ccall xs fn es).
    
    set sv1 := Sv.union (read_i ir) sv0.

    set isin := ii_is_inline ii.

    destruct isin eqn: was_isin.

    2: { econstructor 1; split.
         exact sv1.
         exists [::(MkI ii ir)].

         unfold inline_ir_info.

         set kt := (fun s => @free_tr recCall recCall E _
                                    (flat_i_sem (MkI ii ir) s)).
         exists kt.

         subst kt; split; simpl; intro s.

         { rewrite <- forget_free_inv_lemma; reflexivity. }
         { setoid_rewrite <- rassoc_free_interp_lemma at 1.
           setoid_rewrite bind_ret_r.
           reflexivity.
         }  
    }

    set fdR := add_iinfo ii (get_fun px fn).

    destruct fdR as [fd | ] eqn: was_fdR.
    2: { econstructor 2. }.

    set fd' := rename_fd ii fn fd.

    set Ai := add_iinfo ii
                  (check_rename dead_vars_fd fn fd fd'
                     (Sv.union (vrvs xs) sv1)).
    destruct Ai as [Ai_ok | ] eqn: was_Ai.
    2 :{ econstructor 2. }

    set ii1 := ii_with_location ii.

    set rename_args :=
      assgn_tuple ii1 (map Lvar fd'.(f_params)) AT_rename fd'.(f_tyin) es.

    set rename_res :=
      assgn_tuple ii1 xs AT_rename fd'.(f_tyout) (map Plvar fd'.(f_res)).

    set cR := rename_args ++ fd'.(f_body) ++ rename_res.

    constructor 1; split.
    exact sv1.
    exists cR.

    unfold inline_ir_info.
    
    set kt := (fun s => @free_right_tr recCall recCall E _
                                    (flat_i_sem (MkI ii ir) s)).
    exists kt.

    subst kt; split; simpl; intro s.

    { rewrite <- forget_free_right_inv_lemma.
      reflexivity.
    }  
    { unfold RA_tr, free_right_tr.
      setoid_rewrite <- translate_cmpE.
      unfold CategoryOps.cat, Cat_IFun.
      rewrite interp_translate.
      subst cR.
      unfold flat_i_sem; simpl.

      set Exp_ev := (isem_pexprs (~~ direct_call) (p_globs p) es s).

      set Post_pr := (fun fs : fstate =>
                        iresult s (upd_estate (~~ direct_call) (p_globs p)
                                     xs fs s)).

      unfold isem_pexprs in Exp_ev.
      unfold iresult in Exp_ev, Post_pr.

      (* pre-processing *)
      destruct (sem_pexprs (~~ direct_call) (p_globs p) s es) eqn: was_exp.

      (* we need xrutt *)
      2: { admit. }

      subst Exp_ev; simpl.
      rewrite bind_ret_l.

      setoid_rewrite isem_cmd_cat at 1.
      rewrite interp_bind; simpl.

      set Ren_args := (isem_cmd_ p ev rename_args s).
      unfold rename_args in Ren_args.

      (* idea: renaming either terminates, or there's an error.
         termining case. *)
      assert (exists s1, eutt eq Ren_args (Ret s1)) as H0.
      admit.

      destruct H0 as [s1 H0].
      rewrite H0.
      rewrite bind_ret_l.

      (* the actual call *)
      setoid_rewrite isem_cmd_cat at 1.

      eapply eqit_bind' with (RR:= InputRel).
      (* given arg_eval succeds, InputRel must relate the input fstate
         on the left, with a state after rename_args on the right
         (both from state s) *)
      
      setoid_rewrite interp_trigger; simpl.
      unfold isem_fun_rec, isem_fun_body.
      unfold kget_fundef, ioget.

      destruct (get_fundef (p_funcs p) fn) as [fd1 | ] eqn: was_ffd.
      (* we need xrutt *)
      2: { admit. }

      rewrite was_ffd.
      setoid_rewrite bind_ret_l; simpl.

      set init_fc := (initialize_funcall p ev fd1 (mk_fstate l s)).
      destruct init_fc as [s2 |] eqn: was_init.
      (* we need xrutt *)
      2: { admit. }

      unfold iresult; simpl.
      rewrite bind_ret_l; simpl.

      unfold isem_cmd_.

      (* finalize_funcall still standing in the way *)
      setoid_rewrite <- bind_ret_r at 4.

      eapply eqit_bind' with (RR := CStateRel).
      (* need to relate fd1 and fd', as well as s1 and s2 *)
      admit.

      intros s3 s4 H1.
      (* CStateRel needs to be chosen smartly *)
      admit. 
      
      (* post-processing *)
      intros fsF sF H1.

      (* InputRel needs to have been chosen smartly *)
      admit.
    }
  }

Admitted.



End IT_section1.
    
End IT_section.



(*      
      eapply eqit_bind' with (RR:= InputRel).

      admit.

      intros fs1 s1 H.

      setoid_rewrite isem_cmd_cat at 1.

      unfold interp.

 (interp
       (fun (T : Type) (e : (recCall +' E) T) =>
        ext_handler (handle_recCall p ev) (rassoc_tr (rw_la e))) 
       (Post_pr fs1))

      
      setoid_rewrite isem_cmd_cat at 1.
      rewrite unfold_interp. simpl.
      
      eapply eqit_bind. with (RR:= InputRel).
      
      

      
      destruct (upd_estate (~~ direct_call) (p_globs p) xs fs s) eqn: was_post.
           
                
      unfold handle_recCall.
      unfold isem_fun_rec; simpl.
      unfold isem_fun_body; simpl.
      unfold flat_cmd_sem.
      unfold isem_cmd_rec.
      unfold isem_cmd_.
      unfold isem_foldr.

      unfold interp; simpl.
      
      setoid_rewrite isem_cmd_cat at 1.
      rewrite interp_bind.
      eapply eqit_bind' with (RR:= InputRel).
      admit.

      intros v1 s1 H.
      setoid_rewrite isem_cmd_cat at 1.
      rewrite interp_bind.
      eapply eqit_bind' with (RR:= FStateRel).
      simpl.
      unfold ext_handler, rec_call; simpl.
      setoid_rewrite interp_trigger.
      unfold rassoc_tr, rw_la; simpl.
(*  unfold isem_fun_rec, isem_cmd_.
      unfold isem_fun_body. *)          
      admit.

      intros fs1 s2 H0.
      admit.
    }
  }

Admitted.



End IT_section1.
    
End IT_section.
  
*)
