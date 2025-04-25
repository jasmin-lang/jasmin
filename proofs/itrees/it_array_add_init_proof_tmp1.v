(* ** Imports and settings *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.
Require Import psem_defs psem compiler_util.
Require Export array_init.
Import Utf8.

Require Import Coq.Program.Equality.

From Paco Require Import paco.

Require Import (* psem_of_sem_proof *)
               it_sems_core relational_logic.

Require Import xrutt xrutt_facts.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope seq_scope.

Section WITH_PARAMS.

Context
  {wsw : WithSubWord}
  {dc:DirectCall}
  {asm_op syscall_state : Type}
  {ep : EstateParams syscall_state}
  {spp : SemPexprParams}
  {sip : SemInstrParams asm_op syscall_state}.


Section ADD_INIT.

  Context (p : uprog) (ev:unit).

  Notation gd := (p_globs p).

(*  Notation p' := (add_init_prog p). *)

  Definition undef_except (X:Sv.t) vm :=
    forall x, ~Sv.In x X ->  vm.[x] = undef_addr (vtype x).

  Notation lift_vm sem s1 s2 :=
    (forall vm1,
       vm_eq (evm s1) vm1 ->
       exists2 vm2,
         vm_eq (evm s2) vm2
         & sem (with_vm s1 vm1) (with_vm s2 vm2))
    (only parsing).

  Definition lift_semI s1 i s2 :=
    lift_vm (fun s s' => sem_I (add_init_prog p) ev s i s') s1 s2.

  Definition lift_sem s1 c s2 :=
    lift_vm (fun s s' => sem (add_init_prog p) ev s c s') s1 s2.


Section IT_PROOF.

Context {E E0: Type -> Type} {wE : with_Error E E0} {rE : EventRels E0}.
  
(* Variable vm_uincl : Vm.t -> Vm.t -> Prop. *)

Definition is_some : forall (A : Type), option A -> bool :=
fun (A : Type) (r : option A) =>
  match r with
  | Some _ => true
  | None => false
  end.
     
Definition estate_uincl (s1 s2: estate) :=
  [/\ s1.(escs) = s2.(escs)
    , s1.(emem) = s2.(emem)
    & vm_uincl s1.(evm) s2.(evm)].

Definition values_uincl (vs1 vs2: values) :=
  List.Forall2 value_uincl vs1 vs2.

Definition uincl_spec : EquivSpec :=
  {| rpreF_ := fun (fn1 fn2 : funname) (fs1 fs2 : fstate) =>
                 fn1 = fn2 /\ fs_uincl fs1 fs2 ;
     rpostF_ := fun (fn1 fn2 : funname) (fs1 fs2 fr1 fr2: fstate) =>
                 fs_uincl fr1 fr2 |}.

Definition RecPreRel := fun T1 T2 (e1: recCall T1) (e2: recCall T2) =>
                       match (e1, e2) with
                       | (RecCall fn1 fs1, RecCall fn2 fs2) =>
                           fn1 = fn2 /\ fs_uincl fs1 fs2 end. 

Definition RecPostRel :=
            fun T1 T2 (e1: recCall T1) (v1: T1) (e2: recCall T2) (v2: T2) =>
              match e1 in recCall T1_ return T1_ -> T2 -> Prop with                             | RecCall _ _ =>
           match e2 in recCall T2_ return fstate -> T2_ -> Prop with
           | RecCall _ _ => fs_uincl end end v1 v2.

Lemma xrutt_match_option R1 R2 (RR: R1 -> R2 -> Prop)
  (e1 e2: it_exec.error_data)                       
  (obj1: option R1) (obj2: option R2) 
  (A: forall v1, obj1 = Some v1 -> exists v2, obj2 = Some v2 /\ RR v1 v2) :   
  xrutt (EE_MR (core_logics.errcutoff (is_error wE)) (D:=recCall))
    (EE_MR core_logics.nocutoff (D:=recCall))
    (HeterogeneousRelations.sum_prerel RecPreRel EPreRel)
    (HeterogeneousRelations.sum_postrel RecPostRel EPostRel) RR
    match obj1 with
    | Some v => {| ITreeDefinition._observe := ITreeDefinition.RetF v |}
    | None => Exception.throw e1 (* (ErrType, tt) *)
    end
    match obj2 with
    | Some v => {| ITreeDefinition._observe := ITreeDefinition.RetF v |}
    | None => Exception.throw e2 (* (ErrType, tt) *)
    end.
Proof.
  destruct obj1 as [r1 | ].
  - destruct obj2 as [r2 | ] ; try auto with *.
    + specialize (A r1 erefl).
      destruct A as [v2 [A1 A2]].
      inversion A1; subst.
      eapply xrutt_Ret; auto.
    + specialize (A r1 erefl).
      destruct A as [v2 [A1 A2]]; inversion A1.
  - pstep; red. econstructor; eauto.
    unfold EE_MR, core_logics.errcutoff, is_error; simpl.
    rewrite mid12; auto.  
Qed.

Lemma xrutt_match_option_with_eq R (e1 e2: it_exec.error_data)                  
  (obj1 obj2: option R) 
  (A: forall v, obj1 = Some v -> obj2 = Some v) :    
  xrutt (EE_MR (core_logics.errcutoff (is_error wE)) (D:=recCall))
    (EE_MR core_logics.nocutoff (D:=recCall))
    (HeterogeneousRelations.sum_prerel RecPreRel EPreRel)
    (HeterogeneousRelations.sum_postrel RecPostRel EPostRel) eq
    match obj1 with
    | Some v => {| ITreeDefinition._observe := ITreeDefinition.RetF v |}
    | None => Exception.throw e1 (* (ErrType, tt) *)
    end
    match obj2 with
    | Some v => {| ITreeDefinition._observe := ITreeDefinition.RetF v |}
    | None => Exception.throw e2 (* (ErrType, tt) *)
    end.
Proof.
  eapply xrutt_match_option; eauto.
Qed.

Lemma xrutt_match_exec R1 R2 (RR: R1 -> R2 -> Prop)
  (ef1 ef2: error -> it_exec.error_data)                                
  (obj1: exec R1) (obj2: exec R2) 
  (A: forall v1, obj1 = ok v1 -> exists v2, obj2 = ok v2 /\ RR v1 v2) :   
  xrutt (EE_MR (core_logics.errcutoff (is_error wE)) (D:=recCall))
    (EE_MR core_logics.nocutoff (D:=recCall))
    (HeterogeneousRelations.sum_prerel RecPreRel EPreRel)
    (HeterogeneousRelations.sum_postrel RecPostRel EPostRel) RR
    match obj1 with
    | ok _ v => {| ITreeDefinition._observe := ITreeDefinition.RetF v |}
    | Error e => Exception.throw (ef1 e) (* (ErrType, tt) *)
    end
    match obj2 with
    | ok _ v => {| ITreeDefinition._observe := ITreeDefinition.RetF v |}
    | Error e => Exception.throw (ef2 e) (* (ErrType, tt) *)
    end.
Proof.
  destruct obj1 as [r1 | ].
  - destruct obj2 as [r2 | ] ; try auto with *.
    + specialize (A r1 erefl); destruct A as [v2 [A1 A2]].
      inversion A1; subst; auto.
      eapply xrutt_Ret; auto.
    + specialize (A r1 erefl); destruct A as [v2 [A1 A2]]; inversion A1.
  - pstep; red. econstructor; eauto.
    unfold EE_MR, core_logics.errcutoff, is_error; simpl.
    rewrite mid12; auto.  
Qed.

Lemma xrutt_match_exec_with_eq R 
  (ef1 ef2: error -> it_exec.error_data)                                
  (obj1 obj2: exec R) 
  (A: forall v, obj1 = ok v -> obj2 = ok v) :   
  xrutt (EE_MR (core_logics.errcutoff (is_error wE)) (D:=recCall))
    (EE_MR core_logics.nocutoff (D:=recCall))
    (HeterogeneousRelations.sum_prerel RecPreRel EPreRel)
    (HeterogeneousRelations.sum_postrel RecPostRel EPostRel) eq
    match obj1 with
    | ok _ v => {| ITreeDefinition._observe := ITreeDefinition.RetF v |}
    | Error e => Exception.throw (ef1 e) (* (ErrType, tt) *)
    end
    match obj2 with
    | ok _ v => {| ITreeDefinition._observe := ITreeDefinition.RetF v |}
    | Error e => Exception.throw (ef2 e) (* (ErrType, tt) *)
    end.
Proof.
  eapply xrutt_match_exec; eauto.
Qed.  

Definition fundef_add_init_fd_rel (pT: progT) (f1 f2: @fundef _ _ pT) :=
  f2 = add_init_fd f1.      

Lemma add_init_fd_Prsrv_assoc_p_funcs (fn: funname) :
  forall fd, assoc (p_funcs p) fn = Some fd ->      
         assoc (p_funcs (map_prog add_init_fd p)) fn = Some (add_init_fd fd).
Admitted.       

Lemma add_init_fd_Prsrv_initialize_funcall
  (f1 f2: fundef) (fs1 fs2: fstate) :
  fundef_add_init_fd_rel f1 f2 -> 
  fs_uincl fs1 fs2 ->
  forall st1, initialize_funcall p ev f1 fs1 = ok st1 ->
         exists st2,  
           initialize_funcall (map_prog add_init_fd p) ev f2 fs2 = ok st2 /\
           estate_uincl st1 st2.
Admitted. 

Lemma estate_uincl_Prsrv_finalize_funcall (fn: funname) (f1 f2:
    @fundef asm_op (@_asmop asm_op syscall_state sip) progUnit)
  (s1 s2: estate) :
  fundef_add_init_fd_rel f1 f2 -> 
  estate_uincl s1 s2 ->       
  forall fs1 : fstate,
    finalize_funcall f1 s1 = ok fs1 ->
    exists fs2 : fstate,
        finalize_funcall f2 s2 = ok fs2
        /\ RecPostRel (RecCall fn fs1) fs1 (RecCall fn fs2) fs2.
Admitted. 

Lemma estate_uincl_Prsrv_finalize_funcall1 (fn: funname) (f1 f2:
    @fundef asm_op (@_asmop asm_op syscall_state sip) progUnit)
  (s1 s2: estate) :
  fundef_add_init_fd_rel f1 f2 -> 
  estate_uincl s1 s2 ->       
  forall fs1 : fstate,
    finalize_funcall f1 s1 = ok fs1 ->
    exists fs2 : fstate,
        finalize_funcall f2 s2 = ok fs2
        /\ fs_uincl fs1 fs2.
Admitted. 

Lemma estate_uincl_Prsrv_finalize_funcall2 (fn: funname) (f1 f2:
    fundef)
  (s1 s2: estate) :
  fundef_add_init_fd_rel f1 f2 -> 
  estate_uincl s1 s2 ->       
  forall fs1 : fstate,
    finalize_funcall f1 s1 = ok fs1 ->
    exists fs2 : fstate,
        finalize_funcall f2 s2 = ok fs2
        /\ fs_uincl fs1 fs2.
Admitted. 

Lemma add_init_fd_Prsrv_get_fundef (fn: funname) : 
  forall fd1 : fundef,
    get_fundef (p_funcs p) fn = Some fd1
    -> exists fd2: fundef, 
        get_fundef (p_funcs (map_prog add_init_fd p)) fn = Some fd2
        /\ fundef_add_init_fd_rel fd1 fd2.
Admitted.

Lemma add_init_fd_Prsrv_sem_assgn (s1 s2: estate) x tg ty e :
  estate_uincl s1 s2 ->       
  forall s3 : estate,
    sem_assgn p x tg ty e s1 = ok s3
    -> exists s4 : estate,
        sem_assgn (map_prog add_init_fd p) x tg ty e s2 = ok s4
        /\ estate_uincl s3 s4.
Admitted. 

Lemma estate_uincl_Prsrv_sem_sopn (s1 s2: estate) o xs es :
  estate_uincl s1 s2 ->       
  forall s3 : estate,
    sem_sopn gd o s1 xs es = ok s3
    -> exists s4 : estate,
        sem_sopn gd o s2 xs es = ok s4
        /\ estate_uincl s3 s4.
Admitted. 

Lemma add_init_fd_Prsrv_sem_syscall (s1 s2: estate) xs o es :
  estate_uincl s1 s2 ->       
  forall s3 : estate,
    sem_syscall p xs o es s1 = ok s3
    -> exists s4 : estate,
        sem_syscall (map_prog add_init_fd p) xs o es s2 = ok s4
        /\ estate_uincl s3 s4.
Admitted. 

Lemma estate_uincl_Prsrv_sem_cond (s1 s2: estate) p_globs e :
  estate_uincl s1 s2 ->       
  forall b: bool,
    sem_cond p_globs e s1 = ok b
    -> sem_cond p_globs e s2 = ok b.
Admitted.     

Lemma estate_uincl_Prsrv_sem_bound (s1 s2: estate) p_globs lo hi :
  estate_uincl s1 s2 ->       
  forall zz: Z * Z,
    sem_bound p_globs lo hi s1 = ok zz
    -> sem_bound p_globs lo hi s2 = ok zz.
Admitted.     

Lemma estate_uincl_Prsrv_write_var (s1 s2: estate) v z :
  estate_uincl s1 s2 ->       
  forall s3: estate,
    write_var true v z s1 = ok s3
    -> exists s4, write_var true v z s2 = ok s4 /\ estate_uincl s3 s4.
Admitted.     

(* too strong *)
(*
Lemma estate_uincl_Prsrv_sem_pexprs (s1 s2: estate) es :
  estate_uincl s1 s2 ->       
  forall vs: values,
    sem_pexprs (~~ direct_call) gd s1 es = ok vs
    -> sem_pexprs (~~ direct_call) gd s2 es = ok vs.  
Admitted.     
*)

Lemma estate_uincl_Prsrv_sem_pexprs (s1 s2: estate) es :
  estate_uincl s1 s2 ->       
  forall vs1: values,
    sem_pexprs (~~ direct_call) gd s1 es = ok vs1
    -> exists vs2, 
      sem_pexprs (~~ direct_call) gd s2 es = ok vs2 /\
        values_uincl vs1 vs2.
Admitted. 

(*
(* this should be right *)
Lemma estate_uincl_Prsrv_sem_pexprs_ok (s1 s2: estate) es :
  estate_uincl s1 s2 ->       
  forall vs1: values,
    sem_pexprs (~~ direct_call) gd s1 es = ok vs1
    -> exists vs2, 
      sem_pexprs (~~ direct_call) gd s2 es = ok vs2 /\
        List.Forall2 value_uincl vs1 vs2.
Proof.
  intros.
  destruct s1, s2.
  dependent destruction H; simpl in *; subst.

  have X := sem_pexprs_uincl; simpl in *.
  unfold with_vm in X. simpl in *.
  Set Printing All.
  specialize (X 
  eapply X.
  
Check uincl_onI.
  
  eapply (@X _ _ _ _ _ gd es).
*)
(*
About sem_cond_uincl.
About sem_pexpr_uincl.

Check @sem_cond_uincl. 
*)
(* Check @sem_pexpr_uincl. *)
(* this should be right *)
(*
Lemma estate_uincl_Prsrv_sem_pexpr_ok (s1 s2: estate) e :
  estate_uincl s1 s2 ->       
  forall v1: value,
    sem_pexpr (~~ direct_call) gd s1 e = ok v1
    -> exists v2, 
      sem_pexpr (~~ direct_call) gd s2 e = ok v2 /\ value_uincl v1 v2.
Proof.
Admitted.   
*)
(*  intros. have @X := sem_pexpr_uincl.
  have @Y := sem_cond_uincl. *) 
(*  intros.
  unfold sem_pexprs in *.
  revert H H0. revert vs. revert s1 s2. 
  induction es; simpl; intros.
  - dependent destruction H0; auto.
  - destruct vs; simpl in *.
*)    

Lemma estate_uincl_Prsrv_upd_estate s1 s2 fs1 fs2 xs :
  estate_uincl s1 s2 ->
  fs_uincl fs1 fs2 ->    
  forall s3 : estate,
    upd_estate (~~ direct_call) gd xs fs1 s1 = ok s3
    -> exists s4 : estate,
        upd_estate (~~ direct_call) gd xs fs2 s2 = ok s4 /\ estate_uincl s3 s4.
Admitted.                 


Lemma it_add_init_fdP fn : (* scs mem scs' mem' va vr: *)
  wiequiv_f p (add_init_prog p) ev ev
    (rpreF (eS:= uincl_spec)) fn fn (rpostF (eS:=uincl_spec)).
Proof.
  eapply wequiv_fun_ind.
  intros H fn1 fn2. simpl in *.
  specialize (H fn1 fn2).
  unfold wequiv_fun_body_hyp_rec.
  intros fs1 fs2 [H0 H1] fd1 H3; subst.
  eapply add_init_fd_Prsrv_get_fundef in H3 as H4.
  destruct H4 as [fd2 [H4 H5]].
  exists fd2; auto.
  
(*  unfold wequiv_f_rec, wequiv_f in H. *)
  exists estate_uincl. exists estate_uincl.
(*  unfold wkequiv_io in H. *)

  intros s11 H6.
  eapply add_init_fd_Prsrv_initialize_funcall with (f2 := fd2) (fs2 := fs2) in H6 as H7; eauto.
  destruct H7 as [st2 [H7 H8]].
  exists st2; split; eauto.

  2: { unfold wrequiv, wrequiv_io.
       intros.
       eapply estate_uincl_Prsrv_finalize_funcall1 with (f2 := fd2) (s2 := i2) in H2 as H9; eauto; destruct H9 as [fs3 [H9 H10]].
       eauto.
  }

  unfold wequiv_rec.  (* wequiv, wkequiv. *)

  eapply wequiv_weaken.
  unfold wequiv_f_rec, wequiv_f in H.
  admit.
  admit.
  unfold wequiv.
  unfold wkequiv.
  unfold wkequiv_io.
  
  
(*  destruct fd1, fd2; simpl in *. *)
(*  unfold wkequiv_io in H. *)
  unfold wkequiv_io.
(* unfold sem_fun in H. *)
  intros i1 i2 H11.

  unfold sem_fun in H.
  unfold sem_fun_rec in H.
  unfold rec_call in H.
    
  specialize (H fs1 fs2).
  have X : fn2 = fn2 ∧ fs_uincl fs1 fs2.
  { split; eauto. }
  specialize (H X).
  simpl in *.
  destruct X as [_ X2].
  
(* we end up with the same inductive lemma, nothing interesting *)  


  
  unfold isem_cmd_.
  
Print rel_c.
  wkequiv_io in H.
  
  
  
  
  wkequiv_io, add_init_prog, isem_fun; simpl.
  intros fs1 fs2 H; destruct H as [_ H]. 
  eapply interp_mrec_xrutt 
    with (RPreInv := RecPreRel) (RPostInv := RecPostRel); simpl.

  { clear H fs1 fs2.
    intros T1 T2 [fn1 fs1] [fn2 fs2] [H0 H1]; subst.    
    eapply xrutt_bind with (RR:= (@fundef_add_init_fd_rel _)); eauto.
    (* eq too strong here *)
    { unfold kget_fundef, ioget, get_fundef.
      eapply xrutt_match_option; eauto.
      intros. unfold fundef_add_init_fd_rel.
      exists (add_init_fd v1). split; eauto.
      eapply add_init_fd_Prsrv_assoc_p_funcs; eauto.
    }
        
    { intros f1 f2 H0; subst.
      eapply xrutt_bind with (RR:= estate_uincl). 

      { unfold iresult, err_result; simpl.
        eapply xrutt_match_exec; eauto.
        eapply add_init_fd_Prsrv_initialize_funcall; eauto.
      }  

      { intros s1 s2 H2.
        eapply xrutt_bind with (RR:= estate_uincl). 

        { unfold isem_cmd_, isem_foldr; simpl.
          destruct f1, f2; simpl in *.
          unfold fundef_add_init_fd_rel in H0. simpl in *.
          unfold add_init_fd in H0. simpl in *.
          dependent destruction H0. simpl.
          admit. 
        (*  eapply it_add_init_cmd_xrutt; eauto. *)
        }  

        { intros s3 s4 H3.
          unfold iresult, err_result.
          eapply xrutt_match_exec; eauto.
          eapply estate_uincl_Prsrv_finalize_funcall with (fn := fn2); eauto.
        }
      }
    }
  }
  
  { unfold isem_fun_rec, isem_fun_body.
    eapply xrutt_bind with (RR:= (@fundef_add_init_fd_rel _)).

    { unfold kget_fundef, ioget.
      eapply xrutt_match_option; eauto.
      intros. unfold fundef_add_init_fd_rel.
      exists (add_init_fd v1). split; eauto.
      eapply add_init_fd_Prsrv_assoc_p_funcs; eauto.
    }

    { intros r1 r2 H0; subst.
      eapply xrutt_bind with (RR:= estate_uincl).

      { unfold iresult, err_result.
        eapply xrutt_match_exec; eauto.
        eapply add_init_fd_Prsrv_initialize_funcall; eauto.
      }

      { intros st1 st2 H1.
        eapply xrutt_bind with (RR:= estate_uincl).

        { unfold isem_cmd_.
          destruct r2. simpl.
          admit. 
        (*  eapply it_add_init_cmd_xrutt; eauto. *)
        }
          
        { intros s1 s2 H2.
          unfold iresult, err_result.
          eapply xrutt_match_exec; eauto.
          eapply estate_uincl_Prsrv_finalize_funcall with (fn := fn); eauto.
        } 
      }
    }
  }   
Qed.





(************************************************************************)

Lemma it_add_init_cmd_xrutt (c: cmd) (f_params : seq var_i) (s1 s2: estate)
(*  (FH: fundef_add_init_fd_rel f1 f2)                      *)     
  (H: estate_uincl s1 s2) :
  xrutt (EE_MR (core_logics.errcutoff (is_error wE)) (D:=recCall))
    (EE_MR core_logics.nocutoff (D:=recCall))
    (HeterogeneousRelations.sum_prerel RecPreRel EPreRel)
    (HeterogeneousRelations.sum_postrel RecPostRel EPostRel) estate_uincl
    (isem_cmd_ p ev c s1)
    (isem_cmd_ (map_prog add_init_fd p) ev
       (add_init_c add_init_i (vrvs [seq (Lvar i) | i <- f_params]) c).1 s2).
Proof.
  revert H. revert s1 s2.
  set Pi := fun (i: instr) =>
    forall s1 s2, estate_uincl s1 s2 ->
    xrutt (EE_MR (core_logics.errcutoff (is_error wE)) (D:=recCall))
    (EE_MR core_logics.nocutoff (D:=recCall))
    (HeterogeneousRelations.sum_prerel RecPreRel EPreRel)
    (HeterogeneousRelations.sum_postrel RecPostRel EPostRel) estate_uincl
    (isem_i_body p ev i s1) (isem_cmd_ (map_prog add_init_fd p) ev
     (add_init_i (vrvs [seq (Lvar i) | i <- f_params]) i).1 s2).
(*  set Pi := fun (i: instr) =>
    forall s1 s2, estate_uincl s1 s2 ->
    xrutt (EE_MR (core_logics.errcutoff (is_error wE)) (D:=recCall))
    (EE_MR core_logics.nocutoff (D:=recCall))
    (HeterogeneousRelations.sum_prerel RecPreRel EPreRel)
    (HeterogeneousRelations.sum_postrel RecPostRel EPostRel) estate_uincl
    (isem_cmd_ p ev [::i] s1) (isem_cmd_ (map_prog add_init_fd p) ev
     (add_init_c add_init_i (vrvs [seq (Lvar i) | i <- f_params]) [::i]).1 s2). *)
  set Pr := fun (i:instr_r) => forall ii, Pi (MkI ii i).
  set Pc := fun (c: cmd) =>
    forall s1 s2, estate_uincl s1 s2 ->
    xrutt (EE_MR (core_logics.errcutoff (is_error wE)) (D:=recCall))
    (EE_MR core_logics.nocutoff (D:=recCall))
    (HeterogeneousRelations.sum_prerel RecPreRel EPreRel)
    (HeterogeneousRelations.sum_postrel RecPostRel EPostRel) estate_uincl
    (isem_cmd_ p ev c s1)
    (isem_cmd_ (map_prog add_init_fd p) ev (add_init_c add_init_i (vrvs [seq (Lvar i) | i <- f_params]) c).1 s2).
  eapply (cmd_rect (Pr := Pr) (Pi:=Pi) (Pc:=Pc)).
  { intros; eauto. }
  { subst Pc; simpl; intros. eapply xrutt_Ret; eauto. }
  { subst Pc; simpl; intros.
    unfold isem_cmd_. simpl. unfold isem_foldr. simpl. 
    admit.
  }  
    
 (* eapply xrutt_bind with (RR:= estate_uincl); eauto. } *)  
  { subst Pr; subst Pi. simpl; intros. unfold isem_cmd_. simpl.
    unfold iresult, err_result. unfold isem_cmd_.
    eapply xrutt_match_exec.
    eapply add_init_fd_Prsrv_sem_assgn; eauto. }

  { subst Pr; subst Pi; simpl; intros.
    unfold iresult, err_result.
    eapply xrutt_match_exec.
    eapply estate_uincl_Prsrv_sem_sopn; eauto. }

  { subst Pr; subst Pi; simpl; intros.
    unfold iresult, err_result.
    eapply xrutt_match_exec.
    eapply add_init_fd_Prsrv_sem_syscall; eauto. }

  { subst Pc Pr Pi; simpl; intros e c1 c2 Hc1 Hc2 inf s1 s2 H.
    eapply xrutt_bind with (RR:= eq); simpl; eauto.
    - unfold isem_cond, iresult, err_result.
      destruct p; simpl.
      eapply xrutt_match_exec_with_eq.
      eapply estate_uincl_Prsrv_sem_cond; eauto. 
    - intros b1 b2 H0; subst. 
      destruct b2; eauto.
  }

  { subst Pc Pr Pi; simpl. intros v dir lo hi c0 H inf s1 s2 H0.
    eapply xrutt_bind with (RR:= eq); simpl; eauto.
    - unfold isem_bound, iresult, err_result.
      destruct p; simpl.
      eapply xrutt_match_exec_with_eq.
      + eapply estate_uincl_Prsrv_sem_bound; eauto.
      + intros zz1 [z1 z2] H1; subst; simpl. 
        revert H0; revert s1 s2.  
        induction (wrange dir z1 z2); simpl; intros.
        * eapply xrutt_Ret; eauto.
        * unfold isem_for_round.
          eapply xrutt_bind with (RR:= estate_uincl); simpl; eauto.
          -- unfold iwrite_var, iresult, err_result.
             eapply xrutt_match_exec.
             eapply estate_uincl_Prsrv_write_var; eauto.
          -- intros s3 s4 H1.
             eapply xrutt_bind with (RR:= estate_uincl); eauto.
  }
          
  { subst Pc Pr Pi; simpl. intros alg c0 e inf0 c1 Hc0 Hc1 inf1 s1 s2 H.
    unfold isem_while_loop.
    eapply xrutt_iter with (RI := estate_uincl); eauto.
    intros s3 s4 H0.
    unfold isem_while_round.
    eapply xrutt_bind with (RR:= estate_uincl); eauto.
    intros s5 s6 H1.
    eapply xrutt_bind with (RR:= eq); eauto. 
    - unfold isem_cond, iresult, err_result.
      eapply xrutt_match_exec_with_eq. 
      eapply estate_uincl_Prsrv_sem_cond; eauto. 
    - intros s7 s8 H2; subst.
      destruct s8; eauto.
      + eapply xrutt_bind with (RR:= estate_uincl); eauto.
        intros s7 s8 H2.
        eapply xrutt_Ret; eauto.
      + eapply xrutt_Ret; eauto.
  }
  
  { subst Pc Pr Pi; simpl; intros xs fn es inf s1 s2 H.
    (* eq is not right, should be values_uincl *)
    eapply xrutt_bind with (RR := values_uincl).
    unfold isem_pexprs, iresult, err_result.
    eapply xrutt_match_exec. 
    - eapply estate_uincl_Prsrv_sem_pexprs; eauto.
    - intros vs1 vs2 H0. 
      eapply xrutt_bind with (RR:= fs_uincl).
      + eapply xrutt_trigger; eauto.
        * econstructor; eauto.
          unfold RecPreRel.
          split; auto.
          destruct H; split; auto.
          induction H0; simpl in *. 
          -- intros; dependent destruction H0; auto.
          -- intros t1 t2 H2.
             dependent destruction H2; auto.    
      + intros fs1 fs2 H1.
        unfold iresult, err_result.
        eapply xrutt_match_exec; eauto.
        eapply estate_uincl_Prsrv_upd_estate; eauto.
  }        
Qed.      

      
Lemma it_add_init_fdP fn : (* scs mem scs' mem' va vr: *)
  wiequiv_f p (add_init_prog p) ev ev
    (rpreF (eS:= uincl_spec)) fn fn (rpostF (eS:=uincl_spec)).
Proof.
  unfold wequiv_f, wkequiv_io, add_init_prog, isem_fun; simpl.
  intros fs1 fs2 H; destruct H as [_ H]. 
  eapply interp_mrec_xrutt 
    with (RPreInv := RecPreRel) (RPostInv := RecPostRel); simpl.

  { clear H fs1 fs2.
    intros T1 T2 [fn1 fs1] [fn2 fs2] [H0 H1]; subst.    
    eapply xrutt_bind with (RR:= (@fundef_add_init_fd_rel _)); eauto.
    (* eq too strong here *)
    { unfold kget_fundef, ioget, get_fundef.
      eapply xrutt_match_option; eauto.
      intros. unfold fundef_add_init_fd_rel.
      exists (add_init_fd v1). split; eauto.
      eapply add_init_fd_Prsrv_assoc_p_funcs; eauto.
    }
        
    { intros f1 f2 H0; subst.
      eapply xrutt_bind with (RR:= estate_uincl). 

      { unfold iresult, err_result; simpl.
        eapply xrutt_match_exec; eauto.
        eapply add_init_fd_Prsrv_initialize_funcall; eauto.
      }  

      { intros s1 s2 H2.
        eapply xrutt_bind with (RR:= estate_uincl). 

        { unfold isem_cmd_, isem_foldr; simpl.
          destruct f1, f2; simpl in *.
          unfold fundef_add_init_fd_rel in H0. simpl in *.
          unfold add_init_fd in H0. simpl in *.
          dependent destruction H0. simpl.
          admit. 
        (*  eapply it_add_init_cmd_xrutt; eauto. *)
        }  

        { intros s3 s4 H3.
          unfold iresult, err_result.
          eapply xrutt_match_exec; eauto.
          eapply estate_uincl_Prsrv_finalize_funcall with (fn := fn2); eauto.
        }
      }
    }
  }
  
  { unfold isem_fun_rec, isem_fun_body.
    eapply xrutt_bind with (RR:= (@fundef_add_init_fd_rel _)).

    { unfold kget_fundef, ioget.
      eapply xrutt_match_option; eauto.
      intros. unfold fundef_add_init_fd_rel.
      exists (add_init_fd v1). split; eauto.
      eapply add_init_fd_Prsrv_assoc_p_funcs; eauto.
    }

    { intros r1 r2 H0; subst.
      eapply xrutt_bind with (RR:= estate_uincl).

      { unfold iresult, err_result.
        eapply xrutt_match_exec; eauto.
        eapply add_init_fd_Prsrv_initialize_funcall; eauto.
      }

      { intros st1 st2 H1.
        eapply xrutt_bind with (RR:= estate_uincl).

        { unfold isem_cmd_.
          destruct r2. simpl.
          admit. 
        (*  eapply it_add_init_cmd_xrutt; eauto. *)
        }
          
        { intros s1 s2 H2.
          unfold iresult, err_result.
          eapply xrutt_match_exec; eauto.
          eapply estate_uincl_Prsrv_finalize_funcall with (fn := fn); eauto.
        } 
      }
    }
  }   
Qed.


(*
Lemma it_add_init_instr_xrutt (i: instr) (s1 s2: estate) :
  xrutt (EE_MR (core_logics.errcutoff (is_error wE)) (D:=recCall))
    (EE_MR core_logics.nocutoff (D:=recCall))
    (HeterogeneousRelations.sum_prerel RecPreRel EPreRel)
    (HeterogeneousRelations.sum_postrel RecPostRel EPostRel) estate_uincl
    (isem_i_body p ev i s1) (isem_i_body (map_prog add_init_fd p) ev i s2).
  destruct i.
Admitted.
*)
(*

  }  
  
  2: { eapply xrutt_bind with (RR := eq); simpl.
       - destruct p; simpl.
         unfold kget_fundef.
         unfold ioget; simpl.
         induction p_funcs; simpl.
         + eapply xrutt_Vis; eauto.   
           econstructor; eauto.
           unfold EPreRel.
           unfold core_logics.sum_prerelF.
           destruct (mfun1 (mfun2 (Sum.inl1 (Exception.Throw (ErrType, tt)))));
             auto.

           admit.
           
           intros.
           dependent destruction H0.
           unfold EPostRel in H0.
           unfold core_logics.sum_postrelF in H0.
           destruct (mfun1 (mfun2 (Sum.inl1 (Exception.Throw (ErrType, tt))))).
           destruct t1.
           destruct t1.

           simpl.
           destruct a; simpl.
           admit.

           intros.
           inversion H0; subst.
           clear H1.

           (* here the instantiation with eq is probably not right;
              need looking for right uincl *)
           eapply xrutt_bind with (RR:= eq).
           admit.

           intros.
           inversion H0; subst.
           admit.
  }

  intros.
  destruct d1.
  destruct d2.
  destruct H0 as [H0 H1].
  inversion H0; subst.
  clear H2.
  unfold handle_recCall.
  unfold isem_fun_rec.
  unfold isem_fun_body.
  eapply xrutt_bind with (RR:= eq); eauto.

  2: { intros.
       inversion H0; subst.
       clear H2.
       eapply xrutt_bind with (RR:= eq). (* bad instantiation *)
       unfold iresult; simpl.
       unfold err_result.
       admit.

       intros.
       inversion H0; subst.
       eapply xrutt_bind with (RR:= eq). (* bad instantiation *)
       admit.

       intros.
       inversion H0; subst.
       admit.

Admitted.        
           
*)           
   
Check @add_init_prog.
  
Check @map_prog.  
Print map_prog.  
Print map_prog_name.
Check @add_init_i.
Check @add_init.
Check @Sv.fold.
About Sv.t.
About Smake.

Definition init_pre (s1 s2: estate) : Prop :=
  forall vm1, vm_eq (evm s1) vm1 ->
       exists2 vm2, vm_eq (evm s2) vm2 & vm_uincl vm1 vm2.

Lemma add_init_cmd : forall s1 s2 c1 c2,
    (c2, s2) = add_init_c _ s1 c1 ->
    @wequiv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      init_pre c1 c2 init_pre.



(******************************************************************)

(*
Check @init_state.
Check add_init_c.
Check value_uincl.
Check @wequiv.
Print uprog.
Print estate.
*)
  
Lemma add_init_call : forall s1 s2 c1 c2,
  (c2, s2) = add_init_c _ s1 c1 ->  
  forall vm1,
       vm_eq (evm s1) vm1 ->
       exists2 vm2,
    vm_eq (evm s2) vm2 /\ wequiv init_pre c1 c2 _  .
      
  
  Let Pi s1 i s2 :=
    lift_semI s1 i s2
    /\ forall I,
         undef_except I (evm s1) ->
         let: iI := add_init_i I i in
         undef_except iI.2 (evm s2) /\ lift_sem s1 iI.1 s2.

  Let Pi_r s1 (i:instr_r) s2 := forall ii, Pi s1 (MkI ii i) s2.

   Let Pc s1 c s2 :=
     lift_sem s1 c s2
     /\ forall I,
          undef_except I (evm s1) ->
          let: cI := add_init_c add_init_i I c in
          undef_except cI.2 (evm s2) /\ lift_sem s1 cI.1 s2.

 Let Pfor i vs s1 c s2 :=
   lift_vm (fun s s' => sem_for p' ev i vs s c s') s1 s2.

  Let Pfun scs m fn vargs scs' m' vres :=
    sem_call p' ev scs m fn vargs scs' m' vres.

  Local Lemma RAnil : sem_Ind_nil Pc.
  Proof. 
    move=> s1; split.
    + by move=> vm1 he;exists vm1 => //;constructor.
    by move=> I hu /=;split => // vm1 he; exists vm1 => //; constructor.
  Qed.

  Local Lemma RAcons : sem_Ind_cons p ev Pc Pi.
  Proof.
    move=> s1 s2 s3 i c _ [] hsi hi _ [] hsc hc; split.
    + by move=> vm1 /hsi [vm2] /hsc [vm3] ? hsc' hsi'; exists vm3 => //; apply: Eseq hsi' hsc'.
    move=> I /hi /=; case: add_init_i => c1 I2 [] /= /hc; case: add_init_c => c2 I3 [] /= hu3 hc2 hc1.
    by split => // vm1 /hc1 [] vm2 /hc2 [] vm3 ? hc2' hc1'; exists vm3 => //; apply: sem_app hc1' hc2'.
  Qed.

  Local Lemma RAmkI : sem_Ind_mkI p ev Pi_r Pi.
  Proof. by move=> ii i s1 s2 _ /(_ ii). Qed.
  
  Lemma add_initP ii0 ii1 i s1 s2 I X :
    undef_except I (evm s1) ->
    lift_semI s1 (MkI ii0 i) s2 ->
    lift_sem s1 (add_init ii1 I X (MkI ii0 i)) s2.
  Proof.
    move=> hu hs; rewrite /add_init Sv.fold_spec.
    have : forall x:var, x \in Sv.elements (Sv.diff X I) -> (evm s1).[x] = undef_addr (vtype x).
    + by move=> x /Sv_elemsP hx; rewrite hu //; SvD.fsetdec.
    have : lift_sem s1 [:: MkI ii0 i] s2.
    + by move=> vm1 /hs [vm2] ??; exists vm2 => //;apply sem_seq1.
    clear; elim: Sv.elements s1 [:: MkI ii0 i] => [ | x xs ih] //= s1 l hl hu.
    apply ih; last by move=> y hy; apply hu; rewrite in_cons hy orbT.
    move=> vm1 hu1; rewrite /add_init_aux.
    have hl1 := hl _ hu1.
    case heq: vtype => [||len|] //; case:ifP => _ //.
    set i' := MkI _ _.
    have [vm2 heq2 hi']: exists2 vm2, evm s1 =1 vm2 & sem_I p' ev (with_vm s1 vm1) i' (with_vm s1 vm2).
    + rewrite /i'; have := hu x; rewrite in_cons eq_refl /= => /(_ erefl) {hu i'} hx.
      exists (vm1.[x <- Varr (WArray.empty len)]).
      + move: hu1; rewrite !vm_eq_vm_rel => hu1; apply vm_rel_set_r.
        + by move=> _ /=; rewrite hx heq eqxx.
        by apply: vm_relI hu1.
      constructor; econstructor; first reflexivity.
      + by rewrite /truncate_val /= WArray.castK.
      by apply /write_varP; econstructor => //=; rewrite heq /truncatable eqxx.
    by have [vm3 ? hc']:= hl _ heq2; exists vm3 => //; apply: Eseq hc'.
  Qed.

  Local Lemma aux ii0 ii1 i s1 s2 :
    sem_I p ev s1 (MkI ii0 i) s2 →
    lift_semI s1 (MkI ii0 i) s2 →
    lift_semI s1 (MkI ii0 i) s2 /\
    forall I, undef_except I (evm s1) →
      undef_except (Sv.union I (write_i i)) (evm s2) /\
      let: i' := add_init ii1 I (Sv.union (write_i i) (read_i i)) (MkI ii0 i) in
      lift_sem s1 i' s2.
  Proof.
    move=> hs hs'; split => //.
    move=> I hu; split.
    + by move=> x hx; rewrite -(write_IP hs) ?hu //; SvD.fsetdec.
    by apply add_initP.
  Qed.

  Local Lemma RAasgn : sem_Ind_assgn p Pi_r.
  Proof.
    move=> s1 s2 x tag ty e v v' hse htr hwr ii /=.
    apply aux => //.
    + by constructor; econstructor; eauto.
    move=> vm1 heq1.
    have [vm2 heq2 hwr2 ]:= write_lvar_ext_eq heq1 hwr.
    exists vm2 => //; constructor; econstructor; eauto.
    by rewrite -(sem_pexpr_ext_eq _ _ e heq1).
  Qed.

  Local Lemma RAopn : sem_Ind_opn p Pi_r.
  Proof.
    move=> s1 s2 xs tag ty es hso ii /=. 
    apply aux => //.
    + by constructor; econstructor.
    move: hso; rewrite /sem_sopn; t_xrbindP => vs vs' hse ho hwr vm1 heq1.
    have [vm2 heq2 hwr2 ]:= write_lvars_ext_eq heq1 hwr.
    exists vm2 => //; constructor; econstructor; eauto.
    by rewrite /sem_sopn -(sem_pexprs_ext_eq _ _ es heq1) hse /= ho.
  Qed.

  Local Lemma RAsyscall : sem_Ind_syscall p Pi_r.
  Proof.
    move=> s1 scs m s2 o xs es ves vs he hsys hw ii.
    apply aux => //.
    + by constructor; econstructor; eauto.
    move=> vm1 heq1.
    have [vm2 heq2 hw2 ]:= write_lvars_ext_eq (s1 := with_scs (with_mem s1 m) scs) heq1 hw.
    exists vm2 => //; constructor; econstructor; eauto.
    by rewrite -(sem_pexprs_ext_eq _ _ es heq1).
  Qed.

  Local Lemma RAif_true : sem_Ind_if_true p ev Pc Pi_r.
  Proof.
    move=> s1 s2 e c1 c2 H _ [] hs Hc ii /=; split.
    + move=> vm1 /[dup] heq1 /hs [vm2] ? hc; exists vm2 => //; constructor.
      by apply: Eif_true => //; rewrite -(sem_pexpr_ext_eq _ _ e heq1).
    move=> I /[dup] hu1 /Hc [] /=.
    case: (add_init_c _ _ c1)=> /= c1' O1; case: (add_init_c _ _ c2)=> /= c2' O2.
    move=> hu2 hsc'; split.
    + by move=> ??;rewrite hu2 //;SvD.fsetdec.
    apply add_initP => //.
    move=> vm1 /[dup] heq1 /hsc' [vm2 he hs']; exists vm2 => //.
    by constructor; apply: Eif_true => //; rewrite -(sem_pexpr_ext_eq _ _ e heq1).
  Qed.

  Local Lemma RAif_false : sem_Ind_if_false p ev Pc Pi_r.
  Proof.
    move=> s1 s2 e c1 c2 H _ [] hs Hc ii /=; split.
    + move=> vm1 /[dup] heq1 /hs [vm2] ? hc; exists vm2 => //; constructor.
      by apply: Eif_false => //; rewrite -(sem_pexpr_ext_eq _ _ e heq1).
    move=> I /[dup] hu1 /Hc [] /=.
    case: (add_init_c _ _ c1)=> /= c1' O1; case: (add_init_c _ _ c2)=> /= c2' O2.
    move=> hu2 hsc'; split.
    + by move=> ??;rewrite hu2 //;SvD.fsetdec.
    apply add_initP => //.
    move=> vm1 /[dup] heq1 /hsc' [vm2 he hs']; exists vm2 => //.
    by constructor; apply: Eif_false => //; rewrite -(sem_pexpr_ext_eq _ _ e heq1).
  Qed.

  Local Lemma RAwhile_true : sem_Ind_while_true p ev Pc Pi_r.
  Proof.
    move=> s1 s2 s3 s4 a c e ei c' hsc [] Hc _ he hsc' [] Hc' _ hsi Hi ii.
    have [{}Hi _]:= Hi ii.
    apply aux.
    + by constructor;apply: Ewhile_true;eauto.
    move=> vm1 /Hc [vm2] /[dup] heq /Hc' [vm3] /Hi [vm4] ? /sem_IE h *; exists vm4 => //.
    constructor;apply: Ewhile_true;eauto.
    by rewrite -(sem_pexpr_ext_eq _ _ e heq).
  Qed.

  Local Lemma RAwhile_false : sem_Ind_while_false p ev Pc Pi_r.
  Proof.
    move=> s1 s2 a c e ei c' hsc [] Hc _ he ii.
    apply aux.
    + by constructor;apply: Ewhile_false;eauto.
    move=> vm1 /Hc [vm2] heq ?; exists vm2 => //.
    constructor;apply: Ewhile_false;eauto.
    by rewrite -(sem_pexpr_ext_eq _ _ e heq).
  Qed.

  Local Lemma RAfor : sem_Ind_for p ev Pi_r Pfor.
  Proof.
    move=> s1 s2 i d lo hi c vlo vhi H H' hsf hf ii.
    apply aux.
    + by constructor; econstructor; eauto.
    move=> vm1 /[dup] heq /hf [vm2] ? hs'; exists vm2 => //.
    by constructor; econstructor; eauto; rewrite -(sem_pexpr_ext_eq _ _ _ heq).
  Qed.

  Local Lemma RAfor_nil : sem_Ind_for_nil Pfor.
  Proof. move=> s i c vm1 Hvm1;exists vm1 =>//;constructor. Qed.

  Local Lemma RAfor_cons : sem_Ind_for_cons p ev Pc Pfor.
  Proof.
    move=> s1 s1' s2 s3 i w ws c Hi _ [] Hc _ _ Hf vm1 Hvm1.
    have [vm2 /Hc [vm3] /Hf [vm4] *]:= write_lvar_ext_eq Hvm1 (Hi : write_lval true gd i w s1 = ok s1').
    exists vm4 => //; by econstructor; eauto.
  Qed.

  Local Lemma RAcall : sem_Ind_call p ev Pi_r Pfun.
  Proof.
    move=> s1 scs2 m2 s2 xs fn args vargs vs Hargs Hcall Hfd Hxs ii'.
    apply aux.
    + constructor; econstructor;eauto.
    move=> vm1 heq1.
    have heq1' : (evm (with_mem s1 m2) =1 vm1)%vm := heq1.
    have [vm2 heq2 hwr2 ]:= write_lvars_ext_eq (s1 := (with_scs (with_mem s1 m2) scs2)) heq1 Hxs.
    exists vm2 => //; constructor; econstructor; eauto.
    by rewrite -(sem_pexprs_ext_eq _ _ args).
  Qed.

  Local Lemma RAproc : sem_Ind_proc p ev Pc Pfun.
  Proof.
    move=> scs1 m1 scs2 m2 fn fd vargs vargs' s0 s1 s2 vres vres' Hget Htin Hi Hargs Hsem [] hsi Hrec Hmap Htout Hsys Hfi.
    have hget : get_fundef (p_funcs p') fn = Some (add_init_fd fd).
    + by rewrite /p' get_map_prog Hget.
    set I := vrvs [seq (Lvar i) | i <- f_params fd].
    case: (Hrec I).
    + move=> x hx. 
      move: Hargs; rewrite (write_vars_lvals _ gd) => /disjoint_eq_ons -/(_ (Sv.singleton x)) <-.
      + by move: Hi => [<-] /=; rewrite Vm.initP.
      + by rewrite -/I /disjoint /is_true Sv.is_empty_spec; SvD.fsetdec.
      by SvD.fsetdec.     
    move=> ?  /(_ (evm s1) (fun _ => erefl)) [vm2] heq2 hsem {Hsem Hget}.    
    eapply (EcallRun (f := add_init_fd fd) (s1:= with_vm s1 (evm s1)) (s2:= (with_vm s2 vm2))); eauto.
    + by case: (s1) Hargs.
    by rewrite -Hmap; apply mapM_ext => // y; rewrite /get_var heq2.
  Qed.

  Lemma add_init_fdP f scs mem scs' mem' va vr:
    sem_call p ev scs mem f va scs' mem' vr ->
    sem_call p' ev scs mem f va scs' mem' vr.
  Proof.
    exact:
      (sem_call_Ind
         RAnil
         RAcons
         RAmkI
         RAasgn
         RAopn
         RAsyscall
         RAif_true
         RAif_false
         RAwhile_true
         RAwhile_false
         RAfor
         RAfor_nil
         RAfor_cons
         RAcall
         RAproc).
  Qed.

End ADD_INIT.

End WITH_PARAMS.
