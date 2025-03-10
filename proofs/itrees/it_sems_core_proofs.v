From Coq Require Import
     Arith.PeanoNat
     Lists.List
     Strings.String
     Morphisms
     Setoid
     RelationClasses
     EquivDec
     Equality
     Program.Tactics.

From ExtLib Require Import
     Data.String
     Structures.Monad
     Structures.Traversable
     Data.List
     Core.RelDec
     Structures.Maps
     Data.Map.FMapAList.

From ITree Require Import
     ITree
     ITreeFacts
     Monad
     Basics.HeterogeneousRelations     
     Events.Map
     Events.State
     Events.StateFacts
     Events.Reader
     Events.Exception
     Events.FailFacts.

Require Import Paco.paco.
Require Import Psatz.
Require Import ProofIrrelevance.
Require Import FunctionalExtensionality.

From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq eqtype fintype.

From ITree Require Import
(*     Basics.Tacs *)
     Basics.Category
     Basics.Basics
     Basics.Function
     Core.ITreeDefinition
     Core.KTree
     Eq.Eqit
     Eq.UpToTaus
     Eq.Paco2
     Indexed.Sum
     Indexed.Function
     Indexed.Relation
     Interp.Handler
     Interp.Interp
     Interp.InterpFacts
     Interp.Recursion.

From ITree Require Import Rutt RuttFacts.

From ITree Require Import EqAxiom.

From Jasmin Require Import expr psem_defs psem oseq.
From Jasmin Require Import it_gen_lib it_jasmin_lib it_sems_core.

Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.
Local Open Scope option_scope.

(*
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
*)

Obligation Tactic := done || idtac.

(* PROBLEM with sections *)

(* This files contains proofs to test the semantic models in
 it_sems. It turns out that double recursion leads to a duplication of
 inductive proofs, and thus that mutual recursion leads to simpler
 proofs. The proofs on the modular model are still based on eutt and
 need to be revised. The proofs on the flat models are much longer and
 more laden with detail than those on the error-aware model. *)

Section Lang.
Context (asm_op: Type) (asmop: asmOp asm_op).

Section WSW.
Context {wsw: WithSubWord}.   
Context
  (dc: DirectCall)
  (syscall_state : Type)
  (ep : EstateParams syscall_state)
  (spp : SemPexprParams)
  (sip : SemInstrParams asm_op syscall_state)
  (pT : progT)
  (scP : semCallParams)
  (ev : extra_val_t).

Local Notation FunE := (FunE asmop).
Local Notation FFCall_ := (FFCall asmop). 
Local Notation cmd_Ind := (cmd_Ind asm_op asmop).
Local Notation FunDef := (FunDef asmop pT).
Local Notation FCState := (FCState asmop ep).
Local Notation meval_instr := (meval_instr spp scP). 
Local Notation meval_fcall := (meval_fcall dc spp scP ev). 
Local Notation mevalE_cmd := (mevalE_cmd dc spp scP ev). 


(***************************************************************************)
(*** APPLICATION ***********************************************************)
(** we define a language translation and try to prove equivalence of
function application and commands across the translation under the
appropriate hypothesis. First we specify the translation. *)

(*** TRANSLATION SPEC *******************************************)
Section TRANSF.
Context (tr_lval : lval -> lval)
        (tr_expr : pexpr -> pexpr)
        (tr_opn : sopn -> sopn)
        (tr_sysc : syscall_t -> syscall_t).

Local Notation tr_lvals ls := (map tr_lval ls).
Local Notation tr_exprs es := (map tr_expr es).

Definition Tr_i (Th: instr_r -> instr_r) (i: instr) : instr :=
  match i with MkI ii ir => MkI ii (Th ir) end.  

Fixpoint Tr_ir (i : instr_r) : instr_r :=
  let R := Tr_i Tr_ir in
  match i with
  | Cassgn x tg ty e => Cassgn (tr_lval x) tg ty (tr_expr e)
  | Copn xs tg o es =>
      Copn (tr_lvals xs) tg (tr_opn o) (tr_exprs es)
  | Csyscall xs sc es =>
      Csyscall (tr_lvals xs) (tr_sysc sc) (tr_exprs es)
  | Cif e c1 c2 => Cif (tr_expr e) (map R c1) (map R c2)
  | Cfor i rg c => Cfor i rg (map R c)                     
  | Cwhile a c1 e c2 => Cwhile a (map R c1) (tr_expr e) (map R c2)
  | Ccall xs fn es => Ccall (tr_lvals xs) fn (tr_exprs es)
  end.
Local Notation Tr_instr := (Tr_i Tr_ir).
Local Notation Tr_cmd c := (map Tr_instr c).

Definition Tr_FunDef (f: FunDef) : FunDef :=
  match f with
  | MkFun i tyin p_xs c tyout r_xs xtr =>
    MkFun i tyin p_xs (Tr_cmd c) tyout r_xs xtr end.
    

(*********************************************************************)
(*** PROOFS **********************************************************)

Section TR_tests.

Context (pr1 pr2 : prog)
        (PR : forall T, T -> T -> Prop).
Context (TR_E : forall (E: Type -> Type) T1 T2,
            E T1 -> E T2 -> Prop)
        (VR_E : forall (E: Type -> Type) T1 T2,
            E T1 -> T1 -> E T2 -> T2 -> Prop).

Local Notation RS := (PR estate).
Local Notation RV := (PR values).
Local Notation RV1 := (PR value).
Local Notation RSMV := (PR (syscall_state * mem * seq value)).


Section GEN_ErrAndFlat.

Context (E: Type -> Type).   

Local Notation RV := (PR values).
Local Notation VS := (values * estate)%type.
Local Notation FVS := (funname * VS)%type.

Notation RVS := (fun (vs_st1 vs_st2 : VS) => 
  (RV vs_st1.1 vs_st2.1 /\ RS vs_st1.2 vs_st2.2)).
Notation RFVS := (fun (fvs1 fvs2 : FVS) => 
  (fvs1.1 = fvs2.1 /\ RVS fvs1.2 fvs2.2)).
Notation RC := (fun c1 c2: cmd => c2 = Tr_cmd c1).
Notation RFunDef := (fun f1 f2: FunDef => f2 = Tr_FunDef f1).

Context (rvs_def : PR VS = RVS)
        (rfvs_def : PR FVS = RFVS)
        (rc_def : PR cmd = RC)
        (rfundef_def : PR FunDef = RFunDef).


Section GEN_Error.

Context (HasErr: ErrState -< E).   

Section TR_MutualRec.

(* ME: relation between FCState events *)
Definition TR_D_ME {T1 T2} (d1 : FCState T1)
                           (d2 : FCState T2) : Prop :=
  match (d1, d2) with
  | (FLCode c1 st1, FLCode c2 st2) => RC c1 c2 /\ RS st1 st2
  | (FFCall xs1 fn1 es1 st1, FFCall xs2 fn2 es2 st2) =>
      xs2 = map tr_lval xs1 /\ fn1 = fn2 /\ es2 = map tr_expr es1 /\ RS st1 st2
  | _ => False   
  end.               

(* ME: relation between FCState event outputs, i.e. over estate *)
Program Definition VR_D_ME {T1 T2}
  (d1 : FCState T1) (t1: T1) (d2 : FCState T2) (t2: T2) : Prop.
  dependent destruction d1.
  - dependent destruction d2.
    + exact (RS t1 t2).
    + exact (False).
  - dependent destruction d2.
    + exact (False).
    + exact (RS t1 t2).     
Defined.      

(* NOT USED *)
(*
Definition FCState_det {T} (d: FCState T) : T = estate :=
 match d in (it_sems_core.FCState _ _ T0) return (T0 = estate) with
 | FLCode c st => (fun=> (fun=> erefl)) c st
 | @FFCall _ _ _ _ _ xs f es st =>
     (fun=> (fun=> (fun=> (fun=> erefl)))) xs f es st
 end.
Definition st_cast {T} (d: FCState T) (x: T) : estate.
  rewrite (FCState_det d) in x; exact x.
Defined.
Definition VR_D_ME' {T1 T2}
  (d1 : FCState T1) (t1: T1) (d2 : FCState T2) (t2: T2) : Prop :=
  (match (d1, d2) return (estate -> estate -> Prop) with
  | (FLCode c1 st1, FLCode c2 st2) => RS 
  | (FFCall xs1 f1 es1 st1, FFCall xs2 f2 es2 st2) => RS 
  | _ => fun _ _ => False end)
    (st_cast d1 t1) (st_cast d2 t2).
*)
(***)

Program Definition TR_DE_ME : prerel (FCState +' E) (FCState +' E) :=
  sum_prerel (@TR_D_ME) (TR_E E).

Program Definition VR_DE_ME : postrel (FCState +' E) (FCState +' E) :=
  sum_postrel (@VR_D_ME) (VR_E E).

Context (fcstate_t_def : TR_E (FCState +' E) = TR_DE_ME).
Context (fcstate_v_def : VR_E (FCState +' E) = VR_DE_ME).

Lemma rutt_err_eval_Args fn es1 st1 st2 : 
  RS st1 st2 ->
  rutt (TR_E (FCState +' E)) (VR_E (FCState +' E)) RV
    (err_eval_Args dc spp pr1 fn es1 st1)
    (err_eval_Args dc spp pr2 fn (tr_exprs es1) st2).
Admitted. 

Lemma rutt_err_init_state fn r1 r2 st1 st2 :
  RV r1 r2 ->
  RS st1 st2 ->
  rutt (TR_E (FCState +' E)) (VR_E (FCState +' E)) RS
    (err_init_state dc scP ev pr1 fn r1 st1)
    (err_init_state dc scP ev pr2 fn r2 st2).
Admitted.   

Lemma rutt_err_get_FunCode fn :
  rutt (TR_E (FCState +' E)) (VR_E (FCState +' E)) RC
    (err_get_FunCode pr1 fn)
    (err_get_FunCode pr2 fn).    
Admitted. 

Lemma rutt_err_return_val fn st1 st2 :
  RS st1 st2 ->
  rutt (TR_E (FCState +' E)) (VR_E (FCState +' E)) RV
    (err_return_val dc pr1 fn st1)
    (err_return_val dc pr2 fn st2).    
Admitted. 

Lemma rutt_err_reinstate_caller fn xs v1 v2 st1 st2 st3 st4 :
  RV v1 v2 ->
  RS st1 st2 ->
  RS st3 st4 ->
  rutt (TR_E (FCState +' E)) (VR_E (FCState +' E))
    RS   
    (err_reinstate_caller dc spp scP pr1 fn xs v1
       st1 st3)
    (err_reinstate_caller dc spp scP pr2 fn
       (tr_lvals xs) v2 st2 st4).
Admitted. 

(***)

Lemma rutt_err_mk_AssgnE x tg ty e st1 st2 :
  RS st1 st2 ->
  rutt (sum_prerel (@TR_D_ME) (TR_E E)) (sum_postrel (@VR_D_ME) (VR_E E)) RS
    (err_mk_AssgnE spp pr1 x tg ty e st1)
    (err_mk_AssgnE spp pr2 (tr_lval x) tg ty (tr_expr e) st2).
Admitted.   

Lemma rutt_err_mk_OpnE x tg o e st1 st2 :
  RS st1 st2 ->
  rutt (sum_prerel (@TR_D_ME) (TR_E E)) (sum_postrel (@VR_D_ME) (VR_E E)) RS
    (err_mk_OpnE spp pr1 x tg o e st1)
    (err_mk_OpnE spp pr2 (tr_lvals x) tg (tr_opn o) (tr_exprs e) st2).
Admitted. 

Lemma rutt_err_mk_SyscallE x sc e st1 st2 :
  RS st1 st2 ->
  rutt (sum_prerel (@TR_D_ME) (TR_E E)) (sum_postrel (@VR_D_ME) (VR_E E)) RS
    (err_mk_SyscallE spp scP pr1 x sc e st1)
    (err_mk_SyscallE spp scP pr2 
       (tr_lvals x) (tr_sysc sc) (tr_exprs e) st2).
Admitted. 

Lemma rutt_err_mk_EvalCond e st1 st2 :
  RS st1 st2 ->
   rutt (sum_prerel (@TR_D_ME) (TR_E E)) (sum_postrel (@VR_D_ME) (VR_E E)) eq
    (err_mk_EvalCond spp pr1 e st1)
    (err_mk_EvalCond spp pr2 (tr_expr e) st2).
Admitted.  

Lemma rutt_err_mk_EvalBound e st1 st2 :
  RS st1 st2 ->
  rutt (sum_prerel (@TR_D_ME) (TR_E E)) (sum_postrel (@VR_D_ME) (VR_E E)) eq
    (err_mk_EvalBound spp pr1 e st1)
    (err_mk_EvalBound spp pr2 e st2).
Admitted. 

Lemma rutt_err_mk_WriteIndex xi z st1 st2 :
  RS st1 st2 ->
   rutt (sum_prerel (@TR_D_ME) (TR_E E)) (sum_postrel (@VR_D_ME) (VR_E E)) RS
    (err_mk_WriteIndex xi z st1) (err_mk_WriteIndex xi z st2).
Admitted. 

Lemma comp_gen_ok_ME (fn: funname)
  (xs1 xs2: lvals) (es1 es2: pexprs) (st1 st2: estate) :
  xs2 = map tr_lval xs1 ->
  es2 = map tr_expr es1 -> 
  RS st1 st2 ->
  @rutt (FCState +' E) _ _ _ (TR_E _) (VR_E _)
    (fun a1 a2 => @VR_D_ME _ _ (FFCall_ xs1 fn es1 st1) a1
                             (FFCall_ xs2 fn es2 st2) a2)  
    (meval_fcall pr1 xs1 fn es1 st1) (meval_fcall pr2 xs2 fn es2 st2).
  intros.
  unfold meval_fcall; simpl.
  
  eapply rutt_bind with (RR := RV); inv H; intros.

  { eapply rutt_err_eval_Args; auto. }    

  eapply rutt_bind with (RR := RS); intros.

  { eapply rutt_err_init_state; auto. }

  eapply rutt_bind with (RR := RC); intros.

  { eapply rutt_err_get_FunCode; auto. }

  inv H2. eapply rutt_bind with (RR := RS); intros.
  { eapply rutt_trigger; simpl; intros.
    { rewrite fcstate_t_def. 
      econstructor.
      split; auto; intros.
    }
    rewrite fcstate_v_def in H2.
    dependent destruction H2.    
    unfold VR_D_ME in H2; auto.
  }

  eapply rutt_bind with (RR := RV); intros.
  { eapply rutt_err_return_val; auto. }

  assert ((fun a1 : estate => [eta RS a1]) = RS) as A1.
  { eauto. } 
  
  rewrite A1; eapply rutt_err_reinstate_caller; auto.
Qed.

(* Inductive lemma - GOOD. here we are not tying the coinductive knot,
   as st_cmd_map_r is just a map function. *)
Lemma rutt_cmd_tr_ME_step (cc: cmd) (st1 st2: estate) : 
  RS st1 st2 ->
  @rutt (FCState +' E) _ _ _
    (sum_prerel (@TR_D_ME) (TR_E E))
    (sum_postrel (@VR_D_ME) (VR_E E))
    RS (st_cmd_map_r (meval_instr pr1) cc st1)
    (st_cmd_map_r (meval_instr pr2) (Tr_cmd cc) st2).
  simpl; intros.

  set (Pr := fun (i: instr_r) => forall ii st1 st2, RS st1 st2 -> 
     @rutt (FCState +' E) _ _ _
    (sum_prerel (@TR_D_ME) (TR_E E))
    (sum_postrel (@VR_D_ME) (VR_E E))
    RS 
    (st_cmd_map_r (meval_instr pr1) ((MkI ii i) :: nil) st1)
    (st_cmd_map_r (meval_instr pr2) ((Tr_instr (MkI ii i)) :: nil) st2)).

  set (Pi := fun (i: instr) => forall st1 st2, RS st1 st2 -> 
     @rutt (FCState +' E) _ _ _
    (sum_prerel (@TR_D_ME) (TR_E E))
    (sum_postrel (@VR_D_ME) (VR_E E))
    RS 
    (st_cmd_map_r (meval_instr pr1) (i :: nil) st1)
    (st_cmd_map_r (meval_instr pr2) ((Tr_instr i) :: nil) st2)).

  set (Pc := fun (c: cmd) => forall st1 st2, RS st1 st2 -> 
     @rutt (FCState +' E) _ _ _
    (sum_prerel (@TR_D_ME) (TR_E E))
    (sum_postrel (@VR_D_ME) (VR_E E))
    RS 
    (st_cmd_map_r (meval_instr pr1) c st1)
    (st_cmd_map_r (meval_instr pr2) (Tr_cmd c) st2)).

  revert H; revert st1 st2; revert cc.
  apply (cmd_Ind Pr Pi Pc); rewrite /Pr /Pi /Pc; simpl; eauto; intros.

  { eapply rutt_Ret; eauto. }
  { destruct i; simpl.
    eapply rutt_bind with (RR := RS); simpl in *.

    specialize (H st1 st2 H1).

    setoid_rewrite bind_ret_r in H; auto.
    intros; auto.
  }

  { eapply rutt_bind with (RR := RS); intros.
    eapply rutt_err_mk_AssgnE; auto.     
    eapply rutt_Ret; eauto. 
  }
    
  { eapply rutt_bind with (RR := RS); intros.
    eapply rutt_err_mk_OpnE; auto.
    eapply rutt_Ret; eauto.
  }

  { eapply rutt_bind with (RR := RS); intros.
    eapply rutt_err_mk_SyscallE; auto.
    eapply rutt_Ret; eauto.
  }

  { intros.
    eapply rutt_bind with (RR := RS); intros.
    { eapply rutt_bind with (RR := eq); intros.
      { eapply rutt_err_mk_EvalCond; auto. } 
      inv H2; destruct r2; simpl.
      eapply H; eauto.
      eapply H0; eauto.
    }  
    eapply rutt_Ret; auto.
  }

  { eapply rutt_bind with (RR := RS); simpl; intros.
    destruct rn; destruct p; simpl.    
    eapply rutt_bind with (RR := eq); simpl; intros.
    eapply rutt_err_mk_EvalBound; auto.

    inv H1; eapply rutt_bind with (RR := eq); simpl; intros.
    eapply rutt_err_mk_EvalBound; auto.

    inv H1; revert H0; revert st1 st2.
    induction (wrange d r2 r0); simpl; intros.
    { eapply rutt_Ret; eauto. }
    { eapply rutt_bind with (RR:= RS); simpl; intros.
      { eapply rutt_err_mk_WriteIndex; auto. } 
      eapply rutt_bind with (RR := RS); intros; auto.
    }
      
    eapply rutt_Ret; auto.
  }
    
  { eapply rutt_bind with (RR := RS); intros.
    eapply rutt_iter with (RI := RS); intros; auto.
    eapply rutt_bind with (RR := RS); intros.
    eapply H; auto.

    eapply rutt_bind with (RR := eq); intros.
    eapply rutt_err_mk_EvalCond; auto.

    inv H4; destruct r3.

    eapply rutt_bind with (RR := RS); intros; auto.
    eapply rutt_Ret; auto.
    eapply rutt_Ret; auto.
    eapply rutt_Ret; auto.
  }   
    
  { eapply rutt_bind with (RR := RS); intros.
    eapply rutt_trigger; simpl; intros.
    econstructor.
    unfold TR_D_ME; simpl.
    split; eauto.

    simpl in H0.     
    
    intros; auto.
    simpl in H0.
    dependent destruction H0; auto.
    eapply rutt_Ret; auto.
  }  
Qed.

(* Here we apply the inductive lemma and comp_gen_ok *)
Lemma rutt_cmd_tr_ME (cc: cmd) (st1 st2: estate) : 
  RS st1 st2 ->
  @rutt E _ _ _ 
    (TR_E _) (VR_E _) RS
    (mevalE_cmd pr1 cc st1) (mevalE_cmd pr2 (Tr_cmd cc) st2).
Proof.  
  intros; unfold mevalE_cmd; simpl.
  eapply interp_mrec_rutt; simpl; intros.
  { instantiate (3 := @TR_D_ME).
    instantiate (1 := @VR_D_ME).
    unfold meval_cstate.
    destruct d1.
    { unfold TR_D_ME in H0.
      destruct d2; try intuition.
      inv H1; simpl.
      eapply rutt_cmd_tr_ME_step; eauto.
    }  
   
    { unfold TR_D_ME in H0.
      destruct d2; simpl in *; try intuition.
      inv H0.  
      have CC := (comp_gen_ok_ME f0 xs _ es _ _ _ erefl erefl H4).
      setoid_rewrite fcstate_t_def in CC.
      setoid_rewrite fcstate_v_def in CC.
      eapply CC.
    }  
  }         
  eapply rutt_cmd_tr_ME_step; eauto. 
Qed.


End TR_MutualRec.

End GEN_Error.

End GEN_ErrAndFlat.

End TR_tests.

End TRANSF.

End WSW.

End Lang.


