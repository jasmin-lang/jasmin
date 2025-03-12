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

From ITree Require Import XRutt XRuttFacts.

From ITree Require Import EqAxiom.

From Jasmin Require Import expr psem_defs psem oseq compiler_util xrutt_aux.
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

(* PROBLEM with sections *)

(* This files contains proofs to test the semantic models in
 it_sems. It turns out that double recursion leads to a duplication of
 inductive proofs, and thus that mutual recursion leads to simpler
 proofs. The proofs on the modular model are still based on eutt and
 need to be revised. The proofs on the flat models are much longer and
 more laden with detail than those on the error-aware model. *)

Class with_Error (E: Type -> Type) {HasErr: ErrEvent -< E} := {
  is_error : forall {X}, E X -> bool;
  is_error_has : forall {X} (e:ErrEvent X) , is_error (HasErr X e)
}.
Arguments with_Error : clear implicits.
Arguments with_Error E {_}.

Definition ErrorCutoff {E: Type -> Type} {HasErr: ErrEvent -< E} {wE : with_Error E} X (m : E X) :=
  ~~(is_error m).

Definition NoCutoff {E: Type -> Type} {HasErr: ErrEvent -< E} {wE : with_Error E} X (m : E X) := true.

Definition rutt_err {E1 E2: Type -> Type}
  {HasErr1: ErrEvent -< E1} {wE1 : with_Error E1}
  {HasErr2: ErrEvent -< E2} {wE2 : with_Error E2}
  {O1 O2 : Type}
  (pre_event : prerel E1 E2)
  (post_event: postrel E1 E2)
  (post      : O1 -> O2 -> Prop) :=
  @rutt E1 E2 O1 O2 ErrorCutoff NoCutoff pre_event post_event post.

Instance with_Error_suml {E: Type -> Type} {HasErr: ErrEvent -< E} {wE : with_Error E} (T:Type -> Type) :
  with_Error (T +' E).
Proof.
  apply (@Build_with_Error _ _  (EE_MR (fun X (e: E X) => is_error e) T)).
  move=> x e => /=.
  apply is_error_has.
Defined.


(*
Existing Instance HasErr.
 *)
(*



Section CUTOFF.



Context (E: Type -> Type).
Context (HasErr: ErrEvent -< E).

Context (E0: Type -> Type).
Context (FI: FIso (E0 +' ErrEvent) E).

Definition ErrorCutoff X (m : E X) :=
  match mfun2 _ m with
  | inl1 _ => true
  | inr1 x => false
  end.

Definition NoCutoff : forall X, E X -> bool :=
  fun X m => true.

End CUTOFF.

*)
Section WSW.
Context
  {asm_op: Type}
  {asmop: asmOp asm_op}
  {wsw: WithSubWord}
  {dc: DirectCall}
  {syscall_state : Type}
  {ep : EstateParams syscall_state}
  {spp : SemPexprParams}
  {sip : SemInstrParams asm_op syscall_state}
  {pT : progT}
  {scP : semCallParams}
  (ev : extra_val_t).

Section Section.

  Context {E1 E2: Type -> Type}
          {HasErr1 : ErrEvent -< E1} {HasErr2 : ErrEvent -< E2}
          {wE1 : with_Error E1} {wE2 : with_Error E2}
        (TR_E : forall T1 T2,
            E1 T1 -> E2 T2 -> Prop)
        (VR_E : forall T1 T2,
            E1 T1 -> T1 -> E2 T2 -> T2 -> Prop).

Lemma rutt_iresult (T1 T2:Type) st1 st2 (x1 : exec T1) (x2 : exec T2) (R : T1 -> T2 -> Prop) :
  (forall v1, x1 = ok v1 -> exists2 v2, x2 = ok v2 & R v1 v2) ->
  rutt_err TR_E VR_E R (iresult st1 x1) (iresult st2 x2).
Proof.
  case: x1 => [ v1 | e1] hok.
  + have [v2 -> /=] := hok _ erefl.
    by apply: rutt_Ret.
  apply rutt_CutL => //.
  by rewrite /ErrorCutoff /= is_error_has.
Qed.

End Section.

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

Definition Tr_FunDef (f: fundef) : fundef :=
  match f with
  | MkFun i tyin p_xs c tyout r_xs xtr =>
    MkFun i tyin p_xs (Tr_cmd c) tyout r_xs xtr end.

(*********************************************************************)
(*** PROOFS **********************************************************)

Section TR_tests.

Context (pr1 : prog).

Let pr2 := map_prog Tr_FunDef pr1.

Context (E: Type -> Type)
        (TR_E : forall T1 T2,
            E T1 -> E T2 -> Prop)
        (VR_E : forall T1 T2,
            E T1 -> T1 -> E T2 -> T2 -> Prop).




(*Local Notation RS := (PR estate).
Local Notation RV := (PR values).
Local Notation RV1 := (PR value).
Local Notation RSMV := (PR (syscall_state * mem * seq value)).
*)

Context (FI: FIso (void1 +' ErrEvent) E).

(*
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

*)

Context (HasErr: ErrEvent -< E).
Context (wE: with_Error E).

Definition RC c1 c2 := Tr_cmd c1 = c2.

Context
   (Rv  : value -> value -> Prop)
   (Rscs: syscall_state_t -> syscall_state_t -> Prop)
   (Rm  : mem -> mem -> Prop)
   (RS  : estate -> estate -> Prop).

Notation Rvs := (List.Forall2 Rv).

Definition Rfres (fres1 fres2 : syscall_state_t * mem * values) :=
   [/\ Rscs fres1.1.1 fres2.1.1
      , Rm fres1.1.2 fres2.1.2
      & Rvs fres1.2 fres2.2].

Section TR_MutualRec.

(* ME: relation between FCState events *)
Definition TR_D_ME {T1 T2} (d1 : FCState T1)
                           (d2 : FCState T2) : Prop :=
  match d1, d2 with
  | FLCode c1 st1, FLCode c2 st2 => RC c1 c2 /\ RS st1 st2
  | FFCall scs1 m1 fn1 vs1, FFCall scs2 m2 fn2 vs2 =>
    [/\ Rscs scs1 scs2
      , Rm m1 m2
      , fn1 = fn2
      & Rvs vs1 vs2]
  | _, _ => False
  end.

(* ME: relation between FCState event outputs, i.e. over estate *)
Definition VR_D_ME {T1 T2}
  (d1 : FCState T1) (t1: T1) (d2 : FCState T2) (t2: T2) : Prop :=
  match d1 in FCState T1_ return T1_ -> T2 -> Prop with
  | FLCode _ _ =>
    match d2 in FCState T2_ return estate -> T2_ -> Prop with
    | FLCode _ _ => RS
    | FFCall _ _ _ _ => fun _ _ => False
    end
  | FFCall _ _ _ _ =>
    match d2 in FCState T2_ return syscall_state_t * mem * values -> T2_ -> Prop with
    | FLCode _ _ => fun _ _ => False
    | FFCall _ _ _ _ => Rfres
    end
  end t1 t2.

(***)

Definition TR_DE : prerel (FCState +' E) (FCState +' E) :=
  sum_prerel (@TR_D_ME) TR_E.

Definition VR_DE : postrel (FCState +' E) (FCState +' E) :=
  sum_postrel (@VR_D_ME) VR_E.

(*
Context (fcstate_t_def : TR_E (FCState +' E) = TR_DE_ME).
Context (fcstate_v_def : VR_E (FCState +' E) = VR_DE_ME).
*)
(*
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
*)
(***)

Check @rutt.
(*
(m_t : Type)
(tr_e : m_t -> pexpr -> cexec pexpr)
(tr_lval : m_t -> lval ->

 dead_code_i i O -> I, c

s     -i-> s'
={I}       ={O}
t     -c-> t'


s.mem = t.mem

RS X s t : exists2 vm , t = with_vm s vm & s.(evm) <=[X] vm.
RC I O cs ct = dead_code cs O = ok (I, ct).

fres
Definition Rfres (fres1 fres2 : syscall_state_t * mem * values) :=
   [/\ Rscs fres1.1.1 fres2.1.1
      , Rm fres1.1.2 fres2.1.2
      & List.Forall2 values_uincl fres1.2 fres2.2].






Let Pi_r s (i:instr_r) s' :=
    forall ii s2,
      match dead_code_i is_move_op do_nop onfun (MkI ii i) s2 with
      | Ok (s1, c') =>
        forall vm1', s.(evm) <=[s1] vm1' ->
          exists vm2', s'.(evm) <=[s2] vm2' /\
          sem_oi (with_vm s vm1') c' (with_vm s' vm2')
      | _ => True
      end.

*)

Lemma rutt_err_assgn x tg ty e st1 st2 :
  RS st1 st2 ->
  rutt_err TR_DE VR_DE RS
    (iresult st1 (eval_assgn pr1 x tg ty e st1))
    (iresult st2 (eval_assgn pr2 (tr_lval x) tg ty (tr_expr e) st2)).
Proof.
  move=> hrs; apply rutt_iresult.
Admitted.

Lemma rutt_err_opn x o e st1 st2 :
  RS st1 st2 ->
  rutt_err TR_DE VR_DE RS
    (iresult st1 (sem_sopn (p_globs pr1) o st1 x e))
    (iresult st2 (sem_sopn (p_globs pr2) o st2 (tr_lvals x) (tr_exprs e))).
Admitted.

(*
Lemma sum_postrelI (E1 E2 D1 D2 : Type -> Type) (PR1 : postrel E1 D1) (PR2 : postrel E2 D2) :
  sum_postrel PR1 PR2
: postrel (E1 +' E2) (D1 +' D2) :=
    sum_postrel_inl : forall (A B : Type) (e1 : E1 A) (d1 : D1 B) (a : A) (b : B),
                      PR1 A B e1 a d1 b -> sum_postrel PR1 PR2 A B (inl1 e1) a (inl1 d1) b
  | sum_postrel_inr : forall (A B : Type) (e2 : E2 A) (d2 : D2 B) (a : A) (b : B),
                      PR2 A B e2 a d2 b -> sum_postrel PR1 PR2 A B (inr1 e2) a (inr1 d2) b.
*)
Lemma rutt_msem_i (i: instr_r) (st1 st2: estate) :
  RS st1 st2 ->
  rutt_err TR_DE VR_DE RS (msem_i pr1 i st1) (msem_i pr2 (Tr_ir i) st2).
Proof.
  case: i.
  + by move=> x tag ty e hst /=; apply rutt_err_assgn.
  + admit.
  + admit.
  + move=> e c1 c2 hst.
(*
    Opaque msem_i.
rewrite /=.

RC_bw I O c1 c2 =  dead_code_c c1 O = ok (I, c2)
RC_fw I O c1 c2 =  const_prop_c c1 I = ok (O, c2)

TR_D_ME I O =
fun (T1 T2 : Type) (d1 : FCState T1) (d2 : FCState T2) =>
match d1 with
| FLCode c1 st1 => match d2 with
                   | FLCode c2 st2 => RC I O c1 c2 /\ RS I st1 st2
                   | FFCall _ _ _ _ => False
                   end
| FFCall scs1 m1 fn1 vs1 =>
    match d2 with
    | FLCode _ _ => False
    | FFCall scs2 m2 fn2 vs2 => [/\ Rscs scs1 scs2, Rm m1 m2, fn1 = fn2 & Rvs vs1 vs2]
    end
end

VR_D_ME I O =
fun (T1 T2 : Type) (d1 : FCState T1) (d2 : FCState T2) =>
match d1 with
| FLCode c1 st1 => match d2 with
                   | FLCode c2 st2 => RS O st1 st2
                   | FFCall _ _ _ _ => False
                   end
| FFCall scs1 m1 fn1 vs1 =>
    match d2 with
    | FLCode _ _ => False
    | FFCall scs2 m2 fn2 vs2 => [/\ Rscs scs1 scs2, Rm m1 m2, fn1 = fn2 & Rvs vs1 vs2]
    end
end

[/\ Rscs scs1 scs2, Rm m1 m2, fn1 = fn2 & Rvs vs1 vs2]
Rscs Rm Rvs = eq
Rscs Rm = eq, Rvs = List.Forall2 value_uincl.






forall O,

 rutt_err TR_DE VR_DE RS (msem_i pr1 (Cif e c1 c2) st1) (msem_i pr2 (Cif e' c1' c2') st2).


 /=.
*)
    apply rutt_bind with (RR := eq).
    + admit.
    move=> b _ <-.
    apply rutt_trigger => /=.
    + by apply sum_prerel_inl => /=; split => //; case: b.
    by move=> t1 t2 h; dependent destruction h; auto.
  + admit.
  + move=> al c1 e c2 hst /=.
    apply XRuttFacts.rutt_iter with (RI:=RS) => //.
    move=> s1 s2 hs.
    apply rutt_bind with (RR := RS).
    + apply rutt_trigger => /=.
      + by apply sum_prerel_inl => /=.
      by move=> t1 t2 h; dependent destruction h; auto.
    move=> t1 t2 ht.
    apply rutt_bind with (RR := eq).
    + admit.
    move=> b _ <-.
    case: b.
    + apply rutt_bind with (RR := RS).
      + apply rutt_trigger => /=.
        + by apply sum_prerel_inl.
        by move=> ?? h; dependent destruction h; auto.
      by move=> ?? h; apply rutt_Ret; constructor.
    by apply rutt_Ret; constructor.
  move=> xs fn es hst /=.
  apply rutt_bind with (RR := Rvs).
  + admit.
  move=> vs1 vs2 hvs.
  apply rutt_bind with (RR := Rfres).
  + apply rutt_trigger => /=.
    + apply sum_prerel_inl => /=; split => //.
      + admit. (* RS => Rscs *)
      admit. (* RS => Rmem *)
    move=> ?? h; dependent destruction h; auto.
  move=> [[scs2 m2] vs] [[scs2' m2'] vs'] [/=???].
  admit.
Admitted.

Lemma rutt_msem_fcstate ev1 ev2 T1 T2 (d1 : FCState T1) (d2: FCState T2) :
  TR_D_ME d1 d2 ->
  rutt_err TR_DE VR_DE (fun v1 v2 => VR_D_ME d1 v1 d2 v2) (msem_fcstate pr1 ev1 d1) (msem_fcstate pr2 ev2 d2).
Proof.
  case: d1 d2 => [c1 st1 | scs1 m1 f1 vs1]  [c2 st2 | scs2 m2 f2 vs2] //=.
  + move=> [<- hst].
    elim: c1 st1 st2 hst => [ | [ii i] c hrec] st1 st2 hst /=.
    + by apply rutt_Ret.
    apply rutt_bind with (RR := RS) => //.
    by apply rutt_msem_i.
  move=> [hscs hm <- hvs].
  rewrite /msem_call.
  apply rutt_bind with (RR := fun fd1 fd2 => fd2 = Tr_FunDef fd1).
  + admit.
Admitted.

Lemma rutt_rsem_call ev1 ev2 scs1 m1 fn vs1 scs2 m2 vs2 :
  Rfres (scs1, m1, vs1)  (scs2, m2, vs2) ->
  rutt_err TR_E VR_E Rfres (rsem_call pr1 ev1 scs1 m1 fn vs1) (rsem_call pr2 ev2 scs2 m2 fn vs2).
Proof.
  move=> hpre; apply interp_mrec_rutt with (RPreInv := @TR_D_ME) (RPostInv := @VR_D_ME).
  + move=> T1 T2 d1 d2.

have <- : ErrorCutoff =  (EE_MR ErrorCutoff FCState).
admit.
have <- : NoCutoff = (EE_MR NoCutoff FCState).
rewrite /NoCutoff /EE_MR.
admit.
    by apply rutt_msem_fcstate.
have <- : ErrorCutoff =  (EE_MR ErrorCutoff FCState).
admit.
have <- : NoCutoff = (EE_MR NoCutoff FCState).
rewrite /NoCutoff /EE_MR.
admit.
  have := @rutt_msem_fcstate ev1 ev2 _ _ (FFCall scs1 m1 fn vs1) (FFCall scs2 m2 fn vs2).
  apply => /=; case hpre => //.
Admitted.

(*

Search interp_err.

Definition rsem_call {E} `{ErrEvent -< E}
   (scs1 : syscall_state_t) (m1 : mem)
   (fn : funname) (vargs : values) : itree E (syscall_state_t * mem * values) :=
 mrec msem_fcstate (FFCall scs1 m1 fn vargs).



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
*)
(*
Lemma comp_gen_ok_ME (fn: funname)
  (xs1 xs2: lvals) (es1 es2: pexprs) (st1 st2: estate) :
  xs2 = map tr_lval xs1 ->
  es2 = map tr_expr es1 ->
  RS st1 st2 ->
  rutt_err TR_DE VR_DE
   (msem_i


 (FCState +' E) _ _ _ (TR_E _) (VR_E _)
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
*)
(* Inductive lemma - GOOD. here we are not tying the coinductive knot,
   as st_cmd_map_r is just a map function. *)
(*
Lemma rutt_cmd_tr_ME_step (cc: cmd) (st1 st2: estate) :
  RS st1 st2 ->
  rutt_err (FCState +' E) _ _ _
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
*)

End TR_MutualRec.

End TR_tests.

End TRANSF.

End WSW.



