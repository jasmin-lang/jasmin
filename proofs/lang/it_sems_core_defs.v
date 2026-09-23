From ITree Require Import
     Basics
     ITree
     ITreeFacts
     Events.Exception
     Interp.Recursion
     MonadState.
Import Basics.Monads.

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype seq.

Require Import utils type sem_type values it_exec.
Import MonadNotation.
Local Open Scope monad_scope.

(**** Error semantics ******************************************)
Section Errors.

Context {E : Type -> Type}.

(* error events *)
Definition ErrEvent : Type -> Type := exceptE error.

(* execT (itree E) R = itree E (execS R) *)
Definition handle_Err : ErrEvent ~> execT (itree E) :=
  fun _ e =>
    match e with
    | Throw e' => Ret (Error e')
    end.

(* ErrEvnt handler *)
Definition ext_handle_Err :
  ErrEvent +' E ~> execT (itree E) :=
  fun _ e =>
  match e with
  | inl1 e' => handle_Err e'
  | inr1 e' => Vis e' (pure (fun x => ok x)) end.

(* ErrEvent interpreter *)
Definition interp_Err {A}
  (t: itree (ErrEvent +' E) A) : execT (itree E) A :=
  interp_exec ext_handle_Err t.

(*** auxiliary error functions *)

Definition ioget `{ErrEvent -< E} {V} (err: error) (o: option V) : itree E V :=
  match o with
  | Some v => Ret v
  | None => throw err
  end.

Definition iresult `{ErrEvent -< E} :
  result error ~> itree E :=
  fun _ t => match t with
             | Ok v => Ret v
             | Error e => throw e end.

Definition iassert `{ErrEvent -< E} (b : bool) (e : error) : itree E unit :=
  iresult (assert b e).

End Errors.

Definition preservesE
  E1 E2 E3 {S12 : E1 -< E2} {S23 : E1 -< E3} (F : Handler E2 E3) :=
  forall T (e : E1 T),
    eutt eq (F T (subevent T e)) (trigger e).

#[global] Arguments preservesE _ {_ _ _ _} _.

Section Preserves.

Context
  {E E' : Type -> Type}
  {SErr : ErrEvent -< E}
.

Lemma translate_inr_iresult T (r : exec T) :
  eutt eq
    (translate inr1 (iresult (E := E) r))
    (iresult (E := E' +' E) r).
Proof.
case: r => [r|e]; first by rewrite translate_ret; reflexivity.
by rewrite translate_vis; apply: eqit_Vis => -[].
Qed.

Context {SErr' : ErrEvent -< E'}.

Lemma interp_preserves_throw (F : Handler E E') T e :
  preservesE ErrEvent F ->
  eutt eq (interp F (throw (X := T) e)) (throw e).
Proof. by move=> h; rewrite interp_vis h bind_vis; apply: eqit_Vis. Qed.

Lemma interp_preserves_iresult (F : Handler E E') T (r : exec T) :
  preservesE ErrEvent F ->
  eutt eq (interp F (iresult r)) (iresult r).
Proof.
move=> h; case: r => [r|e]; first by rewrite interp_ret; reflexivity.
rewrite (interp_preserves_throw _ _ h); reflexivity.
Qed.

End Preserves.

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

Lemma bind_throw E E0 {wE : with_Error E E0} A B e (F : A -> itree E B):
    ITree.bind (Exception.throw e) F
    ≅ Exception.throw e.
Proof.
  rewrite /Exception.throw /= bind_vis.
  apply eqit_Vis; case.
Qed.

(* TODO is this somewhere? *)
Lemma eqit_throw
  {Err E R1 R2} {H : exceptE Err -< E} (RR : R1 -> R2 -> Prop) b1 b2 (e : Err) :
  eqit RR b1 b2 (throw (H := H) e) (throw e).
Proof. exact: eqit_Vis. Qed.

Section ItAppSopn.

Context {E : Type -> Type} `{ErrEvent -< E}.

Definition it_sem_prod (ts : seq ctype) (T : Type) := sem_prod ts (itree E T).

Fixpoint it_app_sopn A (ts : seq ctype) : it_sem_prod ts A -> values -> itree E A :=
  match ts return it_sem_prod ts A -> values -> itree E A with
  | [::] => fun (o : itree E A) vs =>
      if vs is [::] then o else throw ErrType
  | t :: ts => fun (o : sem_t t -> it_sem_prod ts A) vs =>
      if vs is v :: vs then
        v' <- iresult (of_val t v) ;;
        it_app_sopn (o v') vs
      else throw ErrType
  end.

#[global] Arguments it_app_sopn {A} ts _ _.

End ItAppSopn.
