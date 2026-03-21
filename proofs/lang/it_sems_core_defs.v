From ITree Require Import
     Basics
     ITree
     ITreeFacts
     Events.Exception
     Interp.Recursion
     MonadState.
Import Basics.Monads.

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.

Require Import utils it_exec.
Import MonadNotation.
Local Open Scope monad_scope.

(**** Error semantics ******************************************)
Section Errors.

(* error events *)
Definition ErrEvent : Type -> Type := exceptE error_data.

(* execT (itree E) R = itree E (execS R) *)
Definition handle_Err {E} : ErrEvent ~> execT (itree E) :=
  fun _ e =>
    match e with
    | Throw e' => Ret (ESerror _ e')
    end.

(* ErrEvnt handler *)
Definition ext_handle_Err {E: Type -> Type} :
  ErrEvent +' E ~> execT (itree E) :=
  fun _ e =>
  match e with
  | inl1 e' => handle_Err e'
  | inr1 e' => Vis e' (pure (fun x => ESok x)) end.

(* ErrEvent interpreter *)
Definition interp_Err {E: Type -> Type} {A}
  (t: itree (ErrEvent +' E) A) : execT (itree E) A :=
  interp_exec ext_handle_Err t.

(*** auxiliary error functions *)

Definition ioget {E: Type -> Type} `{ErrEvent -< E} {V} (err: error_data) (o: option V) : itree E V :=
  match o with
  | Some v => Ret v
  | None => throw err
  end.

Definition err_result {E: Type -> Type} `{ErrEvent -< E} (Err : error -> error_data) :
  result error ~> itree E :=
  fun _ t => match t with
             | Ok v => Ret v
             | Error e => throw (Err e) end.

End Errors.

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
