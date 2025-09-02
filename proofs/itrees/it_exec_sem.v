(* -> was it_sems_exec.v *)

From ITree Require Import
     Basics
     ITree
     ITreeFacts
     Events.Exception
     Interp.Recursion
     MonadState.
Import Basics.Monads.

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.

Require Import tfam_iso it_exec.

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

Definition ioget {E: Type -> Type} `{ErrEvent -< E} {V}
  (err: error_data) (o: option V) : itree E V :=
  match o with
  | Some v => Ret v
  | None => throw err
  end.

End Errors.

(*
#[global] Instance fromErr E E0 {wE : FIso E (ErrEvent +' E0)} : ErrEvent -< E :=
  fun T (e:ErrEvent T) => mfun2 (inl1 e).
*)

Definition is_error {E E0 : Type -> Type} (wE : FIso E (ErrEvent +' E0)) (T : Type) (e : E T) :=
  match mfun1 e with
  | inl1 _ => true
  | inr1 _ => false
  end.
