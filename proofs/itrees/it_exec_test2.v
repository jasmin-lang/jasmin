(* From ITree Require Import
  Monad. *)
  (* 1) not importing the following suffices to compile *)
(*  Basics.CategoryKleisli.  *)

From Jasmin Require Import sem_type utils.  

(************)

From Coq Require Import
     Morphisms.

From ExtLib Require Import
     Structures.Monad.

From ITree Require Import
     Basics.CategoryOps 
     Basics.Function. 

Implicit Types m : Type -> Type.
Implicit Types a b c : Type.

Definition Kleisli m a b : Type := a -> m b.

(* SAZ: We need to show how these are intended to be used. *)
(** A trick to allow rewriting in pointful contexts. *)
Definition Kleisli_arrow {m a b} : (a -> m b) -> Kleisli m a b := fun f => f.
Definition Kleisli_apply {m a b} : Kleisli m a b -> (a -> m b) := fun f => f.

Definition pure {m} `{Monad m} {a b} (f : a -> b) : Kleisli m a b :=
  fun x => ret (f x).

Class Eq1 (M : Type -> Type) : Type :=
  eq1 : forall A, M A -> M A -> Prop.

Section Instances.
  Context {m : Type -> Type}.
  Context `{Monad m}.
  Context `{Eq1 m}.

(*  #[global] Instance Eq2_Kleisli : Eq2 (Kleisli m) :=
    fun _ _ => pointwise_relation _ eq1.

  #[global] Instance Cat_Kleisli : Cat (Kleisli m) :=
    fun _ _ _ u v x =>
      bind (u x) (fun y => v y).

  Definition map {a b c} (g:b -> c) (ab : Kleisli m a b) : Kleisli m a c :=
     cat ab (pure g).
  
  #[global] Instance Initial_Kleisli : Initial (Kleisli m) void :=
    fun _ v => match v : void with end.

  #[global] Instance Id_Kleisli : Id_ (Kleisli m) :=
    fun _ => pure id.
*)

(* each of these instances is critical, and can cause failure *)
(***)  
  #[global] Instance Case_Kleisli : Case (Kleisli m) sum :=
    fun _ _ _ l r => case_sum _ _ _ l r.

(*  
  #[global] Instance Inl_Kleisli : Inl (Kleisli m) sum :=
    fun _ _ => pure inl.

  #[global] Instance Inr_Kleisli : Inr (Kleisli m) sum :=
    fun _ _ => pure inr.

  #[global] Instance Iter_Kleisli `{MonadIter m} : Iter (Kleisli m) sum :=
    fun a b => Basics.iter.
*)
(***)
End Instances.

(*************************)

(* 2) defining Eq1 (either as a class or not) locally suffices to
compile *)
(* 
Class Eq1 (M: Type -> Type) : Type :=
 eq1 : forall A : Type, M A -> M A -> Prop.

Definition Eq1  : (Type -> Type) -> Type :=
fun M : Type -> Type => forall A : Type, M A -> M A -> Prop.
*)

(* 3) defining result locally suffices to compile *)
(* Definition error: Set := bool.

Variant result (E: Type) (A : Type) : Type :=
    Ok (s: A) | Error (s: E).

Arguments Error {E} {A} s.
Arguments Ok E [A] s.

Definition exec t := result error t. *)

(* using list instead of seq makes no difference *)
Require Import List.
Definition llprod (ts: list Type) (tr: Set) : Type :=
  fold_right (fun t tr0 => t -> tr0) tr ts.
(* uncurrying makes no difference *)
Definition llprodP (ts: list Type) (tr: Set) : Type :=
  fold_right (fun t tr0 => (t * tr0)%type) tr ts.
Definition llprodI (ts: list Type) (tr: Set) : Type :=
  llprodP ts tr -> tr.

(* in sem_type this cannot be Set. nothing changes if it is defined
locally as long as it stays out of Set *)
(*
Definition sem_t (t : stype) : Type :=
  match t with
  | sbool    => bool
  | sint     => bool
  | sarr n   => WArray.array n 
  | sword s  => bool 
  end.

Definition relation  : Type -> Type := fun A : Type => A -> A -> Prop.
*) 
  
Section ExecT.

  Context (m : Type -> Type). 
  
  Definition execT (a : Type) : Type :=
    m (exec a)%type.

End ExecT.

(* uses list instead of seq *)
Definition sem_prod ts tr := llprodI (map sem_t ts) tr.

Section Test.

Context (result_rel: forall (W: Set) {X}, relation X -> relation W ->
   relation (result W X)).
  
Context (itree: (Type -> Type) -> Type -> Type).  
Context (eutt: forall {E : Type -> Type} {R1 R2 : Type},
       (R1 -> R2 -> Prop) -> itree E R1 -> itree E R2 -> Prop).

Definition exec_rel {X: Type} (R : relation X) :
   relation (exec X) := @result_rel error X R (fun x y => True). 

(*** NOTE. FAILS when:
1) CategoryKleisli is loaded, 
2) Eq1 is NOT defined locally, but comes from Monad, and 
3) result is NOT defined locally, but comes from utils *)
Definition foo1 E : Eq1 (@execT (itree E)) :=
  fun _ => @eutt E _ _ (exec_rel eq).

End Test.
