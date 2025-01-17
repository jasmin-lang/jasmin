Require Import List.
(* for positive *)
Require Import BinNums.

From Jasmin Require Import utils.
(* compiles: gen_map for Mz.t, word.v for u8 *)
(* From Jasmin Require Import gen_map word. *)
(* does not compile *)
From Jasmin Require Import strings warray_. 

(*
Locate "_ .[ _ ]".

About Ms.get.
About Mt.get.
*)

(* NOTE: compiles if use local version *)
(*
Variant result (E: Type) (A : Type) : Type :=
    Ok (s: A) | Error (s: E).

Arguments Error {E} {A} s.
Arguments Ok E [A] s.
*)

(** shadows utils.v *)

Variant error :=
 | ErrOob | ErrAddrUndef | ErrAddrInvalid | ErrStack | ErrType | ErrArith | ErrSemUndef.

Definition exec t := result error t. 

Definition llprod (ts: list Type) (tr: Set) : Type :=
  fold_right (fun t tr0 => t -> tr0) tr ts.

(***)

Record array (s : positive) : Type := Build_array
  { arr_data : Mz.t (ssralg.GRing.ComRing.sort u8) }.

(** from sem_type.v *)
Variant stype : Set :=
    sbool : stype
  | sint : stype
  | sarr : positive -> stype
  | sword : nat -> stype.

Definition sem_t (t : stype) : Type :=
  match t with
  | sbool    => bool
  | sint     => Z
  | sarr n   => array n 
  | sword s  => nat
  end.

(***)

(* NOTE: compiles with this version *)
(*
Parameter Array : positive -> Type.

Definition sem_t (t : stype) : Type :=
  match t with
  | sbool    => bool
  | sint     => bool
  | sarr n   => Array n 
  | sword s  => bool 
  end.
*)

Definition sem_prod ts tr := llprod (map sem_t ts) tr.


(*********************************************************************)

From ExtLib Require Import
     Structures.Monad.

From ITree Require Import
     Basics.CategoryOps 
     Basics.Function. 

Class Eq1 (M : Type -> Type) : Type :=
  eq1 : forall A, M A -> M A -> Prop.

Definition relation  : Type -> Type := fun A : Type => A -> A -> Prop.

Implicit Types m : Type -> Type.
Implicit Types a b c : Type.

Definition Kleisli m a b : Type := a -> m b.

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
 
Section ExecT.

  Context (m : Type -> Type). 
  
  Definition execT (a : Type) : Type :=
    m (exec a)%type.

End ExecT.

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
