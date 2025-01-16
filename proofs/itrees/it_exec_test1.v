From ITree Require Import
  Monad
  (* 1) not importing Events.Map suffices to compile *)
  Events.Map. 

From Jasmin Require Import sem_type utils.  

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
1) Events.Map is loaded, 
2) Eq1 is NOT defined locally, but comes from Monad, and 
3) result is NOT defined locally, but comes from utils *)
Definition foo1 E : Eq1 (@execT (itree E)) :=
  fun _ => @eutt E _ _ (exec_rel eq).

End Test.
