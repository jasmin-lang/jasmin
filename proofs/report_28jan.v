(* coqc version 8.20.0 compiled with OCaml 5.2.1
   coqtop version 8.20.0 *)

(**)
Require Coq.FSets.FMapAVL.
Require Coq.FSets.FMaps.
Require Coq.Unicode.Utf8.
Require ITree.Basics.Function.


(** (1b) exec definition ****************************************)

(* trigger: result involves choice *)
Definition result  (E A : Type) : Type := E + A.

Definition exec t := result unit t.



(** (7b) definition of Eq1 ****************************************)

Class Eq1 (M : Type -> Type) : Type :=
  eq1 : forall A, M A -> M A -> Prop.



(** (3b) definition of Mmake ***********************************)

Import Coq.FSets.FMaps. 

Module Type CmpType.

  Parameter t : Type.

  Parameter cmp : t -> t -> comparison.

End CmpType.

Module MkOrdT (T: CmpType) <: OrderedType.

  Definition t := T.t.
  Definition eq x y := T.cmp x y = Eq.
  Definition lt x y := T.cmp x y = Lt.

  Lemma eq_refl x: eq x x.
    Admitted.

  Lemma eq_sym x y: eq x y -> eq y x.
    Admitted.

  Lemma eq_trans x y z: eq x y -> eq y z -> eq x z.
    Admitted.

  Lemma lt_trans x y z: lt x y -> lt y z -> lt x z.
    Admitted.

  Lemma lt_not_eq x y: lt x y -> ~ eq x y.
    Admitted.

  Definition compare x y : Compare lt eq x y.
    Admitted.

  Definition eq_dec x y: {eq x y} + {~ eq x y}.
   Admitted.

End MkOrdT.

Module Mmake (K': CmpType). 
  
  Module K := K'.

  Module Ordered := MkOrdT K.

  Module Map := FMapAVL.Make Ordered.

  (* poly makes no difference *)
  Definition t T := Map.t T. 
  (* Polymorphic Definition t T := Map.t T. *)
  
End Mmake.



(** (2b) definition of CmpZ ***********************************)

Module CmpZ : CmpType.
  
  Definition t : Type.
    Admitted.
  Definition cmp : t -> t -> comparison.
    Admitted.

End CmpZ.



(** (4) definition of Mz: depends on (2b, 3b) **********************)

Module Mz := Mmake CmpZ.



(** (6) definition of array_rec: depends on 4 -> (2b, 3b) ********)
      
Record arrayR (T: Type) : Type := { arr_data : Mz.t T }.



(** (5) definition of sem_t: depends on 6 -> (2b, 3b) ********)
      
Definition sem_t (n : nat) : Type := match n with
  | 0    => bool
  | S n   => arrayR bool
  end.



(** (8) definition of execT: depends on 1b **************************)

Section ExecT.

  Context (m : Type -> Type).

  Definition execT (a : Type) : Type := m (exec a)%type.

End ExecT.



(** (9) definition of Case_Kleisli: depends on 7b (not used) ***********)

Import ITree.Basics.CategoryOps. 

Definition Kleisli (m: Type -> Type) (a b: Type) : Type := a -> m b.

Section Instances.

  Context {m : Type -> Type}.
  Context `{Eq1 m}.

  (* trigger: should be poly *)
  Instance Case_Kleisli : Case (Kleisli m) sum. 
  (* Polymorphic Instance Case_Kleisli : Case (Kleisli m) sum.  *)
    Admitted.

End Instances.



(** conflict test ********************************************************)

Section Test.
 
  (** (T1) depends on (7b, 8) -> (1b, 7b) ******************)

  (* trigger: should be poly, but not as the last *)
  Definition Eq1_execT_foo (itree: (Type -> Type) -> Type -> Type) E :
    Eq1 (@execT (itree E)).
  (* Polymorphic Definition foo1 E : Eq1 (@execT (itree E)). *)
  Admitted.
  
  (** (T2) depends on 5 -> (2b, 3b) ************************)

  (* trigger: should be poly, but not as the last *)
  Definition map_sem_t_foo (ts: list nat) := map sem_t ts.  
  (* Polymorphic Definition sem_foo (ts: list nat) := map sem_t ts. *) 

  (** (T3) depends on (6, 1b) -> (1b, 2b, 3b) ****************)

  (* trigger: should be poly, but not as the last *)
  Definition arrayR_exec_foo (s: nat) T := arrayR (exec T). 
  (* Polymorphic Definition array1 (s: nat) T := arrayR (exec T).  *)
  
End Test.
