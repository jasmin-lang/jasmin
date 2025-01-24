(* coqc version 8.20.0 compiled with OCaml 5.2.1
   coqtop version 8.20.0 *)

(**)
Require Coq.FSets.FMapAVL.
Require Coq.FSets.FMaps.
Require Coq.Unicode.Utf8.
Require ITree.Basics.Function.

Variant result (E : Set) (A : Type) : Type :=
| Ok (s: A)
| Error (s: E).

Variant error := | ErrA | ErrB.

Definition exec t := result error t.

(**)
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

  Polymorphic Definition t T := Map.t T.

End Mmake.

Module Export CmpZ.
  
  Definition t : Type.
    Admitted.
  Definition cmp : t -> t -> comparison.
    Admitted.

End CmpZ.

Module Mz := Mmake CmpZ.

Variant wsize := U8 | U16.

Definition wsize_size_minus_1 (s: wsize) : nat.
  Admitted.

Module Type FArrayT.

  Parameter array : Type -> Type.

End FArrayT.

Module FArray : FArrayT.

  (* trigger *)
  Definition array T := Mz.t T. (* list T. *)
  (* can't set it as Polymorphic *)
  
End FArray. 

(* trigger *)  
Definition array1 (s: nat) T := FArray.array (exec T). 
(* Polymorphic Definition array1 (s: positive) T := FArray.array (exec T).  *)
      
Definition llprod (ts: list Type) (tr: Set) : Type.
  Admitted.

Record array (s : nat) : Type := Build_array
  { arr_data : Mz.t bool }.

Variant stype : Set :=
    sbool : stype
  | sarr : nat -> stype 
  | sword : nat -> stype.

Definition sem_t (t : stype) : Type := match t with
  | sbool    => bool
  | sarr n   => array n 
  | sword s  => nat
  end.

(* trigger *)
Definition sem_prod ts tr := llprod (map sem_t ts) tr. 
(* Polymorphic Definition sem_prod ts tr := llprod (map sem_t ts) tr. *)

(**)
Import ITree.Basics.CategoryOps. 

Class Eq1 (M : Type -> Type) : Type :=
  eq1 : forall A, M A -> M A -> Prop.


Definition Kleisli (m: Type -> Type) (a b: Type) : Type := a -> m b.

Section Instances.

  Context {m : Type -> Type}.
  Context `{Eq1 m}.

  (* trigger *)
  Instance Case_Kleisli : Case (Kleisli m) sum. 
  (* Polymorphic Instance Case_Kleisli : Case (Kleisli m) sum.  *)
    Admitted.

End Instances.

Section ExecT.

  Context (m : Type -> Type).

  Definition execT (a : Type) : Type := m (exec a)%type.

End ExecT.

Section Test.

  Context (result_rel:
            forall (W: Set) {X}, relation X -> relation W ->
                                      relation (result W X)).

  Context (itree: (Type -> Type) -> Type -> Type).

  Context (eutt: forall {E : Type -> Type} {R1 R2 : Type},
       (R1 -> R2 -> Prop) -> itree E R1 -> itree E R2 -> Prop).

  Definition exec_rel {X: Type} (R : relation X) :
     relation (exec X) := result_rel error X R (fun x y => True). 
  
  Definition foo1 E : Eq1 (@execT (itree E)) :=
     fun _ => @eutt E _ _ (exec_rel eq).

