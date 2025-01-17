(* coqc version 8.20.0 compiled with OCaml 5.2.1
   coqtop version 8.20.0 *)

Require Coq.FSets.FMapAVL.
Require Coq.FSets.FMaps.
Require mathcomp.word.word.
Require ITree.Basics.Function.

Import Coq.FSets.FMaps.
Import mathcomp.ssreflect.eqtype.
Import mathcomp.ssreflect.ssrnat. 
Import mathcomp.algebra.ssralg.
Import mathcomp.word.word.
Import ITree.Basics.CategoryOps.

Variant result (E : Set) (A : Type) : Type :=
| Ok (s: A)
| Error (s: E).

Variant error := | ErrA | ErrB.

Definition exec t := result error t.

Module Type CmpType.

  Parameter t : eqType.

  Parameter cmp : t -> t -> comparison.

End CmpType.

Module MkOrdT (T: CmpType) <: OrderedType.

  Definition t := Equality.sort T.t.

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

  Definition t T := Map.t T.

End Mmake.

Module Export CmpZ.
  
  Definition t : eqType.
    Admitted.

  Definition cmp : t -> t -> comparison.
    Admitted.

End CmpZ.

Module Mz := Mmake CmpZ.

Variant wsize := U8 | U16.

Definition wsize_size_minus_1 (s: wsize) : nat.
  Admitted.

Coercion nat_of_wsize (sz : wsize) := (wsize_size_minus_1 sz).+1.

Module Type FArrayT.

  Parameter array : Type -> Type.

End FArrayT.

Module FArray : FArrayT.

  Record array_ (T:Type) := MkArray {
    a_map : Mz.t T;
    a_dfl : nat -> T
  }.

  Definition array := array_.

End FArray.

Module Export Array.

  Definition array (s: nat) T := FArray.array (exec T).

End Array.

Definition llprod (ts: list Type) (tr: Set) : Type.
  Admitted.

Record array (s : nat) : Type := Build_array
  { arr_data : Mz.t (ssralg.GRing.ComRing.sort (word U8)) }.

Variant stype : Set :=
  |  sbool : stype
  | sarr : nat -> stype.

Definition sem_t (t : stype) : Type := match t with
  | sbool    => bool
  | sarr n   => array n
  end.

Definition sem_prod ts tr := llprod (map sem_t ts) tr.

Class Eq1 (M : Type -> Type) : Type :=
  eq1 : forall A, M A -> M A -> Prop.

Definition Kleisli (m: Type -> Type) (a b: Type) : Type := a -> m b.

Section Instances.

  Context {m : Type -> Type}.

  Context `{Eq1 m}.

  Instance Case_Kleisli : Case (Kleisli m) sum.
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

  Definition foo1 E : Eq1 (@execT (itree E)) :=
     fun _ => @eutt E _ _ (exec_rel eq).

