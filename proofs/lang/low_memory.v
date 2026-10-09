(* ** Imports and settings *)

From Coq Require Import RelationClasses.
Require memory_example.

From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq eqtype ssralg.
From mathcomp Require Import word_ssrZ.
From Coq Require Import Lia.
Import Utf8 ZArith.
Import ssrring.
Import type word utils.
Import memory_example.
Export memory_model.

Set SsrOldRewriteGoalsOrder.  (* change Set to Unset when porting the file, then remove the line when requiring MathComp >= 2.6 *)

Notation "f '=3' g" := (∀ x, f x =2 g x) (at level 70, g at next level).

Module Memory := MemoryI.

Notation mem := Memory.mem.

Section WITH_POINTER_DATA.
Context {pd: PointerData}.

(* -------------------------------------------------------------- *)
Definition eq_mem m m' : Prop :=
  forall ptr sz, read m ptr sz = read m' ptr sz.

Definition eq_mem_ex (m m' : mem) (top : word Uptr) (stk_max : Z) : Prop :=
  forall p,
    disjoint_zrange top stk_max p (wsize_size U8) ->
    read m Aligned p U8 = read m' Aligned p U8.

(* -------------------------------------------------------------- *)

Definition valid_between (m : mem) (top : word Uptr) (stk_max : Z) : Prop :=
  forall p, between top stk_max p U8 -> validw m Aligned p U8.

Definition zero_between (m : mem) (top : word Uptr) (stk_max : Z) : Prop :=
  forall p, between top stk_max p U8 -> read m Aligned p U8 = ok 0%R.

(* -------------------------------------------------------------- *)
#[ global ]
Instance stack_stable_equiv : Equivalence stack_stable.
Proof.
  split.
  - by [].
  - by move => x y [*]; split.
  move => x y z [???] [???]; split; etransitivity; eassumption.
Qed.

(* -------------------------------------------------------------- *)

(* -------------------------------------------------------------- *)

(* -------------------------------------------------------------- *)
Definition allocatable_stack (m : mem) (z : Z) :=
  (0 <= z <= wunsigned (top_stack m) - wunsigned (stack_limit m))%Z.

(* -------------------------------------------------------------- *)
Local Open Scope Z_scope.

Definition fill_mem (m : mem) (p : pointer) (l : list u8) : exec mem := 
  Let pm :=
   foldM (fun w pm =>
             Let m := write pm.2 Aligned (add p pm.1) w in
             ok (pm.1 + 1, m)) (0%Z, m) l in
    ok pm.2.

End WITH_POINTER_DATA.
