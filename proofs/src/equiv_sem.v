(* -------------------------------------------------------------------- *)
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat ssrint ssralg tuple.
From mathcomp Require Import choice fintype eqtype div seq zmodp.

Require Import finmap strings word dmasm_utils.
Require Import dmasm_type dmasm_var dmasm_expr.
Require Import dmasm_sem dmasm_Ssem dmasm_sem_props dmasm_Ssem_props.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.

Local Open Scope ring_scope.

(* -------------------------------------------------------------------- *)
Fixpoint st_dfl (t : stype) : st2ty t :=
  match t return st2ty t with
  | sword     => 0%R
  | sbool     => false
  | t1 ** t2  => (st_dfl t1, st_dfl t2)
  | sarr n st => [tuple of nseq n.+1 (st_dfl st)]
  end.

Fixpoint sst_dfl (t : stype) : sst2ty t :=
  match t return sst2ty t with
  | sword     => 0%R
  | sbool     => false
  | t1 ** t2  => (sst_dfl t1, sst_dfl t2)
  | sarr n st => (fun _ : nat => sst_dfl st)
  end.

(* -------------------------------------------------------------------- *)
Fixpoint st2sst_ty {t : stype} :=
  match t return st2ty t -> sst2ty t with
  | sword     => fun v => v
  | sbool     => fun v => v
  | t1 ** t2  => fun v => (st2sst_ty v.1, st2sst_ty v.2)
  | sarr n st => fun v => (fun i : nat => st2sst_ty (nth (st_dfl st) v i))
  end.

(* -------------------------------------------------------------------- *)
Definition vmap_to_svmap (v : vmap) : svmap :=
  {| Fv.map := fun x : var => st2sst_ty (v.(Fv.map) x); |}.

(* -------------------------------------------------------------------- *)
Coercion estate_to_sestate (s : estate) :=
  {| semem := s.(emem); sevm := vmap_to_svmap s.(evm); |}.

(* -------------------------------------------------------------------- *)
Goal forall s1 c s2, sem s1 c s2 -> ssem s1 c s2.
Proof.
pose Pi s1 i s2 :=
  sem_i s1 i s2 -> ssem_i s1 i s2.
pose Pf rv d lo hi s1 c s2 :=
  sem_for rv d lo hi s1 c s2 -> ssem_for rv d lo hi s1 c s2.
pose Pc sta str m1 (fd : fundef sta str) ag m2 res :=
  sem_call m1 fd ag m2 res -> ssem_fun fd m1 (st2sst_ty ag) m2 (st2sst_ty res).
apply: (@sem_Ind _ Pi Pf Pc).
Admitted.
