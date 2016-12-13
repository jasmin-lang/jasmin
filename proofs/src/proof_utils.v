(* * Experiments for proof *)

(* ** Setup *)
Require Import ZArith zmod_setoid.
From mathcomp Require Import ssreflect ssrfun ssrbool seq eqtype.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Local Scope Z_scope.

(* ** Assignments and helper lemmas/tactics *)

Definition Assgn {T} (x y : T) := x = y.

Notation "x '<-' y" := (Assgn x y) (at level 70, no associativity).

Lemma assgnK {T} {x y : T} : x <- y -> x = y.
Proof. done. Qed.

Lemma assgnKl {T1 T2} {x1 y1 : T1} {x2 y2 : T2} : (x1,x2) <- (y1,y2) -> x1 = y1.
Proof. by rewrite /Assgn; case. Qed.

Lemma assgnKr {T1 T2} {x1 y1 : T1} {x2 y2 : T2} : (x1,x2) <- (y1,y2) -> x2 = y2.
Proof. by rewrite /Assgn; case. Qed.

Lemma assgnS {T1 T2} {x1 y1 : T1} {x2 y2 : T2} : (x1,x2) <- (y1,y2) -> x1 <- y1 /\ x2 <- y2.
Proof. by rewrite /Assgn; case. Qed.

Definition Ntag (n : nat) (P : Prop) := P.

Lemma add_tag_imp (n : nat) (P : Prop):
  P -> Ntag n P.
Proof. by rewrite /Ntag. Qed.

Lemma remove_tag_imp {n : nat} (P : Prop):
  Ntag n P -> P.
Proof. by rewrite /Ntag. Qed.

Ltac add_tag_rec N :=
  match reverse goal with
  | [ H : _ <- _  |- _ ] =>
    let NN := constr:(S N) in
    apply (add_tag_imp N) in H; add_tag_rec NN
  | _ => idtac
  end.

Ltac add_tag :=
  let Z := constr:(0%nat) in
  add_tag_rec Z.

Ltac remove_tag :=
  match goal with
  | [ H : Ntag ?n _ |- _ ] =>
    apply (@remove_tag_imp n) in H; remove_tag
  | _ => idtac
  end.

Ltac contains_var T V :=
  match T with
  | context[V] => idtac
  | _          => fail 1
  end.

Ltac is_lt N1 N2 :=
  let C := eval compute in (N1 <? N2)%nat in
  match C with
  | false => fail
  | true  => idtac
  end.

Ltac swap_hyps N1 N2 H1 H2 T V :=
  (* H1 uses T containing V, H2 defines V => swap *)
  is_lt N1 N2;
  contains_var T V;
  move: H2 H1 => H1 H2.

Ltac swap_def_before_use :=
  match goal with
  | [ H1 : Ntag ?N1 (_ <- ?T), H2 : Ntag ?N2 (?D <- _) |- _ ] =>
    match D with
    | ?V     => is_var V; swap_hyps N1 N2 H1 H2 T V
    | (?V,_) => is_var V; swap_hyps N1 N2 H1 H2 T V
    | (_,?V) => is_var V; swap_hyps N1 N2 H1 H2 T V
    end
  end.

Ltac push_defs :=
  repeat match goal with
         | [ H : _ <- _ |- _ ] => move: H
         end.

Ltac pop_defs :=
  let L_ignore := fresh "L" in 
  repeat match goal with
        | [ _ : _ |- _ <- _ -> _] =>
          let L1 := fresh "L" in move => L1
         end.

Ltac sort_defs :=
  repeat try (add_tag; swap_def_before_use; remove_tag);
  push_defs;
  pop_defs.

Ltac is_bool_const C :=
  match C with
  | true  => idtac
  | false => idtac
  |_      => fail
  end.

Ltac is_cmp_b O :=
  match O with
  | Z.leb => idtac
  | Z.ltb => idtac
  | _     => fail
  end.

Ltac trans_cmp_b_sym :=
  repeat match goal with
         | [ H : ?C = (?O _ _) |- _ ] =>
           is_bool_const C; is_cmp_b O; apply Logic.eq_sym in H
         | [ _ : _ |- ?C = (?O _ _) ] =>
           is_bool_const C; is_cmp_b O; apply Logic.eq_sym
         end.

Ltac trans_cmp_b_simp :=
  first [ rewrite Z.leb_gt | rewrite Z.leb_le | rewrite Z.ltb_ge | rewrite Z.ltb_lt ].

Ltac trans_cmp_b :=
  trans_cmp_b_sym;
  repeat match goal with
         | [ H : ( _ <=? _) = _ |- _ ] => move: H; trans_cmp_b_simp => H
         | [ _ : _ |- ( _ <=? _) = _ ] => trans_cmp_b_simp
         end.

(* ** General definitions  and lemmas *)

Definition b2i (b : bool) := if b then 1 else 0.

Notation "b ':%Z'"  := (b2i b) (at level 2, left associativity, format "b ':%Z'").

Lemma b2i_false: false:%Z = 0. Proof. done. Qed.
Lemma b2i_true: true:%Z = 1. Proof. done. Qed.

Lemma Zeq_eq0 (x y : Z): 0 = x - y <-> x = y.
Proof.
split.
+ by rewrite -Zeq_plus_swap; move => <-.
+ by move=> ->; ring.
Qed.