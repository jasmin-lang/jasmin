(* * Experiments for proof *)

(* ** Setup *)
Require Import ZArith.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Local Scope Z_scope.

(* ** Axiomatization of required operations *)

Section Reduce.

Definition w : Z := 64.

Variable R : Z.

Variable rem_p : Z.

Variable Z_w : Type.

Variable Z_p : Type.

Variable toZp : Z -> Z_p.

Variable z64 : Z_w.

Variable of64 : Z_w -> Z.

Variable in64 : Z -> Z_w.

Variable bound : Z -> Z -> Z -> bool.

Variable ofbool : bool -> Z_w.

Variable umul_h : Z_w -> Z_w -> Z_w.

Variable umul_l : Z_w -> Z_w -> Z_w.

Variable addc_cf : Z_w -> Z_w -> bool -> bool.

(* hint that there is no overflow *)
Variable addc_ncf : Z_w -> Z_w -> bool -> Z_w.

Variable addc_r : Z_w -> Z_w -> bool -> Z_w.

Variable cmul : bool -> Z_w -> Z_w.

(* ** Definitions *)

Definition rem_p64 := nosimpl in64 rem_p.

Definition b2i (b : bool) : Z := if b then 1 else 0.

Definition umul (x y : Z_w) := (umul_l x y, umul_h x y).

Definition imul (x y : Z_w) := nosimpl umul_l x y.

Definition add (x y : Z_w) : bool * Z_w :=
  (addc_cf x y false, addc_r x y false).

Definition addc (x y : Z_w) (cf : bool) : bool * Z_w :=
  (addc_cf x y cf, addc_r x y cf).

Definition add_ncf (x y : Z_w) : Z_w := addc_ncf x y false.

Definition bound_u64 (x : Z) := bound 0 x (2^64 - 1).

(* ** Rewriting rules  *)

Lemma of64_addc_r (x y : Z_w) (cf : bool):
  of64 (addc_r x y cf) = of64 x + of64 y + b2i cf - b2i (addc_cf x y cf)*R.
Admitted.

Lemma of64_addc_ncf (x y : Z_w) (cf : bool):
  bound_u64 (of64 x + of64 y + b2i cf) ->
  of64 (addc_ncf x y cf) = of64 x + of64 y + b2i cf.
Admitted.

Lemma of640: of64 z64 = 0. Admitted.

Lemma of64_cmul (cf : bool):
  of64 (cmul cf rem_p64) = b2i cf * rem_p. Admitted.

(* ** Addition for 2 limbs  *)

Definition add_2limb(x0 x1 y0 y1 : Z_w) : (Z_w * Z_w) := 
  let (cf, z0) := add  x0 y0      in
  let (cf, z1) := addc x1 y1 cf   in
  let u        := cmul cf rem_p64 in
  let (cf, z0) := add  z0 u       in
  let (cf, z1) := addc z1 z64 cf  in
  let u        := cmul cf rem_p64 in
  let z0       := add_ncf z0 u    in
  (z0,z1).

Lemma corr_add_2limb (x0 x1 y0 y1 : Z_w):
  rem_p = R*R ->
  let r := add_2limb x0 x1 y0 y1 in
  match r with
  | (z0,z1) =>
       (of64 z0) + (of64 z1)*R
     - ((of64 x0) + (of64 x1)*R + (of64 y0) + (of64 y1)*R)
     = 0
  end.
Proof.
  move=> rem_p_R.
  rewrite /= !(of64_addc_r, of64_addc_ncf, of640, of64_cmul, rem_p_R) /=.
  (* ring takes care of the equality *)
  ring.
  (* but we still have to prove that whenever we ignore the carry bit, there
     is no overflow *)
  admit.
Admitted.

(* ** Addition for 4 limbs *)

Definition add_4limb(x0 x1 x2 x3 y0 y1 y2 y3 : Z_w) : (Z_w * Z_w * Z_w * Z_w) := 
  let (cf, z0) := add  x0 y0      in
  let (cf, z1) := addc x1 y1 cf   in
  let (cf, z2) := addc x2 y2 cf   in
  let (cf, z3) := addc x3 y3 cf   in
  let u        := cmul cf rem_p64 in
  let (cf, z0) := add  z0 u       in
  let (cf, z1) := addc z1 z64 cf  in
  let (cf, z2) := addc z2 z64 cf  in
  let (cf, z3) := addc z3 z64 cf  in
  let add0     := cmul cf rem_p64 in
  let z0       := add_ncf z0 add0 in
  (z0,z1,z2,z3).

Lemma corr_add_4_limbs (x0 x1 x2 x3 y0 y1 y2 y3 : Z_w):
  rem_p = R*R*R*R ->
  let r := add_4limb x0 x1 x2 x3 y0 y1 y2 y3 in
  let: (z0,z1,z2,z3) := r in
        (of64 z0) + (of64 z1)*R + (of64 z2)*R*R + (of64 z3)*R*R*R
     - ((of64 x0) + (of64 x1)*R + (of64 x2)*R*R + (of64 x3)*R*R*R +
        (of64 y0) + (of64 y1)*R + (of64 y2)*R*R + (of64 y3)*R*R*R)
     = 0.
Proof.
  move=> rem_p_R.
  rewrite /=.
  rewrite !(of64_addc_r, of64_addc_ncf, of640, of64_cmul, rem_p_R) /=.
  ring.
  (* as in the previous case, we still have to prove absence of overflows *)
  admit.
Admitted.
