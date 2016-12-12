(* * Experiments for proof *)

(* ** Setup *)
Require Import ZArith zmod_setoid proof_utils proof_sem proof_add Psatz.
From mathcomp Require Import ssreflect ssrfun ssrbool seq eqtype.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Local Scope Z_scope.
      
(* ** Addition for 4 limbs  *)

Lemma corr_add_4limb
  (x0 x1 x2 x3 : Z)
  (y0 y1 y2 y3 : Z)
  (t0 t1 t2 t3 : Z)
  (add1 add2 : Z)
  (v0 : Z)
  (z0 z1 z2 z3 : Z)
  (cf0 cf1 cf2 cf3 : bool)
  (ccf0 ccf1 ccf2 ccf3 : bool)
  (cf_f   : bool)

  (B_x0   : is_u64 x0)
  (B_x1   : is_u64 x1)
  (B_x2   : is_u64 x2)
  (B_x3   : is_u64 x3)
  (B_y0   : is_u64 y0)
  (B_y1   : is_u64 y1)
  (B_y2   : is_u64 y2)
  (B_y3   : is_u64 y3)
  (B_t0   : is_u64 t0)
  (B_t1   : is_u64 t1)
  (B_t2   : is_u64 t2)
  (B_t3   : is_u64 t3)
  (B_add1 : is_u64 add1)
  (B_add2 : is_u64 add2)
  (B_v0   : is_u64 v0)
  (B_z0   : is_u64 z0)
  (B_z1   : is_u64 z1)
  (B_z2   : is_u64 z2)
  (B_z3   : is_u64 z3)
  :
  (cf0,t0)   <- adc 1 x0 y0 false ->
  (cf1,t1)   <- adc 1 x1 y1 cf0   ->
  (cf2,t2)   <- adc 1 x2 y2 cf1   -> 
  (cf3,t3)   <- adc 1 x3 y3 cf2   ->
  (add1      <- if cf3 then 38 else 0)  ->
  (ccf0,v0)  <- adc 1 t0 add1 false     ->
  (ccf1,z1)  <- adc 1 t1 0    ccf0      ->
  (ccf2,z2)  <- adc 1 t2 0    ccf1      -> 
  (ccf3,z3)  <- adc 1 t3 0    ccf2      ->
  (add2      <- if ccf3 then 38 else 0)  ->
  (cf_f,z0)  <- adc 1 v0 add2 false
  ->
    ds2i [:: z3; z2; z1; z0]
  = ds2i [:: x3; x2; x1; x0] +
    ds2i [:: y3; y2; y1; y0] +
    (cf3:%Z + ccf3:%Z)*(38 - p256).
Proof.
(* add bounds for constants (FIXME: should be done automatically *)
have B_0  : is_u64 0  by rewrite is_u64K -lock.
have B_38 : is_u64 38 by rewrite is_u64K -lock.
(* combine carry chains *)
pop_defs. combine. sort_defs. push_defs.
(* perform case distinction on first CMOV *)
case cf3; last first.
+ pop_defs. simp. sort_defs.
  by rewrite (assgnKr L2) (assgnKr L0) /adc_v /oflow -(assgnKl L0); simp.
(* perform case distinction on second CMOV *)
+ simp. case ccf3; last first.
  + pop_defs. simp.
    rewrite (assgnKr L2) /adc_v /oflow -(assgnKl L2). simp.
    rewrite (assgnKr L0) /adc_v /oflow -(assgnKl L0). simp.
    by rewrite !(ds2i_cons0, ds2i_singleton); ring.
  + pop_defs. simp.
    rewrite /adc_v /oflow in L4.
    move : (assgnKl L4) => Heq. rewrite -Heq in L4. simp.
    (* ignored carry must be ``false'' *)
    have Heq2: cf_f <- false; simp; last first.
    + rewrite (assgnKr L0) /adc_v in L2.
      rewrite (assgnKr L4).
      rewrite (_ : [:i z3; z2; z1; v0 + 38] = [:i z3; z2; z1; v0] + 38); last first.
      + by rewrite !ds2i_cons Z.pow_0_r; unfold length; ring.
      rewrite (assgnKr L2).
      apply Zeq_eq0. simp. ring_simplify.
      move: (assgnKl L2).
      rewrite /oflow -(assgnKl L0). simp.
      by move=> <-; unfold ds2i; unfold length; simp; ring.
    (* there is no overflow *)
    + split_chainN => ccf7 [L20 L21].
      split_chainN => ccf8 [L22 L23].
      split_chainN => ccf9 [L24 L25].

      rewrite !ds2i_singleton in L24.
      push_defs.
      case ccf7; last (pop_defs; simp; done).
      case ccf8; last (pop_defs; simp; done).
      case ccf9; last (pop_defs; simp; done).
      pop_defs. rewrite (assgnKr L10) in Heq.
      rewrite /adc_v /oflow in Heq. simp. rewrite -(assgnKl L10) in Heq.
      simp. rewrite /adc_cf in Heq. move: Heq. case cf_f; last done.
      move=> G. trans_cmp_b. simp.
      have T: t0 + 38 - p64 + 38 < p64; move: B_t0; rewrite is_u64K -lock; nia.
Qed.