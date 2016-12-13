(* * Proof for 4-limb addition for curve25519 *)

(* ** Setup *)
Require Import ZArith zmod_setoid proof_utils proof_sem proof_add Psatz.
From mathcomp Require Import ssreflect ssrfun ssrbool seq eqtype.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Local Scope Z_scope.

(* ** Multiplication for 4 limbs  *)
Ltac prop_const := repeat
  match goal with
  | [ H : ?X <- ?Y |- _ ] =>
    let Heq := fresh "Weq" in
    is_var X; is_var Y; move : (assgnK H)=> Heq {H};
    push_defs; rewrite Heq; clear Heq; pop_defs
  | [ H : ?X <- 0%Z |- _ ] =>
    let Heq := fresh "Weq" in
    is_var X; move : (assgnK H)=> Heq {H};
    push_defs; rewrite Heq; clear Heq; pop_defs
  end.
 
(* ** Multiplication for 4 limbs  *)

Definition umul_l (x y : Z) := x * y mod p64.
  
Definition umul_h (x y : Z) := (x * y) / p64.

Notation umul x y := (umul_h x y, umul_l x y).

Lemma umul_l_is_u64 (x y : Z) (Hb_x : is_u64 x) (Hb_y : is_u64 y):
  is_u64 (umul_l x y).
Proof.
move: Hb_x Hb_y. rewrite !is_u64K /umul_l =>Hb_x Hb_y.
by apply Z_mod_lt; rewrite -lock.
Qed.

Lemma umul_h_is_u64 (x y : Z) (Hb_x : is_u64 x) (Hb_y : is_u64 y):
  is_u64 (umul_h x y).
Proof.
move: Hb_x Hb_y. rewrite !is_u64K /umul_h -lock =>Hb_x Hb_y. split.
+ apply Z_div_pos; nia.
+ apply Z.div_lt_upper_bound; first done.
  by apply Zmult_lt_compat; [ | nia ].
Qed.

Lemma umul_sem (x y : Z):
  is_u64 x ->
  is_u64 y ->
  [:i umul_h x y; umul_l x y] = x*y.
Proof.
unfold ds2i. unfold length. rewrite /umul_l /umul_h. simp => Hx Hy.
by rewrite Zmod_eq_full -lock; [ ring | ].
Qed.

Lemma ds2i_mul_cons (x1 x2 y : Z) (xs ys : seq Z) :
    ds2i [:: x1 & [:: x2 & xs]] * ds2i [:: y & ys]
  = pow (length [:: x2 & xs])*([:i x1]*ds2i [:: y & ys]) +
    ds2i [:: x2 & xs] * ds2i [:: y & ys].
Proof. by rewrite ds2i_cons ds2i_singleton; ring. Qed.

Lemma ds2i_nil: [::i [::]] = 0. Proof. done. Qed.

Lemma ds2i_mul_scalar (x y1 y2 : Z) (ys : seq Z) :
    is_u64 x ->
    is_u64 y1 ->
      [:i x]*(ds2i [:: y1 & [:: y2 & ys]])
    = pow (length [:: y2 & ys])* [:i umul_h x y1; umul_l x y1] +
      [:i x]*(ds2i [:: y2 & ys]).
Proof.
move=>H1 H2; rewrite (ds2i_cons y1) !ds2i_singleton.
rewrite umul_sem =>//; ring.
Qed.

Lemma ds2i_mul_scalar_scalar (x y : Z) :
    is_u64 x ->
    is_u64 y -> 
      [:i x]*[:i y]
    = [:i umul_h x y; umul_l x y].
Proof. move=> H1 H2; rewrite !ds2i_singleton umul_sem => //. Qed.

Lemma bounds_umul_test (x y : Z)
  (Hb_x : is_u64 x)
  (Hb_y : is_u64 y)
:
  x * y <= 2^128 - 2*2^64 + 1.
Proof. by move: Hb_x Hb_y; rewrite !is_u64K -lock; nia. Qed.

(* ad-hoc tactic for dealing with 5-step umul;adc;adc_v;adc;adc_v sequence *)
Ltac do_step5 Hno_over L0 L1 L2 L3 L4:=
  let Heq := fresh "Weq" in
  rewrite Hno_over in L0;
  rewrite /adc_v /oflow in L1;
  move : (assgnKl L1) => Heq; rewrite -Heq in L1;
  first [ rewrite (assgnK L0) => {L0} | rewrite (assgnKr L0) => {L0}];
  rewrite (assgnKr L1) => {L1} {Heq};

  rewrite Hno_over in L2;
  rewrite /adc_v /oflow in L3;
  move : (assgnKl L3) => Heq; rewrite -Heq in L3;
  rewrite (assgnK L2) => {L2};
  rewrite (assgnKr L3) => {L3};
  rewrite (assgnKr L4) (assgnKl L4) => {L4} {Heq}.

(* ad-hoc tactic for dealing with 3-step umul;adc;adc_v sequence *)
Ltac do_step3 Hno_over L0 L1 L2 :=
  let Heq := fresh "Weq" in
  rewrite Hno_over in L0;
  rewrite /adc_v /oflow in L1;
  move : (assgnKl L1) => Heq; rewrite -Heq in L1;
  rewrite (assgnK L0) => {L0};
  rewrite (assgnKr L1) => {L1} {Heq};
  rewrite (assgnKr L2) (assgnKl L2) => {L2}.

Lemma corr_mul_4limb
  (* inputs *)
  (xa0 xa1 xa2 xa3 : Z)
  (ya0 ya1 ya2 ya3 : Z)

  (* write-once variables *)
  (x0 x1 x2 x3 : Z)

  (* x-index=0, y-index=0 *)
  (y0'00 h'00 l'00 z0 z1'00 : Z)

  (* x-index=0, y-index=1 *)
  (y1'01 h'01 l'01 z1'01 z2''01 z2'01 : Z)
  (cf'01 : bool)

  (* x-index=0, y-index=2 *)
  (y2'02 h'02 l'02 z2'02 z3''02 z3'02 : Z)
  (cf'02 : bool)

  (* x-index=0, y-index=3 *)
  (y3'03 h'03 l'03 z3'03 z4''03 z4'03 : Z)
  (cf'03 : bool)

  (* x-index=1, y-index=0 *)
  (y0'10 h'10 l'10 z1 hprev''10 hprev'10 : Z)
  (cf'10 : bool)

  (* x-index=1, y-index=1 *)
  (y1'11 h''11 l'11  z2''11 h'11 z2'11 hprev''11 hprev'11 : Z)
  (cf''11 cf'11 : bool)

  (* x-index=1, y-index=2 *)
  (y2'12 h''12 l'12 z3''12 h'12 z3'12 hprev''12 hprev'12 : Z)
  (cf''12 cf'12 : bool)

  (* x-index=1, y-index=3 *)
  (y3'13 h''13 l'13 z4''13 h'13 z4'13 z5''13 z5'13 : Z)
  (cf'''13 cf''13 cf'13 : bool)

  (* x-index=2, y-index=0 *)
  (y0'20 h'20 l'20 z2 hprev''20 hprev'20 : Z)
  (cf'20 : bool)

  (* x-index=2, y-index=1 *)
  (y1'21 h''21 l'21 z3''21 h'21 z3'21 hprev''21 hprev'21 : Z)
  (cf''21 cf'21 : bool)

  (* x-index=2, y-index=2 *)
  (y2'22 h''22 l'22 z4''22 h'22 z4'22 hprev''22 hprev'22 : Z)
  (cf'22 cf''22 : bool)

  (* x-index=2, y-index=3 *)
  (y3'23 h''23 l'23 z5''23 h'23 z5'23 z6''23 z6'23 : Z)
  (cf'''23 cf''23 cf'23 : bool)

  (* x-index=3, y-index=0 *)
  (y0'30 h'30 l'30 z3 hprev''30 hprev'30 : Z)
  (cf'30 : bool)

  (* x-index=3, y-index=1 *)
  (y1'31 h''31 l'31 z4'31 h'31 z4 hprev''31 hprev'31 : Z)
  (cf''31 cf'31 : bool)

  (* x-index=3, y-index=2 *)
  (y2'32 h''32 l'32 z5'32 z5 h'32 hprev''32 hprev'32 : Z)
  (cf''32 cf'32 : bool)

  (* x-index=3, y-index=3 *)
  (y3'33 h''33 l'33 z6'33 h'33 z6 z7'33 z7 : Z)
  (cf'''33 cf''33 cf'33 : bool)

  (* bounds *)
  (Hb_xa0: is_u64 xa0)
  (Hb_xa1: is_u64 xa1)
  (Hb_xa2: is_u64 xa2)
  (Hb_xa3: is_u64 xa3)

  (Hb_ya0: is_u64 ya0)
  (Hb_ya1: is_u64 ya1)
  (Hb_ya2: is_u64 ya2)
  (Hb_ya3: is_u64 ya3)

  (Hb_x0: is_u64 x0)
  (Hb_x1: is_u64 x1)
  (Hb_x2: is_u64 x2 )
  (Hb_x3: is_u64 x3)

  (Hb_y0'00: is_u64 y0'00)
  (Hb_h'00: is_u64 h'00)
  (Hb_l'00: is_u64 l'00)
  (Hb_z0: is_u64 z0)
  (Hb_z1'00: is_u64 z1'00)

  (Hb_y1'01: is_u64 y1'01)
  (Hb_h'01: is_u64 h'01)
  (Hb_l'01: is_u64 l'01)
  (Hb_z1'01: is_u64 z1'01)
  (Hb_z2''01: is_u64 z2''01)
  (Hb_z2'01: is_u64 z2'01)

  (Hb_y2'02: is_u64 y2'02)
  (Hb_h'02: is_u64 h'02)
  (Hb_l'02: is_u64 l'02)
  (Hb_z2'02: is_u64 z2'02)
  (Hb_z3''02: is_u64 z3''02)
  (Hb_z3'02: is_u64 z3'02)

  (Hb_y3'03: is_u64 y3'03)
  (Hb_h'03: is_u64 h'03)
  (Hb_l'03: is_u64 l'03)
  (Hb_z3'03: is_u64 z3'03)
  (Hb_z4''03: is_u64 z4''03)
  (Hb_z4'03: is_u64 z4'03)

  (Hb_y0'10: is_u64 y0'10)
  (Hb_h'10: is_u64 h'10)
  (Hb_l'10: is_u64 l'10)
  (Hb_z1: is_u64 z1)
  (Hb_hprev''10: is_u64 hprev''10)
  (Hb_hprev'10: is_u64 hprev'10)

  (Hb_y1'11: is_u64 y1'11)
  (Hb_h''11: is_u64 h''11)
  (Hb_l'11: is_u64 l'11)
  (Hb_z2''11: is_u64 z2''11)
  (Hb_h'11: is_u64 h'11)
  (Hb_z2'11: is_u64 z2'11)
  (Hb_hprev''11: is_u64 hprev''11)
  (Hb_hprev'11: is_u64 hprev'11)

  (Hb_y2'12: is_u64 y2'12)
  (Hb_h''12: is_u64 h''12)
  (Hb_l'12: is_u64 l'12)
  (Hb_z3''12: is_u64 z3''12)
  (Hb_h'12: is_u64 h'12)
  (Hb_z3'12: is_u64 z3'12)
  (Hb_hprev''12: is_u64 hprev''12)
  (Hb_hprev'12: is_u64 hprev'12)

  (Hb_y3'13: is_u64 y3'13)
  (Hb_h''13: is_u64 h''13)
  (Hb_l'13: is_u64 l'13)
  (Hb_z4''13: is_u64 z4''13)
  (Hb_h'13: is_u64 h'13)
  (Hb_z4'13: is_u64 z4'13)
  (Hb_z5''13: is_u64 z5''13)
  (Hb_z5'13: is_u64 z5'13)

  (Hb_y0'20: is_u64 y0'20)
  (Hb_h'20: is_u64 h'20)
  (Hb_l'20: is_u64 l'20)
  (Hb_z2: is_u64 z2)
  (Hb_hprev''20: is_u64 hprev''20)
  (Hb_hprev'20: is_u64 hprev'20)

  (Hb_y1'21: is_u64 y1'21)
  (Hb_h''21: is_u64 h''21)
  (Hb_l'21: is_u64 l'21)
  (Hb_z3''21: is_u64 z3''21)
  (Hb_h'21: is_u64 h'21)
  (Hb_z3'21: is_u64 z3'21)
  (Hb_hprev''21: is_u64 hprev''21)
  (Hb_hprev'21: is_u64 hprev'21)

  (Hb_y2'22: is_u64 y2'22)
  (Hb_h''22: is_u64 h''22)
  (Hb_l'22: is_u64 l'22)
  (Hb_z4''22: is_u64 z4''22)
  (Hb_h'22: is_u64 h'22)
  (Hb_z4'22: is_u64 z4'22)
  (Hb_hprev''22: is_u64 hprev''22)
  (Hb_hprev'22: is_u64 hprev'22)

  (Hb_y3'23: is_u64 y3'23)
  (Hb_h''23: is_u64 h''23)
  (Hb_l'23: is_u64 l'23)
  (Hb_z5''23: is_u64 z5''23)
  (Hb_h'23: is_u64 h'23)
  (Hb_z5'23: is_u64 z5'23)
  (Hb_z6''23: is_u64 z6''23)
  (Hb_z6'23: is_u64 z6'23)

  (Hb_y0'30: is_u64 y0'30)
  (Hb_h'30: is_u64 h'30)
  (Hb_l'30: is_u64 l'30)
  (Hb_z3: is_u64 z3)
  (Hb_hprev''30: is_u64 hprev''30)
  (Hb_hprev'30: is_u64 hprev'30)

  (Hb_y1'31: is_u64 y1'31)
  (Hb_h''31: is_u64 h''31)
  (Hb_l'31: is_u64 l'31)
  (Hb_z4'31: is_u64 z4'31)
  (Hb_h'31: is_u64 h'31)
  (Hb_z4: is_u64 z4)
  (Hb_hprev''31: is_u64 hprev''31)
  (Hb_hprev'31: is_u64 hprev'31)

  (Hb_y2'32: is_u64 y2'32)
  (Hb_h''32: is_u64 h''32)
  (Hb_l'32: is_u64 l'32)
  (Hb_z5'32: is_u64 z5'32)
  (Hb_z5: is_u64 z5)
  (Hb_h'32: is_u64 h'32)
  (Hb_hprev''32: is_u64 hprev''32)
  (Hb_hprev'32: is_u64 hprev'32)

  (Hb_y3'33: is_u64 y3'33)
  (Hb_h''33: is_u64 h''33)
  (Hb_l'33: is_u64 l'33)
  (Hb_z6'33: is_u64 z6'33)
  (Hb_h'33: is_u64 h'33)
  (Hb_z6: is_u64 z6)
  (Hb_z7'33: is_u64 z7'33)
  (Hb_z7: is_u64 z7)
:

  x0 <- xa0 ->

    y0'00 <- ya0 ->
    (h'00, l'00) <- umul y0'00 x0 ->
    z0 <- l'00 ->
    z1'00 <- h'00 ->

    y1'01 <- ya1 ->
    (h'01, l'01) <- umul y1'01 x0 ->
    (cf'01,z1'01) <- adc 1 z1'00 l'01 false -> 
    z2''01 <- 0 ->
    z2'01 <- adc_v 1 z2''01 h'01 cf'01 ->

    y2'02 <- ya2 ->
    (h'02,l'02) <- umul y2'02 x0 ->
    (cf'02,z2'02) <- adc 1 z2'01 l'02 false ->
    z3''02 <- 0 ->
    z3'02  <- adc_v 1 z3''02 h'02 cf'02 ->

    y3'03 <- ya3 ->
    (h'03, l'03) <- umul y3'03 x0 ->
    (cf'03,z3'03) <- adc 1 z3'02 l'03 false ->
    z4''03 <- 0 -> 
    z4'03 <- adc_v 1 z4''03 h'03 cf'03 ->

  x1 <- xa1 ->

    y0'10              <- ya0 ->
    (h'10, l'10)    <- umul y0'10 x1 ->
    (cf'10,z1)   <- adc 1 z1'01 l'10 false ->
    hprev''10       <- 0 ->
    hprev'10        <- adc_v 1 hprev''10 h'10 cf'10 ->

    y1'11              <- ya1 ->
    (h''11,l'11)    <- umul y1'11 x1 ->
    (cf''11,z2''11) <- adc 1 z2'02 l'11 false ->
    h'11            <- adc_v 1 h''11 0 cf''11 ->
    (cf'11,z2'11)   <- adc 1 z2''11 hprev'10 false ->
    hprev''11       <- 0 ->
    hprev'11        <- adc_v 1 hprev''11 h'11 cf'11 ->

    y2'12              <- ya2 ->
    (h''12,l'12)    <- umul y2'12 x1 ->
    (cf''12,z3''12) <- adc 1 z3'03 l'12 false ->
    h'12            <- adc_v 1 h''12 0 cf''12 ->
    (cf'12,z3'12)   <- adc 1 z3''12 hprev'11 false ->
    hprev''12       <- 0 ->
    hprev'12        <- adc_v 1 hprev''12 h'12 cf'12 ->

    y3'13            <- ya3 ->
    (h''13,l'13)     <- umul y3'13 x1 ->
    (cf'''13,z4''13) <- adc 1 z4'03 l'13 false ->
    h'13             <- adc_v 1 h''13 0 cf'''13 ->
    (cf''13,z4'13)   <- adc 1 z4''13 hprev'12 false ->
    z5''13           <- 0 ->
    (cf'13,z5'13)    <- adc 1 z5''13 h'13 cf''13 ->

  x2 <- xa2 ->

    y0'20 <- ya0 ->
    (h'20,l'20) <- umul y0'20 x2 ->
    (cf'20,z2) <- adc 1 z2'11 l'20 false ->
    hprev''20 <- 0 ->
    hprev'20 <- adc_v 1 hprev''20 h'20 cf'20 ->

    y1'21 <- ya1 ->
    (h''21,l'21) <- umul y1'21 x2 ->
    (cf''21, z3''21) <- adc 1 z3'12 l'21 false ->
    h'21 <- adc_v 1 h''21 0 cf''21 ->
    (cf'21,z3'21) <- adc 1 z3''21 hprev'20 false ->
    hprev''21 <- 0 ->
    hprev'21 <- adc_v 1 hprev''21 h'21 cf'21 ->

    y2'22 <- ya2 ->
    (h''22,l'22) <- umul y2'22 x2 ->
    (cf''22,z4''22) <- adc 1 z4'13 l'22 false ->
    h'22 <- adc_v 1 h''22 0 cf''22 ->
    (cf'22,z4'22) <- adc 1 z4''22 hprev'21 false ->
    hprev''22 <- 0 ->
    hprev'22 <- adc_v 1 hprev''22 h'22 cf'22 ->
    
    y3'23 <- ya3 ->
    (h''23, l'23) <- umul y3'23 x2 ->
    (cf'''23,z5''23) <- adc 1 z5'13 l'23 false ->
    h'23 <- adc_v 1 h''23 0 cf'''23 ->
    (cf''23, z5'23) <- adc 1 z5''23 hprev'22 false ->
    z6''23 <- 0 ->
    (cf'23,z6'23) <- adc 1 z6''23 h'23 cf''23 ->

  x3 <- xa3 ->

    y0'30 <- ya0 ->
    (h'30,l'30) <- umul y0'30 x3 ->
    (cf'30,z3) <- adc 1 z3'21 l'30 false ->
    hprev''30 <- 0 ->
    hprev'30 <- adc_v 1 hprev''30 h'30 cf'30 ->

    y1'31 <- ya1 ->
    (h''31,l'31) <- umul y1'31 x3 ->
    (cf''31,z4'31) <- adc 1 z4'22 l'31 false ->
    h'31 <- adc_v 1 h''31 0 cf''31 ->
    (cf'31,z4) <- adc 1 z4'31 hprev'30 false ->
    hprev''31 <- 0 ->
    hprev'31 <- adc_v 1 hprev''31 h'31 cf'31 ->

    y2'32 <- ya2 ->
    (h''32,l'32) <- umul y2'32 x3 ->
    (cf''32,z5'32) <- adc 1 z5'23 l'32 false ->
    h'32 <- adc_v 1 h''32 0 cf''32 ->
    (cf'32,z5) <- adc 1 z5'32 hprev'31 false ->
    hprev''32 <- 0 ->
    hprev'32 <- adc_v 1 hprev''32 h'32 cf'32 ->

    y3'33 <- ya3 ->
    (h''33,l'33) <- umul y3'33 x3 ->
    (cf'''33,z6'33) <- adc 1 z6'23 l'33 false ->
    h'33 <- adc_v 1 h''33 0 cf'''33 ->
    (cf''33,z6) <- adc 1 z6'33 hprev'32 false ->
    z7'33 <- 0 ->
    (cf'33,z7) <- adc 1 z7'33 h'33 cf''33 ->
      ds2i [:: z7; z6; z5 ;z4 ;z3; z2; z1; z0]
    = ds2i [:: ya3; ya2; ya1; ya0] * ds2i [:: xa3; xa2; xa1; xa0].
Proof.
pop_defs. prop_const. sort_defs.
rewrite !ds2i_mul_cons.
rewrite !ds2i_mul_scalar.
rewrite !ds2i_mul_scalar_scalar; try done. unfold length.
unfold ds2i. unfold length. ring_simplify.
rewrite !Z.pow_0_r !Z.pow_1_r !Z.mul_1_r !Z.mul_1_l.
have Hno_over: forall x y c, adc_v 1 x y c = x + y + c:%Z. admit.

do_step5 Hno_over L63 L62 L61 L60 L59.
do_step5 Hno_over L58 L57 L56 L55 L54.
do_step5 Hno_over L53 L52 L51 L50 L49.
do_step3 Hno_over L48 L47 L46.
do_step5 Hno_over L45 L44 L43 L42 L41.
do_step5 Hno_over L40 L39 L38 L37 L36.
do_step5 Hno_over L35 L34 L33 L32 L31.
do_step3 Hno_over L30 L29 L28.
do_step5 Hno_over L27 L26 L25 L24 L23.
do_step5 Hno_over L22 L21 L20 L19 L18.
do_step5 Hno_over L17 L16 L15 L14 L13.
do_step3 Hno_over L12 L11 L10.
do_step3 Hno_over L9 L8 L7.
do_step3 Hno_over L6 L5 L4.
do_step3 Hno_over L3 L2 L1.

rewrite (assgnKr L0) (assgnKl L0) => {L0}.
apply Zeq_eq0; rewrite !b2i_false -lock; unfold Z.of_nat; ring.
Admitted.