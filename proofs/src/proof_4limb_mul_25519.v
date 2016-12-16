(* * Proof for 4-limb addition for curve25519 *)

(* ** Setup *)
Require Import ZArith zmod_setoid proof_utils proof_sem proof_add Psatz.
From mathcomp Require Import ssreflect ssrfun ssrbool seq eqtype.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Local Scope Z_scope.

(* ** Constant and variable renaming   *)

Ltac is_Z_const E :=
  let NE := eval cbv in E in
  match NE with
  | Z0     => idtac
  | Zpos _ => idtac
  | Zneg _ => idtac
  | _      => fail 1
  end.

Ltac prop_const := repeat
  match goal with
  | [ H : ?X <- ?Y |- _ ] =>
    is_var X; is_var Y;
    replace X with Y in *;
    clear H
  | [ H : ?X <- ?E |- _ ] =>    
    is_Z_const E;
    idtac "is_Z_const"; idtac E;
    let NE := eval cbv in E in
    replace X with NE in *;
    try (clear X);
    clear H
  | [ H : is_true (is_u64 ?E) |- _] =>
    is_Z_const E; clear H
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

Lemma Zdiv_mod (a b : Z) : b <> 0 -> a / b * b = a - (a mod b).
Proof. by move=> H; rewrite Zmod_eq_full => //; ring. Qed.

Lemma bounds_umul_h (x y : Z)
  (Hb_x : is_u64 x)
  (Hb_y : is_u64 y) :
  umul_h x y <= 2^64 - 2.
Proof.
move: Hb_x Hb_y. rewrite !is_u64K /umul_h -lock => Hb_x Hb_y.
apply (Zmult_le_reg_r _ _ (2^64)); first done.
rewrite Zdiv_mod; last done.
have Hor: ((x =? 2^64 - 1) && (y =? 2^64 - 1)) \/ ~((x =? 2^64 - 1) && (y =? 2^64 - 1))
  by case ((x =? 2^64 - 1) && (y =? 2^64 - 1)); auto.
elim Hor.
+ by move=> /andP []; rewrite /is_true !Z.eqb_eq => -> ->.
+ move=> /negP /nandP => {Hor} Hor. elim Hor.
  (* x <= 2^64 - 2 *)
  + move=> /negP. rewrite /is_true Bool.not_true_iff_false Z.eqb_neq => H.
    have Hle2: x * y - (x * y) mod 2^64  <= (2^64 - 2)*(2^64 - 1) - 0
      by apply Z.sub_le_mono; [ apply Zmult_le_compat; nia | move: (Z_mod_lt (x*y) (2^64)); nia ].
    by apply (Z.le_trans _ _ _ Hle2); nia.
  (* y <= 2^64 - 2 *)
  + move=> /negP. rewrite /is_true Bool.not_true_iff_false Z.eqb_neq => H.
    have Hle2: x * y - (x * y) mod 2^64  <= (2^64 - 1)*(2^64 - 2) - 0
      by apply Z.sub_le_mono; [ apply Zmult_le_compat; nia | move: (Z_mod_lt (x*y) (2^64)); nia ].
    by apply (Z.le_trans _ _ _ Hle2); nia.
Qed.

Lemma bounds_umul_cases (x y : Z)
  (Hb_x : is_u64 x)
  (Hb_y : is_u64 y) :
  (umul_h x y = 2^64 - 2 /\ umul_l x y = 1)
  \/ umul_h x y <= 2^64 - 3.
Proof.
move: Hb_x Hb_y; rewrite !is_u64K /umul_h /umul_l -lock => Hb_x Hb_y.
have Hor: ((x =? 2^64 - 1) && (y =? 2^64 - 1)) \/ ~((x =? 2^64 - 1) && (y =? 2^64 - 1))
  by case ((x =? 2^64 - 1) && (y =? 2^64 - 1)); auto.
elim Hor.
+ by move=> /andP []; rewrite /is_true !Z.eqb_eq => -> ->; left.
+ move=> /negP /nandP => {Hor} Hor. right.
  apply (Zmult_le_reg_r _ _ (2^64)); first done.
  rewrite Zdiv_mod; last done.
  have G: forall x y,
            0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 ->
            ~~ (x =? 2 ^ 64 - 1) ->
            x * y - (x * y) mod 2 ^ 64 <= (2 ^ 64 - 3) * 2 ^ 64; last first.
  + by elim Hor => Hp ; [ apply G | rewrite Z.mul_comm; apply G ].
  clear x y Hb_x Hb_y Hor. move=> x y Hbx Hby.
  move=> /negP. rewrite /is_true Bool.not_true_iff_false Z.eqb_neq => H.
  have Hor2: ((x =? 2^64 - 2) && (y =? 2^64 - 1)) \/ ~((x =? 2^64 - 2) && (y =? 2^64 - 1))
    by case ((x =? 2^64 - 2) && (y =? 2^64 - 1)); auto.
  elim Hor2.
  (* x =? 2 ^ 64 - 2) && (y =? 2 ^ 64 - 1) *)
  + by move=> /andP []; rewrite /is_true !Z.eqb_eq => -> ->.
  + move=> /negP /nandP => Hor. elim Hor.
    (* x <= 2^64 - 3 *)
    + move=> /negP. rewrite /is_true Bool.not_true_iff_false Z.eqb_neq => H2.
      have Hle2: x * y - (x * y) mod 2^64  <= (2^64 - 3)*(2^64 - 1) - 0
        by apply Z.sub_le_mono;[apply Zmult_le_compat; nia | move: (Z_mod_lt (x*y) (2^64));nia ].
      by apply (Z.le_trans _ _ _ Hle2); nia.
    + move=> /negP. rewrite /is_true Bool.not_true_iff_false Z.eqb_neq => H2.
      have Hle2: x * y - (x * y) mod 2^64  <= (2^64 - 2)*(2^64 - 2) - 0
        by apply Z.sub_le_mono;[apply Zmult_le_compat; nia | move: (Z_mod_lt (x*y) (2^64));nia ].
      by apply (Z.le_trans _ _ _ Hle2); nia.
Qed.

Definition adc_v_nof (x y : Z) (cf : bool) := x + y + cf:%Z.

Lemma adc_v_nof_intro (x y : Z) (cf : bool):
  x + y + cf:%Z < p64 ->
  adc_v 1 x y cf = adc_v_nof x y cf.
Proof.
rewrite -lock. move=> Hlt. rewrite /adc_v /adc_v_nof /oflow.
have : (pow 1 <=? x + y + cf:%Z = adc_cf 1 x y cf) by rewrite /adc_cf -lock.
case (adc_cf 1 x y cf) => Hineq; last by simp.
by move: Hineq; rewrite -Zle_is_le_bool -lock; nia.
Qed.

Lemma adc_v_nof_umul (x y h l : Z) (cf : bool):
  is_u64 x ->
  is_u64 y ->
  (h,l) <- umul x y ->
  adc_v 1 h 0 cf = adc_v_nof h 0 cf.
Proof.
move=> Hbx Hby /assgnKl Humul_h.
apply adc_v_nof_intro.
by move: (bounds_umul_h Hbx Hby); rewrite -lock; case cf; simp; lia.
Qed.

Lemma umul_h_plus_cf (x y : Z) (cf : bool):
  is_u64 x ->
  is_u64 y ->
  umul_h x y + cf:%Z < p64.
Proof.
move=> Hbx Hby.
by move: (bounds_umul_h Hbx Hby); rewrite -lock; case cf; simp; lia.
Qed.

Definition TagEq {T} (x y : T) := x = y.

Lemma TagEqI {T} (x y : T) : x <- y <-> TagEq x y.
Proof. by rewrite /TagEq. Qed.


Ltac inline_adc :=
  match goal with
  (* unfold adc_v_nof *)
  | [ Hd: ?V <- adc_v_nof _ _ _ |- context[?V] ] =>
    idtac V; idtac "";
    (* not_used_var_hyp V; *)
    idtac "not_used"; idtac "";
    rewrite !(assgnK Hd) /adc_v_nof; clear Hd
  (* unfold adc_v *)
  | [ Hd: ?V <- adc_v 1%nat ?X ?Y ?CF_IN |- context[?V] ] =>
    idtac V; idtac "";
    (* not_used_var_hyp V; *)
    idtac "not_used"; idtac "";
    rewrite !(assgnK Hd) /adc_v /oflow;
    (match goal with
     | [ Hc: ?CF_OUT <- adc_cf 1%nat X Y CF_IN |- _ ] =>
       idtac CF_OUT; idtac "fold-CF";
       (* not_used_var_hyp CF_OUT; *)
       (* idtac "not_used"; idtac ""; *)
       rewrite -!(assgnK Hc) (* ; clear Hd *)
     end)
  end.

Ltac inline_umul :=
  match goal with
  (* unfold umul_h and umul_l *)
  | [ Hd: ?V <- umul_h _ _ |- context[?V] ] =>
    idtac V; idtac "";
    (* not_used_var_hyp V; *)
    idtac "not_used"; idtac "";
    rewrite !(assgnK Hd) (* ; clear Hd *)
  | [ Hd: ?V <- umul_l _ _ |- context[?V] ] =>
    idtac V; idtac "";
    (* not_used_var_hyp V; *)
    idtac "not_used"; idtac "";
    rewrite !(assgnK Hd) (* ; clear Hd *)
  end.

Ltac inline :=
  repeat inline_adc;
  repeat inline_umul.

Ltac inline_var_def V :=
  match goal with
  | [ H: V <- _ |- context[V]] => rewrite (assgnK H)
  end.

(* prove no-overflow for ignored carries *)
Ltac not_used_var_hyp V :=
  match goal with
  | [ H : _ <- ?T |- _ ] =>
    match T with context[V] => fail 2 end
  | _                       => idtac
  end.

Ltac not_used_var_goal V :=
  match goal with
  | [ _ : _ |- context[V] ] => fail 1
  | _                      => idtac
  end.

Ltac simp_adc_cf_nof :=
   match reverse goal with
   | [ Hv:  _ <- adc_v  1 ?X ?Y ?CF_IN |- TagEq _ _ ] =>
     (match goal with
      | [ Hcf: ?CF_OUT <- adc_cf 1 X Y CF_IN |- _ ] =>
        not_used_var_hyp CF_OUT; not_used_var_goal CF_OUT;
        clear Hcf;
        idtac Hv; idtac "cf unused";
        rewrite (@adc_v_nof_intro X Y CF_IN) in Hv;
          [idtac | try (by inline; rewrite (Z.add_0_l,Z.add_0_r); apply umul_h_plus_cf) ]

      | [ Hcf: ?CF_OUT <- adc_cf 1 X Y CF_IN |- _ ] =>
        fail 1
      | _ =>
        idtac Hv; idtac "no cf";
        rewrite (@adc_v_nof_intro X Y CF_IN) in Hv;
          [idtac | try (by inline; rewrite (Z.add_0_l,Z.add_0_r); apply umul_h_plus_cf) ]
      end)
   end.

Ltac simp_nof :=
  rewrite -/(@TagEq Z _ _);
  repeat simp_adc_cf_nof;
  rewrite /TagEq.

Ltac split_pair_assgn :=
  match goal with
  (* first split all assignments *)
  | [ Hd: (_,_)  <- (_,_) |- _ ] =>
    idtac "split "; idtac "";
    let Hd1 := fresh Hd in
    let Hd2 := fresh Hd in
    move: (assgnKr Hd) (assgnKl Hd) => Hd1 Hd2 {Hd};
    rewrite -/(Assgn _ _) in Hd1;
    rewrite -/(Assgn _ _) in Hd2
  end.

Ltac tag_occ_goal := repeat
  (match goal with
   | [ H: ?V <- _ |- context[?V] ] =>
     move: H; rewrite (@TagEqI _ _ _) => H
   | [ H1: ?V <- _, H2: TagEq _ ?T |- _ ] =>
     match T with
     | context[V] => move: H1; rewrite (@TagEqI _ _ _) => H1
     end
   end).

Ltac is_unused V :=
  match goal with
  | [ H: TagEq V _ |- _ ]  => fail 1
  | [ H: _ |- context[V] ] => fail 1
  | [ H: TagEq _ ?T |- _ ] => match T with context[V] => fail 2 end
  | [ _:_           |- _ ] => idtac
  end.

Ltac drop_not_tagged := repeat
  (match goal with
   | [ H: _ <- _ |- _ ] => clear H
   | [ H: is_true (is_u64 ?V) |- _] =>
     idtac V; idtac "check-tagged";
     is_unused V;
     idtac V; idtac "clear";
     clear H; try (clear V)
   end).

Ltac remove_tags := repeat
  (match goal with
   | [ H: TagEq _ _ |- _ ] => move: H; rewrite -(@TagEqI _ _ _) => H
   end).

Ltac remove_unused := tag_occ_goal; drop_not_tagged; remove_tags.

Ltac simp_post :=
  rewrite !ds2i_mul_cons;
  rewrite !ds2i_mul_scalar; try done;
  rewrite !ds2i_mul_scalar_scalar; try done; unfold length;
  unfold ds2i,length; ring_simplify;
  rewrite !Z.pow_0_r !Z.pow_1_r !Z.mul_1_r !Z.mul_1_l.

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
(* simplify program by constant propagation *)
pop_defs; prop_const; sort_defs.

(* simplify post-condition *)
simp_post.

(* generate no_overflow obligations and inline defs into post-condition *)
repeat split_pair_assgn; simp_nof; first inline.

(* discharge post-condition *)
apply Zeq_eq0; rewrite -lock; unfold Z.of_nat, b2i; ring.

remove_unused.
rewrite -/(adc_v_nof _ _ _).

Ltac not_umul E :=
  match E with
  | umul_h _ _ => fail 1
  | umul_l _ _ => fail 1
  | _ => idtac
  end.

Ltac expand_upto_umul T :=
  match goal with
  | [ H : _ |- (T _ _ ?CF) < _] =>
    is_var CF; inline_var_def CF
  | [ H : _ |- context[T ?X ?E _]] =>
    is_var X; not_umul E; inline_var_def X
  | [ H : _ |- context[T ?E ?X _]] =>
    is_var X; not_umul E; inline_var_def X
  end.

repeat (first [ expand_upto_umul adc_v_nof
              | expand_upto_umul (adc_cf 1)
              | expand_upto_umul (adc_v 1)]).

rewrite Z.add_0_l.
inline_var_def h'13. inline_var_def cf''13.
inline_var_def z4''13. inline_var_def h''13. inline_var_def cf'''13.
inline_var_def l'13.
move: (bounds_umul_cases Hb_ya3 Hb_xa1). elim.
+ move=> [] Hh Hl. move: Hb_z4''13.
 rewrite !Hh !Hl.
  have : (pow 1 <=? z4'03 + 1 + false:%Z = adc_cf 1 z4'03 1 false) by rewrite /adc_cf -lock.
  rewrite /adc_v /oflow.
  case (adc_cf 1 z4'03 1 false).
  + rewrite -Zle_is_le_bool !(b2i_false,b2i_true) !Z.add_0_r.
    move=> Hb Hz4.
    rewrite (_: z4'03 + 1 - 1 * pow 1 = 0); last first.
    + apply (Z.le_antisymm).
      + move: Hb_z4'03; rewrite !is_u64K -lock //=. 
        rewrite (_ : Z.pow_pos 2 64 = 18446744073709551616); last by done.
        lia.
      + by move: Hz4; rewrite !is_u64K -lock //=; nia.
    have adc_cf_symm: forall x y cf, adc_cf 1 x y cf =  adc_cf 1 y x cf.
      by move=> x y cf; rewrite /adc_cf (Z.add_comm x y).
    rewrite adc_cf_symm adc1_cf_0.
    by rewrite b2i_false -lock /adc_v_nof b2i_true; nia. done.
  + rewrite Z.leb_gt  !(b2i_false,b2i_true).
    move=> Hb Hz4. rewrite /adc_v_nof b2i_false.
    case (adc_cf 1 (z4'03 + 1 + 0 - 0 * pow 1) hprev'12 false); rewrite -lock //=; nia.
+ inline_var_def h'13. inline_var_def h''13.
  rewrite /adc_v_nof -lock.
  case cf'''13; case cf''13; rewrite !(b2i_true,b2i_false); nia.


remove_unused.
rewrite Z.add_0_l.
move: (bounds_umul_cases Hb_ya3 Hb_xa1). elim.
+ move=> [] Hh Hl. move: Hb_z4''13.
  inline_var_def h'13. inline_var_def cf''13.
  inline_var_def z4''13. inline_var_def h''13. inline_var_def cf'''13.
  inline_var_def l'13. rewrite !Hh !Hl.
  have : (pow 1 <=? z4'03 + 1 + false:%Z = adc_cf 1 z4'03 1 false) by rewrite /adc_cf -lock.
  rewrite /adc_v /oflow.
  case (adc_cf 1 z4'03 1 false).
  + rewrite -Zle_is_le_bool !(b2i_false,b2i_true) !Z.add_0_r.
    move=> Hb Hz4.
    rewrite (_: z4'03 + 1 - 1 * pow 1 = 0); last first.
    + apply (Z.le_antisymm).
      + move: Hb_z4'03; rewrite !is_u64K -lock //=. 
        rewrite (_ : Z.pow_pos 2 64 = 18446744073709551616); last by done.
        lia.
      + by move: Hz4; rewrite !is_u64K -lock //=; nia.
    have adc_cf_symm: forall x y cf, adc_cf 1 x y cf =  adc_cf 1 y x cf.
      by move=> x y cf; rewrite /adc_cf (Z.add_comm x y).
    rewrite adc_cf_symm adc1_cf_0.
    by rewrite b2i_false -lock /adc_v_nof b2i_true; nia. done.
  + rewrite Z.leb_gt  !(b2i_false,b2i_true).
    move=> Hb Hz4. rewrite /adc_v_nof b2i_false.
    case (adc_cf 1 (z4'03 + 1 + 0 - 0 * pow 1) hprev'12 false); rewrite -lock //=; nia.
+ inline_var_def h'13. inline_var_def h''13.
  rewrite /adc_v_nof -lock.
  case cf'''13; case cf''13; rewrite !(b2i_true,b2i_false); nia.

remove_unused.
rewrite Z.add_0_l.
move: (bounds_umul_cases Hb_ya3 Hb_xa2). elim.
(* h and l fixed values *)
+ move=> [] Hh Hl. move: Hb_z5''23.
  inline_var_def h'23. inline_var_def cf''23.
  inline_var_def z5''23. inline_var_def h''23. inline_var_def cf'''23.
  inline_var_def l'23. rewrite !Hh !Hl.
  have : (pow 1 <=? z5'13 + 1 + false:%Z = adc_cf 1 z5'13 1 false) by rewrite /adc_cf -lock.
  rewrite /adc_v /oflow.
  case (adc_cf 1 z5'13 1 false).
  + rewrite -Zle_is_le_bool !(b2i_false,b2i_true) !Z.add_0_r.
    move=> Hb Hz5.
    rewrite (_: z5'13 + 1 - 1 * pow 1 = 0); last first.
    + apply (Z.le_antisymm).
      + move: Hb_z5'13; rewrite !is_u64K -lock //=. 
        rewrite (_ : Z.pow_pos 2 64 = 18446744073709551616); last by done.
        lia.
      + by move: Hz5; rewrite !is_u64K -lock //=; nia.
    have adc_cf_symm: forall x y cf, adc_cf 1 x y cf =  adc_cf 1 y x cf.
      by move=> x y cf; rewrite /adc_cf (Z.add_comm x y).
    rewrite adc_cf_symm adc1_cf_0.
    by rewrite b2i_false -lock /adc_v_nof b2i_true; nia. done.
  + rewrite Z.leb_gt  !(b2i_false,b2i_true).
    move=> Hb Hz5. rewrite /adc_v_nof b2i_false.
    case (adc_cf 1 (z5'13 + 1 + 0 - 0 * pow 1) hprev'22 false); rewrite -lock //=; nia.
  (* enough space for two carries *)
+ inline_var_def h'23. inline_var_def h''23.
  rewrite /adc_v_nof -lock.
  case cf'''23; case cf''23; rewrite !(b2i_true,b2i_false); nia.

remove_unused.
rewrite Z.add_0_l.
move: (bounds_umul_cases Hb_ya3 Hb_xa3). elim.
+ move=> [] Hh Hl. move: Hb_z6'33.
  inline_var_def h'33. inline_var_def cf''33.
  inline_var_def z6'33. inline_var_def h''33. inline_var_def cf'''33.
  inline_var_def l'33. rewrite !Hh !Hl.
  have : (pow 1 <=? z6'23 + 1 + false:%Z = adc_cf 1 z6'23 1 false) by rewrite /adc_cf -lock.
  rewrite /adc_v /oflow.
  case (adc_cf 1 z6'23 1 false).
  + rewrite -Zle_is_le_bool !(b2i_false,b2i_true) !Z.add_0_r.
    move=> Hb Hz6.
    rewrite (_: z6'23 + 1 - 1 * pow 1 = 0); last first.
    + apply (Z.le_antisymm).
      + move: Hb_z6'23; rewrite !is_u64K -lock //=. 
        rewrite (_ : Z.pow_pos 2 64 = 18446744073709551616); last by done.
        lia.
      + by move: Hz6; rewrite !is_u64K -lock //=; nia.
    have adc_cf_symm: forall x y cf, adc_cf 1 x y cf =  adc_cf 1 y x cf.
      by move=> x y cf; rewrite /adc_cf (Z.add_comm x y).
    rewrite adc_cf_symm adc1_cf_0.
    by rewrite b2i_false -lock /adc_v_nof b2i_true; nia. done.
  + rewrite Z.leb_gt  !(b2i_false,b2i_true).
    move=> Hb Hz6. rewrite /adc_v_nof b2i_false.
    case (adc_cf 1 (z6'23 + 1 + 0 - 0 * pow 1) hprev'32 false); rewrite -lock //=; nia.
+ inline_var_def h'33. inline_var_def h''33.
  rewrite /adc_v_nof -lock.
  case cf'''33; case cf''33; rewrite !(b2i_true,b2i_false); nia.


 admit.
remove_unused. admit.

move: (Tag L46) => {L46} L46.

admit.
admit.
admit.
by inline; rewrite (Z.add_0_l,Z.add_0_r); apply umul_h_plus_cf.
admit.
by inline; rewrite (Z.add_0_l,Z.add_0_r); apply umul_h_plus_cf.
admit.
by inline; rewrite (Z.add_0_l,Z.add_0_r); apply umul_h_plus_cf.
by inline; rewrite (Z.add_0_l,Z.add_0_r); apply umul_h_plus_cf.
by inline; rewrite (Z.add_0_l,Z.add_0_r); apply umul_h_plus_cf.
admit.
by inline; rewrite (Z.add_0_l,Z.add_0_r); apply umul_h_plus_cf.
admit.
by inline; rewrite (Z.add_0_l,Z.add_0_r); apply umul_h_plus_cf.
by inline; rewrite (Z.add_0_l,Z.add_0_r); apply umul_h_plus_cf.
by inline; rewrite (Z.add_0_l,Z.add_0_r); apply umul_h_plus_cf.
admit.
by inline; rewrite (Z.add_0_l,Z.add_0_r); apply umul_h_plus_cf.
admit.
by inline; rewrite (Z.add_0_l,Z.add_0_r); apply umul_h_plus_cf.
by inline; rewrite (Z.add_0_l,Z.add_0_r); apply umul_h_plus_cf.
by inline; rewrite (Z.add_0_l,Z.add_0_r); apply umul_h_plus_cf.
by inline; rewrite (Z.add_0_l,Z.add_0_r); apply umul_h_plus_cf.
by inline; rewrite (Z.add_0_l,Z.add_0_r); apply umul_h_plus_cf.
Admitted.
by inline; rewrite (Z.add_0_l,Z.add_0_r); apply umul_h_plus_cf.


rewrite Z.add_0_l.
move: (bounds_umul_cases Hb_ya1 Hb_xa1). elim.
+ move=> [] Hh Hl.
  inline_var_def cf'11. inline_var_def z2''11.
  inline_var_def h'11. inline_var_def h''11. inline_var_def cf''11.
  inline_var_def l'11. rewrite !Hh !Hl /adc_v /oflow. simp.
  
+ inline_var_def h'11. inline_var_def h''11.
   rewrite /adc_v -lock /oflow.
   have Hbool: forall b, 0 <= b:%Z < 2 by move=>b; case b; rewrite //=; lia.
   move : (Hbool cf'11) (Hbool (adc_cf 1 (umul_h ya1 xa1) 0 cf''11))  (Hbool cf''11).
   rewrite -lock. case (adc_cf 1 (umul_h ya1 xa1) 0 cf''11); case cf''11; case cf'11;
   rewrite !(b2i_true,b2i_false); nia.
case cf'11; nia.  ove

by inline; rewrite (Z.add_0_l,Z.add_0_r); apply umul_h_plus_cf.
admit.
by inline; rewrite (Z.add_0_l,Z.add_0_r); apply umul_h_plus_cf.
by inline; rewrite (Z.add_0_l,Z.add_0_r); apply umul_h_plus_cf.
by inline; rewrite (Z.add_0_l,Z.add_0_r); apply umul_h_plus_cf.
admit.
by inline; rewrite (Z.add_0_l,Z.add_0_r); apply umul_h_plus_cf.
admit.
by inline; rewrite (Z.add_0_l,Z.add_0_r); apply umul_h_plus_cf.
by inline; rewrite (Z.add_0_l,Z.add_0_r); apply umul_h_plus_cf.
by inline; rewrite (Z.add_0_l,Z.add_0_r); apply umul_h_plus_cf.
admit.
by inline; rewrite (Z.add_0_l,Z.add_0_r); apply umul_h_plus_cf.
admit.
by inline; rewrite (Z.add_0_l,Z.add_0_r); apply umul_h_plus_cf.
admit.
admit.
admit.
Admitted.