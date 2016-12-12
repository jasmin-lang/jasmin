(* * Experiments for proof *)

(* ** Setup *)
Require Import ZArith zmod_setoid proof_utils proof_sem Psatz Setoid Morphisms.
From mathcomp Require Import ssreflect ssrfun ssrbool seq eqtype.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Local Scope Z_scope.

(* ** adc *)

Definition adc_cf (n : nat) (u v : Z) (b : bool) : bool := (pow n) <=? (u + v) + b:%Z.
Definition oflow  (n : nat) (u v : Z) (b : bool) : Z  := (adc_cf n u v b):%Z * (pow n).
Definition adc_v  (n : nat) (u v : Z) (b : bool) : Z  := ((u + v) + b:%Z) - oflow n u v b.
Notation adc n u v b := (adc_cf n u v b, adc_v n u v b).

Lemma adc1_cf_0 (n : Z) :
  is_u64 n -> adc_cf 1 n 0 false = false.
Proof.
rewrite is_u64K /adc_v /oflow /adc_cf b2i_false !Z.add_0_r Z.pow_1_r.
move=> [h1 h2]. rewrite Z.leb_nle.
apply Zgt_not_le. by apply Z.lt_gt.
Qed.

Lemma adc1_v_0 (n : Z) :
  is_u64 n -> adc_v 1 n 0 false = n.
Proof.
move=> Hb. rewrite /adc_v /oflow adc1_cf_0 //=. ring.
Qed.

Lemma adc_cf_0 (n : nat) (ds1 ds2 : seq Z):
  length ds1 = n ->
  all (fun d => is_u64 d) ds1 ->
  all (fun d => Z.eqb d 0) ds2 ->
  adc_cf n [::i ds1] [::i ds2] false = false.
Proof.
move=> Hlen Hall1 Hall2. rewrite (ds2i_0 Hall2).
by rewrite /adc_cf b2i_false !Z.add_0_r Z.leb_gt; apply ds2i_bounded_lt.
Qed.

Lemma adc_v_0 (n : nat) (ds1 ds2 : seq Z):
  length ds1 = n ->
  all (fun d => is_u64 d) ds1 ->
  all (fun d => Z.eqb d 0) ds2 ->
  adc_v n [::i ds1] [::i ds2] false = [::i ds1].
Proof.
move=> Hlen Hall1 Hall2.
rewrite /adc_v /oflow b2i_false !Z.add_0_r adc_cf_0 => //=.
by rewrite (ds2i_0 Hall2); ring.
Qed.

(* ** Ltac *)

Ltac rw_lez :=
  match goal with
  | [ H1 : context[adc_cf _ _ _ false] |- _ ] => rewrite adc1_cf_0 in H1; last done
  | [ H1 : context[adc_v _ _ _ false] |- _  ] => rewrite adc1_v_0 in H1; last done
  | [ H1 : context[adc_cf _ _ _ false] |- _ ] =>
    rewrite adc_cf_0 in H1; [ idtac | done | band_auto | done ]
  | [ H1 : context[adc_v _ _ _ false] |- _ ] =>
    rewrite adc_v_0 in H1; [ idtac | done | band_auto | done ]
  end.

Ltac prop_false :=
  match goal with
  | [ H1 : ?x <- ?c        , H2 : context[?x] |- _ ] =>
    is_bool_const c; is_var x; rewrite (assgnK H1) in H2
  | [ H1 : (?x,_) <- (?c,_), H2 : context[?x] |- _ ] =>
    is_bool_const c; is_var x; rewrite (assgnKl H1) in H2
  | [ H1 : ?x <- 38 , H2   : _ |- _ ] => rewrite (assgnK H1) in H2
  | [ H1 : ?x <- 0 , H2    : _ |- _ ] => rewrite (assgnK H1) in H2
  end.

Ltac prop_var_ctxt :=
  match goal with
  | [ H1 : ?x = ?y, H2 : is_u64 _ |- _ ] => fail 1
  | [ H1 : ?x = ?y, H2 : context[?x] |- _ ] => is_var y; rewrite H1 in H2
  end.

Ltac simp_adc_v :=
  match goal with
  | [ H1 : ?x = adc_v _ _ _ ?cf |- _ ] =>
      rewrite /adc_v /oflow in H1
  end.

Ltac simp_cf :=
  match goal with
  | [ H1 : ?x = _ + _ + _ - (b2i ?cf) * _ , H2 : _ = ?cf |- _ ] =>
      rewrite -H2 in H1
  | [ H1 : ?x = _ + _ - (b2i ?cf) * _ , H2 : _ = ?cf |- _ ] =>
      rewrite -H2 in H1
  end.

Ltac prop_var_goal :=
  match goal with
  | [ H1 : ?x <- ?y    |- _ ] => is_var y; rewrite (assgnK H1)
  | [ H1 : ?x <- ?c    |- _ ] => is_bool_const c; is_var x; rewrite (assgnK H1)
  | [ H1 : (?x,_) <- (?c,_) |- _ ] => is_bool_const c; is_var x; rewrite (assgnKl H1)
  | [ H1 : (_,?x) <- (_,?y) |- _ ] => is_var y; is_var x; rewrite (assgnKr H1)
  | [ _ : _ |- _ ]           =>
    first [ rewrite b2i_true | rewrite b2i_false | rewrite Z.add_0_r ]
  | [ H1 : ?x = _     |- _ ] =>
    first [ rewrite b2i_true in H1 | rewrite b2i_false in H1 | rewrite Z.add_0_r in H1 ]
  end.

Ltac prop_var_goal_all :=
  match goal with
  | [ H1 : ?x = _ |- context[?x] ] => rewrite H1
  end.

Ltac prop_0 :=
  match goal with
  | [ H1 : ?x = 0, H2 : _ |- _ ] => rewrite H1 in H2
  end.

Ltac simp_false :=
  match goal with
  | [ H : context[false:%Z] |- _ ] => rewrite b2i_false ?Z.add_0_r in H
  end.

Ltac simp_0 :=
  match goal with
  | [ H : _ |- _ ]  =>
    first [ rewrite Z.mul_0_l in H | rewrite Z.mul_0_r in H | rewrite Z.mul_1_l in H
          | rewrite Z.pow_1_r in H | rewrite Z.sub_0_r in H 
          | rewrite Z.add_0_l in H | rewrite Z.add_0_r in H ]
  | [ _ : _ |- _ ]  => rewrite Z.mul_0_l ?Z.sub_0_r ?Z.add_0_r
  end.

Ltac simp :=
  repeat first [ rw_lez | prop_false | prop_0 | prop_var_ctxt | prop_var_goal
               | simp_false | simp_0 | simp_adc_v | simp_cf
               | rewrite Z.pow_1_r | rewrite Z.pow_0_r | rewrite Z.add_0_l | rewrite Z.add_0_r
               | rewrite Z.mul_1_l | rewrite Z.mul_1_r ].

Ltac not_adc t :=
  match t with
  | adc_cf _ _ _ _ => fail 1
  | _              => idtac
  end.

Ltac inst_goal :=
  repeat match goal with
         | [ H : ?x = ?y |- context[?x] ] => is_var x; not_adc y; rewrite H
         end.

Ltac inst_goal_flag :=
  repeat match goal with
         | [ H : ?x = ?y |- context[?x] ] => is_var x; rewrite H
         end.

(* ** Combining adc in carry chains *)

Lemma combine_chain1_cf (x0 y0 x1 y1 t0 t1 : Z) (cf0 cf1 cf2 :bool)
  (B_x0: is_u64 x0)
  (B_x1: is_u64 x1)
  (B_y0: is_u64 y0)
  (B_y1: is_u64 y1) :
  (cf1,t0) <- adc 1 x0 y0 cf0 ->
  (cf2,t1) <- adc 1 x1 y1 cf1 ->
  cf2      <- adc_cf 2 [:i x1; x0] [:i y1; y0] cf0.
Proof.
move/assgnS => [] L0 L1. move/assgnS => [] L2 L3 {L3} {L1}.
push_defs. rewrite /adc_cf /Assgn. unfold ds2i. unfold length. simp.
have Hsucc : forall i, i = Z.succ (i - 1); first (move=> i; ring).
have Hle: forall i, is_u64 i -> i <= p64 - 1.
+ move=> i. move/is_u64K => [] G1 G2.
  rewrite (Hsucc p64) in G2.
  by apply Zlt_succ_le in G2.
have Hge: forall i, is_u64 i -> 0 <= i.
+ by move=> i; move/is_u64K => [] G1 G2.
rewrite Z.pow_2_r.
case cf2; last first.
+ case cf1; last first.
  + move=> H1 H2. simp. trans_cmp_b.
    rewrite (_:   p64 * x1 + x0   + (p64 * y1 + y0) + cf0:%Z
                = p64 * (x1 + y1) + (x0 + y0 + cf0:%Z)); last ring.
    move: H1 H2; rewrite !Z_le_leq_succ => H1 H2.
    apply (Z.le_trans _ (p64 * (p64 - 1) + (p64 - 1))).
    + apply (Z.add_le_mono); last done.
      apply (Zmult_le_compat_l _ _ _ H2 p64_ge0).
    rewrite (_ : p64 * (p64 - 1) + (p64 - 1) = (p64 * p64) - 1); last ring.
    by apply Z.eq_le_incl.
  + move=> H1 H2. simp. trans_cmp_b.
    move: H1 H2; rewrite !Z_le_leq_succ => H1 H2.    
    rewrite (_:   p64 * x1 + x0 + (p64 * y1 + y0) + cf0:%Z
                = p64 * (x1 + y1) + (x0 + y0 + cf0:%Z)); last ring.
    apply (Z.le_trans _ (p64 * (p64 - 2) + ((p64 - 1) + (p64 - 1) + 1))).
    apply (Z.add_le_mono).
    + apply (Zmult_le_compat_l _ _ _); last apply p64_ge0.
      by apply (Zplus_le_reg_r _ _ 1); rewrite (_: p64 - 2 + 1 = p64 -1); last ring.
    + apply (Z.add_le_mono); last by case cf0.
      apply (Z.add_le_mono _ _ _ _ (Hle _ B_x0) (Hle _ B_y0)).
    + by rewrite (_ :   p64 * (p64 - 2) + (p64 - 1 + (p64 - 1) + 1)
                      = p64 * p64 - 1); [ apply Z.eq_le_incl | ring ].
+ case cf1.
  + move=> H1 H2. simp. trans_cmp_b.
    rewrite (_:   p64 * x1 + x0 + (p64 * y1 + y0) + cf0:%Z
                = p64*(x1 + y1) + (x0 + y0 + cf0:%Z)); last ring.
    rewrite (_ : p64*p64 = p64*(p64 - 1) + p64); last ring.
    apply (Z.add_le_mono); last done.
    apply (Zmult_le_compat_l); last apply p64_ge0.
    by apply (Zplus_le_reg_r _ _ 1); ring_simplify.
  + move=> G H {G}. simp. trans_cmp_b.
    rewrite (_ :   p64 * x1 + x0 + (p64 * y1 + y0) + cf0:%Z
                 = p64 * (x1 + y1) + (x0 + y0 + cf0:%Z)); last ring.
    rewrite (_ : p64*p64 = p64*p64 + (0 + 0 + 0)); last ring.
    apply (Z.add_le_mono).
    + by apply (Zmult_le_compat_l); last apply p64_ge0.
    apply (Z.add_le_mono).
    + by apply (Z.add_le_mono _ _ _ _ (Hge _ B_x0) (Hge _ B_y0)).
    by case cf0.
Qed.

Lemma combine_chainN_cf (n : nat) (xn yn tn : seq Z) (xsn ysn tsn : Z) (cf0 cfn cfsn :bool) :
  length xn = n ->
  length yn = n ->
  all (fun d => is_u64 d) xn ->
  all (fun d => is_u64 d) yn ->
  (cfn,[::i tn]) <- adc n [::i xn] [::i yn] cf0 ->
  (cfsn,tsn)     <- adc 1 xsn ysn cfn ->
  cfsn           <- adc_cf (S n) [:i xsn & xn] [:i ysn & yn] cf0.
Proof.
move=> Hlen_x Hlen_y Hall_x Hall_y.
move/assgnS => [] L0 L1. move/assgnS => [] L2 L3 {L3} {L1}.
push_defs. rewrite /adc_cf /Assgn. rewrite !ds2i_cons Hlen_x Hlen_y.
have Hsucc : forall i, i = Z.succ (i - 1); first (move=> i; ring).
have Hle: forall i, is_u64 i -> i <= p64 - 1.
+ move=> i. move/is_u64K => [] G1 G2.
  rewrite (Hsucc p64) in G2.
  by apply Zlt_succ_le in G2.
have Hge: forall i, is_u64 i -> 0 <= i.
+ by move=> i; move/is_u64K => [] G1 G2.
rewrite Z.pow_1_r.
move=> H1 H2. rewrite !Nat2Z.inj_succ !Z.pow_succ_r; last apply Zle_0_nat.
move: H1 H2. case cfsn; last first.
+ case cfn; last first.
  + move=> H1 H2. simp. trans_cmp_b.
    rewrite (_:   pow n * xsn + [::i xn] + (pow n * ysn + [::i yn]) + cf0:%Z 
                = pow n * (xsn + ysn) + ([::i xn] + [::i yn] + cf0:%Z)); last ring.
    move: H1 H2; rewrite !Z_le_leq_succ => H1 H2.
    apply (Z.le_trans _ (pow n * (p64 - 1) + (pow n - 1))).
    + apply (Z.add_le_mono); last done.
      apply (Zmult_le_compat_l _ _ _ H2); first apply (pow_ge0).
    rewrite (_ : pow n * (p64 - 1) + (pow n - 1) = (p64 * pow n) - 1); last ring.
    by apply Z.eq_le_incl.
  + move=> H1 H2. simp. trans_cmp_b.
    move: H1 H2; rewrite !Z_le_leq_succ => H1 H2.    
    rewrite (_:   pow n * xsn + [::i xn] + (pow n * ysn + [::i yn]) + cf0:%Z
                = pow n * (xsn + ysn) + ([::i xn] + [::i yn] + cf0:%Z)); last ring.
    apply (Z.le_trans _ (pow n * (p64 - 2) + ((pow n - 1) + (pow n - 1) + 1))).
    apply (Z.add_le_mono).
    + apply (Zmult_le_compat_l _ _ _); last apply pow_ge0.
      by apply (Zplus_le_reg_r _ _ 1); rewrite (_: p64 - 2 + 1 = p64 -1); last ring.
    + apply (Z.add_le_mono); last by case cf0.
      apply (Z.add_le_mono _ _ _ _).
      + by apply ds2i_bounded_le.
      + by apply ds2i_bounded_le.      
    + by rewrite (_ :   pow n * (p64 - 2) + (pow n - 1 + (pow n - 1) + 1)
                      = p64 * pow n - 1); [ apply Z.eq_le_incl | ring ].
+ case cfn.
  + move=> H1 H2. simp. trans_cmp_b.
    rewrite (_:   pow n * xsn + [::i xn] + (pow n * ysn + [::i yn]) + cf0:%Z
                = pow n * (xsn + ysn) + ([::i xn] + [::i yn] + cf0:%Z)); last ring.
    rewrite (_ : p64*pow n = pow n*(p64 - 1) + pow n); last ring.
    apply (Z.add_le_mono); last done.
    apply (Zmult_le_compat_l); last (apply pow_ge0).
    by apply (Zplus_le_reg_r _ _ 1); ring_simplify.
  + move=> G H {G}. simp. trans_cmp_b.
    rewrite (_ :   pow n * xsn + [::i xn] + (pow n * ysn + [::i yn]) + cf0:%Z
                 = pow n * (xsn + ysn) + ([::i xn] + [::i yn] + cf0:%Z)); last ring.
    rewrite (_ : p64 * pow n = pow n * p64 + (0 + 0 + 0)); last ring.
    apply (Z.add_le_mono).
    + by apply (Zmult_le_compat_l); last apply pow_ge0.
    apply (Z.add_le_mono).
    + apply (Z.add_le_mono _ _ _ _). apply (ds2i_nneg Hall_x). apply (ds2i_nneg Hall_y).
    by case cf0.
Qed.

Lemma combine_chain1_v (x0 y0 x1 y1 t0 t1 : Z) (cf0 cf1 cf2 :bool)
  (B_x0: is_u64 x0)
  (B_x1: is_u64 x1)
  (B_y0: is_u64 y0)
  (B_y1: is_u64 y1) : 
  (cf1,t0)    <- adc 1 x0 y0 cf0 ->
  (cf2,t1)    <- adc 1 x1 y1 cf1 ->
  [:i t1; t0] <- adc_v 2 [:i x1; x0] [:i y1; y0] cf0.
Proof.
move=> L0 L1.
move: (combine_chain1_cf B_x0 B_x1 B_y0 B_y1 L0 L1) => H.
move: L0 L1.
move/assgnS => [] L0 L1. move/assgnS => [] L2 L3.
rewrite L1 L3 L0 /adc_v /oflow /Assgn. unfold ds2i. unfold length. simp.
apply Zeq_eq0.
ring_simplify. rewrite {2}(_ : 2 = Z.of_nat 2); last done.
unfold ds2i in H. unfold length in H.
rewrite !Z.pow_1_r !Z.pow_0_r !Z.mul_1_l !Z.add_0_r in H.
rewrite -H. move : L2. rewrite L0 => L2. rewrite -L2.
ring.
Qed.

Lemma combine_chain1 (x0 y0 x1 y1 t0 t1 : Z) (cf0 cf1 cf2 :bool)
  (B_x0: is_u64 x0)
  (B_x1: is_u64 x1)
  (B_y0: is_u64 y0)
  (B_y1: is_u64 y1) : 
  (cf1,t0)          <- adc 1 x0 y0 cf0 ->
  (cf2,t1)          <- adc 1 x1 y1 cf1 ->
  (cf2,[:i t1; t0]) <- adc 2 [:i x1; x0] [:i y1; y0] cf0.
Proof.
move=> H1 H2. congr pair.
+ by apply (combine_chain1_cf B_x0 B_x1 B_y0 B_y1 H1 H2).
+ by apply (combine_chain1_v B_x0 B_x1 B_y0 B_y1 H1 H2).
Qed.

Lemma combine_chainN_v (n : nat) (xn yn tn : seq Z) (xsn ysn tsn : Z) (cf0 cfn cfsn :bool) :
  length xn = n ->
  length yn = n ->
  length tn = n -> 
  all (fun d => is_u64 d) xn ->
  all (fun d => is_u64 d) yn ->
  all (fun d => is_u64 d) tn ->
  (cfn,[::i tn]) <- adc n [::i xn] [::i yn] cf0 ->
  (cfsn, tsn)    <- adc   1     xsn           ysn           cfn ->
  [:i tsn & tn]  <- adc_v (S n) [:i xsn & xn] [:i ysn & yn] cf0.
Proof.
move=> Hlen1 Hlen2 Hlen3 Hall1 Hall2 Hall3 L0 L1.
move: (combine_chainN_cf Hlen1 Hlen2 Hall1 Hall2 L0 L1) => H.
move: L0 L1.
rewrite !ds2i_cons. rewrite Hlen3 Hlen2 Hlen1.
move/assgnS => [] L0 L1. move/assgnS => [] L2 L3.
rewrite L1 L3 L0 /adc_v /oflow /Assgn. simp.
apply Zeq_eq0.
ring_simplify. rewrite !Nat2Z.inj_succ !Z.pow_succ_r; last apply Zle_0_nat.
rewrite !ds2i_cons Hlen1 Hlen2 in H. rewrite -H. move: L2; rewrite L0 => L2.
rewrite -L2.
ring.
Qed.

Lemma combine_chainN (n : nat) (xn yn tn : seq Z) (xsn ysn tsn : Z) (cf0 cfn cfsn :bool) :
  length xn = n ->
  length yn = n ->
  length tn = n -> 
  all (fun d => is_u64 d) xn ->
  all (fun d => is_u64 d) yn ->
  all (fun d => is_u64 d) tn ->
  (cfn,[::i tn])        <- adc n [::i xn] [::i yn] cf0 ->
  (cfsn,tsn)            <- adc 1     xsn           ysn           cfn ->
  (cfsn, [:i tsn & tn]) <- adc (S n) [:i xsn & xn] [:i ysn & yn] cf0.
Proof.
move=> Hlen1 Hlen2 Hlen3 Hall1 Hall2 Hall3 H1 H2. congr pair.
+ by apply (combine_chainN_cf Hlen1 Hlen2 Hall1 Hall2 H1 H2).
+ by apply (combine_chainN_v Hlen1 Hlen2 Hlen3 Hall1 Hall2 Hall3 H1 H2).
Qed.

(* ** Ltac for automatic application of combination lemmas *)

Ltac add_len N Tn Xn Yn G1 G2 G3 G4 G5 G6 :=
  have G1 : (length Xn = N); first done;
  have G2 : (length Yn = N); first done;
  have G3 : (length Tn = N); first done;
  have G4 : all (fun d => is_u64 d) Xn; first band_auto;
  have G5 : all (fun d => is_u64 d) Yn; first band_auto;
  have G6 : all (fun d => is_u64 d) Tn; first band_auto.

Ltac combine1 :=
  idtac "combine1_enter";
  match goal with
  | [ H1  : (?cf1,_) <- adc 1 ?X0 ?Y0 false,
      H2  : (_,_)    <- adc 1 ?X1 ?Y1 ?cf1,
      Bx0 : is_true (is_u64 ?X0),
      Bx1 : is_true (is_u64 ?X1),
      By0 : is_true (is_u64 ?Y0),
      By1 : is_true (is_u64 ?Y1)
      |- _ ] =>
    idtac "combine_chain_1";
    move: (combine_chain1 Bx0 Bx1 By0 By1 H1 H2) => {H1} {H2} H1
  end.

Ltac combineN :=
  idtac "combineN_enter";
  match goal with
  | [ H1  : (?cf1,ds2i ?Tn) <- adc ?N (ds2i ?Xn)  (ds2i ?Yn) false,
      H2  : (_,_)           <- adc 1  ?Xsn        ?Ysn       ?cf1
      |- _ ] =>
    idtac "combine_chainN";
    let Hlen_x := fresh "Hl_x" in
    let Hlen_y := fresh "Hl_y" in
    let Hlen_t := fresh "Hl_t" in
    let Hall_x := fresh "Ha_x" in
    let Hall_y := fresh "Ha_y" in
    let Hall_t := fresh "Ha_t" in
    add_len N Tn Xn Yn Hlen_x Hlen_y Hlen_t Hall_x Hall_y Hall_t;
    move: (combine_chainN Hlen_x Hlen_y Hlen_t Hall_x Hall_y Hall_t H1 H2)
      => {H1} {H2} {Hlen_x} {Hlen_y} {Hlen_t} {Hall_x} {Hall_y} {Hall_t} H1
  end.

Ltac combine := repeat combine1; repeat combineN.

(* ** ... *)

Lemma congr_eq (f : Z -> Z) {x y : Z}:
  x = y -> f x = f y.
Proof.
by move=> H; f_equal.
Qed.

Lemma Z_mod_pow_pow (x : Z) (n : nat) :
  x ^ (Z.of_nat (S n)) mod (x ^ (Z.of_nat 1)) = 0.
Proof.
rewrite !Nat2Z.inj_succ Z.pow_succ_r; last (apply Zle_0_nat).
rewrite Nat2Z.inj_0 Z.pow_succ_r ?Z.pow_0_r ?Z.mul_1_r; last done.
by rewrite Z.mul_comm Z_mod_mult.
Qed.

Lemma Z_mod_pow (x : Z) (n : nat) :
  x ^ (Z.of_nat (S n)) mod x = 0.
Proof.
rewrite !Nat2Z.inj_succ Z.pow_succ_r; last (apply Zle_0_nat).
by rewrite Z.mul_comm Z_mod_mult.
Qed.

Lemma p128_is_0: eqmod64 p128 0.
Proof. rewrite /eqmod64 Z_mod_pow. done. Qed.

Lemma p192_is_0: eqmod64 p192 0.
Proof. rewrite /eqmod64 Z_mod_pow. done. Qed.

Lemma p256_is_0: eqmod64 p256 0.
Proof. rewrite /eqmod64 Z_mod_pow. done. Qed.

Lemma assgn_eqL {A B} (x : A) (y z : B):
  ((x,y) <- (x,z)) <-> (y <- z).
Proof. by rewrite /Assgn; split; [ move=> [] H | move=> ->]. Qed.

Lemma assgn_eqR {A B} (x : A) (y z : B):
  ((y,x) <- (z,x)) <-> (y <- z).
Proof. by rewrite /Assgn; split; [ move=> [] H | move=> ->]. Qed.

Lemma split_chain1 (x0 y0 x1 y1 t0 t1 : Z) (cf0 cf2 :bool)
  (B_x0: is_u64 x0)
  (B_x1: is_u64 x1)
  (B_y0: is_u64 y0)
  (B_y1: is_u64 y1)
  (B_t0: is_u64 t0)
  (B_t1: is_u64 t1) : 
  (cf2,[:i t1; t0]) <- adc 2 [:i x1; x0] [:i y1; y0] cf0 ->
  exists cf1,
    (cf1,t0) <- adc 1 x0 y0 cf0 /\
    (cf2,t1) <- adc 1 x1 y1 cf1.
Proof.
move=> H1. rewrite /adc_v /oflow in H1.
move : (assgnKl H1) => H2. rewrite -H2 in H1.
move : (assgnKr H1) => H3 {H1}.
have Hnz: p64 <> 0 by rewrite -lock.
have Hgt0: 0 < p64 by rewrite -lock.
have Heq_true: forall b, true = b <-> b = true; first by move=> [].
have Heq_false: forall b, false = b <-> b = false; first by move=> [].
exists (adc_cf 1 x0 y0 cf0).
rewrite assgn_eqL /adc_v /oflow.
rewrite !ds2i_cons in H3; simp.
rewrite /adc_cf in H2; unfold ds2i in H2; unfold length in H2; simp.
move : (congr_eq (fun x => x mod p64) H3) => H4.
rewrite -/(eqmod64 _ _) in H4.
repeat (move: H4; rewrite -/(eqmod64 _ _) ?{1}p64_is_0 ?{1}p128_is_0 /eqmod64 => H4). simp.
rewrite Zmod_small in H4; last by rewrite  -(is_u64K _).
have : (p64 <=? (x0 + y0 + cf0:%Z))= adc_cf 1 x0 y0 cf0 by rewrite /adc_cf Z.pow_1_r.
case (adc_cf 1 x0 y0 cf0); simp => Hcf; last first.
+ move: Hcf; rewrite Z.leb_gt => Hcf.
  rewrite Zmod_small in H4; last first.
  + move: B_x0 B_y0 Hcf; rewrite !is_u64K; case cf0; simp; lia.
  split; first done.
  have Hcf2: cf2 = adc_cf 1 x1 y1 false.
  + rewrite p128_mul in H2. rewrite /adc_cf Z.pow_1_r; simp.
    rewrite (_ :   p64 * x1 + x0 + (p64 * y1 + y0) + cf0:%Z
                 = p64*(x1 + y1) + (x0 + y0 + cf0:%Z)) in H2; last ring.
    have Hleq3: x0 + y0 + cf0:%Z <= p64 - 1 by lia.
    move: H2. case cf2; simp.
    + rewrite !Heq_true !Z.leb_le => Hleq.
      by have Hleq2: p64 * (x1 + y1) + (x0 + y0 + cf0:%Z) <= p64 * (x1 + y1) + (p64 - 1); nia.
    + rewrite !Heq_false !Z.leb_gt => Hleq1.
      have Hcf0: 0 <= cf0:%Z <= 1; first by case cf0.
      have Hleq2: p64 * (x1 + y1) <= p64 * (x1 + y1) + (x0 + y0 + cf0:%Z).
      + by move: B_t0; rewrite -H4 is_u64K; lia.
      by nia.
  by rewrite -Hcf2 assgn_eqL /Assgn; nia.
+ move: Hcf; rewrite Z.leb_le => Hcf.
  rewrite (_ : ((x0 + y0 + cf0:%Z) mod p64) = ((x0 + y0 + cf0:%Z - p64) mod p64)) in H4; last first.
  + rewrite -/(eqmod64 _ _) p64_is_0 /eqmod64; f_equal; ring.
  rewrite Zmod_small in H4; last first.
  + move: B_x0 B_y0 Hcf; rewrite !is_u64K; case cf0; simp; lia.
  split; first done.
  have Hcf2: cf2 = adc_cf 1 x1 y1 true.
  + rewrite p128_mul in H2. rewrite /adc_cf Z.pow_1_r; simp.
    rewrite (_ :   p64 * x1 + x0 + (p64 * y1 + y0) + cf0:%Z
                 = p64*(x1 + y1) + (x0 + y0 + cf0:%Z)) in H2; last ring.
    have Hcf0: 0 <= cf0:%Z <= 1; first by case cf0.
    move: H2. case cf2; simp.
    + rewrite !Heq_true !Z.leb_le => Hleq.
      have Hleq2: p64 * (x1 + y1) + (x0 + y0 + cf0:%Z) <= p64 * (x1 + y1) + (2*p64 - 1).
      + by apply Zplus_le_compat_l; move: B_x0 B_y0; rewrite !is_u64K; lia.
      by nia.
    + rewrite !Heq_false !Z.leb_gt => Hleq1.
      have Hleq2: p64 * (x1 + y1) + p64 <= p64 * (x1 + y1) + (x0 + y0 + cf0:%Z) by lia.
      by nia.
  by rewrite -Hcf2 assgn_eqL /Assgn; nia.
Qed.

Section SplitProof.

Variable n : nat.

Notation pn := (pow n).

Definition eqmod_pn (x y : Z) := x mod pn = y mod pn.
Instance relation_eqmod_pn : Equivalence eqmod_pn := relation_eqmod pn.
Instance Zadd_eqmod_pn   : Proper (eqmod_pn ==> eqmod_pn ==> eqmod_pn) Z.add := Zadd_eqmod pn.
Instance Zminus_eqmod_pn : Proper (eqmod_pn ==> eqmod_pn ==> eqmod_pn) Z.sub := Zminus_eqmod pn.
Instance Zmul_eqmod_pn   : Proper (eqmod_pn ==> eqmod_pn ==> eqmod_pn) Z.mul := Zmul_eqmod pn.
Lemma pn_is_0 : eqmod_pn pn 0. Proof. by rewrite (mod_is_0 pn). Qed.

Lemma split_chainN (xn yn tn : seq Z) (xsn ysn tsn : Z) (cf0 cfsn :bool) :
  length xn = n ->
  length yn = n ->
  length tn = n -> 
  all (fun d => is_u64 d) xn ->
  all (fun d => is_u64 d) yn ->
  all (fun d => is_u64 d) tn ->
  is_u64 xsn ->
  is_u64 ysn ->
  is_u64 tsn ->
  (cfsn, [:i tsn & tn]) <- adc (S n) [:i xsn & xn] [:i ysn & yn] cf0 ->
  exists cfn,
    (cfn,[::i tn]) <- adc n [::i xn] [::i yn] cf0 /\
    (cfsn,tsn)     <- adc 1 xsn ysn cfn.
Proof.
move=> Hlenx Hleny Hlent Hallx Hally Hallt Hux Huy Hut H1. rewrite /adc_v /oflow in H1.
move : (assgnKl H1) => H2. rewrite -H2 in H1.
move : (assgnKr H1) => H3 {H1}.
have Hgt0: 0 < pn by apply pow_pos.
have Hnz: pn <> 0 by lia.
have Heq_true: forall b, true = b <-> b = true; first by move=> [].
have Heq_false: forall b, false = b <-> b = false; first by move=> [].
have Hpow_s: pow (S n) = p64 * pn by rewrite Nat2Z.inj_succ Z.pow_succ_r; last apply Zle_0_nat.
have Hcf0: 0 <= cf0:%Z <= 1; first by case cf0.
move: (ds2i_nneg Hallx) (ds2i_bounded_lt Hlenx Hallx) => H_lb0_x H_ub_x.
move: (ds2i_nneg Hally) (ds2i_bounded_lt Hleny Hally) => H_lb0_y H_ub_y.
move: (ds2i_nneg Hallt) (ds2i_bounded_lt Hlent Hallt) => H_lb0_t H_ub_t.
exists (adc_cf n [::i xn] [::i yn] cf0 ).
rewrite assgn_eqL /adc_v /oflow.
rewrite !ds2i_cons in H3; simp.
rewrite /adc_cf in H2. simp. rewrite Hpow_s in H3.
move : (congr_eq (fun x => x mod pn) H3) => H4.
repeat (move: H4; rewrite -/(eqmod_pn _ _) ?{1}pn_is_0 /eqmod_pn => H4). simp.
rewrite Zmod_small in H4; last by (split; [ apply ds2i_nneg | apply ds2i_bounded_lt]).
have : (pn <=? [::i xn] + [::i yn] + cf0:%Z) = adc_cf n [::i xn] [::i yn] cf0 by rewrite /adc_cf.
case (adc_cf n [::i xn] [::i yn] cf0); simp => Hcf; last first.
+ move: Hcf; rewrite Z.leb_gt => Hcf.
  rewrite Zmod_small in H4; last by lia.
  split; first done.
  have Hcfsn: cfsn = adc_cf 1 xsn ysn false.
  + rewrite /adc_cf Z.pow_1_r; simp.
    rewrite Hpow_s !ds2i_cons Hlenx Hleny in H2. 
    rewrite (_ :   pn * xsn + [::i xn] + (pn * ysn + [::i yn]) + cf0:%Z
                 = pn * (xsn + ysn) + ([::i xn] + [::i yn] + cf0:%Z)) in H2; last ring.
    have Hleq3: [::i xn] + [::i yn] + cf0:%Z <= pn - 1 by lia.
    move: H2. case cfsn; simp.
    + rewrite !Heq_true !Z.leb_le => Hleq.
      have Hleq2: pn * (xsn + ysn) + ([::i xn] + [::i yn] + cf0:%Z)
                  <= pn * (xsn + ysn) + (pn - 1) by lia.
      by nia.
    + rewrite !Heq_false !Z.leb_gt => Hleq1.
      have Hleq2: pn * (xsn + ysn)
                  <= pn * (xsn + ysn) + ([::i xn] + [::i yn] + cf0:%Z) by lia.
      by nia.
  by rewrite -Hcfsn assgn_eqL /Assgn; nia.
+ move: Hcf; rewrite Z.leb_le => Hcf.
  rewrite (_ : (([::i xn] + [::i yn] + cf0:%Z) mod pn)
             = (([::i xn] + [::i yn] + cf0:%Z - pn) mod pn)) in H4; last first.
  + rewrite -/(eqmod_pn _ _) pn_is_0 /eqmod_pn; f_equal; ring.
  rewrite Zmod_small in H4; last by lia.
  split; first done.
  have Hcfsn: cfsn = adc_cf 1 xsn ysn true.
  + rewrite /adc_cf Z.pow_1_r; simp.
    rewrite Hpow_s !ds2i_cons Hlenx Hleny in H2.
    rewrite (_ :   pn * xsn + [::i xn] + (pn * ysn + [::i yn]) + cf0:%Z
                 = pn * (xsn + ysn) + ([::i xn] + [::i yn] + cf0:%Z)) in H2; last ring.
    move: H2. case cfsn; simp.
    + rewrite !Heq_true !Z.leb_le => Hleq.
      have Hleq2: pn * (xsn + ysn) + ([::i xn] + [::i yn] + cf0:%Z) <= pn * (xsn + ysn) + (2*pn - 1).
      + by apply Zplus_le_compat_l; nia.
      by nia.
    + rewrite !Heq_false !Z.leb_gt => Hleq1.
      have Hleq2: pn * (xsn + ysn) + pn <= pn * (xsn + ysn) + ([::i xn] + [::i yn] + cf0:%Z); first lia.
      by nia.
  by rewrite -Hcfsn assgn_eqL /Assgn; nia.
Qed.

End SplitProof.

Ltac split_chainN :=
  match goal with
  | [ H : (?cf_res,(ds2i (?tsn::?ts)))
          <- (adc (S ?N) (ds2i (?xsn::?xs)) (ds2i (?ysn::?ys)) ?cf_in) |- _ ] =>
    move: (@split_chainN N xs ys ts xsn ysn tsn cf_in cf_res); case;
    [ by unfold length | by unfold length | by unfold length
      | by band_auto | by band_auto | by band_auto
      | done | done  | done | apply H | idtac ]
  end.