(* * Experiments for proof *)

(* ** Setup *)
Require Import ZArith.
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
        | [ _ : _ |- ?x <- ?y -> _] =>
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

(* ** Word sizes and general lemmas *)

Definition b2i (b : bool) := if b then 1 else 0.

Notation "b ':%Z'"  := (b2i b) (at level 2, left associativity, format "b ':%Z'").

Notation p64 := (locked (2^64)).
Notation pow n := (p64^(Z.of_nat n)).
Notation p128  := (pow 2).
Notation p192  := (pow 3).
Notation p256  := (pow 4).

Lemma Z_pow_pos_gt0 (n : nat) : 0 < 2 ^ (Z.of_nat n).
Proof.
elim n; first done.
move=> {n} n H1. rewrite Nat2Z.inj_succ Z.pow_succ_r; last apply Nat2Z.is_nonneg.
rewrite (_: 0 = 2 * 0); last done.
by apply Zmult_lt_compat_l.
Qed.

Lemma pow_pos (n : nat) : 0 < pow n.
Proof.
elim n; first done.
move => {n} n Hpos. rewrite Nat2Z.inj_succ Z.pow_succ_r; last apply Nat2Z.is_nonneg.
rewrite (_: 0 = p64 * 0); last ring.
apply Zmult_lt_compat_l; last done.
rewrite (_: 64 = Z.of_nat 64); last done.
by rewrite -lock; apply Z_pow_pos_gt0.
Qed.

Lemma Z_le_leq_succ (x y : Z): x < y <-> x <= y - 1.
Proof.
symmetry. rewrite {2}(_: y = Z.succ (y - 1)); last ring.
split.
+ by apply Zle_lt_succ.
+ by move=> H; apply Zlt_succ_le in H.
Qed.

Lemma pow_ge0 (n : nat): 0 <= pow n.
Proof. apply Z.lt_le_incl. apply pow_pos. Qed.

Lemma p64_ge0: 0 <= p64.
Proof.
apply Z.lt_le_incl. rewrite -(Z.pow_1_r p64) (_ : 1 = Z.of_nat 1); last done.
by apply pow_pos.
Qed.

Lemma Zeq_eq0 (x y : Z): 0 = x - y -> x = y.
Proof. by rewrite -Zeq_plus_swap; move => <-. Qed.

(* ** adc *)

Definition adc_cf (n : nat) (u v : Z) (b : bool) : bool := (pow n) <=? (u + v) + b:%Z.
Definition oflow  (n : nat) (u v : Z) (b : bool) : Z  := (adc_cf n u v b):%Z * (pow n).
Definition adc_v  (n : nat) (u v : Z) (b : bool) : Z  := ((u + v) + b:%Z) - oflow n u v b.
Notation adc n u v b := (adc_cf n u v b, adc_v n u v b).

Lemma b2i_false: false:%Z = 0. Proof. done. Qed.
Lemma b2i_true: true:%Z = 1. Proof. done. Qed.

Definition is_u64 (n : Z) := (0 <=? n) && (n <? p64).

Lemma is_u64K (n : Z): is_true (is_u64 n) <-> ( (0 <= n) /\ (n < p64)).
Proof.
rewrite /is_u64. split.
+ case/andP. rewrite /is_true Z.leb_le Z.ltb_lt. done.
+ case => H1 H2. apply/andP. rewrite /is_true Z.leb_le Z.ltb_lt. done.
Qed.

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

(* ** ds2i: list of digits to integer *)

Fixpoint ds2i (ds : seq Z) :=
  match ds with
  | [::]  => 0
  | d::ds => pow (length ds)*d + ds2i ds
  end.

Notation "[ ::i x0 ]" := (ds2i x0) (at level 0, format "[ ::i  x0 ]").

Notation "[ :i x0 ]" := (ds2i [:: x0]) (at level 0, format "[ :i  x0 ]").

Notation "[ :i x & s ]" := (ds2i (x :: s)) (at level 0, only parsing).

Notation "[ :i x0 , x1 , .. , xn & s ]" := (ds2i (x0 :: x1 :: .. (xn :: s) ..))
  (at level 0, format
  "'[hv' [ :i '['  x0 , '/'  x1 , '/'  .. , '/'  xn ']' '/ '  &  s ] ']'").

Notation "[ :i x0 ; x1 ; .. ; xn ]" := (ds2i (x0 :: x1 :: .. [:: xn] ..))
  (at level 0, format "[ :i '['  x0 ; '/'  x1 ; '/'  .. ; '/'  xn ']' ]").

Lemma ds2i_cons (x : Z) (xs : seq Z) : ds2i [:: x & xs] = pow (length xs)*x + ds2i xs.
Proof. by rewrite //=. Qed.

Lemma ds2i_0 (ds : seq Z) :
  all (fun d => Z.eqb d 0) ds ->  ds2i ds = 0.
Proof.
elim ds; first done.
move=> {ds} d ds Hind Hz. rewrite ds2i_cons.
rewrite //= in Hz. move/andP: Hz => [].
rewrite {1}/is_true Z.eqb_eq => -> Hall. rewrite Z.mul_0_r Z.add_0_l.
by apply Hind.
Qed.

Lemma ds2i_nneg (ds : seq Z):
  all (fun d => is_u64 d) ds ->
  0 <= [::i ds].
Proof.
elim ds; first done.
move=> {ds} d ds Hind. move/andP => [] Hd Hds.
rewrite ds2i_cons.
rewrite (_ : 0 = 0 + 0); last ring.
apply (Z.add_le_mono).
apply (Z.mul_nonneg_nonneg). apply pow_ge0. move/is_u64K : Hd => [] H1 H2. done.
apply (Hind Hds).
Qed.

Lemma ds2i_bounded_lt (n : nat) (ds : seq Z):
  length ds = n ->
  all (fun d => is_u64 d) ds ->
  [::i ds] < pow n.
Proof.
move: ds.
elim n.
+  move=> [] //=.
+ move=> {n} n //= Hind ds //=.
  case ds; first done. move=> {ds} d ds Hlen Hall.
  rewrite //= in Hall. move/andP: Hall => [] His Hall.  
  rewrite //= in Hlen. move: Hlen => [] Hlen.
  move: (Hind ds Hlen Hall). rewrite ds2i_cons Hlen !Z.pow_pos_fold Zpos_P_of_succ_nat.
  rewrite Z.pow_succ_r; last apply Nat2Z.is_nonneg.
  move=> Hlt.
  have H3: pow n * d + [::i ds] < pow n * d + pow n.
  + apply Z.add_le_lt_mono; [ apply Z.eq_le_incl; ring | done].
  apply (Z.lt_le_trans _ _ _ H3).
  move: His.
  rewrite is_u64K. case.
  move=> G1 G2. rewrite (_: p64 = Z.succ (p64 - 1)) in G2; last ring.
  move: (Zlt_succ_le _ _ G2) => G3.
  rewrite (_: pow n * d + pow n = (d + 1) * pow n); last ring.
  apply Z.mul_le_mono_pos_r. apply pow_pos.
  rewrite (_: p64 = p64 - 1 + 1); last ring.
  by apply Z.add_le_mono_r.
Qed.

Lemma ds2i_bounded_le (n : nat) (ds : seq Z):
  length ds = n ->
  all (fun d => is_u64 d) ds ->
  [::i ds] <= pow n - 1.
Proof.
move=> H1 H2. apply Zlt_succ_le. ring_simplify.
by apply ds2i_bounded_lt.
Qed.

(* ** adc with 0 argument *)

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

Ltac band_auto :=
  rewrite //=;
  repeat
    match goal with
    | [ |- is_true (is_u64 _) ] => exact
    | [ |- is_true (_ && _)   ] => apply/andP
    | [ |- _ /\ _              ] => split
    | [ |- is_true true       ] => done
    end.

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
    first [ rewrite Z.mul_0_l in H | rewrite Z.mul_1_l in H
          | rewrite Z.pow_1_r in H | rewrite Z.sub_0_r in H ]
  | [ _ : _ |- _ ]  => rewrite Z.mul_0_l ?Z.sub_0_r ?Z.add_0_r
  end.

Ltac simp :=
  repeat first [ rw_lez | prop_false | prop_0 | prop_var_ctxt | prop_var_goal
               | simp_false | simp_0 | simp_adc_v | simp_cf
               | rewrite Z.pow_1_r | rewrite Z.pow_0_r
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

(* ** Lemmas for splitting *)

Lemma Z_eq_mod (x y n : Z):
  x = y -> x mod n = y mod n.
Proof.
move=> H. by congr (fun x => x mod n).
Qed.

Ltac is_not_mod t :=
  match t with
  | _ mod _ => fail 1
  | _ => idtac
  end.

Ltac push_in_mod_aux T1 T2 N H Lem :=
  is_not_mod T1;
  is_not_mod T2; 
  rewrite (Lem T1 T2 N) in H.

Ltac push_in_mod :=
  match goal with
  | [ H : context[(?T1 + ?T2) mod ?N] |- _ ] => push_in_mod_aux T1 T2 N H Zplus_mod
  | [ H : context[(?T1 - ?T2) mod ?N] |- _ ] => push_in_mod_aux T1 T2 N H Zminus_mod
  | [ H : context[(?T1 * ?T2) mod ?N] |- _ ] => push_in_mod_aux T1 T2 N H Zmult_mod
  end.

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

Ltac mod_simp :=
  match goal with
  | [ H : context[?N mod ?N] |- _ ] => rewrite Z_mod_same_full in H
  | [ H : context[(?N ^ (Z.of_nat (S _))) mod ?N ] |- _ ] =>
    rewrite Z_mod_pow in H
  end.

(*
Ltac not_has_mod t n :=
  match t with
  | _ mod _   => fail 
  | ?T1 + ?T2 => not_has_mod T1; not_has_mod T2
  | ?T1 - ?T2 => not_has_mod T1; not_has_mod T2
  | ?T1 * ?T2 => not_has_mod T1; not_has_mod T2
  | _         => idtac
  end.

Ltac push_out_mod_aux T1 T2 N H Lem :=
  not_has_mod T1;
  not_has_mod T2;
  rewrite -(Lem T1 T2 N) in H.
*)

(*
Ltac push_out_mod :=
  match goal with
  | [ H : context[(?T1 mod ?N + ?T2 mod ?N) mod ?N] |- _ ] =>
    push_out_mod_aux T1 T2 N H Zplus_mod
  | [ H : context[(?T1 mod ?N - ?T2 mod ?N) mod ?N] |- _ ] =>
    push_in_mod_aux T1 T2 N H Zminus_mod
  | [ H : context[(?T1 mod ?N * ?T2 mod ?N) mod ?N] |- _ ] =>
    push_in_mod_aux T1 T2 N H Zmult_mod
  end.
*)

Lemma split_chain1 (x0 y0 x1 y1 t0 t1 : Z) (cf0 cf2 :bool)
  (B_x0: is_u64 x0)
  (B_x1: is_u64 x1)
  (B_y0: is_u64 y0)
  (B_y1: is_u64 y1) : 
  (cf2,[:i t1; t0]) <- adc 2 [:i x1; x0] [:i y1; y0] cf0 ->
  exists cf1,
    (cf1,t0) <- adc 1 x0 y0 cf0 /\
    (cf2,t1) <- adc 1 x1 y1 cf1.
Proof.
move=> H1. rewrite /adc_v /oflow in H1.
move : (assgnKl H1) => H2. rewrite -H2 in H1.
move : (assgnKr H1) => H3. clear H1.
exists (adc_cf 1 x0 y0 cf0).
rewrite /adc_v.
rewrite !ds2i_cons in H3; simp. 
move : (Z_eq_mod p64 H3) => H4.
repeat push_in_mod. repeat mod_simp. repeat push_out_mod.

 simp. rewrite Z_mod_div_pow.
rewrite !Z_mod_same_full in H4.
 repeat push_out_mod.


rewrite Zplus_mod Zminus_mod {1}Zplus_mod in H4.
Search ((_  + _) mod _ = (_ mod _ + _) mod _)%Z.
have H_t0: t0 = x0 + y0 + cf0:%Z - oflow 1 x0 y0 cf0.

split.
+ rewrite /Assgn /oflow. congr pair.
  admit.
+ rewrite /Assgn. congr pair.
  + admit.
  + 
Admitted.

Lemma split_chainN (n : nat) (xn yn tn : seq Z) (xsn ysn tsn : Z) (cf0 cfsn :bool) :
  length xn = n ->
  length yn = n ->
  length tn = n -> 
  all (fun d => is_u64 d) xn ->
  all (fun d => is_u64 d) yn ->
  all (fun d => is_u64 d) tn ->
  (cfsn, [:i tsn & tn]) <- adc (S n) [:i xsn & xn] [:i ysn & yn] cf0 ->
  exists cfn,
    (cfn,[::i tn]) <- adc n [::i xn] [::i yn] cf0 /\
    (cfsn,tsn)     <- adc 1 xsn ysn cfn.
Proof.
Admitted.

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
  (B_0    : is_u64 0)
  (B_38   : is_u64 38) (* FIXME: we should derive bound-facts on constants automatically *)
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
(* combine carry chains *)
pop_defs. combine. sort_defs.
push_defs. case cf3; last first.
+ pop_defs. simp. sort_defs.
  by rewrite (assgnKr L2) (assgnKr L0) /adc_v /oflow -(assgnKl L0); simp.
+ simp. case ccf3; last first.
  + pop_defs. simp.
    rewrite (assgnKr L2) /adc_v /oflow -(assgnKl L2). simp.
    rewrite (assgnKr L0) /adc_v /oflow -(assgnKl L0). simp.
    have Ds2i_simp1: forall xs, [:i 0 & xs] = [::i xs ]; first (move=>xs; rewrite ds2i_cons; ring).
    have Ds2i_simp2: forall x, [:i x] = x. move=>xs; rewrite ds2i_cons. unfold length. unfold ds2i. rewrite Z.pow_0_r. ring.
    apply Zeq_eq0. rewrite !(Ds2i_simp1, Ds2i_simp2). ring.
  + pop_defs. simp.
    rewrite /adc_v /oflow in L4.
    move : (assgnKl L4) => Heq. rewrite -Heq in L4. simp.
    have Heq2: cf_f <- false; last first. simp.
    + rewrite (assgnKr L0) /adc_v in L2.
      rewrite (assgnKr L4).
      rewrite (_ : [:i z3; z2; z1; v0 + 38] = [:i z3; z2; z1; v0] + 38); last first.
      + by rewrite !ds2i_cons Z.pow_0_r; unfold length; ring.
      rewrite (assgnKr L2).
      apply Zeq_eq0. simp. ring_simplify.
      move: (assgnKl L2).
      rewrite /oflow -(assgnKl L0). simp.
      move=> <-. unfold ds2i. unfold length. simp. ring.
    + move: (@split_chainN 3%nat [:: t2; t1; t0] [:: 0; 0; 38] [:: z2; z1; v0] t3 0 z3 false true).
      case; try (rewrite //=; fail). band_auto. band_auto. band_auto.
      move=> cccf2 [] L5 L6.

      move: (@split_chainN 2%nat [:: t1; t0] [:: 0; 38] [:: z1; v0] t2 0 z2 false cccf2).
      case; try (rewrite //=; fail). band_auto. band_auto. band_auto.
      move=> cccf1 [] L7 L8.

      move: (@split_chainN 1%nat [:: t0] [:: 38] [:: v0] t1 0 z1 false cccf1).
      case; try (rewrite //=; fail). band_auto. band_auto. band_auto.
      move=> cccf0 [] L9 L10.
      unfold ds2i in L9. unfold length in L9. rewrite !Z.pow_0_r !Z.mul_1_l !Z.add_0_r in L9.
      push_defs.
      case cccf0; last (pop_defs; simp; done).
      case cccf1; last (pop_defs; simp; done).
      case cccf2; last (pop_defs; simp; done).
      pop_defs. rewrite (assgnKr L10) in Heq.
      rewrite /adc_v /oflow in Heq. simp. rewrite -(assgnKl L10) in Heq.
      simp. rewrite /adc_cf in Heq. move: Heq. case cf_f; last done.
      move=> G. trans_cmp_b. simp.
      have: p64 > t0 + 38 - p64 + 38; last done.
      rewrite (_ : t0 + 38 - p64 + 38 = (t0 - p64) + (38 + 38)); last ring.
      apply (Zgt_trans _ (0 + (38 + 38))).
      apply Z.lt_gt; rewrite -Z.ltb_lt; rewrite -lock //=; done.
      apply Z.lt_gt.
      apply (Z.add_lt_le_mono); first last. apply Z.eq_le_incl. done.
      rewrite (Z.lt_sub_0). move: B_t0. rewrite is_u64K. case. done.
Qed.