(* -------------------------------------------------------------------- *)
From mathcomp Require Import ssreflect eqtype ssrbool choice ssrfun seq.
Require Export String ZArith pos_map.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* -------------------------------------------------------------------- *)
Scheme Equality for Ascii.ascii.
(* ascii_beq :  Ascii.ascii ->  Ascii.ascii -> bool *)
(* ascii_eq_dec *)

Lemma ascii_eqP : Equality.axiom ascii_beq. 
Proof. 
  move=> x y;apply:(iffP idP).
  + by apply: internal_ascii_dec_bl.
  by apply: internal_ascii_dec_lb.
Qed.

Definition ascii_eqMixin := EqMixin ascii_eqP.
Canonical  ascii_eqType  := EqType Ascii.ascii ascii_eqMixin.

Definition ascii_choiceMixin := CanChoiceMixin Ascii.ascii_nat_embedding.
Canonical  ascii_choiceType  := ChoiceType Ascii.ascii ascii_choiceMixin.

Definition ascii_countMixin := CanCountMixin Ascii.ascii_nat_embedding.
Canonical  ascii_countType  := CountType Ascii.ascii ascii_countMixin.

(* -------------------------------------------------------------------- *)
Scheme Equality for String.string.
(* string_beq is defined
   string_eq_dec is defined *)

Lemma string_eqP : Equality.axiom string_beq. 
Proof. 
  move=> x y;apply:(iffP idP).
  + by apply: internal_string_dec_bl.
  by apply: internal_string_dec_lb.
Qed.

Definition string_eqMixin := EqMixin string_eqP.
Canonical  string_eqType  := EqType string string_eqMixin.

Fixpoint code (s : string) :=
  if s is String a s then a :: code s else [::].

Fixpoint decode (s : seq Ascii.ascii) :=
  if s is a :: s then String a (decode s) else EmptyString.

Lemma codeK : cancel code decode.
Proof. by elim=> //= a s ->. Qed.

Definition string_choiceMixin := CanChoiceMixin codeK.
Canonical  string_choiceType  := ChoiceType string string_choiceMixin.

Definition string_countMixin := CanCountMixin codeK.
Canonical  string_countType  := CountType string string_countMixin.

(* -------------------------------------------------------------------- *)

Definition a2P_app c n := 
  match c with
  | Ascii.Ascii b1 b2 b3 b4 b5 b6 b7 b8 =>
    b2P_app b1 (b2P_app b2 (b2P_app b3 (b2P_app b4
      (b2P_app b5 (b2P_app b6 (b2P_app b7 (b2P_app b8 n)))))))
  end.

Definition a2P c := a2P_app c xH.

Lemma a2P_appP c n : a2P_app c n = FMapPositive.append (a2P c) n.
Proof. by case: c=> * => /=;rewrite !b2P_appP -!appendA. Qed.

Lemma log_a2P c : log_inf (a2P c) = 8%Z.
Proof. by case: c=> * /=;rewrite !log_b2P_app. Qed.

Lemma a2P_app_inj c1 c2 n1 n2 : a2P_app c1 n1 = a2P_app c2 n2 -> c1 = c2 /\ n1 = n2.
Proof. 
  case: c1 => ???? ????; case: c2 => ???? ???? /=.
  by do !(move=> /b2P_app_inj [] ->).
Qed.

Fixpoint s2P_app s n:= 
  match s with
  | EmptyString => n
  | String c s => s2P_app s (a2P_app c n)
  end.

Definition s2P s := s2P_app s xH.

Lemma s2P_appP s n : s2P_app s n = FMapPositive.append (s2P s) n.
Proof. 
  elim: s n => [ | c s Hs] n //=.
  by rewrite /s2P /= !Hs /= a2P_appP -!appendA. 
Qed.
  
Lemma s2P_app_inj s1 s2 n1 n2: 
  log_inf n1 = log_inf n2 ->
  s2P_app s1 n1 = s2P_app s2 n2 -> s1 = s2 /\ n1 = n2.
Proof.
  elim: s1 s2 n1 n2 => [ | c1 s1 Hs1] [ | c2 s2] //= n1 n2 Hlog.
  + move=> Heq;move:Hlog;rewrite Heq.
    rewrite s2P_appP a2P_appP !log_app log_a2P=> ?.
    by have ?:= log_inf_correct1 (s2P s2);omega.
  + move=> Heq;move:Hlog;rewrite -Heq.
    rewrite s2P_appP a2P_appP !log_app log_a2P=> ?.
    by have ?:= log_inf_correct1 (s2P s1);omega.
  move=> /Hs1 [].
  + by rewrite !a2P_appP !log_app !log_a2P Hlog.
  by move=> -> /a2P_app_inj [] -> ->.
Qed.

Lemma s2P_inj : injective s2P.
Proof. by move=> s1 s2;rewrite /s2P => /s2P_app_inj []. Qed.

Module InjString.

  Definition t := [eqType of string].

  Definition t2P := s2P.
 
  Definition t2P_inj := s2P_inj.

End InjString.

Module Ms := Mmake InjString.
