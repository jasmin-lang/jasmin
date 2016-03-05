(* -------------------------------------------------------------------- *)
From mathcomp Require Import ssreflect eqtype ssrbool choice ssrfun seq.
Require Export String.
Require Import ZArith.

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

(* Map from string *)

Definition cons_bit b n := 
  if b then xO n else xI n.

Definition ascii_toN c n := 
  match c with
  | Ascii.Ascii b1 b2 b3 b4 b5 b6 b7 b8 =>
    cons_bit b1 (cons_bit b2 (cons_bit b3 (cons_bit b4
      (cons_bit b5 (cons_bit b6 (cons_bit b7 (cons_bit b8 n)))))))
  end.

Fixpoint stoN_aux s n:= 
  match s with
  | EmptyString => n
  | String c s => stoN_aux s (ascii_toN c n)
  end.

Definition stoN s := stoN_aux s xH.

Lemma cons_bit_lt b p : (log_inf p < log_inf (cons_bit b p))%Z.
Proof.
  case:b=> /=; apply Z.lt_succ_diag_r.
Qed.

Lemma ascii_toN_lt c p: (log_inf p < log_inf (ascii_toN c p))%Z.
Proof.
  case: c => ???????? /=.
  have H : forall b p1, (log_inf p < log_inf p1 -> log_inf p < log_inf (cons_bit b p1))%Z.
  + move=> b p1 H;apply: (Z.lt_trans _ (log_inf p1))=>//;apply cons_bit_lt.
  do 7!apply H; apply cons_bit_lt.
Qed.

Lemma stoN_aux_le s p: (log_inf p <= log_inf (stoN_aux s p))%Z.
Proof.
  elim: s p=> [ | c s Hs] p /=;first by apply Z.le_refl.
  apply: Z.le_trans (Hs (ascii_toN c p)).
  apply Z.lt_le_incl;apply ascii_toN_lt.
Qed.

Lemma stoN_neq s c p1 p2: log_inf p1 = log_inf p2 -> p1 <> stoN_aux s (ascii_toN c p2).
Proof.
  move=> Hlog Heq. apply (Z.lt_irrefl (log_inf p1));rewrite {2}Heq.
  apply (Z.lt_le_trans _ (log_inf (ascii_toN c p2))).
  + by rewrite Hlog; apply ascii_toN_lt.
  apply stoN_aux_le.  
Qed.

Lemma log_ascii c p : log_inf (ascii_toN c p) = (8 + log_inf p)%Z.
Proof.
  case: c => *;rewrite /ascii_toN.
  have H: forall b p, log_inf (cons_bit b p) = Z.succ (log_inf p).
  + by move=> [] p1;rewrite /cons_bit //.
  rewrite !H;omega.
Qed.

Lemma ascii_toN_inj c1 p1 c2 p2: ascii_toN c1 p1 = ascii_toN c2 p2 -> c1 = c2 /\ p1 = p2.
Proof.
  move: c1 c2=> [] ???????? [] ???????? /=.
  have H : forall b p b' p',  cons_bit b p = cons_bit b' p' -> b = b' /\ p = p'.
  + by move=> [] ? [] ? => //= -[].
  by do !move=> /H [] ->.
Qed.

Lemma stoN_inj : injective stoN.
Proof.
  move=> s1 s2;rewrite /stoN.
  have H: forall p1 p2, log_inf p1 = log_inf p2 -> 
         stoN_aux s1 p1 = stoN_aux s2 p2 -> s1 = s2 /\ p1 = p2.
  + elim: s1 s2=> [ | c1 s1 Hs1] [ | c2 s2] //= p1 p2.
    + by move=> /(@stoN_neq s2 c2).
    + by move=> /esym /(@stoN_neq s1 c1) ? /esym.
    move=> Heq /Hs1 /=;rewrite !log_ascii Z.add_cancel_l => -[] // ->.
    by move=> /ascii_toN_inj []-> ->.
  by move=> /H [].  
Qed.

Require Import FMapPositive.

Module Ms.

  Definition t (T:Type) := PositiveMap.t T.

  Definition empty {T} : t T := PositiveMap.empty T.

  Definition get {T} (m: t T) (s:string) := PositiveMap.find (stoN s) m. 

  Definition set {T} (m: t T) (s:string) (t:T) := PositiveMap.add (stoN s) t m.

  Delimit Scope smap_scope with ms.
  Local Open Scope smap_scope.
  Notation "m .[ s ]" := (get m s): smap_scope.
  Reserved Notation "x .[ k <- v ]"
     (at level 2, k at level 200, v at level 200, format "x .[ k  <-  v ]").

  Notation "x .[ k <- v ]" := (set x k v) : smap_scope.
  
  Lemma setP {T} m x y (v:T) : m.[x <- v].[y] = if x == y then Some v else m.[y].
  Proof.
    case eqP=> [-> | Hdiff];first by apply PositiveMap.gss.
    by apply PositiveMap.gso=> /stoN_inj /esym.
  Qed.

  Lemma setP_eq {T} m x (v:T) : m.[x <- v].[x] = Some v.
  Proof. by rewrite setP eq_refl. Qed.

  Lemma setP_neq {T} m x y (v:T) : x <> y -> m.[x <- v].[y] = m.[y].
  Proof. by rewrite setP=> /eqP /negPf ->. Qed.

End Ms.
