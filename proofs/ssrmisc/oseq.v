(* -------------------------------------------------------------------- *)
From Coq Require Setoid.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq eqtype.

(* -------------------------------------------------------------------- *)
Lemma pmap_idfun_some {T : Type} (s : seq T) :
  pmap idfun [seq Some x | x <- s] = s.
Proof. by elim: s => /= [|x s ->]. Qed.

(* -------------------------------------------------------------------- *)
Notation ocons x := (omap (cons x)).

(* -------------------------------------------------------------------- *)
Section ONth.
Context {T : Type}.

Fixpoint onth (s : seq T) (i : nat) :=
  if s is x :: s' then
    if i is i'.+1 then onth s' i' else Some x
  else None.

Lemma onth_nth s i : onth s i = nth None (map Some s) i.
Proof. by elim: s i => [|x s ih] [|i] /=. Qed.
End ONth.

(* -------------------------------------------------------------------- *)
Lemma onthP {T : eqType} (x0 : T) s i v :
  reflect
    (onth s i = Some v)
    ((i < size s) && (nth x0 s i == v)).
Proof.
rewrite onth_nth; case: ltnP => /= [lt_is|]; last first.
+ by constructor; rewrite nth_default //= size_map.
by rewrite (nth_map x0) //; apply: (iffP eqP) => [<-|[]].
Qed.

(* -------------------------------------------------------------------- *)
Lemma onth_default {T : Type} (s : seq T) i :
  i >= size s -> onth s i = None.
Proof. by move=> le_si; rewrite onth_nth nth_default ?size_map. Qed.

(* -------------------------------------------------------------------- *)
Lemma onth_sizeP {T : eqType} (x0 : T) s i v : i < size s ->
  (onth s i == Some v) = (nth x0 s i == v).
Proof.
move=> lt_is; apply/eqP/eqP.
+ by move/onthP => /(_ x0); rewrite lt_is => /eqP.
+ by move=> h; apply/(onthP x0); rewrite lt_is; apply/eqP.
Qed.

(* -------------------------------------------------------------------- *)
Lemma onth_nth_size {T: eqType} (x0: T) s i :
  i < size s ->
  onth s i = Some (nth x0 s i).
Proof.
by move => sz; apply/eqP; rewrite (onth_sizeP x0).
Qed.

(* -------------------------------------------------------------------- *)
Lemma onth_cat T (s1 s2 : seq T) n :
  onth (s1 ++ s2) n = (if n < size s1 then onth s1 n else onth s2 (n - size s1)).
Proof. by rewrite !onth_nth map_cat nth_cat size_map. Qed.

(* -------------------------------------------------------------------- *)
Section OSeq.
Context {T : Type}.

Definition oseq (s : seq (option T)) :=
  if size s == size (pmap idfun s) then Some (pmap idfun s) else None.

Lemma oseq_nil : oseq [::] = Some [::].
Proof. by []. Qed.

Lemma oseq_cons x s :
  oseq (x :: s) = obind (fun x => ocons x (oseq s)) x.
Proof.
rewrite /oseq; case: x => [x|] /=.
+ by rewrite eqSS; case: eqP.
+ by rewrite gtn_eqF // ltnS size_pmap; apply/count_size.
Qed.
End OSeq.

(* -------------------------------------------------------------------- *)
Lemma oseqP {T : eqType} (s : seq (option T)) (u : seq T) :
  (oseq s == Some u) = (s == [seq Some x | x <- u]).
Proof.
apply/eqP/eqP=> [|->] //; last first.
+ by rewrite /oseq pmap_idfun_some size_map eqxx.
rewrite /oseq; case: ifP=> // /eqP eqsz [<-].
rewrite pmapS_filter map_id -{1}[s]filter_predT.
apply: eq_in_filter=> x x_in_s /=; move/esym/eqP: eqsz.
by rewrite size_pmap -all_count => /allP /(_ _ x_in_s).
Qed.

(* -------------------------------------------------------------------- *)
Section OMap.
Context {T U : Type} (f : T -> option U).

Fixpoint omap (s : seq T) :=
  if s is x :: s' then
    if f x is Some y then ssrfun.omap (cons y) (omap s') else None
  else Some [::].
End OMap.

(* -------------------------------------------------------------------- *)
Notation "[ 'oseq' E | i <- s ]" := (omap (fun i => E) s)
  (at level 0, E at level 99, i ident,
   format "[ '[hv' 'oseq'  E '/ '  |  i  <-  s ] ']'") : seq_scope.

Notation "[ 'oseq' E | i : T <- s ]" := (omap (fun i : T => E) s)
  (at level 0, E at level 99, i ident, only parsing) : seq_scope.

(* -------------------------------------------------------------------- *)

Declare Scope option_scope.
Delimit Scope option_scope with O.

Notation "m >>= f" := (ssrfun.Option.bind f m)
  (at level 58, left associativity) : option_scope.

Local Open Scope option_scope.

(* -------------------------------------------------------------------- *)

Lemma obindI {T1 T2:Type} {f:T1 -> option T2} {o t2} :
  (o >>= f) = Some t2 -> exists t1, o = Some t1 /\ f t1 = Some t2.
Proof. by case: o => [t1|]//=;exists t1. Qed.
