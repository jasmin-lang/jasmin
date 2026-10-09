From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype ssralg.
From mathcomp Require Import word_ssrZ.
Require Import xseq.
Require Import strings warray_.
Require Import sem_type.
Require Import type_facts.
Import Utf8.

Lemma convertible_subatype t1 t2 :
  convertible t1 t2 ->
  subatype t1 t2.
Proof.
  case: t1 t2 => [||ws1 n1|ws1] [||ws2 n2|ws2] //=.
  by move=> /eqP [<-].
Qed.

Lemma compat_atype_subatype b t1 t2:
  compat_atype b t1 t2 -> subatype t1 t2.
Proof. by case: b => //=; apply convertible_subatype. Qed.

Lemma compat_atypeE b ty ty' :
  compat_atype b ty ty' →
  match ty' return Prop with
  | aword sz' =>
    exists2 sz, ty = aword sz & if b then ((sz ≤ sz')%CMP:Prop) else sz' = sz
  | _ => convertible ty ty'
end.
Proof.
  rewrite /compat_atype; case: b => [/subatypeE|]; case: ty' => //.
  + by move=> ws [ws' [*]]; eauto.
  move=> ws'.
  case: ty => //= ws /eqP [->].
  by eauto.
Qed.

Lemma compat_atypeEl b ty ty' :
  compat_atype b ty ty' →
  match ty return Prop with
  | aword sz =>
    exists2 sz', ty' = aword sz' & if b then ((sz ≤ sz')%CMP:Prop) else sz = sz'
  | _ => convertible ty ty'
  end.
Proof.
  rewrite /compat_atype; case: b => [/subatypeEl|].
  + by case: ty => // ws [ws' [*]]; eauto.
  case: ty => //= ws /eqP <-.
  by eauto.
Qed.

Lemma compat_ctype_subctype b t1 t2:
  compat_ctype b t1 t2 -> subctype t1 t2.
Proof. by case: b => //= /eqP ->. Qed.

Lemma compat_ctypeE b ty ty' :
  compat_ctype b ty ty' →
  match ty' with
  | cword sz' =>
    exists2 sz, ty = cword sz & if b then ((sz ≤ sz')%CMP:Prop) else sz' = sz
  | _ => ty = ty'
end.
Proof.
  rewrite /compat_ctype; case: b => [/subctypeE|/eqP ->]; case: ty' => //.
  + by move=> ws [ws' [*]]; eauto.
  by eauto.
Qed.

Lemma compat_atype_ctype sw ty1 ty2 :
  compat_atype sw ty1 ty2 ->
  compat_ctype sw (eval_atype ty1) (eval_atype ty2).
Proof.
  case: sw => /=.
  + by apply subatype_subctype.
  move=> hconv; apply /eqP; move: hconv.
  by apply convertible_eval_atype.
Qed.

Lemma sem_prod_ok_ok {T: Type} (tin : seq ctype) (o : sem_prod tin T) :
  sem_forall (fun et => exists t, et = ok t) tin (sem_prod_ok tin o).
Proof. elim: tin o => /= [o | a l hrec o v]; eauto. Qed.

Lemma sem_forall_m {T: Type} (P Q: T → Prop) (tin: seq ctype) (o: sem_prod tin T) :
  (∀ t, P t → Q t) →
  sem_forall P tin o →
  sem_forall Q tin o.
Proof. move => ?; elim: tin o => // t ts ih o h /= v; exact: ih. Qed.

Lemma size_collect {A} n acc :
  sem_forall (λ x, size x = n + size acc) (nseq n A) (collect n acc).
Proof.
  elim: n acc.
  + by move => acc; rewrite /= size_rev.
  move => n ih acc /= a /=.
  move: ih => /(_ (a :: acc)) /=.
  by apply: sem_forall_m => x; rewrite addSnnS.
Qed.

Lemma sem_forall_prod_app {A B} (f: A → B) (P: A → Prop) (Q: B → Prop) tin x :
  (∀ a, P a → Q (f a)) →
  sem_forall P tin x →
  sem_forall Q tin (sem_prod_app x f).
Proof.
  move => hpq.
  elim: tin x; first by move => x; exact: hpq.
  move => t ts ih o hPo /= v; exact: ih.
Qed.
