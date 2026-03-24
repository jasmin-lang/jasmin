(* * Syntax and semantics of the Jasmin source language *)

(* ** Imports and settings *)
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype ssralg.
From mathcomp Require Import word_ssrZ.
Require Import xseq.
Require Export strings type warray_.
Import Utf8.

(* ----------------------------------------------------------- *)

Class WithSubWord := { sw_allowed : bool }.

Definition nosubword   := {| sw_allowed := false |}.
Definition withsubword := {| sw_allowed := true |}.

Definition compat_atype (sw:bool) :=
  if sw then subatype else convertible.

Lemma compat_atype_refl b ty : compat_atype b ty ty.
Proof. by rewrite /compat_atype; case: b. Qed.
#[global]Hint Resolve compat_atype_refl : core.

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

Definition compat_ctype (sw:bool) :=
  if sw then subctype else eq_op.

Lemma compat_ctype_refl b ty : compat_ctype b ty ty.
Proof. by rewrite /compat_ctype; case: b. Qed.
#[global]Hint Resolve compat_ctype_refl : core.

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

Lemma compat_ctypeEl b ty ty' :
  compat_ctype b ty ty' →
  match ty return Prop with
  | cword sz =>
    exists2 sz', ty' = cword sz' & if b then ((sz ≤ sz')%CMP:Prop) else sz = sz'
  | _ => ty = ty'
  end.
Proof.
  rewrite /compat_ctype; case: b => [/subctypeEl|/eqP ->].
  + by case: ty => // ws [ws' [*]]; eauto.
  by case: ty'; eauto.
Qed.

Lemma compat_atype_ctype sw ty1 ty2 :
  compat_atype sw ty1 ty2 ->
  forall env,
    compat_ctype sw (eval_atype env ty1) (eval_atype env ty2).
Proof.
  move=> hc env.
  case: sw hc => /= hc.
  + by apply subatype_subctype.
  apply /eqP.
  by apply convertible_eval_atype.
Qed.

(* ----------------------------------------------------------- *)
Definition sem_t (t : ctype) : Type :=
  match t with
  | cbool    => bool
  | cint     => Z
  | carr n   => WArray.array n
  | cword s  => word s
  end.

Definition sem_prod ts tr := lprod (map sem_t ts) tr.

Definition sem_ot (t:ctype) : Type :=
  if t is cbool then option bool
  else sem_t t.

Definition sem_tuple ts := ltuple (map sem_ot ts).

Fixpoint sem_prod_ok {T: Type} (tin : seq ctype) : sem_prod tin T -> sem_prod tin (exec T) :=
  match tin return sem_prod tin T -> sem_prod tin (exec T) with
  | [::] => fun o => ok o
  | t :: ts => fun o v => @sem_prod_ok T ts (o v)
  end.
Arguments sem_prod_ok {T}%_type_scope tin%_seq_scope _.

Fixpoint sem_forall {T: Type} (P: T -> Prop) (tin : seq ctype) : sem_prod tin T -> Prop :=
  match tin return sem_prod tin T -> Prop with
  | [::] => P
  | t :: ts => fun o => forall v, @sem_forall T P ts (o v)
  end.
Arguments sem_forall {T}%_type_scope P%_function_scope tin%_seq_scope _.

Lemma sem_prod_ok_ok {T: Type} (tin : seq ctype) (o : sem_prod tin T) :
  sem_forall (fun et => exists t, et = ok t) tin (sem_prod_ok tin o).
Proof. elim: tin o => /= [o | a l hrec o v]; eauto. Qed.

Lemma sem_prod_ok_error {T: Type} (tin : seq ctype) (o : sem_prod tin T) e :
  sem_forall (fun et => et <> Error e) tin (sem_prod_ok tin o).
Proof. by elim: tin o => /= [o | a l hrec o v]; eauto. Qed.

Lemma sem_forall_m {T: Type} (P Q: T → Prop) (tin: seq ctype) (o: sem_prod tin T) :
  (∀ t, P t → Q t) →
  sem_forall P tin o →
  sem_forall Q tin o.
Proof. move => ?; elim: tin o => // t ts ih o h /= v; exact: ih. Qed.

(* -------------------------------------------------------------------- *)
Fixpoint collect {A: ctype} (n: nat) : seq (sem_t A) → sem_prod (nseq n A) (seq (sem_t A)) :=
  match n return seq (sem_t A) → sem_prod (nseq n A) (seq (sem_t A)) with
  | 0 => rev
  | S n => λ (acc: seq (sem_t A)) (a : sem_t A), (collect n (a :: acc) : sem_prod (nseq n A) (seq (sem_t A)))
  end.

Lemma size_collect {A} n acc :
  sem_forall (λ x, size x = n + size acc) (nseq n A) (collect n acc).
Proof.
  elim: n acc.
  + by move => acc; rewrite /= size_rev.
  move => n ih acc /= a /=.
  move: ih => /(_ (a :: acc)) /=.
  by apply: sem_forall_m => x; rewrite addSnnS.
Qed.

(* -------------------------------------------------------------------- *)

Notation wmsf := (word msf_size).

(* -------------------------------------------------------------------- *)

Definition curry A B (n: nat) (f: seq (sem_t A) → B) : sem_prod (nseq n A) B :=
  (fix loop n :=
   match n return seq (sem_t A) → sem_prod (nseq n A) B with
   | 0 => f
   | n'.+1 => λ acc a, loop n' (a :: acc)
   end) n [::].

Fixpoint sem_prod_const {A} (lt: seq ctype) (a: A) : sem_prod lt A :=
  match lt with
  | [::]     => a
  | _ :: lt' => fun _ => sem_prod_const lt' a
  end.

Definition sem_prod_id (t: ctype) : sem_t t -> sem_ot t :=
  if t is cbool
  then Some
  else id.

Fixpoint sem_prod_app {A B} (lt: seq ctype) :
  sem_prod lt A -> (A -> B) -> sem_prod lt B :=
  match lt with
  | [::]     => fun a g => g a
  | _ :: lt' => fun f g x => sem_prod_app (f x) g
  end.

(* Construct an n-tuple.
 * Return a t1 -> ... -> tn -> (t1, ..., tn) function where t1, ..., tn are the
 * semantics of a list of ctype.
 *)

Definition add_tuple (t:Type) (ts:seq Type) (x:t) (xs:ltuple ts) : ltuple (t::ts) :=
  match ts return ltuple ts -> ltuple (t::ts) with
  | [::] => fun _ => x
  | _::_ => fun xs => (x, xs)
  end xs.

Fixpoint sem_prod_tuple (lt: seq ctype) : sem_prod lt (sem_tuple lt) :=
  match lt return sem_prod lt (sem_tuple lt) with
  | [::] => tt
  | t :: lt' =>
      fun v =>
      sem_prod_app (sem_prod_tuple lt') (fun xs => add_tuple (sem_prod_id v) xs)
  end.

Section APP.

Context (T : Type) (of_T : forall t : ctype, T -> exec (sem_t t)).

Fixpoint app_sopn A ts : sem_prod ts (exec A) → seq T → exec A :=
  match ts return sem_prod ts (exec A) → seq T → exec A with
  | [::] => λ (o : exec A) (vs: seq T), if vs is [::] then o else type_error
  | t :: ts => λ (o: sem_t t → sem_prod ts (exec A)) (vs: seq T),
    if vs is v :: vs
    then Let v := of_T t v in app_sopn (o v) vs
    else type_error
  end.

End APP.

(* -------------------------------------------------------------------- *)
Lemma sem_forall_prod_app {A B} (f: A → B) (P: A → Prop) (Q: B → Prop) tin x :
  (∀ a, P a → Q (f a)) →
  sem_forall P tin x →
  sem_forall Q tin (sem_prod_app x f).
Proof.
  move => hpq.
  elim: tin x; first by move => x; exact: hpq.
  move => t ts ih o hPo /= v; exact: ih.
Qed.
