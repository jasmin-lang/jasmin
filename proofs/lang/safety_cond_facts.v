(* * Facts about the language of the safety conditions.

   [safety_cond.v] and [op_semi.v] are in the extraction cone and contain
   definitions only; what is proved about the language, about [mk_sem_op] and
   about the conditions of the library is here. *)

(* ** Imports and settings *)
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq eqtype ssralg.
From mathcomp Require Import word_ssrZ.
Require Import op_semi values.
Import Utf8.

Local Open Scope Z_scope.
Local Open Scope seq_scope.

(* -------------------------------------------------------------------- *)
(* ** Extensionally equal semantics                                      *)

Lemma sem_prod_eq_sym {T} tin (f g : sem_prod tin T) :
  sem_prod_eq tin f g -> sem_prod_eq tin g f.
Proof. by elim: tin f g => /= [f g -> // | t tin ih f g h v]; apply: ih (h v). Qed.

Lemma sem_prod_eq_trans {T} tin (f g h : sem_prod tin T) :
  sem_prod_eq tin f g -> sem_prod_eq tin g h -> sem_prod_eq tin f h.
Proof.
by elim: tin f g h => /= [f g h -> // | t tin ih f g h h1 h2 v]; apply: ih (h1 v) (h2 v).
Qed.

(* Two extensionally equal semantics satisfy the same properties. *)
Lemma sem_forall_eq {T} (P : T -> Prop) tin (f g : sem_prod tin T) :
  sem_prod_eq tin f g -> sem_forall P tin g -> sem_forall P tin f.
Proof.
by elim: tin f g => /= [f g -> // | t tin ih f g heq hg v]; apply: (ih _ _ (heq v) (hg v)).
Qed.

Lemma sem_prod_ok_app_g {A B} tin (x : sem_prod tin A) (g : A -> B) :
  sem_prod_eq tin (sem_prod_ok tin (sem_prod_app x g))
                  (sem_prod_app x (fun a => ok (g a))).
Proof. by elim: tin x => //= t ts ih x v; apply: ih. Qed.

(* Two post-treatments that agree on the results the semantics can produce
   give two equal semantics. *)
Lemma sem_prod_eq_prod_app_ext {A B} (f g : A -> B) (P : A -> Prop) tin x :
  (forall a, P a -> f a = g a) ->
  sem_forall P tin x ->
  sem_prod_eq tin (sem_prod_app x f) (sem_prod_app x g).
Proof. by move=> h; elim: tin x => /= [x /h -> | t ts ih x hx v] //; apply: ih. Qed.

(* [curry] is written with an anonymous [fix]; the statement repeats it so that
   the accumulator can be generalised. *)
Lemma sem_prod_ok_curry_gen (A : ctype) B (f : seq (sem_t A) -> B) n acc :
  sem_prod_eq (nseq n A)
    ((fix loop n := match n return seq (sem_t A) -> sem_prod (nseq n A) (exec B) with
                    | O => fun acc => ok (f acc)
                    | S n' => fun acc a => loop n' (a :: acc) end) n acc)
    (sem_prod_ok (nseq n A)
      ((fix loop n := match n return seq (sem_t A) -> sem_prod (nseq n A) B with
                      | O => f
                      | S n' => fun acc a => loop n' (a :: acc) end) n acc)).
Proof. by elim: n acc => //= n ih acc a; apply: ih. Qed.

Lemma sem_prod_ok_curry (A : ctype) B (f : seq (sem_t A) -> B) n :
  sem_prod_eq (nseq n A) (@curry A (exec B) n (fun vs => ok (f vs)))
              (sem_prod_ok (nseq n A) (@curry A B n f)).
Proof. exact: (sem_prod_ok_curry_gen f n [::]). Qed.

(* -------------------------------------------------------------------- *)
(* ** An operation without condition                                     *)

Lemma mk_semi_aux_id {T} (P : values -> T -> exec T) vs tin (f : sem_prod tin T) :
  (forall vs r, P vs r = ok r) ->
  sem_prod_eq tin (mk_semi_aux P vs tin f) (sem_prod_ok tin f).
Proof. by move=> h; elim: tin vs f => /= [vs f | t tin ih vs f v]; [apply h | apply ih]. Qed.

(* Without condition, [mk_sem_op] is the total semantics. *)
Lemma mk_sem_op_nil tin t err f :
  sem_prod_eq tin (@mk_sem_op tin t [::] err f) (sem_prod_ok tin f).
Proof. by apply: mk_semi_aux_id. Qed.

(* -------------------------------------------------------------------- *)
(* ** What the conditions of the library compute                         *)

Lemma wunsigned_eqb0 ws (w : word ws) : (wunsigned w =? 0)%Z = (w == 0%w).
Proof.
apply/idP/idP => [/ZeqbP h1 | /eqP ->]; last by rewrite wunsigned0; apply/ZeqbP.
by apply/eqP/wunsigned_inj; rewrite h1 wunsigned0.
Qed.

Lemma safety_cond_holds_not_zero ws k (vs : values) (w : word ws) :
  nth undef_b vs k = Vword w -> safety_cond_holds vs (sc_not_zero ws k) = (w != 0%w).
Proof.
by move=> h;
  rewrite /safety_cond_holds /sc_not_zero /sc_neqi /sc_toint /= h /= truncate_word_u /=
          wunsigned_eqb0.
Qed.

Lemma safety_cond_holds_in_range vs lo hi c z :
  sem_safety_cond vs c = ok (Vint z) ->
  safety_cond_holds vs (sc_in_range lo hi c) = (lo <=? z)%Z && (z <=? hi)%Z.
Proof. by rewrite /safety_cond_holds /sc_in_range /sc_and /sc_lei /= => ->. Qed.

Lemma safety_cond_holds_wi_range vs sg sz c z :
  sem_safety_cond vs c = ok (Vint z) ->
  safety_cond_holds vs (sc_wi_range sg sz c) = signed in_uint_range in_sint_range sg sz z.
Proof.
by rewrite /sc_wi_range; case: sg => /= h; rewrite (safety_cond_holds_in_range _ _ h).
Qed.
