(* * Syntax and semantics of the Jasmin source language *)

(* ** Imports and settings *)
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype ssralg.
From mathcomp Require Import word_ssrZ.
Require Import xseq.
Require Export strings warray_ abstract_type.
Import Utf8.

(* ----------------------------------------------------------- *)

Class WithSubWord := { sw_allowed : bool }.

Definition nosubword   := {| sw_allowed := false |}.
Definition withsubword := {| sw_allowed := true |}.

Definition compat_type (sw:bool) :=
  if sw then subtype else eq_op.

Lemma compat_type_refl b ty : compat_type b ty ty.
Proof.  rewrite /compat_type;case: b =>  //=. Qed.
#[global]Hint Resolve compat_type_refl : core.

Lemma compat_type_subtype b t1 t2:
  compat_type b t1 t2 -> subtype t1 t2.
Proof. by case: b  => //=;  destruct (is_not_sabstract t1) => //= /eqP ->. Qed.

Lemma compat_typeE b ty ty' :
  compat_type b ty ty' →
  match ty' with
  | sword sz' =>
    exists2 sz, ty = sword sz & if b then ((sz ≤ sz')%CMP:Prop) else sz' = sz
  | _ => ty = ty'
end.
Proof.
  rewrite /compat_type; case: b => [/subtypeE|/eqP ->]; case: ty' => //.
  + by move=> ws [ws' [*]]; eauto.
  by eauto.
Qed.

Lemma compat_typeEl b ty ty' :
  compat_type b ty ty' →
  match ty with
  | sword sz =>
    exists2 sz', ty' = sword sz' & if b then ((sz ≤ sz')%CMP:Prop) else sz = sz'
  | _ => ty' = ty
  end.
Proof.
  rewrite /compat_type; case: b => [/subtypeEl|/eqP ->].
  + by case: ty => // ws [ws' [*]] ; eauto.
  by case: ty'; eauto  => s; case s ; eauto.
Qed.

(* ----------------------------------------------------------- *)
Definition sem_t (t : stype) : Type :=
  match t with
  | sbool    => bool
  | sint     => Z
  | sarr n   => WArray.array n
  | sword s  => word s
  | sabstract s => Cabstract.iabstract s
  end.

Definition sem_prod ts tr := lprod (map sem_t ts) tr.

Definition sem_ot (t:stype) : Type :=
  if t is sbool then option bool
  else sem_t t.

Definition sem_tuple ts := ltuple (map sem_ot ts).

Fixpoint sem_prod_ok {T: Type} (tin : seq stype) : sem_prod tin T -> sem_prod tin (exec T) :=
  match tin return sem_prod tin T -> sem_prod tin (exec T) with
  | [::] => fun o => ok o
  | t :: ts => fun o v => @sem_prod_ok T ts (o v)
  end.
Arguments sem_prod_ok {T}%_type_scope tin%_seq_scope _.

Fixpoint sem_forall {T: Type} (P: T -> Prop) (tin : seq stype) : sem_prod tin T -> Prop :=
  match tin return sem_prod tin T -> Prop with
  | [::] => P
  | t :: ts => fun o => forall v, @sem_forall T P ts (o v)
  end.
Arguments sem_forall {T}%_type_scope P%_function_scope tin%_seq_scope _.

Lemma sem_prod_ok_ok {T: Type} (tin : seq stype) (o : sem_prod tin T) :
  sem_forall (fun et => exists t, et = ok t) tin (sem_prod_ok tin o).
Proof. elim: tin o => /= [o | a l hrec o v]; eauto. Qed.

Lemma sem_prod_ok_error {T: Type} (tin : seq stype) (o : sem_prod tin T) e :
  sem_forall (fun et => et <> Error e) tin (sem_prod_ok tin o).
Proof. by elim: tin o => /= [o | a l hrec o v]; eauto. Qed.

(* -------------------------------------------------------------------- *)

Notation wmsf := (word msf_size).

(* -------------------------------------------------------------------- *)

Definition curry A B (n: nat) (f: seq (sem_t A) → B) : sem_prod (nseq n A) B :=
  (fix loop n :=
   match n return seq (sem_t A) → sem_prod (nseq n A) B with
   | 0 => f
   | n'.+1 => λ acc a, loop n' (a :: acc)
   end) n [::].

Fixpoint sem_prod_const {A} (lt: seq stype) (a: A) : sem_prod lt A :=
  match lt with
  | [::]     => a
  | _ :: lt' => fun _ => sem_prod_const lt' a
  end.

Definition sem_prod_id (t: stype) : sem_t t -> sem_ot t :=
  if t is sbool
  then Some
  else id.

Fixpoint sem_prod_app {A B} (lt: seq stype) :
  sem_prod lt A -> (A -> B) -> sem_prod lt B :=
  match lt with
  | [::]     => fun a g => g a
  | _ :: lt' => fun f g x => sem_prod_app (f x) g
  end.

(* Construct an n-tuple.
 * Return a t1 -> ... -> tn -> (t1, ..., tn) function where t1, ..., tn are the
 * semantics of a list of stype.
 *)

Definition add_tuple (t:Type) (ts:seq Type) (x:t) (xs:ltuple ts) : ltuple (t::ts) :=
  match ts return ltuple ts -> ltuple (t::ts) with
  | [::] => fun _ => x
  | _::_ => fun xs => (x, xs)
  end xs.

Fixpoint sem_prod_tuple (lt: seq stype) : sem_prod lt (sem_tuple lt) :=
  match lt return sem_prod lt (sem_tuple lt) with
  | [::] => tt
  | t :: lt' =>
      fun v =>
      sem_prod_app (sem_prod_tuple lt') (fun xs => add_tuple (sem_prod_id v) xs)
  end.

Definition sem_prod_cat lt0 lt1 A :
  sem_prod (lt0 ++ lt1) A = sem_prod lt0 (sem_prod lt1 A).
Proof.
  induction lt0 as [|t lt0' IH];
    first done.
  rewrite /sem_prod /=.
  rewrite /sem_prod /= in IH.
  by rewrite IH.
Defined.

Definition add_arguments {A} {lt0 lt1} (f: sem_prod lt0 (sem_prod lt1 A))
  : sem_prod (lt0 ++ lt1) A.
  rewrite sem_prod_cat.
  by apply: f.
Defined.

Lemma add_arguments_nil A lt f: @add_arguments A [::] lt f = f.
Proof. by rewrite /add_arguments /eq_rect_r /=. Qed.

Definition behead_tuple tin tout :
  sem_prod tin (exec (sem_tuple tout))
  -> sem_prod tin (exec (sem_tuple (behead tout))) :=
  match tout
  return sem_prod tin (exec (sem_tuple tout))
         -> sem_prod tin (exec (sem_tuple (behead tout)))
  with
  | [::] =>
      fun f => sem_prod_app f (fun x => Let _ := x in ok tt)
  | t :: tout' =>
      match tout'
      return sem_prod tin (exec (sem_tuple (t :: tout')))
             -> sem_prod tin (exec (sem_tuple tout'))
      with
      | [::] =>
          fun f => sem_prod_app f (fun x => Let _ := x in ok tt)
      | _ =>
          fun f => sem_prod_app f (fun x => Let: (r, p) := x in ok p)
      end
  end.

Section APP.

Context (T : Type) (of_T : forall t : stype, T -> exec (sem_t t)).

Fixpoint app_sopn A ts : sem_prod ts (exec A) → seq T → exec A :=
  match ts return sem_prod ts (exec A) → seq T → exec A with
  | [::] => λ (o : exec A) (vs: seq T), if vs is [::] then o else type_error
  | t :: ts => λ (o: sem_t t → sem_prod ts (exec A)) (vs: seq T),
    if vs is v :: vs
    then Let v := of_T t v in app_sopn (o v) vs
    else type_error
  end.

End APP.
