(* * Syntax and semantics of the Jasmin source language *)

(* ** Imports and settings *)
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype ssralg.
From mathcomp Require Import word_ssrZ.
Require Import xseq.
Require Export strings warray_.
Import Utf8.

(* ----------------------------------------------------------- *)

Class WithSubWord := { sw_allowed : bool }.

Definition nosubword   := {| sw_allowed := false |}.
Definition withsubword := {| sw_allowed := true |}.

(* TODO: move compat_type to type? *)
Section CONV.

Context {len:eqType} (conv : len -> len -> bool).

Definition compat_type_gen (sw:bool) :=
  if sw then subtype_gen conv else convertible_gen conv.

(* TODO: try to not declare stype as eqType? to be sure we never use eq_op *)
Lemma compat_type_gen_refl b ty : Reflexive conv -> compat_type_gen b ty ty.
Proof.
  move=> conv_refl; rewrite /compat_type_gen.
  case: b.
  + by apply subtype_gen_refl.
  by apply convertible_gen_refl.
Qed.
(* #[global]Hint Resolve compat_type_gen_refl : core. *)

(*
Instance fd : Equivalence convertible.
Proof.
  split.
  - move=> ?. apply convertible_refl.
  - move=> ??. apply convertible_sym.
  - move=> ???. apply convertible_trans.
Defined.

Instance to : Equivalence conv -> Proper (convertible_gen conv ==> convertible_gen conv ==> eq) (subtype_gen conv).
Proof.
  move=> conv_trans.
  move=> ty11 ty12 eq_ty1 ty21 ty22 eq_ty2.
  case: ty11 ty12 ty21 ty22 eq_ty1 eq_ty2 => [||?|ws11] [||?|ws12] [||?|ws21] [||?|ws22] //=.
  + move=> h1 h2. apply /idP/idP. move=> h3. do 2 (etransitivity; try eassumption). symmetry. eassumption.
   move=> h3. do 2 (etransitivity; try eassumption). symmetry. eassumption.
  
(*    by move=> /eqP -> /eqP ->. *)
  move=> /eqP [] -> /eqP [] ->.
  done.
Qed. *)

Lemma convertible_gen_subtype_gen ty1 ty2 :
  convertible_gen conv ty1 ty2 -> subtype_gen conv ty1 ty2.
Proof.
  case: ty1 ty2 => [||len1|ws1] [||len2|ws2] //=.
  by move=> /eqP [<-].
Qed.

Lemma compat_type_gen_subtype_gen b t1 t2:
  compat_type_gen b t1 t2 -> subtype_gen conv t1 t2.
Proof.
  case: b => //=.
  by apply convertible_gen_subtype_gen.
Qed.

Lemma compat_type_genE b ty ty' :
  compat_type_gen b ty ty' →
  match ty' return Prop with
  | sword sz' =>
    exists2 sz, ty = sword sz & if b then ((sz ≤ sz')%CMP:Prop) else sz' = sz
  | _ => convertible_gen conv ty ty'
end.
Proof.
  rewrite /compat_type_gen; case: b => [/subtype_genE|]; case: ty' => //.
  + by move=> ws [ws' [*]]; eauto.
  move=> ws'.
  case: ty => //= ws /eqP [->].
  by eauto.
Qed.

Lemma compat_type_genEl b ty ty' :
  compat_type_gen b ty ty' →
  match ty return Prop with
  | sword sz =>
    exists2 sz', ty' = sword sz' & if b then ((sz ≤ sz')%CMP:Prop) else sz = sz'
  | _ => convertible_gen conv ty ty'
  end.
Proof.
  rewrite /compat_type_gen; case: b => [/subtype_genEl|].
  + by case: ty => // ws [ws' [*]]; eauto.
  case: ty => //= ws /= /eqP <-.
  by eauto.
Qed.

End CONV.

Definition compat_atype b (t t' : atype) :=
  compat_type_gen (fun '(ws1, len1) '(ws2, len2) => arr_size ws1 len1 == arr_size ws2 len2) b t t'.

Definition compat_ctype b (t t' : ctype) :=
  compat_type_gen eq_op b t t'.

Lemma convertible_c_eq (ty1 ty2 : ctype) : convertible_gen eq_op ty1 ty2 -> ty1 = ty2.
Proof.
  case: ty1 ty2 => [||len1|ws1] [||len2|ws2] //=.
  + by move=> /eqP ->.
  by move=> /eqP [->].
Qed.

Lemma compat_atypeE b ty ty' :
  compat_atype b ty ty' →
  match ty' return Prop with
  | sword sz' =>
    exists2 sz, ty = sword sz & if b then ((sz ≤ sz')%CMP:Prop) else sz' = sz
  | _ => convertible ty ty'
  end.
Proof.
  exact: compat_type_genE.
Qed.

Lemma compat_atypeEl b ty ty' :
  compat_atype b ty ty' →
  match ty return Prop with
  | sword sz =>
    exists2 sz', ty' = sword sz' & if b then ((sz ≤ sz')%CMP:Prop) else sz = sz'
  | _ => convertible ty ty'
  end.
Proof. exact: compat_type_genEl. Qed.

Lemma compat_atype_refl b ty : compat_atype b ty ty.
Proof. apply compat_type_gen_refl. by move=> [??]. Qed.
#[global]Hint Resolve compat_atype_refl : core.

Lemma compat_atype_subatype b ty1 ty2 : compat_atype b ty1 ty2 -> subatype ty1 ty2.
Proof. exact: compat_type_gen_subtype_gen. Qed.

Lemma compat_ctypeE b ty ty' :
  compat_ctype b ty ty' →
  match ty' return Prop with
  | sword sz' =>
    exists2 sz, ty = sword sz & if b then ((sz ≤ sz')%CMP:Prop) else sz' = sz
  | _ => ty = ty'
  end.
Proof.
  move=> /compat_type_genE.
  by case: ty' => [||len'|ws'] //= /convertible_c_eq.
Qed.

Lemma compat_ctypeEl b ty ty' :
  compat_ctype b ty ty' →
  match ty return Prop with
  | sword sz =>
    exists2 sz', ty' = sword sz' & if b then ((sz ≤ sz')%CMP:Prop) else sz = sz'
  | _ => ty = ty'
  end.
Proof.
Proof.
  move=> /compat_type_genEl.
  by case: ty => [||len|ws] // /convertible_c_eq.
Qed.

Lemma compat_ctype_refl b ty : compat_ctype b ty ty.
Proof. exact: compat_type_gen_refl. Qed.
#[global]Hint Resolve compat_ctype_refl : core.

Lemma compat_ctype_subctype b ty1 ty2 : compat_ctype b ty1 ty2 -> subctype ty1 ty2.
Proof. exact: compat_type_gen_subtype_gen. Qed.

(* ----------------------------------------------------------- *)
Definition sem_t (t : ctype) : Type :=
  match t with
  | sbool     => bool
  | sint      => Z
  | sarr n    => WArray.array n
  | sword s   => word s
  end.

Definition sem_prod ts tr := lprod (map sem_t ts) tr.

Definition sem_ot (t:ctype) : Type :=
  if t is sbool then option bool
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
  if t is sbool
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
 * semantics of a list of stype.
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
