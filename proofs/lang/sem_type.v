(* * Syntax and semantics of the Jasmin source language *)

(* ** Imports and settings *)
From mathcomp Require Import all_ssreflect all_algebra.
From CoqWord Require Import ssrZ.
Require Import Psatz xseq.
Require Export strings warray_.
Import Utf8.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition sem_t (t : stype) : Type :=
  match t with
  | sbool    => bool
  | sint     => Z
  | sarr n   => WArray.array n
  | sword s  => word s
  end.

Definition sem_prod ts tr := lprod (map sem_t ts) tr.

Definition sem_ot (t:stype) : Type :=
  if t is sbool then option bool
  else sem_t t.

Definition sem_tuple ts := ltuple (map sem_ot ts).

(* -------------------------------------------------------------------------- *)
Definition is_not_sarr t := ~~ is_sarr t.


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
Fixpoint sem_prod_tuple (lt: seq stype) : sem_prod lt (sem_tuple lt) :=
  match lt return sem_prod lt (sem_tuple lt) with
  | [::] =>
      tt
  | t :: lt' =>
      let f := match lt'
               return sem_prod lt' (sem_tuple lt')
                      -> sem_prod (t :: lt') (sem_tuple (t :: lt'))
               with
               | [::] =>
                   fun _ => @sem_prod_id t
               | _ :: _ =>
                   fun rec_lt' x => sem_prod_app rec_lt' (fun p => (sem_prod_id x, p))
               end in
      f (sem_prod_tuple lt')
  end.

Lemma sem_prod_cat lt0 lt1 A :
  sem_prod (lt0 ++ lt1) A = sem_prod lt0 (sem_prod lt1 A).
Proof.
  induction lt0 as [|t lt0' IH];
    first done.
  rewrite /sem_prod /=.
  rewrite /sem_prod /= in IH.
  by rewrite IH.
Qed.

Definition add_arguments {A} {lt0 lt1} (f: sem_prod lt0 (sem_prod lt1 A))
  : sem_prod (lt0 ++ lt1) A.
  rewrite sem_prod_cat.
  by apply: f.
Defined.

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
