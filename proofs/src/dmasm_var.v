(* * Syntax and semantics of the dmasm source language *)

(* ** Imports and settings *)
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat ssrint ssralg tuple.
From mathcomp Require Import choice fintype eqtype div seq zmodp.
Require Import strings dmasm_utils dmasm_type.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.

Open Scope string_scope.
Local Open Scope ring_scope.

(* ** Types for idents 
 * -------------------------------------------------------------------- *)

Definition ident := string.

Module Mid := Ms.

(* ** Dependent Type for variables 
 * -------------------------------------------------------------------- *)

Record var := Var { vtype : stype; vname : ident }.

Definition var2pair v := (v.(vtype), v.(vname)).
Definition pair2var p := Var (fst p) (snd p).
Lemma codeK_var : cancel var2pair pair2var. Proof. by rewrite /cancel; case => //. Qed.
Definition var_eqMixin     := comparableClass (@LEM var).
Canonical  var_eqType      := Eval hnf in EqType var var_eqMixin.
Definition var_choiceMixin := CanChoiceMixin codeK_var.
Canonical  var_choiceType  := ChoiceType var var_choiceMixin.

(* ** Variable map
 * -------------------------------------------------------------------- *)

Module Mv.

  Import DMst Mid.
  Record t (to:stype -> Type) := MkT {
    dft : forall x,to x.(vtype);
    map : DMst.t (fun ty => Ms.t (to ty));
  }.

  Definition empty {to} (dft : forall x, to x.(vtype)) : t to := {|
     dft := dft;
     map := DMst.empty _;
  |}.

  Definition get {to} (m: t to) (x:var) : to x.(vtype) := 
    match (m.(map).[x.(vtype)])%dms with 
    | Some mi => 
      match (mi.[x.(vname)])%ms with 
      | Some v => v
      | None   => m.(dft) x
      end
    | None =>  m.(dft) x
    end.

  Definition set {to} (m: t to) (x:var) (v:to x.(vtype)) : t to :=
    let mi := 
      match (m.(map).[x.(vtype)])%dms with 
      | Some mi => mi
      | None    => Mid.empty _ 
      end in
    let mi := (mi.[x.(vname) <- v])%ms in
    {| dft := m.(dft);
       map := (m.(map).[x.(vtype) <- mi])%dms; |}.

  Lemma get0 {to} (dft: forall x, to x.(vtype)) (x:var) : get (empty dft) x = dft x.
  Proof. by rewrite /empty /get DMst.get0. Qed.

  Lemma setP_eq {to} (m:t to) (x:var) (v:to x.(vtype)) : get (@set to m x v) x = v.
  Proof. by rewrite /set /get DMst.setP_eq Mid.setP_eq. Qed.

  Lemma setP_neq {to} (m:t to) x y (v:to x.(vtype)) : x != y ->  get (@set to m x v) y = get m y.
  Proof.  
    move=> neq;rewrite /set /get.
    case : (boolP ((vtype x) == (vtype y))) => [/eqP eq | ?] /=;last by rewrite DMst.setP_neq.
    move: v;rewrite eq => v; rewrite DMst.setP_eq Mid.setP_neq.
    + by case: (_.[_])%dms => //; rewrite Mid.get0.
    by apply: contra neq; case: x y eq {v}=> tx sx [] ty sy /= -> /eqP ->.
  Qed.

End Mv.

Delimit Scope mvar_scope with mv.
Local Open Scope mvar_scope.
Notation "vm .[ x ]" := (@Mv.get _ vm x) : mvar_scope.

Reserved Notation "x .[ k <- v ]"
     (at level 2, k at level 200, v at level 200, format "x .[ k  <-  v ]").

Notation "vm .[ x  <- v ]" := (@Mv.set _ vm x v) : mvar_scope.

