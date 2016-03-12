(* * Syntax and semantics of the dmasm source language *)

(* ** Imports and settings *)
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat ssrint ssralg tuple.
From mathcomp Require Import choice fintype eqtype div seq zmodp.
Require Import pos_map strings dmasm_utils dmasm_type.

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

(* ** Type for variables 
 * -------------------------------------------------------------------- *)

Record var := Var { vtype : stype; vname : ident }.

Definition var_beq (v1 v2:var) :=
  let (t1,n1) := v1 in
  let (t2,n2) := v2 in
  (t1 == t2) && (n1 == n2).

Lemma var_eqP : Equality.axiom var_beq. 
Proof. 
  move=> [t1 n1] [t2 n2];apply:(iffP idP) => /= [/andP[]/eqP->/eqP->| []->->] //.
  by rewrite !eq_refl.
Qed.

Definition var_eqMixin := EqMixin var_eqP.
Canonical  var_eqType  := EqType var var_eqMixin.

Definition var2pair v := (v.(vtype), v.(vname)).
Definition pair2var p := Var (fst p) (snd p).

Lemma codeK_var : cancel var2pair pair2var. Proof. by rewrite /cancel; case => //. Qed.
Definition var_choiceMixin := CanChoiceMixin codeK_var.
Canonical  var_choiceType  := ChoiceType var var_choiceMixin.

(* ** Right values
 * -------------------------------------------------------------------- *)

Inductive rval : stype -> Set :=
| Rvar  :> forall (x:var), rval x.(vtype)
| Rpair :  forall st1 st2, rval st1 -> rval st2 -> rval (st1 ** st2).

(* ** Module type for variables map 
 * -------------------------------------------------------------------- *)

Module Type Vmap.

  Parameter t : (stype -> Type) -> Type.

  Parameter empty : forall to, (forall x, to x.(vtype)) -> t to.

  Parameter get : forall {to}, t to -> forall (x:var), to x.(vtype).
  
  Parameter set : forall {to}, t to -> forall (x:var), to x.(vtype) -> t to.

  Parameter get0 : 
    forall {to} (dft: forall x, to x.(vtype)) (x:var), 
      get (empty dft) x = dft x.

  Parameter setP_eq :
    forall {to} (m:t to) (x:var) (v:to x.(vtype)), 
      get (@set to m x v) x = v.

  Parameter setP_neq : 
    forall {to} (m:t to) x y (v:to x.(vtype)), 
      x != y -> get (@set to m x v) y = get m y.

End Vmap.

(* ** Variables map, to be used when computation is needed
 * -------------------------------------------------------------------- *)
Module Mv <: Vmap.

  Import DMst Mid.
  Record rt_ (to:stype -> Type) := MkT {
    dft : forall x,to x.(vtype);
    map : DMst.t (fun ty => Ms.t (to ty));
  }.

  Definition t := rt_.

  Definition empty {to} (dft : forall x, to x.(vtype)) : t to := {|
     dft := dft;
     map := DMst.empty _;
  |}.

  Definition get {to} (m: t to) (x:var) : to x.(vtype) := 
    match (m.(map).[x.(vtype)])%mt with 
    | Some mi => 
      match (mi.[x.(vname)])%ms with 
      | Some v => v
      | None   => m.(dft) x
      end
    | None =>  m.(dft) x
    end.

  Definition set {to} (m: t to) (x:var) (v:to x.(vtype)) : t to :=
    let mi := 
      match (m.(map).[x.(vtype)])%mt with 
      | Some mi => mi
      | None    => Mid.empty _ 
      end in
    let mi := (mi.[x.(vname) <- v])%ms in
    {| dft := m.(dft);
       map := (m.(map).[x.(vtype) <- mi])%mt; |}.

  Lemma get0 {to} (dft: forall x, to x.(vtype)) (x:var) : get (empty dft) x = dft x.
  Proof. by rewrite /empty /get DMst.get0. Qed.

  Lemma setP_eq {to} (m:t to) (x:var) (v:to x.(vtype)) : get (@set to m x v) x = v.
  Proof. by rewrite /set /get DMst.setP_eq Mid.setP_eq. Qed.

  Lemma setP_neq {to} (m:t to) x y (v:to x.(vtype)) : x != y ->  get (@set to m x v) y = get m y.
  Proof.  
    move=> neq;rewrite /set /get.
    case : (boolP ((vtype x) == (vtype y))) => [/eqP eq | ?] /=;last by rewrite DMst.setP_neq.
    move: v;rewrite eq => v; rewrite DMst.setP_eq Mid.setP_neq.
    + by case: (_.[_])%mt => //; rewrite Mid.get0.
    by apply: contra neq; case: x y eq {v}=> tx sx [] ty sy /= -> /eqP ->.
  Qed.

End Mv.

Delimit Scope mvar_scope with mv.
Notation "vm .[ x ]" := (@Mv.get _ vm x) : mvar_scope.
Notation "vm .[ x  <- v ]" := (@Mv.set _ vm x v) : mvar_scope.
Arguments Mv.get to m%mvar_scope x.
Arguments Mv.set to m%mvar_scope x v.

(* ** Variables function: to be not used if computation is needed, 
 *                       but extentianality is permited 
 * -------------------------------------------------------------------- *)

Module Fv <: Vmap.
  Record rt_ (to : stype -> Type) := Vmap {
    map : forall x, to x.(vtype)
  }.

  Definition t := rt_.

  Definition empty {to} dval : t to := {| map := dval |}.

  Definition get {to} (vm : t to) x := nosimpl (vm.(map) x).

  Definition set {to:stype -> Type} (vm : t to) x (v : to x.(vtype)) : t to :=
    nosimpl ( 
    Vmap (fun y =>
      match (x =P y) with
      | ReflectT eq => eq_rect x (fun x => to x.(vtype)) v y eq
      | _           => vm.(map) y
      end)).

  Lemma get0 to dval x: @get to (empty dval) x = dval x.
  Proof. done. Qed.
    

  Lemma setP_eq to (vm:t to) x (v:to x.(vtype)) : 
    get (@set _ vm x v) x = v.
  Proof.
    rewrite /get /set /=;case: eqP => // p.
    by rewrite (eq_irrelevance p (erefl x)).
  Qed.

  Lemma setP_neq to (vm:t to) x y (v:to x.(vtype)) : 
    x != y ->
    get (@set _ vm x v) y = get vm y.
  Proof. by rewrite /get /set /=;case: eqP. Qed.

  Definition ext_eq  {to} (vm1 vm2 : t to) :=
    forall x, get vm1 x = get vm2 x.

  Axiom map_ext: forall to (vm1 vm2 : t to), ext_eq vm1 vm2 -> vm1 = vm2.

End Fv.

Delimit Scope vmap_scope with vmap.
Notation "vm .[ id ]" := (Fv.get vm id) : vmap_scope.
Notation "vm .[ k  <- v ]" := (@Fv.set _ vm k v) : vmap_scope.
Notation "vm1 =v vm2" := (Fv.ext_eq vm1 vm2) (at level 70, no associativity) : vmap_scope.
Arguments Fv.get to vm%vmap_scope x.
Arguments Fv.set to vm%vmap_scope x v.
Arguments Fv.ext_eq to vm1%vmap_scope vm2%vmap_scope.

Module Type WrInp.

  Parameter to : stype -> Type.
  Parameter fst : forall {t1 t2:stype}, to (t1 ** t2) -> to t1.
  Parameter snd : forall {t1 t2:stype}, to (t1 ** t2) -> to t2.
  
End WrInp.

Module WRmake (M:Vmap) (T:WrInp).
  Import M T.

  Record tosubst := ToSubst {
    ts_v  : var;
    ts_to : to ts_v.(vtype);
  }.

  Fixpoint write_subst {t} (l:rval t) : to t -> list tosubst -> list tosubst := 
    match l in rval t_ return to t_ -> list tosubst -> list tosubst with
    | Rvar x => fun v s =>  (@ToSubst x v) :: s
    | Rpair t1 t2 rv1 rv2 => fun v s => 
      write_subst rv2 (snd v) (write_subst rv1 (fst v) s)
    end.

  Definition write_vmap := 
     foldr (fun (ts:tosubst) vm => @M.set _ vm ts.(ts_v) ts.(ts_to)).

  Definition write_rval {t} (vm:M.t to) (l:rval t) (v:to t) :=
     write_vmap vm (write_subst l v [::]).

End WRmake.
