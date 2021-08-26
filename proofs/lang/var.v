(* ** License
 * -----------------------------------------------------------------------
 * Copyright 2016--2017 IMDEA Software Institute
 * Copyright 2016--2017 Inria
 *
 * Permission is hereby granted, free of charge, to any person obtaining
 * a copy of this software and associated documentation files (the
 * "Software"), to deal in the Software without restriction, including
 * without limitation the rights to use, copy, modify, merge, publish,
 * distribute, sublicense, and/or sell copies of the Software, and to
 * permit persons to whom the Software is furnished to do so, subject to
 * the following conditions:
 *
 * The above copyright notice and this permission notice shall be
 * included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
 * EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.
 * IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY
 * CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT,
 * TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE
 * SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 * ----------------------------------------------------------------------- *)

(* ** Imports and settings *)
Require Import Setoid Morphisms.
From mathcomp Require Import all_ssreflect all_algebra.
Require Import strings utils gen_map type ident.
Require Import Utf8.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition ident := string.

(* ** Variables map, to be used when computation is needed
 * -------------------------------------------------------------------- *)
Module Type IDENT.

  Parameter ident : eqType.

  Declare Module Mid : MAP with Definition K.t := ident.

End IDENT.

Module MvMake (I:IDENT).

  Import I Mid.
  Existing Instance K.cmpO.

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

  Definition var_cmp (x y:var) :=
    Lex (stype_cmp x.(vtype) y.(vtype)) (K.cmp x.(vname) y.(vname)).

  Instance varO : Cmp var_cmp.
  Proof.
    constructor=> [x y | y x z c | [??] [??]] ;rewrite /var_cmp !Lex_lex.
    + by apply lex_sym;apply cmp_sym.
    + by apply lex_trans=> /=; apply cmp_ctrans.
    by move=> /lex_eq [] /= /(@cmp_eq _ _ stypeO) -> /(@cmp_eq _ _ K.cmpO) ->.
  Qed.

  Lemma var_surj (x:var) : x = Var x.(vtype) x.(vname).
  Proof. by case: x. Qed.

  Module Mv.

  Record rt_ (to:stype -> Type) := MkT {
    dft : forall (x:var) ,to x.(vtype);
    tbl : Mt.t (fun ty => Mid.t (to ty));
  }.

  Definition t := rt_.

  Definition empty {to} (dft : forall (x:var), to x.(vtype)) : t to := {|
     dft := dft;
     tbl := Mt.empty _;
  |}.

  Definition get {to} (m: t to) (x:var) : to x.(vtype) :=
    match (m.(tbl).[x.(vtype)])%mt with
    | Some mi =>
      match mi.[x.(vname)] with
      | Some v => v
      | None   => m.(dft) x
      end
    | None =>  m.(dft) x
    end.

  Definition set {to} (m: t to) (x:var) (v:to x.(vtype)) : t to :=
    let mi :=
      match (m.(tbl).[x.(vtype)])%mt with
      | Some mi => mi
      | None    => Mid.empty _
      end in
    let mi := mi.[x.(vname) <- v] in
    {| dft := m.(dft);
       tbl := (m.(tbl).[x.(vtype) <- mi])%mt; |}.

  Definition remove to (m: t to) x :=
    match (m.(tbl).[x.(vtype)])%mt with
    | Some mi =>
      {| dft := m.(dft);
         tbl :=  m.(tbl).[x.(vtype) <- Mid.remove mi x.(vname)]%mt; |}
    | None    => m
    end.

  Definition indom to x (m: t to) :=
    match (m.(tbl).[x.(vtype)])%mt with
    | Some mi =>
      match mi.[x.(vname)] with
      | Some _ => true
      | None   => false
      end
    | None => false
    end.

  Definition map {to1 to2} (f:forall t, to1 t -> to2 t) (m: t to1) : t to2 :=
    {| dft := fun (x:var) => f x.(vtype) (dft m x);
       tbl := Mt.map (fun t mi => Mid.map (f t) mi) m.(tbl); |}.

  Definition map2 {to1 to2 to3}
     (fd:forall x, to3 x.(vtype))
     (f:forall x, to1 x.(vtype) -> to2 x.(vtype) -> to3 x.(vtype))
     (m1: t to1) (m2: t to2): t to3 :=
    let dft1 := m1.(dft) in
    let dft2 := m2.(dft) in
    let doty ty mi1 mi2 :=
       match mi1, mi2 with
       | None, None => None
       | Some mi1, None     =>
         Some (Mid.mapi
           (fun id (v1:to1 ty) => let x := Var ty id in (f x v1 (dft2 x):to3 ty))
           mi1)
       | None    , Some mi2 =>
         Some (Mid.mapi
           (fun id (v2:to2 ty) => let x := Var ty id in (f x (dft1 x) v2:to3 ty))
           mi2)
       | Some mi1, Some mi2 =>
         Some (Mid.map2 (fun id (o1:option (to1 ty)) (o2: option (to2 ty))  =>
           match o1, o2 with
           | None   , None    => None
           | Some v1, None    => let x := Var ty id in Some (f x v1 (dft2 x))
           | None   , Some v2 => let x := Var ty id in Some (f x (dft1 x) v2)
           | Some v1, Some v2 => let x := Var ty id in (Some (f x v1 v2): option (to3 ty))
           end) mi1 mi2)
        end in
    {| dft := fd;
       tbl := Mt.map2 doty m1.(tbl) m2.(tbl) |}.

  Local Notation "vm .[ x ]" := (@get _ vm x).
  Local Notation "vm .[ x  <- v ]" := (@set _ vm x v).

  Lemma get0 {to} (dft: forall x, to x.(vtype)) (x:var) : (empty dft).[x] = dft x.
  Proof. by rewrite /empty /get Mt.get0. Qed.

  Lemma setP_eq {to} (m:t to) (x:var) (v:to x.(vtype)) : m.[x <- v].[x] = v.
  Proof. by rewrite /set /get Mt.setP_eq Mid.setP_eq. Qed.

  Lemma setP_neq {to} (m:t to) x y (v:to x.(vtype)) :
    x != y ->   m.[x <- v].[y] = m.[y].
  Proof.
    move=> neq;rewrite /set /get.
    case : (boolP ((vtype x) == (vtype y))) => [/eqP eq | ?] /=;
      last by rewrite Mt.setP_neq.
    move: v;rewrite eq => v; rewrite Mt.setP_eq Mid.setP_neq.
    + by case: (_.[_])%mt => //; rewrite Mid.get0.
    by apply: contra neq=> /eqP eqn;rewrite (var_surj x) eq eqn -var_surj.
  Qed.

  Lemma indom0 {to} (dft: forall x, to x.(vtype)) (x:var): ~~indom x (empty dft).
  Proof. by rewrite /indom Mt.get0. Qed.

  Lemma indom_set_eq {to} (m:t to) (x:var) (v:to x.(vtype)): indom x m.[x<-v].
  Proof. by rewrite /indom /set /= Mt.setP_eq Mid.setP_eq. Qed.

  Lemma indom_set_neq {to} (m:t to) (x y:var) (v:to x.(vtype)):
     x !=y -> indom y m.[x<- v] = indom y m.
  Proof.
    move=> H;rewrite /indom /set /=.
    case: (vtype x =P vtype y)=> [Heq | /eqP ?];last by rewrite Mt.setP_neq.
    rewrite -Heq Mt.setP_eq Mid.setP_neq.
    + by case: (_.[_])%mt => //;rewrite Mid.get0.
    by apply: contra H=> /eqP eqn;rewrite (var_surj x) Heq eqn -var_surj.
  Qed.

  Lemma indom_setP {to} (m:t to) (x y:var) (v:to x.(vtype)):
     indom y m.[x<-v] = (x == y) || indom y m.
  Proof.
   case : (boolP (x==y)) => [/eqP <-| ] /=;first by rewrite indom_set_eq.
   by apply indom_set_neq.
  Qed.

  Lemma indom_getP  {to} (m:t to) x: ~~indom x m -> m.[x] = dft m x.
  Proof.
    by rewrite /indom /get;case: Mt.get => // ?;case: Mid.get.
  Qed.

  Lemma dft_setP {to} (m:t to) (x:var) (v:to x.(vtype)): dft (set m v) = dft m.
  Proof. done. Qed.

  Lemma removeP_eq to (m: t to) x: (remove m x).[x] = dft m x.
  Proof.
    rewrite /remove/get;case H: (tbl m).[_]%mt => [mi|] /=;last by rewrite H.
    by rewrite Mt.setP_eq removeP_eq.
  Qed.

  Lemma removeP_neq to (m: t to) x y: x != y -> (remove m x).[y] = m.[y].
  Proof.
    rewrite /remove/get=> Hxy;case: (vtype x =P vtype y) => /= [Heq | /eqP Hneq].
    + rewrite Heq;case H: (tbl m).[_]%mt => [mi|] /=;last by rewrite H.
      rewrite Mt.setP_eq Mid.removeP_neq //.
      by apply: contra Hxy => /eqP Hn;rewrite (var_surj x) (var_surj y) Heq Hn.
    by case H: (tbl m).[_]%mt => [mi|] //=;rewrite Mt.setP_neq.
  Qed.

  Lemma indom_removeP to (m: t to) x y:
    indom y (remove m x) = (x != y) && indom y m.
  Proof.
    rewrite /remove/indom.
    case: (vtype x =P vtype y) => /= [Heq | /eqP Hneq].
    + rewrite -Heq;case H: ((tbl m).[_]%mt) => [mi|]/=;last by rewrite H andbC.
      rewrite Mt.setP_eq Mid.removeP.
      case: (_ =P _) => [Heqn | Hneqn ].
      + by rewrite {1}(var_surj x) {1}(var_surj y) -Heq Heqn eq_refl.
      have -> // : x != y.
      by apply /eqP=> Hx;apply Hneqn;rewrite Hx.
    have -> : x != y.
    + by apply /eqP=> Hx;move:Hneq;rewrite Hx eq_refl.
    by case H: ((tbl m).[_]%mt) => [mi|] //=;rewrite Mt.setP_neq.
  Qed.

  Lemma indom_removeP_eq to (m: t to) x:
    ~~indom x (remove m x).
  Proof. by rewrite indom_removeP eq_refl. Qed.

  Lemma indom_removeP_neq to (m: t to) x y: x != y ->
    indom y (remove m x) = indom y m.
  Proof. by rewrite indom_removeP=> ->. Qed.

  Lemma dft_removeP to (m: t to) x: dft (remove m x) = dft m.
  Proof. by rewrite /dft/remove;case:(tbl m).[_]%mt. Qed.

  Lemma mapP {to1 to2} (f:forall t, to1 t -> to2 t) (m: t to1) x:
    (map f m).[x] = f x.(vtype) m.[x].
  Proof.
    rewrite /map /get /=.
    rewrite Mt.mapP;case: Mt.get => //= mi.
    by rewrite Mid.mapP; case: Mid.get.
  Qed.

  Lemma indom_mapP {to1 to2} (f:forall t, to1 t -> to2 t) (m: t to1) x:
     indom x (map f m) = indom x m.
  Proof.
    rewrite /map /indom /= Mt.mapP.
    by case: Mt.get => //= ?;rewrite Mid.mapP;case Mid.get.
  Qed.

  Lemma dft_mapP {to1 to2} (f:forall t, to1 t -> to2 t) (m: t to1):
     dft (map f m) = fun x : var => f (vtype x) (dft m x).
  Proof. done. Qed.

  Lemma map2Pred {to1 to2 to3}
    (fd: forall x,  to3 x.(vtype))
    (f:forall x, to1 x.(vtype) -> to2 x.(vtype) -> to3 x.(vtype)) m1 m2 x P:
    (~~indom x m1 -> ~~indom x m2 -> P (f x (dft m1 x) (dft m2 x)) -> P (fd x)) ->
    P (f x m1.[x] m2.[x]) -> P (map2 fd f m1 m2).[x].
  Proof.
    rewrite /indom /map2 /get /= Mt.map2P //.
    case: ((tbl m1).[vtype x])%mt=>[mi1|];case: ((tbl m2).[vtype x])%mt=>[mi2|];last by auto.
    + rewrite Mid.map2P //.
      by case: (Mid.get mi1 (vname x));case: (Mid.get mi2 (vname x))=> //;
         last (by auto); case: (x) P.
    + by rewrite Mid.mapiP //;case: (Mid.get mi1 (vname x));case: (x) P =>//=;auto.
    by rewrite Mid.mapiP //;case: (Mid.get mi2 (vname x));case: (x) P=> //=;auto.
  Qed.

  Lemma map2P {to1 to2 to3}
    (fd: forall x,  to3 x.(vtype))
    (f:forall x, to1 x.(vtype) -> to2 x.(vtype) -> to3 x.(vtype)) m1 m2 x:
    (~~indom x m1 -> ~~indom x m2 -> fd x = f x (dft m1 x) (dft m2 x)) ->
    (map2 fd f m1 m2).[x] = f x m1.[x] m2.[x].
  Proof. by apply map2Pred => // ?? H1 H2;rewrite H2 // H1. Qed.

  Lemma indom_map2P {to1 to2 to3} fd
      (f:forall x, to1 x.(vtype) -> to2 x.(vtype) -> to3 x.(vtype)) m1 m2 x:
     indom x (map2 fd f m1 m2) = indom x m1 || indom x m2.
  Proof.
    rewrite /map2 /indom /= Mt.map2P //.
    case: ((tbl m1).[vtype x])%mt=> [mi1 | ];case: ((tbl m2).[vtype x])%mt => [mi2 | ] //.
    + by rewrite Mid.map2P //; case: Mid.get => [?|] /=;case: Mid.get.
    + by rewrite Mid.mapiP;case: Mid.get.
    by rewrite Mid.mapiP;case: Mid.get.
  Qed.

  Lemma dft_map2P {to1 to2 to3} fd
      (f:forall x, to1 x.(vtype) -> to2 x.(vtype) -> to3 x.(vtype)) m1 m2:
     dft (map2 fd f m1 m2) = fd.
  Proof. done. Qed.

  End Mv.

End MvMake.

(* ** Types for idents
 * -------------------------------------------------------------------- *)


Module Var := MvMake Ident.
Export Var. (* Enrico: On pert les structures canoniques si pas de import *)
Notation var   := Var.var.
Notation vtype := Var.vtype.
Notation vname := Var.vname.
Notation Var   := Var.Var.

Definition var2pair (v:var) := (v.(vtype), v.(vname)).
Definition pair2var (p:stype * ident) := Var (fst p) (snd p).

Lemma codeK_var : cancel var2pair pair2var. Proof. by rewrite /cancel; case => //. Qed.

Declare Scope mvar_scope.
Delimit Scope mvar_scope with mv.
Notation "vm .[ x ]" := (@Mv.get _ vm x) : mvar_scope.
Notation "vm .[ x  <- v ]" := (@Mv.set _ vm x v) : mvar_scope.
Arguments Mv.get to m%mvar_scope x.
Arguments Mv.set to m%mvar_scope x v.

Lemma vtype_diff x x': vtype x != vtype x' -> x != x'.
Proof. by apply: contra => /eqP ->. Qed.

Lemma vname_diff x x': vname x != vname x' -> x != x'.
Proof. by apply: contra => /eqP ->. Qed.

(* ** Variables function: to be not used if computation is needed,
 *                       but extentianality is permited
 * -------------------------------------------------------------------- *)

Module Type FvT.
  Parameter t : (stype -> Type) -> Type.
  Parameter empty :
    forall {to:stype -> Type} (dval : forall (x:var), to x.(vtype)), t to.

  Parameter get :
    forall {to:stype -> Type} (vm:t to) (x:var), to x.(vtype).

  Parameter set :
    forall {to:stype -> Type} (vm : t to) x (v : to x.(vtype)), t to.

  Axiom get0 : forall to dval x, @get to (empty dval) x = dval x.

  Axiom setP_eq : forall to (vm:t to) x (v:to x.(vtype)),
    get (@set _ vm x v) x = v.

  Axiom setP_neq : forall to (vm:t to) x y (v:to x.(vtype)),
    x != y -> get (@set _ vm x v) y = get vm y.

  Definition ext_eq  {to} (vm1 vm2 : t to) :=
    forall x, get vm1 x = get vm2 x.

End FvT.

Module Fv : FvT.

  Definition t := Mv.t.

  Definition empty := @Mv.empty.

  Definition get := @Mv.get.

  Definition set := @Mv.set.

  Lemma get0 to dval x : @get to (empty dval) x = dval x.
  Proof. by apply: Mv.get0. Qed.

  Lemma setP_eq to (vm:t to) x (v:to x.(vtype)) :
    get (@set _ vm x v) x = v.
  Proof. apply Mv.setP_eq. Qed.

  Lemma setP_neq to (vm:t to) x y (v:to x.(vtype)) :
    x != y -> get (@set _ vm x v) y = get vm y.
  Proof. apply Mv.setP_neq. Qed.

  Definition ext_eq  {to} (vm1 vm2 : t to) :=
    forall x, get vm1 x = get vm2 x.

End Fv.

Declare Scope vmap_scope.
Delimit Scope vmap_scope with vmap.
Notation "vm .[ id ]" := (Fv.get vm id) : vmap_scope.
Notation "vm .[ k  <- v ]" := (@Fv.set _ vm k v) : vmap_scope.
Notation "vm1 =v vm2" := (Fv.ext_eq vm1 vm2) (at level 70, no associativity) : vmap_scope.
Arguments Fv.get to vm%vmap_scope x.
Arguments Fv.set to vm%vmap_scope x v.
Arguments Fv.ext_eq to vm1%vmap_scope vm2%vmap_scope.

Module Type Vmap.

  Parameter t : (stype -> Type) -> Type.

  Parameter empty : forall to, (forall (x:var), to x.(vtype)) -> t to.

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

(* ** Finite set of variables (computable)
 *
 * -------------------------------------------------------------------- *)

Module CmpVar.

  Definition t := [eqType of var].

  Definition cmp : t -> t -> comparison := var_cmp.

  Definition cmpO : Cmp cmp := varO.

End CmpVar.

Module Sv := Smake CmpVar.
Module SvP := MSetEqProperties.EqProperties Sv.
Module SvD := MSetDecide.WDecide Sv.

Lemma Sv_memP x s: reflect (Sv.In x s) (Sv.mem x s).
Proof.
  apply: (@equivP (Sv.mem x s));first by apply idP.
  by rewrite -Sv.mem_spec.
Qed.

Lemma Sv_elemsP x s : reflect (Sv.In x s) (x \in Sv.elements s).
Proof.
  apply: (equivP idP);rewrite SvD.F.elements_iff.
  elim: (Sv.elements s) => /= [|v vs];split => //=.
  + by move /SetoidList.InA_nil.
  + by rewrite inE => /orP [ /eqP -> | /H];auto.
  case/SetoidList.InA_cons => [ -> |]; rewrite inE ?eq_refl //.
  by move /H => ->; rewrite orbT.
Qed.

Lemma Sv_elems_eq x s : Sv.mem x s = (x \in (Sv.elements s)).
Proof. by apply: sameP (Sv_memP x s) (Sv_elemsP x s). Qed.

Definition disjoint s1 s2 := Sv.is_empty (Sv.inter s1 s2).

Instance disjoint_m :
  Proper (Sv.Equal ==> Sv.Equal ==> eq) disjoint.
Proof.
  by move => s1 s1' Heq1 s2 s2' Heq2;rewrite /disjoint Heq1 Heq2.
Qed.

Instance disjoint_sym : Symmetric disjoint.
Proof.
  move=> x y h; rewrite/disjoint.
  erewrite SvD.F.is_empty_m. exact h.
  SvD.fsetdec.
Qed.

Lemma disjoint_w x x' y :
  Sv.Subset x x' →
  disjoint x' y →
  disjoint x y.
Proof.
  move=> le e; apply SvD.F.is_empty_iff in e.
  apply SvD.F.is_empty_iff.
  SvD.fsetdec.
Qed.

(* Non dependant map *)
Module Mvar :=  Mmake CmpVar.

Definition Mvar_eq T (m1 m2:Mvar.t T) :=
  forall x, Mvar.get m1 x = Mvar.get m2 x.

Polymorphic Instance equiv_Mvar_eq T : Equivalence (@Mvar_eq T).
Proof.
  split=> //.
  + by move=> m1 m2 Hm z;rewrite Hm.
  by move=> m1 m2 m3 Hm1 Hm2 z;rewrite Hm1 Hm2.
Qed.

Instance Mvar_get_m T:
  Proper (@Mvar_eq T ==> eq ==> eq) Mvar.get.
Proof. by move=> m1 m2 Hm ?? <-. Qed.

Instance Mvar_set_m T:
  Proper (@Mvar_eq T ==> eq ==> eq ==> @Mvar_eq T) Mvar.set.
Proof. by move=> m1 m2 Hm ?? <- ?? <- z;rewrite !Mvar.setP;case:ifP. Qed.

Instance Mvar_remove_m T:
  Proper (@Mvar_eq T ==> eq ==> @Mvar_eq T) Mvar.remove.
Proof. by move=> m1 m2 Hm ?? <- z;rewrite !Mvar.removeP;case:ifP. Qed.
