(* * Syntax and semantics of the dmasm source language *)

(* ** Imports and settings *)
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat ssrint ssralg tuple.
From mathcomp Require Import choice fintype eqtype div seq zmodp.
Require Import strings dmasm_utils gen_map dmasm_type.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition ident := string.

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

Definition var2pair (v:var) := (v.(vtype), v.(vname)).
Definition pair2var (p:stype * ident) := Var (fst p) (snd p).

Lemma codeK_var : cancel var2pair pair2var. Proof. by rewrite /cancel; case => //. Qed.
Definition var_choiceMixin := CanChoiceMixin codeK_var.
Canonical  var_choiceType  := ChoiceType var var_choiceMixin.

Definition var_cmp (x y:var) := 
  Lex (stype_cmp x.(vtype) y.(vtype)) (string_cmp x.(vname) y.(vname)).

Instance varO : Cmp var_cmp.
Proof.
  constructor=> [x y | y x z c | [??] [??]] ;rewrite /var_cmp !Lex_lex.
  + by apply lex_sym;apply cmp_sym.
  + by apply lex_trans=> /=; apply cmp_ctrans.
  by move=> /lex_eq [] /= /(@cmp_eq _ _ stypeO) -> /(@cmp_eq _ _ stringO) ->.
Qed.

(* ** Variables map, to be used when computation is needed
 * -------------------------------------------------------------------- *)
Module Type VAR.

  Declare Module Mid : MAP.

  Parameter var : eqType.
  
  Parameter Var   : stype -> Mid.K.t -> var.   
  Parameter vtype : var -> stype.
  Parameter vname : var -> Mid.K.t.

  Parameter var_surj :forall (x:var), x = Var x.(vtype) x.(vname).

End VAR.

Module MvMake (V:VAR).

  Import V Mid.

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

  Definition map {to1 to2} (f:forall t, to1 t -> to2 t) (m: t to1) : t to2 :=
    {| dft := fun (x:var) => f x.(vtype) (dft m x);
       tbl := Mt.map (fun t mi => Mid.map (f t) mi) m.(tbl); |}.

  Definition indom to x (m: t to) := 
    match (m.(tbl).[x.(vtype)])%mt with 
    | Some mi => 
      match mi.[x.(vname)] with 
      | Some _ => true
      | None   => false
      end
    | None => false
    end.

  Definition remove to (m: t to) x := 
    match (m.(tbl).[x.(vtype)])%mt with 
    | Some mi => 
      {| dft := m.(dft); 
         tbl :=  m.(tbl).[x.(vtype) <- Mid.remove mi x.(vname)]%mt; |}
    | None    => m
    end.

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

  Lemma mapP {to1 to2} (f:forall t, to1 t -> to2 t) (m: t to1) x: 
    get (map f m) x = f x.(vtype) (get m x).
  Proof.
    rewrite /map /get /=.
    rewrite Mt.mapP;case: Mt.get => //= mi.       
    by rewrite Mid.mapP; case: Mid.get.   
  Qed.

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

End MvMake.

(* ** Types for idents 
 * -------------------------------------------------------------------- *)

Module Var.

  Module Mid := Ms.

  Definition var := [eqType of var].
  
  Definition Var   := Var.
  Definition vtype := vtype.
  Definition vname := vname.

  Lemma var_surj (x:var) : x = Var x.(vtype) x.(vname).
  Proof. by case x. Qed.

End Var.
 
Module Mv := MvMake Var.

Delimit Scope mvar_scope with mv.
Notation "vm .[ x ]" := (@Mv.get _ vm x) : mvar_scope.
Notation "vm .[ x  <- v ]" := (@Mv.set _ vm x v) : mvar_scope.
Arguments Mv.get to m%mvar_scope x.
Arguments Mv.set to m%mvar_scope x v.

(* ** Right values
 * -------------------------------------------------------------------- *)

Inductive rval : stype -> Type :=
| Rvar  :> forall (x:var), rval x.(vtype)
| Rpair :  forall st1 st2, rval st1 -> rval st2 -> rval (st1 ** st2).

(* ** Variables function: to be not used if computation is needed, 
 *                       but extentianality is permited 
 * -------------------------------------------------------------------- *)

Module Fv.
  Record rt_ (to : stype -> Type) := Vmap {
    map : forall (x:var), to x.(vtype)
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
