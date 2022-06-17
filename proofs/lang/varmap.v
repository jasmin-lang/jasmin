(* * Non-dependent map from variables to values,
   * parametric in the type relation between the variable and its value *)

(* ** Imports and settings *)
From mathcomp Require Import all_ssreflect.
Require Export var values.
Import ssrbool.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition undef_addr t :=
  match t with
  | sarr n => Varr (WArray.empty n)
  | t0 => undef_v t0 erefl
  end.

Lemma subtype_undef_addr t1 t2 : 
  compat_type t1 t2 -> value_uincl (undef_addr t1) (undef_addr t2).
Proof. by case: t2 => > /compat_typeE => [|||/is_swordP[?]] ->. Qed.

Lemma compat_uincl_undef t v :
  compat_type t (type_of_val v) -> value_uincl (undef_addr t) v.
Proof.
  (case: v => // [||||? /[dup]/is_undef_tE];
    last by case=> -> ? /compat_typeE => [||/is_swordP[?]] ->)
    => > /compat_typeE => [|||/is_swordP[?]] -> //=.
  by split=> //; exact: (WArray.uincl_empty _ (Z.le_refl _)).
Qed.

Class VmapRel := {
  vm_rel : rel stype ;
  vm_relxx : reflexive vm_rel ;
  vm_supeq : subrel eq_op vm_rel ;
  vm_subcomp : subrel vm_rel compat_type
}.

Module Type VmapT.
  Parameter t : forall {vmr: VmapRel}, Type.

  Section Section.
  Context {vmr: VmapRel}.

  Parameter empty : t.
  Parameter get_var : forall (vm: t) (x: var), value.
  Parameter set_var : forall (vm: t) (x: var) (v : value), exec t.
  Parameter update : forall (s : Sv.t) (vm1 vm2 : t), t.
  Definition R_all (R: relation _) vm1 vm2 :=
    forall x, R (get_var vm1 x) (get_var vm2 x).
  Definition R_on (R: relation _) s vm1 vm2 :=
    forall x, Sv.In x s -> R (get_var vm1 x) (get_var vm2 x).
  Definition R_except (R: relation _) s vm1 vm2 :=
    forall x, ~Sv.In x s -> R (get_var vm1 x) (get_var vm2 x).

  Axiom get_var0 : forall x, get_var empty x = undef_addr (vtype x).
  Axiom get_varP : forall vm x, typerel_undef vm_rel (vtype x) (get_var vm x).
  Axiom set_varP : forall vm vm' x y v, set_var vm x v = ok vm' ->
    get_var vm' y = if x == y then rdflt v (truncate_defined_val (vtype x) v)
      else get_var vm y.
  Axiom set_varP_neq : forall vm vm' x y v,
    set_var vm x v = ok vm' -> x != y -> get_var vm' y = get_var vm y.
  Axiom set_varP_eq : forall vm vm' x v, set_var vm x v = ok vm' ->
    get_var vm' x = rdflt v (truncate_defined_val (vtype x) v).
  Axiom set_var_ok : forall vm x v,
    typerel_undef vm_rel (vtype x) (rdflt v (truncate_defined_val (vtype x) v)) ->
    exists vm', set_var vm x v = ok vm'.
  Axiom set_set : forall vm1 vm1' vm2 x v, set_var vm1 x v = ok vm1' ->
    exists vm2', set_var vm2 x v = ok vm2'.
  Axiom set_get : forall vm1 vm2 x,
    exists vm1', set_var vm1 x (get_var vm2 x) = ok vm1'.
  Axiom updateP : forall s x vm1 vm2, get_var (update s vm1 vm2) x =
    (if Sv.mem x s then get_var vm2 else get_var vm1) x.

  End Section.

End VmapT.

Module Vmap : VmapT.

  Section Section.
  Context {vmr: VmapRel}.

  Record _t := {
    mv :> Mvar.t value ;
    mvP x v : Mvar.get mv x = Some v -> typerel_undef vm_rel (vtype x) v
  }.
  Definition t := _t.

  Definition empty : t.
    refine {| mv := Mvar.empty value ; mvP := _|}.
    by move=> ??; rewrite Mvar.get0.
  Defined.

  Definition get_var (vm: t) x := odflt (undef_addr (vtype x)) (Mvar.get vm x).

  Definition set_var (vm: t) (x: var) (v: value) : exec t.
    refine (let v' := rdflt v (truncate_defined_val (vtype x) v) in
      if Sumbool.sumbool_of_bool (typerel_undef vm_rel (vtype x) v') is left h
      then ok {| mv := Mvar.set vm x v' ; mvP := _ |}
      else type_error).
     by move=> >; rewrite Mvar.setP;
      case: ifP => /eqP ?; last exact: mvP; subst=> -[<-].
  Defined.

  Lemma __update_proof (vm1 vm2 : t) s x v :
    Mvar.get (Mvar.map2 (fun x e1 e2 => if Sv.mem x s then e2 else e1) vm1 vm2) x = Some v
    -> typerel_undef vm_rel (vtype x) v.
  Proof. by rewrite Mvar.map2P; case: ifP => _ // /mvP. Qed.

  Definition update s (vm1 vm2 : t) :=
    {| mv := Mvar.map2 (fun x e1 e2 => if Sv.mem x s then e2 else e1) vm1 vm2
     ; mvP := @__update_proof vm1 vm2 s |}.

  Definition R_all (R: relation _) vm1 vm2 :=
    forall x, R (get_var vm1 x) (get_var vm2 x).
  Definition R_on (R: relation _) s vm1 vm2 :=
    forall x, Sv.In x s -> R (get_var vm1 x) (get_var vm2 x).
  Definition R_except (R: relation _) s vm1 vm2 :=
    forall x, ~Sv.In x s -> R (get_var vm1 x) (get_var vm2 x).

  Lemma get_var0 x : get_var empty x = undef_addr (vtype x).
  Proof. by rewrite /get_var Mvar.get0. Qed.

  Lemma get_varP vm x : typerel_undef vm_rel (vtype x) (get_var vm x).
  Proof.
    rewrite /get_var; case: Option.odfltP => [_ /mvP //|_].
    by case: (vtype x) => //= ?; exact: vm_relxx.
  Qed.

  Lemma set_varP_neq vm vm' x y v :
    set_var vm x v = ok vm' -> x != y -> get_var vm' y = get_var vm y.
  Proof.
    by rewrite /set_var; case: Sumbool.sumbool_of_bool => //;
      move=> ? [<-] hneq; rewrite /get_var (Mvar.setP_neq _ _ hneq).
  Qed.

  Lemma set_varP_eq vm vm' x v : set_var vm x v = ok vm' ->
      get_var vm' x = rdflt v (truncate_defined_val (vtype x) v).
  Proof.
    by rewrite /set_var; case: Sumbool.sumbool_of_bool => Hc //;
      case=> <-; rewrite /get_var Mvar.setP_eq.
  Qed.

  Lemma set_varP vm vm' x y v : set_var vm x v = ok vm' ->
    get_var vm' y = if x == y then rdflt v (truncate_defined_val (vtype x) v)
      else get_var vm y.
  Proof.
    by case: ifP; first (move=> /eqP ->; exact: set_varP_eq);
      move=> /negbT /set_varP_neq; apply.
  Qed.

  Lemma set_var_ok vm x v :
    typerel_undef vm_rel (vtype x) (rdflt v (truncate_defined_val (vtype x) v)) ->
    exists vm', set_var vm x v = ok vm'.
  Proof.
    by rewrite /set_var; case: Sumbool.sumbool_of_bool => hc; eauto; rewrite hc.
  Qed.

  Lemma set_set vm1 vm1' vm2 x v : set_var vm1 x v = ok vm1' ->
    exists vm2', set_var vm2 x v = ok vm2'.
  Proof.
    by move=> /set_varP_eq h; move: h (get_varP vm1' x) => -> /(set_var_ok vm2).
  Qed.

  Lemma set_get vm1 vm2 x : exists vm1', set_var vm1 x (get_var vm2 x) = ok vm1'.
  Proof.
    rewrite /get_var /set_var; case: Sumbool.sumbool_of_bool; first by eexists.
    move=> /negP h; exfalso; apply: h. case: Option.odfltP => [?/mvP|_].
    + by move=> ?; case: Result.rdfltP => [?|//] /truncate_defined_val_has_type
        /esym/eqP/vm_supeq/(typerel_undefI vm_subcomp).
    by case: (vtype x) => //= >; rewrite /truncate_defined_val /=
      sumbool_of_boolET (Eqdep_dec.UIP_dec Pos.eq_dec (eqP _)) /=
      /typerel_undef /= vm_relxx.
  Qed.

  Lemma updateP s x vm1 vm2 : get_var (update s vm1 vm2) x =
    (if Sv.mem x s then get_var vm2 else get_var vm1) x.
  Proof. by rewrite /update /get_var /= Mvar.map2P; case: ifP. Qed.

  End Section.
End Vmap.

Notation "vm .[ id ]" := (Vmap.get_var vm id) : vmap_scope.
Notation "vm .[ k <- v ]" := (Vmap.set_var vm k v) : vmap_scope.

(*
Definition on_arr_var A (v: exec value) (f:forall n, WArray.array n -> exec A) :=
  Let v := v in
  match v with
  | Varr n t => f n t
  | _ => type_error
  end.

Lemma on_arr_varP A (f : forall n, WArray.array n -> exec A) v vm x P :
  (forall n t, vm_rel (vtype x) (sarr n) -> Vmap.get_var vm x = @Varr n t -> f n t = ok v -> P) ->
  on_arr_var (ok (Vmap.get_var vm x)) f = ok v -> P.
Proof.
  by move=> h; case: Vmap.get_var h (Vmap.get_varP vm x) => // ?? h/h; apply.
Qed.

Notation "'Let' ( n , t ) ':=' s '.[' v ']' 'in' body" :=
  (@on_arr_var _ (get_var s.(evm) v) (fun n (t:WArray.array n) => body)) (at level 25, s at level 0).

Notation "'Let' ( n , t ) ':=' gd ',' s '.[' v ']' 'in' body" :=
  (@on_arr_var _ (get_gvar gd s.(evm) v) (fun n (t:WArray.array n) => body)) (at level 25, gd at level 0, s at level 0).

Notation "vm1 '=P' vm2" := (eq_on s vm1 vm2) (at level 70, vm2 at next level,
  format "'[hv ' vm1  =P  vm2 ']'").

CONSISTENCY!!!

Definition eq_on := Vmap.R_on eq.

Notation "vm1 '=[' s ']' vm2" := (eq_on s vm1 vm2) (at level 70, vm2 at next level,
  format "'[hv ' vm1  =[ s ]  '/'  vm2 ']'").

Definition vmap_eq_except := Vmap.R_except eq.

Notation "vm1 = vm2 [\ s ]" := (vmap_eq_except s vm1 vm2) (at level 70, vm2 at next level,
  format "'[hv ' vm1  '/' =  vm2  '/' [\ s ] ']'").

Definition vm_uincl := Vmap.R_all value_uincl.

Notation "vm1 '<=P' vm2" := (vmap_uincl_on s vm1 vm2) (at level 70, vm2 at next level,
  format "'[hv ' vm1  <=P  vm2 ']'").

Definition vmap_uincl_on := Vmap.R_on value_uincl.

Notation "vm1 '<=[' s ']' vm2" := (vmap_uincl_on s vm1 vm2) (at level 70, vm2 at next level,
  format "'[hv ' vm1  <=[ s ]  '/'  vm2 ']'").

Definition vmap_uincl_ex := Vmap.R_except value_uincl.

Notation "vm1 '<=[\' s ']' vm2" := (vmap_uincl_ex s vm1 vm2) (at level 70, vm2 at next level,
  format "'[hv ' vm1  <=[\ s ]  '/'  vm2 ']'").
*)