From mathcomp Require Import ssreflect ssrfun ssrbool seq eqtype ssralg.
From mathcomp Require Import word_ssrZ.
From Coq Require Import ZArith Setoid Morphisms.
Require Export var type values.
Import Utf8 ssrbool.

Set SsrOldRewriteGoalsOrder.  (* change Set to Unset when porting the file, then remove the line when requiring MathComp >= 2.6 *)

(* ----------------------------------------------------------- *)
Section Section.

Context {wsw: WithSubWord}.

Definition compat_val ty v :=
  compat_ctype (sw_allowed || ~~is_defined v) (type_of_val v) ty.

Definition truncatable wdb ty v :=
 match v, ty with
 | Vbool _, cbool => true
 | Vint _, cint   => true
 | Varr len _, carr len' => len == len'
 (* TODO: change the order of the conditions to simplify proofs
  suggestion: ws' ≤ ws || sw_allowed || ~~ wdb *)
 | Vword ws w, cword ws' =>  ~~wdb || (sw_allowed || (ws' <= ws)%CMP)
 | Vundef t _, _ => subctype t ty
 | _, _ => false
 end.

Lemma truncatable_arr wdb len a : truncatable wdb (carr len) (@Varr len a).
Proof. by rewrite /truncatable /= eqxx. Qed.

Definition vm_truncate_val ty v :=
 match v, ty with
 | Vbool _, cbool => v
 | Vint _, cint   => v
 | Varr len _, carr len' => if len == len' then v else undef_addr ty
 | Vword ws w, cword ws' =>
   if (sw_allowed || (ws' <= ws)%CMP) then
     if (ws <= ws')%CMP then Vword w else Vword (zero_extend ws' w)
   else undef_addr ty
 | Vundef t _, _ => undef_addr ty
 | _, _ => undef_addr ty
 end.

Lemma compat_val_undef_addr t : compat_val t (undef_addr t).
Proof. by rewrite /compat_val; case: t => //= w; rewrite orbT /= wsize_le_U8. Qed.
Hint Resolve compat_val_undef_addr : core.

Lemma vm_truncate_val_compat v ty : compat_val ty (vm_truncate_val ty v).
Proof.
Opaque undef_addr.
  case : v => [b | i | p t | ws w | t ht] => //=.
  1-2: by case: ty => [||len|ws'] //=; rewrite /compat_val.
  + by case: ty => [||len|ws'] //=; case: eqP => [<-|//]; rewrite /compat_val.
  case: ty => [||len|ws'] //=; case: ifP => //= h; rewrite /compat_val; case: ifP => //=.
  by case: sw_allowed h => //= h1 h2; rewrite (cmp_le_antisym h2 h1).
Transparent undef_addr.
Qed.

Lemma compat_value_uincl_undef ty v :
  compat_val ty v ->
  value_uincl (undef_addr ty) v.
Proof.
  move=> /compat_ctypeEl.
  case: v => //= [b <- | z <- | len a <- | ws w [ws' -> hle] | t i] //=.
  + by apply WArray.uincl_empty.
  by (case: (is_undef_tE i) => ?; subst t) => [ <- | <- | [ws ->]].
Qed.

End Section.

(* ----------------------------------------------------------- *)

Module Type VM.

  Parameter t : forall {wsw:WithSubWord}, Type.

  Parameter init : forall {wsw:WithSubWord}, t.

  Parameter get : forall {wsw:WithSubWord}, t -> var -> value.

  Parameter set : forall {wsw:WithSubWord}, t -> var -> value -> t.

  Parameter initP : forall {wsw:WithSubWord} x,
    get init x = undef_addr (eval_atype (vtype x)).

  Parameter getP : forall {wsw:WithSubWord} vm x,
    compat_val (eval_atype (vtype x)) (get vm x).

  Parameter setP : forall {wsw:WithSubWord} vm x v y,
    get (set vm x v) y = if x == y then vm_truncate_val (eval_atype (vtype x)) v else get vm y.

  Parameter setP_eq : forall {wsw:WithSubWord} vm x v, get (set vm x v) x = vm_truncate_val (eval_atype (vtype x)) v.

  Parameter setP_neq : forall {wsw:WithSubWord} vm x v y, x != y -> get (set vm x v) y = get vm y.

End VM.

Module Vm : VM.
  Section Section.

  Context {wsw: WithSubWord}.

  Definition wf (data: Mvar.t value) :=
    forall x v, Mvar.get data x = Some v -> compat_val (eval_atype (vtype x)) v.

  Record t_ := { data :> Mvar.t value; prop : wf data }.
  Definition t := t_.

  Lemma init_prop : wf (Mvar.empty value).
  Proof. by move=> x v; rewrite Mvar.get0. Qed.

  Definition init := {| prop := init_prop |}.

  Definition get (vm:t) (x:var) := odflt (undef_addr (eval_atype (vtype x))) (Mvar.get vm x).

  Lemma set_prop (vm:t) x v : wf (Mvar.set vm x (vm_truncate_val (eval_atype (vtype x)) v)).
  Proof.
    move=> y vy; rewrite Mvar.setP; case: eqP => [<- [<-] | _ /prop //].
    apply vm_truncate_val_compat.
  Qed.

  Definition set (vm:t) (x:var) v :=
    {| data := Mvar.set vm x (vm_truncate_val (eval_atype (vtype x)) v); prop := @set_prop vm x v |}.

  Lemma initP x : get init x = undef_addr (eval_atype (vtype x)).
  Proof. done. Qed.

  Lemma getP vm x : compat_val (eval_atype (vtype x)) (get vm x).
  Proof. rewrite /get; case h : Mvar.get => [ v | ] /=;[apply: prop h | apply compat_val_undef_addr]. Qed.

  Lemma setP vm x v y :
    get (set vm x v) y = if x == y then vm_truncate_val (eval_atype (vtype x)) v else get vm y.
  Proof. by rewrite /get /set Mvar.setP; case: eqP => [<- | hne]. Qed.

  Lemma setP_eq vm x v : get (set vm x v) x = vm_truncate_val (eval_atype (vtype x)) v.
  Proof. by rewrite setP eqxx. Qed.

  Lemma setP_neq vm x v y : x != y -> get (set vm x v) y = get vm y.
  Proof. by rewrite setP => /negbTE ->. Qed.

  End Section.

End Vm.

Declare Scope vm_scope.
Delimit Scope vm_scope with vm.
Notation "vm .[ x ]" := (@Vm.get _ vm x) : vm_scope.
Notation "vm .[ x <- v ]" := (@Vm.set _ vm x v) : vm_scope.
Open Scope vm_scope.


Section GET_SET.

Context {wsw: WithSubWord}.

Definition set_var wdb vm x v :=
  Let _ := assert (DB wdb v) ErrAddrUndef in
  Let _ := assert (truncatable wdb (eval_atype (vtype x)) v) ErrType in
  ok vm.[x <- v].

(* Ensure that the variable is defined *)
Definition get_var wdb vm x :=
  let v := vm.[x]%vm in
  Let _ := assert (~~wdb || is_defined v) ErrAddrUndef in
  ok v.

Definition get_vars wdb vm := mapM (get_var wdb vm).

Definition vm_initialized_on vm : seq var → Prop :=
  all (λ x, is_ok (get_var true vm x >>= of_val (eval_atype (vtype x)))).

End GET_SET.

(* Attempt to simplify goals of the form [vm.[y0 <- z0]...[yn <- zn].[x]]. *)
Ltac t_vm_get :=
  repeat (
    rewrite Vm.setP_eq
    || (rewrite Vm.setP_neq; last (apply/eqP; by [|apply/nesym]))
  ).

(* ----------------------------------------------------------------------- *)
(* Generic relation over varmap                                            *)

Section REL.

  Context {wsw1 wsw2 : WithSubWord}.

  Section Section.

  Context (R:value -> value -> Prop).

  Definition vm_rel (P : var -> Prop) (vm1 : @Vm.t wsw1) (vm2 : @Vm.t wsw2) :=
    forall x, P x -> R (Vm.get vm1 x) (Vm.get vm2 x).

  Lemma vm_rel_set (P : var -> Prop) vm1 vm2 x v1 v2 :
    (P x -> R (vm_truncate_val (wsw:=wsw1) (eval_atype (vtype x)) v1) (vm_truncate_val (wsw:=wsw2) (eval_atype (vtype x)) v2)) ->
    vm_rel (fun z => x <> z /\ P z) vm1 vm2 ->
    vm_rel P vm1.[x <- v1] vm2.[x <- v2].
  Proof. move=> h hu y hy; rewrite !Vm.setP; case: eqP => heq; subst; auto. Qed.

  Lemma vm_rel_set_r (P : var -> Prop) vm1 vm2 x v2 :
    (P x -> R vm1.[x] (vm_truncate_val (wsw:=wsw2) (eval_atype (vtype x)) v2)) ->
    vm_rel (fun z => x <> z /\ P z) vm1 vm2 ->
    vm_rel P vm1 (vm2.[x <- v2]).
  Proof. move=> h hu y hy; rewrite !Vm.setP; case: eqP => heq; subst; auto. Qed.

  Lemma vm_rel_set_l (P : var -> Prop) vm1 vm2 x v1 :
    (P x -> R (vm_truncate_val (wsw:=wsw1) (eval_atype (vtype x)) v1) vm2.[x]) ->
    vm_rel (fun z => x <> z /\ P z) vm1 vm2 ->
    vm_rel P vm1.[x <- v1] vm2.
  Proof. move=> h hu y hy; rewrite !Vm.setP; case: eqP => heq; subst; auto. Qed.

  End Section.

  #[export] Instance vm_rel_impl :
    Proper (subrelation ==>
            pointwise_lifting (Basics.flip Basics.impl) (Tcons var Tnil) ==>
            @eq Vm.t ==> @eq Vm.t ==> Basics.impl) vm_rel.
  Proof. by move=> R1 R2 hR P1 P2 hP vm1 ? <- vm2 ? <- h x hx; apply/hR/h/hP. Qed.

  #[export] Instance vm_rel_m :
    Proper (relation_equivalence ==>
            pointwise_lifting iff (Tcons var Tnil) ==>
            @eq Vm.t ==> @eq Vm.t ==> iff) vm_rel.
  Proof.
    move=> R1 R2 hR P1 P2 hP vm1 ? <- vm2 ? <-; split; apply vm_rel_impl => //.
    1,3: by move=> ??;apply hR.
    1,2: by move=> x /=; case: (hP x).
  Qed.

  Definition vm_eq (vm1:Vm.t (wsw:=wsw1)) (vm2:Vm.t (wsw:=wsw2)) :=
    forall x, vm1.[x] = vm2.[x].

  Definition eq_on     (X:Sv.t) := vm_rel (@eq value) (fun x => Sv.In x X).
  Definition eq_ex (X:Sv.t) := vm_rel (@eq value) (fun x => ~Sv.In x X).

  Definition vm_uincl (vm1:Vm.t (wsw:=wsw1)) (vm2:Vm.t (wsw:=wsw2)) :=
    forall x, value_uincl vm1.[x] vm2.[x].

  Definition uincl_on     (X:Sv.t) := vm_rel value_uincl (fun x => Sv.In x X).
  Definition uincl_ex (X:Sv.t) := vm_rel value_uincl (fun x => ~Sv.In x X).

  #[export] Instance eq_on_impl :
    Proper (Basics.flip Sv.Subset ==> @eq Vm.t ==> @eq Vm.t ==> Basics.impl) eq_on.
  Proof. by move=> s1 s2 hS; apply vm_rel_impl. Qed.

  #[export] Instance eq_on_m :
    Proper (Sv.Equal ==> @eq Vm.t ==> @eq Vm.t ==> iff) eq_on.
  Proof. by move=> s1 s2 hS; apply vm_rel_m. Qed.

  #[export] Instance eq_ex_impl :
    Proper (Sv.Subset ==> @eq Vm.t ==> @eq Vm.t ==> Basics.impl) eq_ex.
  Proof. by move=> s1 s2 hS; apply vm_rel_impl => // x hnx hx; apply/hnx/hS. Qed.

  #[export] Instance eq_ex_m :
    Proper (Sv.Equal ==> @eq Vm.t ==> @eq Vm.t ==> iff) eq_ex.
  Proof. by move => s1 s2 hS; apply vm_rel_m => // x; exact: not_iff_compat. Qed.

  #[export] Instance uincl_on_impl :
    Proper (Basics.flip Sv.Subset ==> @eq Vm.t ==> @eq Vm.t ==> Basics.impl) uincl_on.
  Proof. by move=> s1 s2 hS; apply vm_rel_impl. Qed.

  #[export] Instance uincl_on_m :
    Proper (Sv.Equal ==> @eq Vm.t ==> @eq Vm.t ==> iff) uincl_on.
  Proof. by move=> s1 s2 hS; apply vm_rel_m. Qed.

  #[export] Instance uincl_ex_impl :
    Proper (Sv.Subset ==> @eq Vm.t ==> @eq Vm.t ==> Basics.impl) uincl_ex.
  Proof. by move=> s1 s2 hS; apply vm_rel_impl => // x hnx hx; apply/hnx/hS. Qed.

  #[export] Instance uincl_ex_m :
    Proper (Sv.Equal ==> @eq Vm.t ==> @eq Vm.t ==> iff) uincl_ex.
  Proof. by move => s1 s2 hS; apply vm_rel_m => // x; exact: not_iff_compat. Qed.

  Lemma vm_uincl_vm_rel vm1 vm2 : vm_uincl vm1 vm2 <-> vm_rel value_uincl (fun _ => True) vm1 vm2.
  Proof. by split => [h x _ | h x]; apply h. Qed.

End REL.

Notation "vm1 '=1' vm2" := (vm_eq vm1 vm2)
  (at level 70, vm2 at next level) : vm_scope.

Notation "vm1 '=[' s ']' vm2" := (eq_on s vm1 vm2)
  (at level 70, vm2 at next level,
  format "'[hv ' vm1  =[ s ] '/'  vm2 ']'") : vm_scope.

Notation "vm1 '=[\' s ']' vm2" := (eq_ex s vm1 vm2)
  (at level 70, vm2 at next level,
  format "'[hv ' vm1  =[\ s ] '/'  vm2 ']'") : vm_scope.

Notation "vm1 '<=1' vm2" := (vm_uincl vm1 vm2)
  (at level 70, vm2 at next level,
  format "'[hv ' vm1  <=1  '/'  vm2 ']'") : vm_scope.

Notation "vm1 '<=[' s ']' vm2" := (uincl_on s vm1 vm2)
  (at level 70, vm2 at next level,
  format "'[hv ' vm1  <=[ s ] '/'  vm2 ']'") : vm_scope.

Notation "vm1 '<=[\' s ']' vm2" := (uincl_ex s vm1 vm2)
  (at level 70, vm2 at next level,
  format "'[hv ' vm1  <=[\ s ] '/'  vm2 ']'") : vm_scope.

Section REL_EQUIV.
  Context {wsw : WithSubWord}.

  Lemma vm_rel_refl R P : Reflexive R -> Reflexive (vm_rel R P).
  Proof. by move=> h x v _. Qed.

  Lemma vm_rel_sym R P : Symmetric R -> Symmetric (vm_rel R P).
  Proof. by move=> h x y hxy v hv; apply/h/hxy. Qed.

  Lemma vm_rel_trans R P : Transitive R -> Transitive (vm_rel R P).
  Proof. move=> h x y z hxy hyz v hv; apply: h (hxy v hv) (hyz v hv). Qed.

  #[export]Instance equiv_vm_rel R P : Equivalence R -> Equivalence (vm_rel R P).
  Proof.
    by constructor; [apply: vm_rel_refl | apply: vm_rel_sym | apply: vm_rel_trans].
  Qed.

  #[export]Instance equiv_vm_eq : Equivalence vm_eq.
  Proof. by constructor => > // => [h1 x | h1 h2 x]; rewrite h1 ?h2. Qed.

  #[export]Instance equiv_eq_on s : Equivalence (eq_on s).
  Proof. apply equiv_vm_rel; apply eq_equivalence. Qed.

  #[export]Instance equiv_eq_ex s : Equivalence (eq_ex s).
  Proof. apply equiv_vm_rel; apply eq_equivalence. Qed.

  #[export]Instance po_vm_rel R P: PreOrder R -> PreOrder (vm_rel R P).
  Proof. by constructor; [apply: vm_rel_refl | apply: vm_rel_trans]. Qed.

  #[export]Instance po_value_uincl : PreOrder value_uincl.
  Proof. constructor => // ???; apply value_uincl_trans. Qed.

  #[export]Instance po_vm_uincl : PreOrder vm_uincl.
  Proof.
   constructor => [ vm1 // | vm1 vm2 vm3].
   rewrite !vm_uincl_vm_rel; apply vm_rel_trans => ???; apply value_uincl_trans.
  Qed.

  #[export]Instance po_uincl_on s : PreOrder (uincl_on s).
  Proof. apply po_vm_rel; apply po_value_uincl. Qed.

  #[export]Instance po_uincl_ex s : PreOrder (uincl_ex s).
  Proof. apply po_vm_rel; apply po_value_uincl. Qed.

  Lemma vm_uincl_refl vm : vm <=1 vm.
  Proof. done. Qed.

  Lemma eq_on_refl s vm : vm =[s] vm.
  Proof. by apply vm_rel_refl. Qed.

  Lemma eq_ex_refl s vm : vm =[\s] vm.
  Proof. by apply vm_rel_refl. Qed.

  Lemma uincl_on_refl vm s : vm <=[s] vm.
  Proof. done. Qed.

  Lemma uincl_ex_refl s vm : vm <=[\s] vm.
  Proof. apply vm_rel_refl => ?; apply value_uincl_refl. Qed.

  Lemma uincl_exT vm2 vm1 vm3 s:
    vm1 <=[\s] vm2 -> vm2 <=[\s] vm3 -> vm1 <=[\s] vm3.
  Proof. apply vm_rel_trans => ???; apply value_uincl_trans. Qed.

  Lemma eq_on_empty vm1 vm2 :
    vm1 =[Sv.empty] vm2.
  Proof. by move => ?; SvD.fsetdec. Qed.

  Lemma uincl_on_empty vm1 vm2 :
    vm1 <=[Sv.empty] vm2.
  Proof. by move => ?; SvD.fsetdec. Qed.

  Hint Resolve eq_on_empty uincl_on_empty : core.

  Instance uincl_ex_trans dom : Transitive (uincl_ex dom).
  Proof. by move => x y z; apply: uincl_exT. Qed.

  Lemma vm_uincl_init vm : Vm.init <=1 vm.
  Proof. move=> z; rewrite Vm.initP; apply/compat_value_uincl_undef/Vm.getP. Qed.

End REL_EQUIV.

#[export] Hint Resolve vm_uincl_refl eq_on_refl eq_ex_refl uincl_on_refl uincl_ex_refl vm_uincl_init : core.
#[export] Hint Resolve eq_on_empty uincl_on_empty : core.
#[export] Hint Resolve truncatable_arr : core.

#[export] Existing Instance vm_rel_impl.
#[export] Existing Instance vm_rel_m.
#[export] Existing Instance eq_on_impl.
#[export] Existing Instance eq_on_m.
#[export] Existing Instance eq_ex_impl.
#[export] Existing Instance eq_ex_m.
#[export] Existing Instance uincl_on_impl.
#[export] Existing Instance uincl_on_m.
#[export] Existing Instance uincl_ex_impl.
#[export] Existing Instance uincl_ex_m.
#[export] Existing Instance equiv_vm_rel.
#[export] Existing Instance equiv_vm_eq.
#[export] Existing Instance equiv_eq_on.
#[export] Existing Instance equiv_eq_ex.
#[export] Existing Instance po_vm_rel.
#[export] Existing Instance po_value_uincl.
#[export] Existing Instance po_vm_uincl.
#[export] Existing Instance po_uincl_on.
#[export] Existing Instance po_uincl_ex.
#[export] Existing Instance uincl_ex_trans.

#[ global ]Arguments get_var {wsw} wdb vm%_vm_scope x.
#[ global ]Arguments set_var {wsw} wdb vm%_vm_scope x v.

