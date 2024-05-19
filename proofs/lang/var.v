(* ** Imports and settings *)
Require Import Setoid Morphisms.
From mathcomp Require Import ssreflect ssrfun ssrbool seq eqtype.
Require Import strings utils gen_map type ident tagged.
Require Import Utf8.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* ------------------------------------------------------------------------- *)


Module FunName : TaggedCore.
  Import PrimInt63.
  Definition t : Type := int.
  Definition tag (x : t) : int := x.

  Lemma tagI : injective tag.
  Proof. done. Qed.

End FunName.

Module TFunName <: TAGGED with Definition t := FunName.t
  := Tagged (FunName).

#[global] Canonical funname_eqType  := Eval compute in TFunName.t_eqType.

Module Mf  := TFunName.Mt.
Module Sf  := TFunName.St.
Module SfP := TFunName.StP.
Module SfD := TFunName.StD.

Definition funname := FunName.t.

Definition get_fundef {T} (p: seq (funname * T)) (f: funname) :=
  xseq.assoc p f.

(* ** Variables map, to be used when computation is needed
 * -------------------------------------------------------------------- *)

Module MvMake (I:IDENT).

  Import I Mid.
#[global]
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

#[global]
  Instance varO : Cmp var_cmp.
  Proof.
    constructor=> [x y | y x z c | [??] [??]] ;rewrite /var_cmp !Lex_lex.
    + by apply lex_sym;apply cmp_sym.
    + by apply lex_trans=> /=; apply cmp_ctrans.
    by move=> /lex_eq [] /= /(@cmp_eq _ _ stypeO) -> /(@cmp_eq _ _ K.cmpO) ->.
  Qed.

  Lemma var_surj (x:var) : x = Var x.(vtype) x.(vname).
  Proof. by case: x. Qed.

End MvMake.

Module Var := MvMake Ident.
Export Var.
Notation var   := Var.var.
Notation vtype := Var.vtype.
Notation vname := Var.vname.
Notation Var   := Var.Var.
Notation vbool i := {| vtype := sbool; vname := i; |}.

Lemma vtype_diff x x': vtype x != vtype x' -> x != x'.
Proof. by apply: contra => /eqP ->. Qed.

Lemma vname_diff x x': vname x != vname x' -> x != x'.
Proof. by apply: contra => /eqP ->. Qed.

(* ------------------------------------------------------------------------- *)
Definition is_glob_var (x: var) : bool :=
  if Ident.id_kind x.(vname) is Global then true else false.

Definition is_inline_var (x: var) : bool :=
  if Ident.id_kind x.(vname) is Inline then true else false.

Definition is_var_in_memory (x: var) : bool :=
  match Ident.id_kind x.(vname) with
  | Stack _ | Reg (_, Pointer _) | Global => true
  | Const | Inline | Reg (_, Direct) => false
  end.

Definition is_ptr (x: var) : bool :=
  match Ident.id_kind x.(vname) with
  | Reg (_, Pointer _) | Stack (Pointer _) => true
  | _ => false end.

Definition is_reg_ptr (x: var) : bool :=
  if Ident.id_kind x.(vname) is Reg (_, Pointer _) then true else false.

Definition is_regx (x: var) : bool :=
  if Ident.id_kind x.(vname) is Reg(Extra, _) then true else false.

Definition is_reg_array x :=
  if Ident.id_kind x.(vname) is Reg (_, Direct) then
    if x.(vtype) is sarr _ then true else false
  else false.

(* ** Finite set of variables (computable)
 *
 * -------------------------------------------------------------------- *)

Module CmpVar.

  Definition t := [eqType of var].

  Definition cmp : t -> t -> comparison := var_cmp.

  Definition cmpO : Cmp cmp := varO.

End CmpVar.

(* FIXME: move this *)
Module SExtra (T : CmpType).

Module Sv := Smake T.
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
  elim: (Sv.elements s) => /= [|v vs H]; split => //=.
  + by move /SetoidList.InA_nil.
  + by rewrite inE => /orP [ /eqP -> | /H];auto.
  case/SetoidList.InA_cons => [ -> |]; rewrite inE ?eq_refl //.
  by move /H => ->; rewrite orbT.
Qed.

Lemma Sv_elems_eq x s : Sv.mem x s = (x \in (Sv.elements s)).
Proof. by apply: sameP (Sv_memP x s) (Sv_elemsP x s). Qed.

Definition disjoint s1 s2 := Sv.is_empty (Sv.inter s1 s2).

#[global]
Instance disjoint_m :
  Proper (Sv.Equal ==> Sv.Equal ==> eq) disjoint.
Proof.
  by move => s1 s1' Heq1 s2 s2' Heq2;rewrite /disjoint Heq1 Heq2.
Qed.

#[global]
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

Lemma disjointP s1 s2 :
  reflect (forall x, Sv.In x s1 -> ~ Sv.In x s2) (disjoint s1 s2).
Proof.
  case: (@idP (disjoint s1 s2)) => hdisj; constructor.
  + move=> x h1 h2.
    move: hdisj; rewrite /disjoint => /Sv.is_empty_spec /(_ x) /Sv.inter_spec.
    by apply.
  move=> h; apply: hdisj.
  rewrite /disjoint.
  by apply /Sv.is_empty_spec => x /Sv.inter_spec []; apply h.
Qed.

Lemma disjoint_diff A B :
  disjoint A B →
  Sv.Equal (Sv.diff B A) B.
Proof.
  rewrite /disjoint /is_true Sv.is_empty_spec.
  SvD.fsetdec.
Qed.

Lemma in_disjoint_diff x a b c :
  Sv.In x a →
  Sv.In x b →
  disjoint a (Sv.diff b c) →
  Sv.In x c.
Proof. rewrite /disjoint /is_true Sv.is_empty_spec; SvD.fsetdec. Qed.

(* ---------------------------------------------------------------- *)
Lemma Sv_mem_add (s: Sv.t) (x y: Sv.elt) :
  Sv.mem x (Sv.add y s) = (x == y) || Sv.mem x s.
Proof.
  case: eqP.
  - move => <-; exact: SvP.add_mem_1.
  move => ne; exact: (SvD.F.add_neq_b _ (not_eq_sym ne)).
Qed.

Lemma Sv_Subset_union_left (a b c: Sv.t) :
  Sv.Subset a b → Sv.Subset a (Sv.union b c).
Proof. SvD.fsetdec. Qed.

Lemma Sv_Subset_union_right (a b c: Sv.t) :
  Sv.Subset a c → Sv.Subset a (Sv.union b c).
Proof. SvD.fsetdec. Qed.

Lemma Sv_union_empty (a : Sv.t) :
  Sv.Equal (Sv.union Sv.empty a) a.
Proof. SvD.fsetdec. Qed.

(* ---------------------------------------------------------------- *)

Definition sv_of_option (oa : option Sv.elt) : Sv.t :=
  oapp Sv.singleton Sv.empty oa.

(* ---------------------------------------------------------------- *)
Definition sv_of_list T (f: T → Sv.elt) : seq T → Sv.t :=
  foldl (λ s r, Sv.add (f r) s) Sv.empty.

Lemma sv_of_listE T (f: T → Sv.elt) x m :
  Sv.mem x (sv_of_list f m) = (x \in map f m).
Proof.
  suff h : forall s, Sv.mem x (foldl (λ (s : Sv.t) (r : T), Sv.add (f r) s) s m) = (x \in map f m) || Sv.mem x s by rewrite h orbF.
  elim: m => //= z m hrec s.
  rewrite hrec in_cons SvD.F.add_b /SvD.F.eqb.
  case: SvD.F.eq_dec => [-> | /eqP]; first by rewrite eqxx /= orbT.
  by rewrite eq_sym => /negbTE ->.
Qed.

Lemma sv_of_listP T (f: T → Sv.elt) x m :
  reflect (Sv.In x (sv_of_list f m)) (x \in map f m).
Proof. rewrite -sv_of_listE; apply Sv_memP. Qed.

Lemma sv_of_list_map A B (f: A → B) (g: B → Sv.elt) m :
  sv_of_list g (map f m) = sv_of_list (g \o f) m.
Proof.
  rewrite /sv_of_list.
  elim: m Sv.empty => // a m ih z.
  by rewrite /= ih.
Qed.

Lemma sv_of_list_mem_head X f (x : X) xs :
  Sv.mem (f x) (sv_of_list f (x :: xs)).
Proof. rewrite sv_of_listE. exact: mem_head. Qed.

Lemma sv_of_list_mem_tail X f v (x : X) xs :
  Sv.mem v (sv_of_list f xs)
  -> Sv.mem v (sv_of_list f (x :: xs)).
Proof.
  rewrite !sv_of_listE.
  rewrite in_cons.
  move=> ->.
  exact: orbT.
Qed.

Lemma sv_of_list_fold T f l s :
  Sv.Equal (foldl (λ (s : Sv.t) (r : T), Sv.add (f r) s) s l) (Sv.union s (sv_of_list f l)).
Proof.
  rewrite /sv_of_list; elim: l s => //= [ | a l hrec] s; first by SvD.fsetdec.
  rewrite hrec (hrec (Sv.add _ _)); SvD.fsetdec.
Qed.

Lemma sv_of_list_cons T (f : T -> _) x l :
  Sv.Equal (sv_of_list f (x::l)) (Sv.add (f x) (sv_of_list f l)).
Proof. rewrite /sv_of_list /= sv_of_list_fold; SvD.fsetdec. Qed.

Lemma sv_of_list_eq_ext {X} f g (xs : seq X) :
  (forall x, List.In x xs -> f x = g x) ->
  Sv.Equal (sv_of_list f xs) (sv_of_list g xs).
Proof.
  move=> /map_ext h.
  split; move=> /sv_of_listP ?; apply: sv_of_listP.
  - by rewrite -h.
  by rewrite h.
Qed.

Lemma disjoint_subset_diff xs ys :
  disjoint xs ys
  -> Sv.Subset xs (Sv.diff xs ys).
Proof.
  move=> /disjoint_sym /disjoint_diff /SvP.MP.equal_sym.
  exact: SvP.MP.subset_equal.
Qed.

Lemma in_add_singleton x y :
  Sv.In x (Sv.add y (Sv.singleton x)).
Proof. apply: SvD.F.add_2. exact: SvD.F.singleton_2. Qed.

Lemma disjoint_equal_l xs ys zs:
  Sv.Equal xs ys
  -> disjoint xs zs
  -> disjoint ys zs.
Proof.
  move=> heq /Sv.is_empty_spec h. apply/Sv.is_empty_spec. SvD.fsetdec.
Qed.

Lemma disjoint_equal_r xs ys zs:
  Sv.Equal xs ys
  -> disjoint ys zs
  -> disjoint xs zs.
Proof.
  move=> heq /Sv.is_empty_spec h. apply/Sv.is_empty_spec. SvD.fsetdec.
Qed.

Lemma disjoint_union xs ys zs :
  disjoint (Sv.union xs ys) zs
  -> disjoint xs zs /\ disjoint ys zs.
Proof.
 move=> /Sv.is_empty_spec H.
 split.
 all: apply/Sv.is_empty_spec.
 all: SvD.fsetdec.
Qed.

Lemma disjoint_add x xs ys :
  disjoint (Sv.add x xs) ys
  -> disjoint (Sv.singleton x) ys /\ disjoint xs ys.
Proof.
  move=> /Sv.is_empty_spec h.
  split.
  all: apply/Sv.is_empty_spec.
  all: move: h.
  all: SvD.fsetdec.
Qed.

Lemma union_disjoint xs ys zs :
  disjoint xs zs
  -> disjoint ys zs
  -> disjoint (Sv.union xs ys) zs.
Proof.
  rewrite /disjoint.
  move=> /Sv.is_empty_spec h0.
  move=> /Sv.is_empty_spec h1.
  apply/Sv.is_empty_spec.
  move: h0 h1.
  clear.
  SvD.fsetdec.
Qed.

Lemma disjoint_singleton x s :
  disjoint (Sv.singleton x) s = ~~ Sv.mem x s.
Proof.
  case: disjointP; case: Sv_memP => //.
  - move => H K; elim: (K _ _ H); SvD.fsetdec.
  by move => H K; elim: K => y /Sv.singleton_spec ->.
Qed.

Lemma Sv_equal_add_add x s :
  Sv.Equal (Sv.add x (Sv.add x s)) (Sv.add x s).
Proof. SvD.fsetdec. Qed.

Lemma Sv_neq_not_in_singleton x y :
  x <> y
  -> ~ Sv.In y (Sv.singleton x).
Proof. SvD.fsetdec. Qed.

Lemma Sv_subset_remove s x :
  Sv.subset (Sv.remove x s) s.
Proof. apply/Sv.subset_spec. by apply: SvP.MP.subset_remove_3. Qed.

Lemma Sv_diff_empty s :
  Sv.Equal (Sv.diff s Sv.empty) s.
Proof. SvD.fsetdec. Qed.

Lemma enum_in_Sv X (_ : finTypeC X) to_var s x :
  Sv.Subset (sv_of_list to_var cenum) s ->
  Sv.In (to_var x) s.
Proof.
  apply; apply/sv_of_listP.
  apply: (@map_f (@ceqT_eqType X _eqC)).
  exact: mem_cenum.
Qed.

(* Deduce inequalities from [~ Sv.In x (Sv.add y0 (... (Sv.add yn s)))]. *)
Ltac t_notin_add :=
  repeat (move=> /Sv.add_spec /Decidable.not_or [] ?);
  move=> ?.

End SExtra.

Module SvExtra := SExtra CmpVar.
Export SvExtra.

(* Non dependant map *)
Module Mvar :=  Mmake CmpVar.

Definition Mvar_eq T (m1 m2:Mvar.t T) :=
  forall x, Mvar.get m1 x = Mvar.get m2 x.

#[global]
Polymorphic Instance equiv_Mvar_eq T : Equivalence (@Mvar_eq T).
Proof.
  split=> //.
  + by move=> m1 m2 Hm z;rewrite Hm.
  by move=> m1 m2 m3 Hm1 Hm2 z;rewrite Hm1 Hm2.
Qed.

#[global]
Instance Mvar_get_m T:
  Proper (@Mvar_eq T ==> eq ==> eq) Mvar.get.
Proof. by move=> m1 m2 Hm ?? <-. Qed.

#[global]
Instance Mvar_set_m T:
  Proper (@Mvar_eq T ==> eq ==> eq ==> @Mvar_eq T) Mvar.set.
Proof. by move=> m1 m2 Hm ?? <- ?? <- z;rewrite !Mvar.setP;case:ifP. Qed.

#[global]
Instance Mvar_remove_m T:
  Proper (@Mvar_eq T ==> eq ==> @Mvar_eq T) Mvar.remove.
Proof. by move=> m1 m2 Hm ?? <- z;rewrite !Mvar.removeP;case:ifP. Qed.
