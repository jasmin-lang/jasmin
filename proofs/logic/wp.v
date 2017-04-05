Require Ssem.

Import Utf8.
Import Morphisms.
Import ssreflect.
Import ssrbool.
Import eqtype.
Import seq.
Import ZArith.
Local Open Scope Z_scope.

Import utils.
Import type.
Import var.
Import expr.
Import sem.
Import Ssem.
Import memory.
Import UnsafeMemory.

Definition MkI_inj {ii i ii' i'} (H: MkI ii i = MkI ii' i') :
  ii = ii' ∧ i = i' :=
  let 'Logic.eq_refl := H in conj Logic.eq_refl Logic.eq_refl.

Definition Some_inj {A} (a a': A) (H: Some a = Some a') : a = a' :=
  let 'Logic.eq_refl := H in Logic.eq_refl.

Definition ok_inj {E A} (a a': A) (H: Ok E a = ok a') : a = a' :=
  let 'Logic.eq_refl := H in Logic.eq_refl.

Lemma of_sval_to_sval ty x :
  of_sval ty (to_sval x) = ok x.
Proof. by move: x; case ty. Qed.

Lemma sto_word_inv x i :
  sto_word x = ok i →
  x = i.
Proof. case: x => // i' H; apply ok_inj in H. congruence. Qed.

Lemma sto_int_inv x i :
  sto_int x = ok i →
  x = i.
Proof. case: x => // i' H; apply ok_inj in H. congruence. Qed.

Lemma sto_bool_inv x b :
  sto_bool x = ok b →
  x = b.
Proof. case: x => // i' H; apply ok_inj in H. congruence. Qed.

Lemma sto_arr_inv x a :
  sto_arr x = ok a →
  ∃ n, x = SVarr n a.
Proof. case: x => // n a' H;apply ok_inj in H. exists n; congruence. Qed.

Lemma slet_inv {A s x} {f: _ → _ → exec A} {y} :
  SLet (n, t) := s.[x] in f n t = ok y →
  ∃ n (Tx: vtype x = sarr n), f n (eq_rect _ _ (sevm s).[x]%vmap _ Tx) = ok y.
Proof.
  unfold son_arr_var.
  generalize ((sevm s).[x])%vmap.
  case: (vtype x) => // n t E.
  exists n, Logic.eq_refl. exact E.
Qed.

Lemma ssem_inv { prg s c s' } :
  ssem prg s c s' →
  match c with
  | [::] => s' = s
  | i :: c' => ∃ si, ssem_I prg s i si ∧ ssem prg si c' s'
end.
Proof. case; eauto. Qed.

Lemma ssem_I_inv { prg s i s' } :
  ssem_I prg s i s' →
  ∃ i' ii, i = MkI ii i' ∧ ssem_i prg s i' s'.
Proof. case; eauto. Qed.

Lemma ssem_i_inv { prg s i s' } :
  ssem_i prg s i s' →
  match i with
  | Cassgn x tg e => ∃ v, ssem_pexpr s e = ok v ∧ swrite_lval x v s = ok s'
  | Cif e c1 c2 => ∃ b : bool, ssem_pexpr s e = ok (SVbool b) ∧ ssem prg s (if b then c1 else c2) s'
  | _ => True
  end.
Proof.
  case; eauto; clear.
  - (* Cassgn *)
  move=> s s' x _ e; apply: rbindP; eauto.
  - (* Cif true *)
  move=> s s' e c1 c2; apply: rbindP => v Hv /sto_bool_inv ?; subst v; eauto.
  - (* Cif false *)
  move=> s s' e c1 c2; apply: rbindP => v Hv /sto_bool_inv ?; subst v; eauto.
Qed.

Lemma swrite_lval_inv {x v s s'} :
  swrite_lval x v s = ok s' →
  match x with
  | Lnone _ => s' = s
  | Lvar x => ∃ v', of_sval (vtype x) v = ok v' ∧
                    s' = {| semem := semem s ; sevm := (sevm s).[ x <- v' ] |}
  | Lmem x e =>
    ∃ (Tx: vtype x = sword),
    ∃ vx ve w: word, eq_rect _ _ ((sevm s).[ x ]) _ Tx = vx ∧ ssem_pexpr s e = ok (SVword ve) ∧ v = w ∧
               s' = {| semem := write_mem (semem s) (I64.add vx ve) w ; sevm := sevm s |}
  | Laset x i =>
    ∃ n (Tx: vtype x = sarr n) (vi : Z) (w: word),
  ssem_pexpr s i = ok (SVint vi) ∧
  v = w ∧
  let q := FArray.set (eq_rect (vtype x) ssem_t ((sevm s).[x]) (sarr n) Tx) vi w in
  s' = {| semem := semem s ; sevm := (sevm s).[x <- eq_rect _ _ q _ (Logic.eq_sym Tx)] |}
end%vmap.
Proof.
  destruct x as [ vi | x | x e | x i ].
  - move=> H; apply ok_inj in H; auto.
  - apply: rbindP => vm H K; apply ok_inj in K; subst s'.
    revert H; apply: rbindP => v' H X; apply ok_inj in X; subst vm; eauto.
  - apply: rbindP => vx /sto_word_inv H.
    apply: rbindP => ve.
    apply: rbindP => ve' He /sto_word_inv ?; subst ve'.
    apply: rbindP => w /sto_word_inv -> X; apply ok_inj in X; subst s'.
    unfold sget_var in H.
    case: x H=> [[[] x] xi] //.
    exists Logic.eq_refl, vx, ve, w.
    split. simpl in *. congruence. auto.
  - move=> /slet_inv [n [Tx H]].
    exists n, Tx.
    apply: rbindP H=> vi;apply: rbindP => vj Hi /sto_int_inv H;subst vj.
    apply: rbindP => w /sto_word_inv ->;apply: rbindP => vm' L [<-].
    exists vi, w;split=> //;split=>//=;f_equal;f_equal.
    by case: x Tx L=>  -[ty x] xi /= ?;subst ty => /= -[] <-.
Qed.

Definition hpred : Type :=
  sestate → Prop.

Notation "A ⊂ B" := (∀ x, A x → B x) (at level 80) : msem_scope.

Local Open Scope msem_scope.

Section HOARE_LOGIC.

Context (prg: prog).

Definition hoare (Pre: hpred) (c: cmd) (Post: hpred) : Prop :=
  ∀ s s' : sestate,
    ssem prg s c s' →
    Pre s → Post s'.

Lemma hoare_conseq (P1 Q1: hpred) (c: cmd) (P2 Q2: hpred) :
  P2 ⊂ P1 → Q1 ⊂ Q2 →
  hoare P1 c Q1 → hoare P2 c Q2.
Proof. firstorder. Qed.

Lemma hoare_skip_core P : hoare P [::] P.
Proof. by move => s s' H; case (ssem_inv H). Qed.

Lemma hoare_skip (Q P: hpred) : Q ⊂ P → hoare Q [::] P.
Proof. eauto using hoare_conseq, hoare_skip_core. Qed.

Lemma hoare_cons R P Q i c :
  hoare P [:: i] R →  hoare R c Q →  hoare P (i :: c) Q.
Proof.
  by
  move=> Hi Hc s s' /ssem_inv [ s1 [Hi' Hc']] H;
  eauto using SEseq, SEskip.
Qed.

Lemma hoare_assgn (P: hpred) ii x tag e :
  hoare
    (λ s, ∀ v s',
        ssem_pexpr s e = ok v →
        swrite_lval x v s = ok s' →
        P s')
    [:: MkI ii (Cassgn x tag e) ] P.
Proof.
  move=> s s1 / ssem_inv [ s' [Hi /ssem_inv]] ->.
  case: (ssem_I_inv Hi) => i' [ ii' [ /MkI_inj [? ?] Hi' ] ]; clear Hi; subst ii' i'.
  move: (ssem_i_inv Hi') => [ v [ Hv Hs' ] ].
  exact (λ H, H _ _ Hv Hs').
Qed.

End HOARE_LOGIC.

Section WEAKEST_PRECONDITION.

(* A formula is a predicate over an environment that maps logical variables to value. *)
(* This predicate should be extensional *)

Definition env : Type := Mv.t ssem_t.
Definition env_ext (m m': env) : Prop :=
  ∀ x, (m.[x] = m'.[x])%mv.

Definition env_ext_refl m : env_ext m m := λ x, Logic.eq_refl.

Definition env_ext_sym m m' (H: env_ext m m') : env_ext m' m :=
  λ x, Logic.eq_sym (H x).

Definition env_ext_trans m' m m'' (H: env_ext m m') (H': env_ext m' m'') :
  env_ext m m'' :=
  λ x, Logic.eq_trans (H x) (H' x).

Lemma env_ext_empty m m' :
  (∀ x, m x = m' x) →
  env_ext (Mv.empty m) (Mv.empty m').
Proof. by move=> E x; rewrite ! Mv.get0. Qed.

Lemma env_ext_set m m' x v :
  env_ext m m' →
  (env_ext (m.[x <- v]) (m'.[x <- v]))%mv.
Proof.
  move=> E y.
  case: (x =P y) => [ <- | H ].
  rewrite ! Mv.setP_eq //.
  assert (x != y) by (case: eqP => //).
  rewrite ! Mv.setP_neq //.
Qed.

Definition formula : Type :=
  sigT (Proper (@eq mem ==> env_ext ==> iff)).

Lemma formula_m (f: mem → env → Prop) :
  (∀ m s s', env_ext s s' → f m s → f m s') →
  Proper (@eq mem ==> env_ext ==> iff) f.
Proof.
  move=> E m ? <- s s' H.
  split; eauto using env_ext_sym.
Qed.

Instance constant_formula_m (P: Prop) : Proper (@eq mem ==> env_ext ==> iff) (λ _ _, P) :=
  formula_m _ (λ _ _ _ _ (p: P), p).

Example ftrue: formula := existT _ (λ _ _, True) _.
Example ffalse: formula := existT _ (λ _ _, False) _.

Definition formula_of_hpred (P: hpred) : formula.
Proof.
  refine (existT _ (λ (m: mem) (s: env), P {| semem := m ; sevm := Fv.empty (λ x, s.[x])%mv |}) _).
  apply formula_m.
  move=> m s s' E H.
  refine (eq_ind _ P H _ _).
  f_equal.
  apply Fv.map_ext. auto.
Defined.

Notation "⟨ P ⟩" := (formula_of_hpred P) : msem_scope.

Definition formula_denote (f: formula) : hpred :=
  λ s, projT1 f (semem s) (Mv.empty (λ x, (sevm s).[x])%vmap).

Notation "⟦ f ⟧" := (formula_denote f) : msem_scope.

Lemma formula_of_hpred_denote P :
  ∀ s, ⟦ ⟨P⟩ ⟧ s ↔ P s.
Proof.
  unfold formula_of_hpred, formula_denote. simpl.
  by
  move=> [ m vm ]; split; move=> H; refine (eq_ind _ P H _ _); f_equal; apply Fv.map_ext; move=> x;
  rewrite Fv.get0 Mv.get0.
Qed.

Remark ffalse_denote (P: Prop) s : ⟦ ffalse ⟧ s → P.
Proof. easy. Qed.

Variant stype' : Type := sint' | sbool'.

Definition stype_of_stype' (ty: stype') : stype :=
  match ty with
  | sint' => sint
  | sbool' => sbool
  end.

Local Coercion stype_of_stype' : stype' >-> stype.

Definition op2_type (op: sop2) : stype' * stype' :=
  match op with
  | (Oand | Oor ) => (sbool', sbool')
  | (Oadd | Omul | Osub) => (sint', sint')
  | (Oeq | Oneq | Olt | Ole | Ogt | Oge) => (sint', sbool')
  end.

Definition op2_type_i op := fst (op2_type op).
Definition op2_type_o op := snd (op2_type op).

Definition sem_texpr_sop2 op : ssem_t (op2_type_i op) → ssem_t (op2_type_i op) → ssem_t (op2_type_o op) :=
  match op with
  | Oand => andb
  | Oor => orb
  | Oadd => Z.add
  | Omul => Z.mul
  | Osub => Z.sub
  | Oeq => Z.eqb
  | Oneq => λ x y, negb (Z.eqb x y)
  | Olt => Z.ltb
  | Ole => Z.leb
  | Ogt => Z.gtb
  | Oge => Z.geb
  end.

Inductive texpr : stype → Type :=
| Tconst : Z → texpr sint
| Tbool : bool → texpr sbool
| Tcast : texpr sint → texpr sword
| Tvar x : texpr (vtype x)
| Tget : positive → Ident.ident → texpr sint → texpr sword
| Tload : Ident.ident → texpr sword → texpr sword
| Tnot : texpr sbool → texpr sbool
| Tapp2 op (_ _: texpr (op2_type_i op)) : texpr (op2_type_o op)
.

Section SEM_TEXPR.
  Context (m: mem) (s: env).
  Fixpoint sem_texpr ty (e: texpr ty) : ssem_t ty :=
    match e in texpr ty return ssem_t ty with
    | Tconst z => z
    | Tbool b => b
    | Tcast e => I64.repr (sem_texpr sint e)
    | Tvar x => s.[x]
    | Tget n x e =>
      let a := s.[{| vtype := sarr n; vname := x |}] in
      let i := sem_texpr sint e in
      FArray.get a i
    | Tload x e =>
      let w1 := s.[{| vtype := sword; vname := x |}] in
      let w2 := sem_texpr sword e in
      let w := read_mem m (I64.add w1 w2) in
      w
    | Tnot e => negb (sem_texpr sbool e)
    | Tapp2 op e1 e2 =>
      let v1 := sem_texpr (op2_type_i op) e1 in
      let v2 := sem_texpr (op2_type_i op) e2 in
      sem_texpr_sop2 op v1 v2
    end%mv.
End SEM_TEXPR.

Lemma sem_texpr_m (m: mem) (s s': env) :
  env_ext s s' →
  ∀ ty e, sem_texpr m s ty e = sem_texpr m s' ty e.
Proof.
  move=> E ty e. 
  elim: e => //=;congruence.
Qed.

Scheme Equality for stype.

Fixpoint type_check_pexpr (e: pexpr) (ty: stype) : option (texpr ty) :=
  match e with
  | Pconst z => match ty with sint => Some (Tconst z) | _ => None end
  | Pbool b => match ty with sbool => Some (Tbool b) | _ => None end
  | Pcast p =>
    match type_check_pexpr p sint with
    | Some tp => match ty with sword => Some (Tcast tp) | _ => None end
    | None => None end
  | Pvar x =>
    match stype_eq_dec (vtype x) ty with
    | left EQ => Some (eq_rect _ _ (Tvar x) _ EQ)
    | right _ => None
    end
  | Pget x i =>
    match x with
    | {| v_var := Var (sarr n) t |} =>
    match type_check_pexpr i sint with
    | Some ti => match ty with sword => Some (Tget n t ti) | _ => None end
    | None => None end
    | _ => None end
  | Pload x i =>
    match x with
    | {| v_var := Var sword p |} =>
    match type_check_pexpr i sword with
    | Some ti => match ty with sword => Some (Tload p ti) | _ => None end
    | None => None end
    | _ => None end
  | Pnot p =>
    match type_check_pexpr p sbool with
    | Some tp => match ty with sbool => Some (Tnot tp) | _ => None end
    | None => None end
  | Papp2 op p q =>
    match type_check_pexpr p (op2_type_i op) with
    | Some tp =>
    match type_check_pexpr q (op2_type_i op) with
    | Some tq =>
      match stype_eq_dec (op2_type_o op) ty with
      | left EQ => Some (eq_rect _ _ (Tapp2 op tp tq) _ EQ)
      | _ => None end
    | None => None end
    | None => None end
  end.

Lemma ssem_sop2_inv op vp vq v :
  ssem_sop2 op vp vq = ok v →
  ∀ p q,
    of_sval (op2_type_i op) vp = ok p →
    of_sval (op2_type_i op) vq = ok q →
    of_sval (op2_type_o op) v = ok (sem_texpr_sop2 op p q).
Proof.
  case: op; simpl; intros;
    repeat
      match goal with
      | H : ?a = ?b |- _ => subst a || subst b
      | H : sto_bool _ = ok _ |- _ => apply sto_bool_inv in H
      | H : sto_int _ = ok _ |- _ => apply sto_int_inv in H
      | H : _ = ok _ |- _ => apply ok_inj in H
      end; reflexivity.
Qed.

Lemma type_check_pexprP {e ty te} :
  type_check_pexpr e ty = Some te →
  ∀ m s v,
  ssem_pexpr (SEstate m s) e = ok v →
  ∀ s',
  (∀ x, s.[x]%vmap = s'.[x]%mv) →
  of_sval _ v = ok (sem_texpr m s' ty te).
Proof.
  elim: e ty te.
  - move=> z [] // te H; apply Some_inj in H; subst.
    move=> m s v H; apply ok_inj in H; subst v.
    reflexivity.
  - move=> b [] // te H; apply Some_inj in H; subst.
    move=> m s v H; apply ok_inj in H; subst v.
    reflexivity.
  - move=> p IHp ty te; simpl.
    move: (IHp sint); clear IHp.
    case: (type_check_pexpr p _) => // tp IHp.
    move: te. case: ty => // te H; apply Some_inj in H; subst.
    specialize (IHp _ Logic.eq_refl).
    move=> m s v.
    apply: rbindP => vp; apply: rbindP => ip Ep /sto_int_inv ?; subst ip.
    move=> H; apply ok_inj in H; subst.
    move=> s' E. simpl.
    specialize (IHp _ _ _ Ep _ E).
    apply sto_int_inv in IHp. congruence.
  - move=> v ty te. simpl. case: stype_eq_dec => //.
    move=> EQ H; apply Some_inj in H; subst.
    move=> m s v' H; apply ok_inj in H; subst v'.
    move=> s' E. simpl. unfold sget_var. rewrite E.
    apply of_sval_to_sval.
  - move=> [[]] // [] // n t vi e IH ty te /=.
    move: (IH sint). clear IH.
    case: (type_check_pexpr _ _) => // tt IH.
    specialize (IH _ Logic.eq_refl).
    move: te. case: ty => // te H; apply Some_inj in H; subst.
    move=> m s v; apply: rbindP => vp; apply: rbindP => i Ei /sto_int_inv ?; subst i.
    move=> H; apply ok_inj in H; subst.
    move=> s' E /=.
    specialize (IH _ _ _ Ei _ E).
    apply sto_int_inv in IH.
    congruence.
  - move=> [[]] // [] // x xi p IHp ty te; simpl.
    move: (IHp sword); clear IHp.
    case: (type_check_pexpr p _) => // tp IHp.
    specialize (IHp _ Logic.eq_refl).
    move: te. case: ty => // te H; apply Some_inj in H; subst.
    move=> m s v; apply: rbindP => vp; apply: rbindP => ip Ep /sto_word_inv ?; subst ip.
    move=> H; apply ok_inj in H; subst.
    move=> s' E /=.
    specialize (IHp _ _ _ Ep _ E).
    apply ok_inj in IHp; subst vp.
    congruence.
  - move=> p IHp ty te /=.
    move: (IHp sbool); clear IHp.
    case: (type_check_pexpr p _) => // tp IHp.
    move: te. case: ty => // te H; apply Some_inj in H; subst.
    specialize (IHp _ Logic.eq_refl).
    move=> m s v; apply: rbindP => vp; apply: rbindP => ip Ep /sto_bool_inv ?; subst ip.
    move=> H; apply ok_inj in H; subst.
    move=> s' E /=.
    specialize (IHp _ _ _ Ep _ E).
    apply sto_bool_inv in IHp. congruence.
  - move=> op p IHp q IHq ty te /=.
    move: (IHp (op2_type_i op)). clear IHp.
    case: (type_check_pexpr p _) => // tp IHp.
    specialize (IHp _ Logic.eq_refl).
    move: (IHq (op2_type_i op)). clear IHq.
    case: (type_check_pexpr q _) => // tq IHq.
    specialize (IHq _ Logic.eq_refl).
    case (stype_eq_dec _ _) => // EQ. subst ty.
    move=> H; apply Some_inj in H; subst te.
    move=> m s v; apply: rbindP => vp Ep; apply: rbindP => vq Eq.
    move=> H.
    move=> s' E /=.
    specialize (IHp _ _ _ Ep _ E).
    specialize (IHq _ _ _ Eq _ E).
    eauto using ssem_sop2_inv.
Qed.

Definition has_pointer_type (x: var) : { vtype x = sword } + { True } :=
  match vtype x with
  | sword => left Logic.eq_refl
  | _ => right I
  end.

Definition has_array_type (x: var) : { n | vtype x = sarr n } + { True } :=
  match vtype x with
  | sarr n => inleft (exist _ n Logic.eq_refl)
  | _ => inright I
  end.

Definition post_assgn (x: lval) {ty} (w: ssem_t ty) (f: formula) (m: mem) (s: env) : Prop :=
  match x with
  | Lnone _ => projT1 f m s
  | Lvar {| v_var := x |} =>
    match stype_eq_dec ty (vtype x) with
    | left EQ =>
      let v : ssem_t (vtype x) := eq_rect _ _ w _ EQ in projT1 f m (s.[x <- v])%mv
    | right _ => False
    end
  | Lmem {| v_var := x |} e =>
    match has_pointer_type x with
    | left Tx =>
    match type_check_pexpr e sword with
    | Some te =>
    match stype_eq_dec ty sword with
    | left EQ =>
      ∀ i m',
      sem_texpr m s sword te = i →
      let v := eq_rect _ _ w _ EQ in
      write_mem m (I64.add (eq_rect _ _ (s.[x])%mv _ Tx) i) v = m' →
      projT1 f m' s
    | right _ => False end
    | None => False end
    | right _ => False end
  | Laset x e =>
    match has_array_type x with
    | inleft (exist n Tx as Tx') =>
    match type_check_pexpr e sint with
    | Some te =>
    match stype_eq_dec ty sword with
    | left EQ =>
      ∀ i,
      let t := eq_rect _ _  s.[x]%mv _ Tx in
      sem_texpr m s sint te = i →
      let v := eq_rect _ _ w _ EQ in
      let a : ssem_t (vtype x) := eq_rect _ _ (FArray.set t i v) _ (Logic.eq_sym Tx) in
      projT1 f m (s.[x <- a])%mv
    | right _ => False end
    | None => False end
    | inright _ => False end
  end.

Definition type_of_pexpr (e: pexpr) : stype :=
  match e with
  | Pconst _ => sint
  | Pbool _ | Pnot _ => sbool
  | Pcast _
  | Pget _ _
  | Pload _ _
    => sword
  | Pvar {| v_var := x |} => vtype x
  | Papp2 op _ _ => op2_type_o op
  end.

Definition default_texpr (ty: stype') : texpr ty :=
  match ty with
  | sbool' => Tbool true
  | sint' => Tconst 42
  end.

Definition texpr_of_pexpr (ty: stype') (pe: pexpr) : texpr ty :=
  match type_check_pexpr pe ty with
  | Some te => te
  | None => default_texpr ty
  end.

Lemma post_assgn_m { s s' } :
  env_ext s s' →
  ∀ x ty (v: ssem_t ty) f m,
  post_assgn x v f m s →
  post_assgn x v f m s'.
Proof.
  move=> E [ x | [x xn] | [x xn] e | x e ] ty v f m /=.
  - (* Lnone *) by apply (projT2 f m).
  - (* Lvar *)
    case: stype_eq_dec => // Te.
    apply (projT2 f m). auto.
    subst. simpl. apply env_ext_set, env_ext_sym, E.
  - (* Lmem *)
    case: has_pointer_type => // Ty.
    case (type_check_pexpr e _) eqn: Te; auto.
    case: stype_eq_dec => // ?; subst.
    move=> /= H ? ? ? ?; subst.
    rewrite (projT2 f). apply: H; auto.
    repeat (f_equal; auto using sem_texpr_m, env_ext_sym).
    auto using env_ext_sym.
  - (* Laset *)
    case: has_array_type => // [[n Tx]].
    case (type_check_pexpr e _) eqn: Te; auto.
    case: stype_eq_dec => // ?; subst.
    move=> /= H ? ?; subst.
    rewrite (projT2 f). apply: H; auto. auto.
    rewrite (sem_texpr_m _ _ _ E) E.
    apply env_ext_set, env_ext_sym, E.
Qed.

Definition wp_assgn (x: lval) (e: pexpr) (f: formula) : formula.
  refine (
  let ty := type_of_pexpr e in
  match type_check_pexpr e ty with
  | Some te =>
    existT _ (
    λ m s,
    ∀ v, sem_texpr m s ty te = v → post_assgn x v f m s
    ) _
  | None => ffalse
  end).
Proof.
  abstract (
  apply: formula_m => m s s' E X v Hv;
  specialize (X v); apply: (post_assgn_m E); apply: X; rewrite <- Hv;
  eauto using sem_texpr_m
  ).
Defined.

Definition wp_set (x: var) (e: pexpr) (f: formula) : formula.
  refine
  match type_check_pexpr e (vtype x) with
  | Some te =>
    existT _ (
    λ m s,
    ∀ v, sem_texpr m s (vtype x) te = v → projT1 f m (s.[x <- v])%mv) _
  | None => ffalse
  end.
Proof.
  abstract (
  apply formula_m;
  move=> m s s' E X v V;
  rewrite (projT2 f m); [| reflexivity | apply env_ext_set, env_ext_sym, E ];
  apply X; etransitivity; [ apply sem_texpr_m, E | exact V ]).
Defined.

Definition wp_aset (x: var) (e e': pexpr) (f: formula) : formula.
  refine
  match has_array_type x with
  | inleft (exist n Tx as Tx') =>
  match type_check_pexpr e sint with
  | Some te =>
  match type_check_pexpr e' sword with
  | Some te' =>
    existT _ (
    λ m s,
    ∀ i v,
      let t := eq_rect _ _  s.[x]%mv _ Tx in
      sem_texpr m s sint te = i →
      sem_texpr m s sword te' = v →
      let a : ssem_t (vtype x) := eq_rect _ _ (FArray.set t i v) _ (Logic.eq_sym Tx) in
      projT1 f m (s.[x <- a])%mv) _
  | None => ffalse end
  | None => ffalse end
  | inright _ => ffalse end.
Proof.
  abstract (
  apply formula_m;
  move=> m s s' E X i v /= Hi Hv;
  rewrite (projT2 f m); [| reflexivity | apply env_ext_set, env_ext_sym, E ];
  specialize (X i v);
  rewrite ! (sem_texpr_m _ _ _ E) in X;
  specialize (X Hi Hv);
  rewrite E in X;
  exact X
  ).
Defined.

Definition wp_store (x: var) (e e': pexpr) (f: formula) : formula.
  refine
  match has_pointer_type x with
  | left Tx =>
  match type_check_pexpr e sword with
  | Some te =>
  match type_check_pexpr e' sword with
  | Some te' =>
    existT _ (
    λ m s,
    ∀ i v m',
      sem_texpr m s sword te = i →
      sem_texpr m s sword te' = v →
      write_mem m (I64.add (eq_rect _ _ (s.[x])%mv _ Tx) i) v = m' →
      projT1 f m' s
    ) _
  | None => ffalse end
  | None => ffalse end
  | right _ => ffalse end.
Proof.
  abstract (
  apply formula_m;
  move=> m s s' E X i v m' /= Hi Hv Hm';
  specialize (X i v m');
  rewrite (projT2 f m'); [ | reflexivity | apply env_ext_sym, E ];
  rewrite ! (sem_texpr_m _ _ _ E) in X;
  rewrite E in X;
  exact (X Hi Hv Hm')).
Defined.

Lemma eq_rect_eq {K} (T T1 T2: K) F (x1: F T1) (x2: F T2) (H1: T1 = T) (H2: T2 = T):
  (∀ E, x1 = eq_rect _ _ x2 _ E) →
  eq_rect T1 F x1 T H1 = eq_rect T2 F x2 T H2.
Proof.
  subst. exact (λ H, H Logic.eq_refl).
Qed.

Lemma wp_assgn_sound prg ii x e tg f :
  hoare prg ⟦wp_assgn x e f⟧ [:: MkI ii (Cassgn x tg e)] ⟦f⟧.
Proof.
  move=> [m vm] s1 /ssem_inv [s' [/ssem_I_inv [i' [ii' [/MkI_inj [? <-]] /ssem_i_inv [v [Hv Hs']]]] /ssem_inv ->]]; subst ii'.
  unfold wp_assgn.
  case (type_check_pexpr _ _) eqn: EQ. 2: apply: ffalse_denote.
  move: (type_check_pexprP EQ _ _ _ Hv) => R /=.
  specialize (R _ (λ x, Logic.eq_sym (Mv.get0 _ x))).
  case: x Hs' => [ xi | [x xn] | [x xn] e' | x e' ] /swrite_lval_inv.
  - (* Lnone *)
    move=> -> H; apply: H; eauto.
  - (* Lvar *)
    move=> /= [ v' [Hvv' ?] ] /(_ _ Logic.eq_refl); subst s'.
    case: stype_eq_dec => // Te.
    unfold formula_denote; simpl.
    apply (projT2 f m). reflexivity.
    apply: env_ext_empty.
    move=> y.
    case: (x =P y).
    move=> <-. rewrite ! (Fv.setP_eq, Mv.setP_eq).
    move: Te v' Hvv'. intros ().
    move=> v' Hvv' /=.
    apply: ok_inj. etransitivity. symmetry. apply: Hvv'. auto.
    move=> NE. rewrite ! (Fv.setP_neq, Mv.setP_neq) //; case: eqP => //.
  - (* Lmem *)
    move=> [Tx [vx [ve [w [Hvx [Hve [? ?]]]]]]] /(_ _ Logic.eq_refl) /=; subst.
    case: has_pointer_type => // Tx'.
    case (type_check_pexpr e' _) eqn: Te'. 2: easy.
    case: stype_eq_dec => // Te /(_ _ _ Logic.eq_refl) /(_ Logic.eq_refl) /=.
    unfold formula_denote; simpl.
    apply (projT2 f). 2: apply: env_ext_empty; reflexivity.
    f_equal. f_equal.
    rewrite Mv.get0.
    apply eq_rect_eq. clear. move=> E.
    by move: (Eqdep_dec.UIP_dec type.stype_eq_dec E Logic.eq_refl) ->.
    move: (type_check_pexprP Te' _ _ _ Hve) => Re.
    apply: ok_inj; apply Re. auto.
    simpl in *.
    clear Tx'. revert Tx. generalize (vtype x). clear x. intros s ->.
    destruct (type_of_pexpr e) => //.
    move: (Eqdep_dec.UIP_dec type.stype_eq_dec Te Logic.eq_refl) ->. simpl.
    apply ok_inj in R. subst. auto.
  - (* Laset *)
    move=> [ n [ Tx [ vi [ w [ Hvi [? ?]]]]]] /(_ _ Logic.eq_refl); simpl in *; subst.
    case: has_array_type => // [[n' Tx']].
    case (type_check_pexpr e' _) eqn: Te'. 2: easy.
    case: stype_eq_dec => // Te /(_ _ Logic.eq_refl).
    unfold formula_denote. simpl.
    apply (projT2 f). reflexivity.
    apply: env_ext_empty.
    move=> y. rewrite Mv.get0.
    case: (v_var x =P y).
    move=> <-. rewrite ! (Fv.setP_eq, Mv.setP_eq, Mv.get0).
    move: (type_check_pexprP Te' _ _ _ Hvi) => /(_ _ (λ x, Logic.eq_sym (Mv.get0 _ x))) Re.
    apply ok_inj in Re. subst.
    apply eq_rect_eq.
    assert (n = n'). congruence. subst n'. move=> E.
    move: (Eqdep_dec.UIP_dec type.stype_eq_dec E Logic.eq_refl) ->. simpl. f_equal.
    apply eq_rect_eq. clear. move=> E.
    move: (Eqdep_dec.UIP_dec type.stype_eq_dec E Logic.eq_refl) ->. reflexivity.
    destruct (type_of_pexpr e) => //.
    move: (Eqdep_dec.UIP_dec type.stype_eq_dec Te Logic.eq_refl) ->. simpl.
    apply ok_inj in R. subst. auto.
    move=> NE. rewrite ! (Fv.setP_neq, Mv.setP_neq) //; case: eqP => //.
Qed.

Definition formula_equiv (P Q: formula) : Prop :=
  ∀ m s, projT1 P m s ↔ projT1 Q m s.

Local Infix "≡" := formula_equiv (at level 80) : msem_scope.
Local Notation "(≡)" := (formula_equiv) (at level 8) : msem_scope.

Instance formula_equivE : Equivalence (≡).
Proof.
  constructor.
  move=> f m s; tauto.
  move=> f f' H m s. specialize (H m s). tauto.
  move=> x y z Hxy Hyz m s. specialize (Hxy m s). specialize (Hyz m s). tauto.
Qed.

Definition wp_if (e: pexpr) (wp_c1 wp_c2: formula → formula) (post: formula) : formula.
  refine
  match type_check_pexpr e sbool with
  | Some te =>
    existT _ (
      λ m s,
      ∀ Q,
      post ≡ Q →
      (sem_texpr m s sbool te = true → projT1 (wp_c1 Q) m s) ∧
      (sem_texpr m s sbool te = false → projT1 (wp_c2 Q) m s)
    ) _
  | None => ffalse
  end.
Proof.
  abstract (
  apply formula_m;
  move=> m s s' E X Q HQ;
  specialize (X Q HQ);
  (split; [ destruct X as [ X _ ] | destruct X as [ _ X ] ]);
  move=> Hb;
  [ rewrite (projT2 (wp_c1 Q) m) | rewrite (projT2 (wp_c2 Q) m) ];
  (reflexivity || apply env_ext_sym, E || apply X);
  rewrite (sem_texpr_m _ _ _ E);
  exact Hb).
Defined.

Lemma wp_if_sound prg ii e c1 wp_c1 c2 wp_c2 f :
  (∀ f, hoare prg ⟦wp_c1 f⟧ c1 ⟦f⟧) →
  (∀ f, hoare prg ⟦wp_c2 f⟧ c2 ⟦f⟧) →
  hoare prg ⟦wp_if e wp_c1 wp_c2 f ⟧ [:: MkI ii (Cif e c1 c2) ] ⟦f⟧.
Proof.
  move=> WP1 WP2 .
  move=> s s1 /ssem_inv [s' [H' /ssem_inv]] ->.
  case: (ssem_I_inv H') => v [ii' [/MkI_inj [? ?]]]. clear H'. subst ii' v.
  move=> / ssem_i_inv [ b [ Hb REC ] ].
  unfold wp_if.
  case (type_check_pexpr e _) eqn: EQ. 2: apply ffalse_denote.
  destruct s as (m, vm).
  move: (type_check_pexprP EQ _ _ _ Hb) => Y /= X.
  move: (X f ltac:(reflexivity)) => [X1 X2]. clear X.
  destruct b.
    refine (WP1 _ _ _ REC _).
    apply X1; clear X1 X2.
    apply (@ok_inj error); symmetry; apply Y. auto.
  refine (WP2 _ _ _ REC _).
  apply X2; clear X1 X2.
  apply (@ok_inj error); symmetry; apply Y. auto.
Qed.

Definition wp_if' (e: pexpr) (wp_c1 wp_c2: formula → formula) (Q: formula) : formula.
  refine
  match type_check_pexpr e sbool with
  | Some te =>
    existT _ (
      λ m s,
      (sem_texpr m s sbool te = true → projT1 (wp_c1 Q) m s) ∧
      (sem_texpr m s sbool te = false → projT1 (wp_c2 Q) m s)
    ) _
  | None => ffalse
  end.
Proof.
  abstract (
  apply formula_m;
  move=> m s s' E X;
  (split; [ destruct X as [ X _ ] | destruct X as [ _ X ] ]);
  move=> Hb;
  [ rewrite (projT2 (wp_c1 Q) m) | rewrite (projT2 (wp_c2 Q) m) ];
  (reflexivity || apply env_ext_sym, E || apply X);
  rewrite (sem_texpr_m _ _ _ E);
  exact Hb).
Defined.

Lemma wp_if'_sound prg ii e c1 wp_c1 c2 wp_c2 f :
  (∀ f, hoare prg ⟦wp_c1 f⟧ c1 ⟦f⟧) →
  (∀ f, hoare prg ⟦wp_c2 f⟧ c2 ⟦f⟧) →
  hoare prg ⟦wp_if' e wp_c1 wp_c2 f ⟧ [:: MkI ii (Cif e c1 c2) ] ⟦f⟧.
Proof.
  move=> WP1 WP2 .
  move=> s s1 /ssem_inv [s' [H' /ssem_inv]] ->.
  case: (ssem_I_inv H') => v [ii' [/MkI_inj [? ?]]]. clear H'. subst ii' v.
  move=> / ssem_i_inv [ b [ Hb REC ] ].
  unfold wp_if'.
  case (type_check_pexpr e _) eqn: EQ. 2: apply ffalse_denote.
  destruct s as (m, vm).
  move: (type_check_pexprP EQ _ _ _ Hb) => Y /= X.
  move: X => [X1 X2].
  destruct b.
    refine (WP1 _ _ _ REC _).
    apply X1; clear X1 X2.
    apply (@ok_inj error); symmetry; apply Y. auto.
  refine (WP2 _ _ _ REC _).
  apply X2; clear X1 X2.
  apply (@ok_inj error); symmetry; apply Y. auto.
Qed.

End WEAKEST_PRECONDITION.
