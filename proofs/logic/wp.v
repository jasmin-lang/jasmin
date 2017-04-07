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

Inductive texpr : sstype → Type :=
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

Scheme Equality for sstype.

Fixpoint type_check_pexpr (e: pexpr) (ty: sstype) : option (texpr ty) :=
  match e with
  | Pconst z => match ty with ssint => Some (Tconst z) | _ => None end
  | Pbool b => match ty with ssbool => Some (Tbool b) | _ => None end
  | Pcast p =>
    match type_check_pexpr p ssint with
    | Some tp => match ty with ssword => Some (Tcast tp) | _ => None end
    | None => None end
  | Pvar x =>
    match sstype_eq_dec (vtype x) ty with
    | left EQ => Some (eq_rect _ _ (Tvar x) _ EQ)
    | right _ => None
    end
  | Pget x i =>
    match x with
    | {| v_var := Var (sarr n) t |} =>
    match type_check_pexpr i sint with
    | Some ti => match ty with ssword => Some (Tget n t ti) | _ => None end
    | None => None end
    | _ => None end
  | Pload x i =>
    match x with
    | {| v_var := Var sword p |} =>
    match type_check_pexpr i sword with
    | Some ti => match ty with ssword => Some (Tload p ti) | _ => None end
    | None => None end
    | _ => None end
  | Pnot p =>
    match type_check_pexpr p sbool with
    | Some tp => match ty with ssbool => Some (Tnot tp) | _ => None end
    | None => None end
  | Papp2 op p q =>
    match type_check_pexpr p (op2_type_i op) with
    | Some tp =>
    match type_check_pexpr q (op2_type_i op) with
    | Some tq =>
      match sstype_eq_dec (op2_type_o op) ty with
      | left EQ => Some (eq_rect _ _ (Tapp2 op tp tq) _ EQ)
      | _ => None end
    | None => None end
    | None => None end
  end.

Lemma ssem_sop2_ex op vp vq :
  ∀ p q,
    of_sval (op2_type_i op) vp = ok p →
    of_sval (op2_type_i op) vq = ok q →
    ∃ v, ssem_sop2 op vp vq = ok v ∧
         of_sval _ v = ok (sem_texpr_sop2 op p q).
Proof.
  case: op; simpl; intros;
    repeat
      match goal with
      | H : ?a = ?b |- _ => subst a || subst b
      | H : sto_bool _ = ok _ |- _ => apply sto_bool_inv in H
      | H : sto_int _ = ok _ |- _ => apply sto_int_inv in H
      end;
    try (eexists; split; reflexivity).
Qed.

Lemma of_sval_inj x ty ty' v v' :
  of_sval ty x = ok v →
  of_sval ty' x = ok v' →
  ∃ E : ty' = ty, v = eq_rect _ _ v' _ E.
Proof.
  case: ty v ty' v' => v [] v' H H';
  repeat match goal with
  | H : ?a = ?b |- _ => subst a || subst b
  | H : _ |- _ => apply sto_bool_inv in H
  | H : _ |- _ => apply sto_int_inv in H
  | H : _ |- _ => apply sto_word_inv in H
  end; move=> //;
  try (exists Logic.eq_refl; simpl; congruence).
Qed.

Lemma of_sval_error x ty v ty' :
  of_sval ty x = ok v →
  ty ≠ ty' →
  of_sval ty' x = type_error.
Proof.
  case: ty v ty' => v [] H // _;
  repeat match goal with
  | H : ?a = ?b |- _ => subst a || subst b
  | H : _ |- _ => apply sto_bool_inv in H
  | H : _ |- _ => apply sto_int_inv in H
  | H : _ |- _ => apply sto_word_inv in H
  | H : _ |- _ => apply sto_arr_inv in H
  end; move=> //.
Qed.

Lemma ssem_sop2_error_1 op vp exn :
    of_sval (op2_type_i op) vp = Error exn →
    ∀ vq, ∃ exn', ssem_sop2 op vp vq = Error exn'.
Proof.
  case: op; case: vp=> //= q Hq vq;
  try (eexists; reflexivity).
Qed.

Lemma ssem_sop2_error_2 op vp vq exn :
  ∀ p,
    of_sval (op2_type_i op) vp = ok p →
    of_sval (op2_type_i op) vq = Error exn →
    ∃ exn', ssem_sop2 op vp vq = Error exn'.
Proof.
  case: op => /= p Hp; case: vq => /= q Hq;
  repeat match goal with
  | H : ?a = ?b |- _ => subst a || subst b
  | H : _ = Error _ |- _ => apply Error_inj in H
  | H : _ |- _ => apply sto_bool_inv in H
  | H : _ |- _ => apply sto_int_inv in H
  | H : _ |- _ => apply sto_word_inv in H
  | H : _ |- _ => apply sto_arr_inv in H
  end; move=> //=;
  try (eexists; reflexivity).
Qed.

Lemma type_check_pexprP m s e ty :
  match type_check_pexpr e ty with
  | Some te =>
  ∃ v,
  ssem_pexpr (SEstate m s) e = ok v ∧
  of_sval _ v = ok (sem_texpr m (Mv.empty (λ x, s.[x])%vmap) ty te)
  | None => ∃ exn, Let v := ssem_pexpr (SEstate m s) e in of_sval ty v = Error exn
  end.
Proof.
  elim: e ty => /=.
  - move=> z [] //=; eauto; eexists; reflexivity.
  - move=> b [] //=; eauto; eexists; reflexivity.
  - move=> p /(_ sint); case: (type_check_pexpr _ _).
    + move=> tp [vp [Ep /sto_int_inv ?]]; subst vp; move=> [] //=; try rewrite Ep; simpl; eauto; eexists; reflexivity.
    + case=> exn -> /=; eauto.
  - move=> [[xt x] xi] ty /=. case: sstype_eq_dec.
    + move=> EQ /=. subst.
       eexists. split. eauto. unfold sget_var, of_sval; simpl.
       case: xt => //.
    + unfold sget_var, of_sval. case: ty; case: xt => //=; eexists; reflexivity.
  - move=> [[]] [] //=; eauto. move=> n x vi e /(_ ssint).
    unfold son_arr_var.
    case: (type_check_pexpr _ _).
    + move=> te [vp [Ep /sto_int_inv ?]]; subst vp; case=> //=; rewrite Ep; simpl; eauto; eexists; reflexivity.
    + case=> exn -> /=; eauto.
  - move=> [[]] [] //=; eauto. move=> x xi p /(_ ssword) /=.
    case: (type_check_pexpr p _).
    + move=> tp [v [Ep /sto_word_inv ?]]; subst v; case=> //=; rewrite Ep; simpl; eauto; eexists; reflexivity.
    + case=> exn -> /=; eauto.
  - move=> p /(_ ssbool); case: (type_check_pexpr p _).
    + move=> tp [v [Ep /sto_bool_inv ?]]; subst v; case=>//=; rewrite Ep; simpl; eauto; eexists; reflexivity.
    + case=> exn -> /=; eauto.
  - move=> op p /(_ (op2_type_i op)); case: (type_check_pexpr _ _).
    + move=> tp [vp [Ep IHp]] q /(_ (op2_type_i op)); rewrite Ep.
      case: (type_check_pexpr _ _).
      * move=> tq [vq [Eq IHq]] ty; rewrite Eq.
        case: (ssem_sop2_ex _ _ _ _ _ IHp IHq) => v [Ev Hv].
        case: sstype_eq_dec.
        move=> ?; subst; simpl; eauto.
        simpl. rewrite Ev => /of_sval_error /=.
        move=> H; erewrite H; eauto; eexists; reflexivity.
      * move=> /= [exn]. case: ssem_pexpr => /=.
        move=> vq /= Eq ty.
        case: (ssem_sop2_error_2 _ _ _ _ _ IHp Eq) => exn' -> /=; eauto.
        move=> ? [] ->; eauto.
    + case=> exn.
      case: (ssem_pexpr _ p) => [ vp | [] ] //= Ep q _ ty; eauto.
      case: (ssem_pexpr _ q)=> [ vq | [] ] //= ; eauto.
      case: (ssem_sop2_error_1 _ _ _ Ep vq) => exn' -> /=; eauto.
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

Definition vtype_eq_sarr x n (E: vtype x = sarr n) : ssarr = vtype x.
Proof. by rewrite E. Defined.

Definition post_assgn (x: lval) {ty} (w: ssem_t ty) (f: formula) (m: mem) (s: env) : Prop :=
  match x with
  | Lnone _ => projT1 f m s
  | Lvar {| v_var := x |} =>
    match sstype_eq_dec ty (vtype x) with
    | left EQ =>
      let v : ssem_t (vtype x) := eq_rect _ _ w _ EQ in projT1 f m (s.[x <- v])%mv
    | right _ => False
    end
  | Lmem {| v_var := x |} e =>
    match has_pointer_type x with
    | left Tx =>
    match type_check_pexpr e sword with
    | Some te =>
    match sstype_eq_dec ty sword with
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
    match sstype_eq_dec ty sword with
    | left EQ =>
      ∀ i,
      let t := eq_rect _ _  s.[x]%mv _ Tx in
      sem_texpr m s sint te = i →
      let v := eq_rect _ _ w _ EQ in
      let a : ssem_t (vtype x) := eq_rect _ _ (FArray.set t i v) _ (vtype_eq_sarr _ _ Tx) in
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

Definition eval_texpr (s: sestate) {ty} (e: texpr ty) : ssem_t ty :=
  let 'SEstate m vm := s in
  sem_texpr m (Mv.empty (λ x, (vm).[x])%vmap) ty e.

Lemma texpr_of_pexpr_bool s e b :
  ssem_pexpr s e = ok (SVbool b) →
  eval_texpr s (texpr_of_pexpr sbool' e) = b.
Proof.
  destruct s as [m vm].
  move=> h.
  unfold texpr_of_pexpr.
  generalize (type_check_pexprP m vm e (stype_of_stype' sbool')).
  rewrite h; clear h.
  case: type_check_pexpr => /= [ te [v [Ev /sto_bool_inv Hv]] | [exn Hv] ];
  congruence.
Qed.

Lemma texpr_of_pexpr_int s e b :
  ssem_pexpr s e = ok (SVint b) →
  eval_texpr s (texpr_of_pexpr sint' e) = b.
Proof.
  destruct s as [m vm].
  move=> h.
  unfold texpr_of_pexpr.
  generalize (type_check_pexprP m vm e (stype_of_stype' sint')).
  rewrite h; clear h.
  case: type_check_pexpr => /= [ te [v [Ev /sto_int_inv Hv]] | [exn Hv] ];
  congruence.
Qed.

Lemma post_assgn_m { s s' } :
  env_ext s s' →
  ∀ x ty (v: ssem_t ty) f m,
  post_assgn x v f m s →
  post_assgn x v f m s'.
Proof.
  move=> E [ x | [x xn] | [x xn] e | x e ] ty v f m /=.
  - (* Lnone *) by apply (projT2 f m).
  - (* Lvar *)
    case: sstype_eq_dec => // Te.
    apply (projT2 f m). auto.
    subst. simpl. apply env_ext_set, env_ext_sym, E.
  - (* Lmem *)
    case: has_pointer_type => // Ty.
    case (type_check_pexpr e _) eqn: Te; auto.
    case: sstype_eq_dec => // ?; subst.
    move=> /= H ? ? ? ?; subst.
    rewrite (projT2 f). apply: H; auto.
    repeat (f_equal; auto using sem_texpr_m, env_ext_sym).
    auto using env_ext_sym.
  - (* Laset *)
    case: has_array_type => // [[n Tx]].
    case (type_check_pexpr e _) eqn: Te; auto.
    case: sstype_eq_dec => // ?; subst.
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
  generalize (type_check_pexprP m vm e (type_of_pexpr e)).
  case: (type_check_pexpr _ _). 2: intro; apply: ffalse_denote.
  move=> te [w' [Hw' R]] /=.
  case: x Hs' => [ xi | [x xn] | [x xn] e' | x e' ] /swrite_lval_inv.
  - (* Lnone *)
    move=> -> H; apply: H; eauto.
  - (* Lvar *)
    move=> /= [ v' [Hvv' ?] ] /(_ _ Logic.eq_refl); subst s'.
    case: sstype_eq_dec => // Te.
    unfold formula_denote; simpl.
    apply (projT2 f m). reflexivity.
    apply: env_ext_empty.
    move=> y.
    case: (x =P y).
    move=> <-. rewrite ! (Fv.setP_eq, Mv.setP_eq).
    move: Te v' Hvv'. intros ().
    move=> v' Hvv' /=.
    apply: ok_inj. etransitivity. symmetry. apply: Hvv'. congruence.
    move=> NE. rewrite ! (Fv.setP_neq, Mv.setP_neq) //; case: eqP => //.
  - (* Lmem *)
    move=> [Tx [vx [ve [w [Hvx [Hve [? ?]]]]]]] /(_ _ Logic.eq_refl) /=; subst.
    case: has_pointer_type => // Tx'.
    case (type_check_pexpr e' _) eqn: Te'. 2: easy.
    case: sstype_eq_dec => // Te /(_ _ _ Logic.eq_refl) /(_ Logic.eq_refl) /=.
    unfold formula_denote; simpl.
    apply (projT2 f). 2: apply: env_ext_empty; reflexivity.
    f_equal. f_equal.
    rewrite Mv.get0.
    apply (eq_rect_eq _ _ _ (λ t, ssem_t (sstype_of_stype t))). clear. move=> E.
    by move: (Eqdep_dec.UIP_dec stype_eq_dec E Logic.eq_refl) ->.
    generalize (type_check_pexprP m vm e' ssword); rewrite Te'.
    case=> v' [Hv' /sto_word_inv ?]; subst v'.
    congruence.
    simpl in *.
    clear Tx'. revert Tx. generalize (vtype x). clear x. intros s ->.
    destruct (type_of_pexpr e) => //.
    move: (Eqdep_dec.UIP_dec sstype_eq_dec Te Logic.eq_refl) ->. simpl.
    apply sto_word_inv in R. subst. congruence.
  - (* Laset *)
    move=> [ n [ Tx [ vi [ w [ Hvi [? ?]]]]]] /(_ _ Logic.eq_refl); simpl in *; subst.
    case: has_array_type => // [[n' Tx']].
    case (type_check_pexpr e' _) eqn: Te'. 2: easy.
    case: sstype_eq_dec => // Te /(_ _ Logic.eq_refl).
    unfold formula_denote. simpl.
    apply (projT2 f). reflexivity.
    apply: env_ext_empty.
    move=> y. rewrite Mv.get0.
    case: (v_var x =P y).
    move=> <-. rewrite ! (Fv.setP_eq, Mv.setP_eq, Mv.get0).
    generalize (type_check_pexprP m vm e' ssint); rewrite Te'.
    case=> q [Re /sto_int_inv ?]; subst q.
    rewrite Re in Hvi. apply ok_inj in Hvi.
    assert (n = n'). congruence. subst n'.
    case: x Tx Tx' => [[xn ty] xi] /= Tx Tx'. subst. simpl.
    move: (Eqdep_dec.UIP_dec stype_eq_dec Tx' Logic.eq_refl) ->. simpl.
    destruct (type_of_pexpr e) => //.
    move: (Eqdep_dec.UIP_dec sstype_eq_dec Te Logic.eq_refl) ->. simpl.
    f_equal. congruence.
    apply sto_word_inv in R. congruence.
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
  generalize (type_check_pexprP m vm e ssbool); rewrite EQ.
  case=> v [Y /sto_bool_inv ?] /= X; subst v.
  rewrite Y in Hb; apply ok_inj in Hb.
  move: (X f ltac:(reflexivity)) => [X1 X2]. clear X.
  destruct b.
    refine (WP1 _ _ _ REC _).
    apply X1; clear X1 X2.
    congruence.
  refine (WP2 _ _ _ REC _).
  apply X2; clear X1 X2.
  congruence.
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
  generalize (type_check_pexprP m vm e ssbool); rewrite EQ.
  case=> v [Y /sto_bool_inv ?] /= X; subst v.
  rewrite Y in Hb; apply ok_inj in Hb.
  move: X => [X1 X2].
  destruct b.
    refine (WP1 _ _ _ REC _).
    apply X1; clear X1 X2.
    congruence.
  refine (WP2 _ _ _ REC _).
  apply X2; clear X1 X2.
  congruence.
Qed.

End WEAKEST_PRECONDITION.
