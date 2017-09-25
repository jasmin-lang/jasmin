Require Ssem.

Import Utf8.
Import Morphisms.
Import all_ssreflect.
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

Context (prg: prog) (gd: glob_defs).

Definition hoare (Pre: hpred) (c: cmd) (Post: hpred) : Prop :=
  ∀ s s' : sestate,
    ssem prg gd s c s' →
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
        ssem_pexpr gd s e = ok v →
        swrite_lval gd x v s = ok s' →
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

Notation "'mv_of_fv' s" := (Mv.empty (λ x, s.[x])%vmap) (at level 10).
Notation "'fv_of_mv' s" := (Fv.empty (λ x, s.[x])%mv) (at level 10).

Definition formula_of_hpred (P: hpred) : formula.
Proof.
  refine (existT _ (λ (m: mem) (s: env), P {| semem := m ; sevm := fv_of_mv s |}) _).
  apply formula_m.
  move=> m s s' E H.
  refine (eq_ind _ P H _ _).
  f_equal.
  apply Fv.map_ext. auto.
Defined.

Notation "⟨ P ⟩" := (formula_of_hpred P) : msem_scope.

Definition formula_denote (f: formula) : hpred :=
  λ s, projT1 f (semem s) (mv_of_fv (sevm s)).

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

(*Print sstype.

Variant stype' : Type := sint' | sbool' | sword'.

Definition stype_of_stype' (ty: stype') : stype :=
  match ty with
  | sint'  => sint
  | sbool' => sbool
  | sword' => sword
  end.

Local Coercion stype_of_stype' : stype' >-> stype.
*)
Definition op1_type (op: sop1) : sstype * sstype :=
  match op with
  | Onot => (ssbool, ssbool)
  | Olnot | Oneg
    => (ssword, ssword)
  | Oarr_init => (ssint, ssarr)
  end.

Definition op1_type_i op := fst (op1_type op).
Definition op1_type_o op := snd (op1_type op).

Definition sem_texpr_sop1 op : ssem_t (op1_type_i op) → ssem_t (op1_type_o op) :=
  match op with
  | Onot => negb
  | Olnot => I64.not
  | Oneg => I64.neg
  | Oarr_init => fun _ => (FArray.cnst I64.zero)
  end.

Definition op2_type (op: sop2) : sstype * sstype :=
  match op with
  | (Oand | Oor ) => (ssbool, ssbool)
  | (Oadd ty| Omul ty| Osub ty | Oland ty | Olor ty | Olxor ty) =>
    match ty with 
    | Op_int => (ssint, ssint)
    | Op_w   => (ssword, ssword)
    end
  | (Olsr | Olsl | Oasr) => (ssword, ssword)
  | (Oeq ty| Oneq ty| Olt ty| Ole ty| Ogt ty| Oge ty) =>
    match ty with
    | Cmp_int => (ssint, ssbool)
    | _       => (ssword, ssbool)
    end
  end.

Definition op2_type_i op := fst (op2_type op).
Definition op2_type_o op := snd (op2_type op).

Definition sem_texpr_sop2 op : ssem_t (op2_type_i op) → ssem_t (op2_type_i op) → ssem_t (op2_type_o op) :=
  match op with
  | Oand => andb
  | Oor => orb
  | Oadd Op_int  => Z.add
  | Omul Op_int  => Z.mul
  | Osub Op_int  => Z.sub
  | Oadd Op_w    => I64.add
  | Omul Op_w    => I64.mul
  | Osub Op_w    => I64.sub
  | Oland Op_int => Z.land
  | Oland Op_w => I64.and
  | Olor Op_int => Z.lor
  | Olor Op_w => I64.or
  | Olxor Op_int => Z.lxor
  | Olxor Op_w => I64.xor
  | Olsr => sem_lsr
  | Olsl => sem_lsl
  | Oasr => sem_asr
  | Oeq  Cmp_int => Z.eqb
  | Oeq  Cmp_uw  => weq
  | Oeq  Cmp_sw  => weq
  | Oneq Cmp_int => λ x y, negb (Z.eqb x y)
  | Oneq Cmp_uw  => λ x y, negb (weq x y)
  | Oneq Cmp_sw  => λ x y, negb (weq x y)
  | Olt  Cmp_int => Z.ltb
  | Olt  Cmp_uw  => wult
  | Olt  Cmp_sw  => wslt
  | Ole  Cmp_int => Z.leb
  | Ole  Cmp_uw  => wule
  | Ole  Cmp_sw  => wsle
  | Ogt  Cmp_int => Z.gtb
  | Ogt  Cmp_uw  => λ x y, wult y x
  | Ogt  Cmp_sw  => λ x y, wslt y x
  | Oge  Cmp_int => Z.geb
  | Oge  Cmp_uw  => λ x y, wule y x
  | Oge  Cmp_sw  => λ x y, wsle y x
  end.

Inductive texpr : sstype → Type :=
| Tconst : Z → texpr sint
| Tbool : bool → texpr sbool
| Tcast : texpr sint → texpr sword
| Tvar x : texpr (vtype x)
| Tglobal : global → texpr sword
| Tget : positive → Ident.ident → texpr sint → texpr sword
| Tload : Ident.ident → texpr sword → texpr sword
| Tapp1 op : texpr (op1_type_i op) → texpr (op1_type_o op)
| Tapp2 op (_ _: texpr (op2_type_i op)) : texpr (op2_type_o op)
| Tif `(texpr sbool) ty (_ _: texpr ty) : texpr ty
.

Context (gd: glob_defs).

Section SEM_TEXPR.
  Context (m: mem) (s: env).
  Fixpoint sem_texpr ty (e: texpr ty) : ssem_t ty :=
    match e in texpr ty return ssem_t ty with
    | Tconst z => z
    | Tbool b => b
    | Tcast e => I64.repr (sem_texpr sint e)
    | Tvar x => s.[x]
    | Tglobal g => odflt I64.zero (get_global_word gd g)
    | Tget n x e =>
      let a := s.[{| vtype := sarr n; vname := x |}] in
      let i := sem_texpr sint e in
      FArray.get a i
    | Tload x e =>
      let w1 := s.[{| vtype := sword; vname := x |}] in
      let w2 := sem_texpr sword e in
      let w := read_mem m (I64.add w1 w2) in
      w
    | Tapp1 op e =>
      let v := sem_texpr (op1_type_i op) e in
      sem_texpr_sop1 op v
    | Tapp2 op e1 e2 =>
      let v1 := sem_texpr (op2_type_i op) e1 in
      let v2 := sem_texpr (op2_type_i op) e2 in
      sem_texpr_sop2 op v1 v2
    | Tif b _ e1 e2 =>
      if sem_texpr sbool b
      then sem_texpr _ e1
      else sem_texpr _ e2
    end%mv.
End SEM_TEXPR.

Lemma sem_texpr_m (m: mem) (s s': env) :
  env_ext s s' →
  ∀ ty e, sem_texpr m s ty e = sem_texpr m s' ty e.
Proof.
  move=> E ty e.
  elim: e => //=; try congruence.
  clear; by move=> p -> ty e -> e' -> //.
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
  | Pglobal g => match ty with ssword => Some (Tglobal g) | _ => None end
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
  | Papp1 op p =>
    match type_check_pexpr p (op1_type_i op) with
    | Some tp =>
      match sstype_eq_dec (op1_type_o op) ty with
      | left EQ => Some (eq_rect _ _ (Tapp1 op tp) _ EQ)
      | _ => None end
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
  | Pif b p q =>
    match type_check_pexpr b ssbool with
    | Some tb =>
    match type_check_pexpr p ty with
    | Some tp =>
    match type_check_pexpr q ty with
    | Some tq => Some (Tif tb ty tp tq)
    | None => None end
    | None => None end
    | None => None end
  end.

Lemma ssem_sop1_ex op vp :
  ∀ p,
    of_sval (op1_type_i op) vp = ok p →
    ∃ v, ssem_sop1 op vp = ok v ∧
         of_sval _ v = ok (sem_texpr_sop1 op p).
Proof.
  case: op => /=;intros;
    repeat
      match goal with
      | H : ?a = ?b |- _ => subst a || subst b
      | H : sto_bool _ = ok _ |- _ => apply sto_bool_inv in H
      | H : sto_word _ = ok _ |- _ => apply sto_word_inv in H
      | H : sto_int _ = ok _ |- _ => apply sto_int_inv in H
      end;
    try (eexists; split; reflexivity).
Qed.

Lemma ssem_sop2_ex op vp vq :
  ∀ p q,
    of_sval (op2_type_i op) vp = ok p →
    of_sval (op2_type_i op) vq = ok q →
    ∃ v, ssem_sop2 op vp vq = ok v ∧
         of_sval _ v = ok (sem_texpr_sop2 op p q).
Proof.
  case: op => [||[]|[]|[]|[]|[]|[]||||[]|[]|[]|[]|[]|[]] /=;intros;
    repeat
      match goal with
      | H : ?a = ?b |- _ => subst a || subst b
      | H : sto_bool _ = ok _ |- _ => apply sto_bool_inv in H
      | H : sto_int _ = ok _ |- _ => apply sto_int_inv in H
      | H : sto_word _ = ok _ |- _ => apply sto_word_inv in H
      end;
    try (eexists; split; reflexivity).
Qed.

(*
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
*)

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

Lemma ssem_sop1_error op vp exn :
    of_sval (op1_type_i op) vp = Error exn →
    ∃ exn', ssem_sop1 op vp = Error exn'.
Proof.
  case: op; case: vp=> //= q Hq;
  try (eexists; reflexivity).
Qed.

Lemma ssem_sop2_error_1 op vp exn :
    of_sval (op2_type_i op) vp = Error exn →
    ∀ vq, ∃ exn', ssem_sop2 op vp vq = Error exn'.
Proof.
  case: op => [||[]|[]|[]|[]|[]|[]||||[]|[]|[]|[]|[]|[]]; case: vp=> //= q Hq vq;
  try (eexists; reflexivity).
Qed.

Lemma ssem_sop2_error_2 op vp vq exn :
  ∀ p,
    of_sval (op2_type_i op) vp = ok p →
    of_sval (op2_type_i op) vq = Error exn →
    ∃ exn', ssem_sop2 op vp vq = Error exn'.
Proof.
  case: op => [||[]|[]|[]|[]|[]|[]||||[]|[]|[]|[]|[]|[]] /= p Hp; case: vq => /= q Hq;
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

Lemma of_sval_has_type ty s v :
  of_sval ty s = ok v →
  ty = sval_sstype s.
Proof.
  case: ty v => v /= V.
  apply sto_bool_inv in V; subst; reflexivity.
  apply sto_int_inv in V; subst; reflexivity.
  apply sto_arr_inv in V; subst; reflexivity.
  apply sto_word_inv in V; subst; reflexivity.
Qed.

Lemma type_check_pexprP m s e ty :
  match type_check_pexpr e ty with
  | Some te =>
  ∃ v,
  ssem_pexpr gd (SEstate m s) e = ok v ∧
  of_sval _ v = ok (sem_texpr m (mv_of_fv s) ty te)
  | None => ∃ exn, Let v := ssem_pexpr gd (SEstate m s) e in of_sval ty v = Error exn
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
  - by move=> g []; eauto; exists ErrType.
  - move=> [[]] [] //=; eauto. move=> n x vi e /(_ ssint).
    unfold son_arr_var.
    case: (type_check_pexpr _ _).
    + move=> te [vp [Ep /sto_int_inv ?]]; subst vp; case=> //=; rewrite Ep; simpl; eauto; eexists; reflexivity.
    + case=> exn -> /=; eauto.
  - move=> [[]] [] //=; eauto. move=> x xi p /(_ ssword) /=.
    case: (type_check_pexpr p _).
    + move=> tp [v [Ep /sto_word_inv ?]]; subst v; case=> //=; rewrite Ep; simpl; eauto; eexists; reflexivity.
    + case=> exn -> /=; eauto.
  - move=> op p /(_ (op1_type_i op)); case: (type_check_pexpr _ _).
    + move=> tp [vp [Ep IHp]] ty; rewrite Ep.
      case: (ssem_sop1_ex _ _ _ IHp) => v [Ev Hv].
      case: sstype_eq_dec.
        move=> ?; subst; simpl; eauto.
      simpl. rewrite Ev => /of_sval_error /=.
      move=> H; erewrite H; eauto; eexists; reflexivity.
    + case=> exn.
      case: (ssem_pexpr _ _ p) => [ vp | [] ] //= Ep ty; eauto.
      case: (ssem_sop1_error _ _ _ Ep) => exn' -> /=; eauto.
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
      case: (ssem_pexpr _ _ p) => [ vp | [] ] //= Ep q _ ty; eauto.
      case: (ssem_pexpr _ _ q)=> [ vq | [] ] //= ; eauto.
      case: (ssem_sop2_error_1 _ _ _ Ep vq) => exn' -> /=; eauto.
  - move=> b /(_ ssbool); case: (type_check_pexpr _ _).
    2: case=> exn -> /=; eauto; fail.
    move=> tb [v [Eb /sto_bool_inv ?]]; subst v; rewrite Eb {Eb}.
    move=> p hp q hq ty.
    move:(hp ty) (hq ty) => {hp hq}.
    case: (type_check_pexpr _ _).
    + move=> tp [vp [Ep IHp]]; rewrite Ep.
      pose proof of_sval_has_type _ _ _ IHp; subst ty.
      case: (type_check_pexpr _ _).
      * move=> tq [vq [Eq IHq]] /=; rewrite Eq IHp /= IHq /=.
        eexists; split; first reflexivity.
        by case: (sem_texpr _ _ _ tb).
      * case=> exn /=.
        case: (ssem_pexpr _ _ q) => [ vq | ] /=; eauto.
        rewrite IHp; move=> -> /=; eauto.
    + case=> exn.
      case: (ssem_pexpr _ _ p) => /= [ vp Ep | ]; eauto.
      case: (of_sval (sval_sstype vp) vp) => /= [ _ | ].
      2: move=> exn' _; case: ssem_pexpr => /=; eauto.
      case: (type_check_pexpr _ _).
      * move=> tq [vq [Eq IHq]] /=. rewrite Eq /=.
        pose proof of_sval_has_type _ _ _ IHq; subst ty.
        destruct (of_sval (sval_sstype vp) vq) eqn: X.
        2: simpl; eauto.
        exfalso.
        rewrite <- (of_sval_has_type _ _ _ X) in Ep. clear -Ep.
        case: vp Ep => //=.
      * case=> exn'.
        case: (ssem_pexpr _ _ q) => /= [ vq Eq | ]; eauto.
        case: (of_sval _ _) => [_|] /=; last by eauto.
        by case: (sem_texpr _ _ _ tb); eauto.
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
  | Lnone _ _ => projT1 f m s
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

Fixpoint type_of_pexpr (e: pexpr) : sstype :=
  match e with
  | Pconst _ => sint
  | Pbool _ => sbool
  | Pcast _
  | Pget _ _
  | Pload _ _
  | Pglobal _
    => sword
  | Pvar {| v_var := x |} => vtype x
  | Papp1 op _ => op1_type_o op
  | Papp2 op _ _ => op2_type_o op
  | Pif _ e _ => type_of_pexpr e
  end.

Definition default_texpr (ty: sstype) : texpr ty :=
  match ty with
  | ssbool => Tbool true
  | ssint  => Tconst 42
  | ssword => Tcast (Tconst 999)
  | ssarr  => Tapp1 Oarr_init (Tconst 666)  
  end.

Definition texpr_of_pexpr (ty: sstype) (pe: pexpr) : texpr ty :=
  match type_check_pexpr pe ty with
  | Some te => te
  | None => default_texpr ty
  end.

Definition eval_texpr (s: sestate) {ty} (e: texpr ty) : ssem_t ty :=
  let 'SEstate m vm := s in
  sem_texpr m (mv_of_fv vm) ty e.

Lemma texpr_of_pexpr_bool s e b :
  ssem_pexpr gd s e = ok (SVbool b) →
  eval_texpr s (texpr_of_pexpr ssbool e) = b.
Proof.
  destruct s as [m vm].
  move=> h.
  unfold texpr_of_pexpr.
  generalize (type_check_pexprP m vm e ssbool).
  rewrite h; clear h.
  case: type_check_pexpr => /= [ te [v [Ev /sto_bool_inv Hv]] | [exn Hv] ];
  congruence.
Qed.

Lemma texpr_of_pexpr_int s e b :
  ssem_pexpr gd s e = ok (SVint b) →
  eval_texpr s (texpr_of_pexpr ssint e) = b.
Proof.
  destruct s as [m vm].
  move=> h.
  unfold texpr_of_pexpr.
  generalize (type_check_pexprP m vm e ssint).
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
  move=> E [ x t | [x xn] | [x xn] e | x e ] ty v f m /=.
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

Lemma of_sval_inv ty v w :
  of_sval ty v = ok w →
  v = to_sval w.
Proof.
  case: ty w.
  - move => b /sto_bool_inv; exact: id.
  - move => i /sto_int_inv; exact: id.
  - move => a /sto_arr_inv; exact: id.
  - move => w /sto_word_inv; exact: id.
Qed.

Lemma post_assgn_sound x ty (v: ssem_t ty) m vm s' f:
  swrite_lval gd x (to_sval v) (SEstate m vm) = ok s' →
  (post_assgn x v f m (mv_of_fv vm)) →
  ⟦f⟧ s'.
Proof.
  case: x => [ xi t | [x xn] | [x xn] e' | x e' ] /swrite_lval_inv.
  - (* Lnone *)
    move=> -> H; apply: H; eauto.
  - (* Lvar *)
    case.
    + move=> /= [ v' [Hvv' ?] ]; subst s'.
      case: sstype_eq_dec => // Te.
      unfold formula_denote; simpl.
      apply (projT2 f m). reflexivity.
      apply: env_ext_empty.
      move=> y.
      case: (x =P y).
      move=> <-. rewrite ! (Fv.setP_eq, Mv.setP_eq).
      subst; rewrite of_sval_to_sval in Hvv'; apply ok_inj in Hvv'; auto.
      move=> NE. rewrite ! (Fv.setP_neq, Mv.setP_neq) //; case: eqP => //.
    + case => /= he ?; subst s'.
      case: sstype_eq_dec => // Te. exfalso.
      by case: x Te he => xt xi /= <-; rewrite of_sval_to_sval.
  - (* Lmem *)
    move=> [Tx [vx [ve [w [Hvx [Hve [Hv ?]]]]]]] /=; subst.
    case: has_pointer_type => // Tx'.
    case (type_check_pexpr e' _) eqn: Te'. 2: easy.
    case: sstype_eq_dec => // Te /(_ _ _ Logic.eq_refl) /(_ Logic.eq_refl) /=.
    unfold formula_denote; simpl.
    apply (projT2 f). 2: apply: env_ext_empty; reflexivity.
    subst. inversion Hv. clear Hv. subst. simpl.
    f_equal. f_equal.
    rewrite Mv.get0.
    apply (eq_rect_eq _ _ _ (λ t, ssem_t (sstype_of_stype t))). clear. move=> E.
    by move: (Eqdep_dec.UIP_dec stype_eq_dec E Logic.eq_refl) ->.
    generalize (type_check_pexprP m vm e' ssword); rewrite Te'.
    case=> v' [Hv' /sto_word_inv ?]; subst v'.
    congruence.
  - (* Laset *)
    move=> [ n [ Tx [ vi [ w [ Hvi [Hv ?]]]]]]; simpl in *; subst.
    case: has_array_type => // [[n' Tx']].
    case (type_check_pexpr e' _) eqn: Te'. 2: easy.
    case: sstype_eq_dec => // Te /(_ _ Logic.eq_refl).
    subst. inversion_clear Hv.
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
    congruence.
    move=> NE. rewrite ! (Fv.setP_neq, Mv.setP_neq) //; case: eqP => //.
Qed.

Lemma wp_assgn_sound prg ii x e tg f :
  hoare prg gd ⟦wp_assgn x e f⟧ [:: MkI ii (Cassgn x tg e)] ⟦f⟧.
Proof.
  move=> [m vm] s1 /ssem_inv [s' [/ssem_I_inv [i' [ii' [/MkI_inj [? <-]] /ssem_i_inv [v [Hv Hs']]]] /ssem_inv ->]]; subst ii'.
  unfold wp_assgn.
  generalize (type_check_pexprP m vm e (type_of_pexpr e)).
  case: (type_check_pexpr _ _). 2: intro; apply: ffalse_denote.
  move=> te [w' [Hw' R]] /=.
  assert (w' = v) by congruence; clear Hw'; subst w'.
  clear Hv.
  move: te R Hs'; move: (type_of_pexpr e). clear e.
  move=> ty te /of_sval_inv -> Hs' /(_ _ Logic.eq_refl).
  exact: post_assgn_sound.
Qed.

Definition sopn_type (op: sopn) : seq sstype * seq sstype :=
  match op with
    (* FIXME
  | Olnot => ([:: ssword ], [:: ssword])
  | (Oxor | Oland | Olor | Olsr | Olsl | Omuli)
    => ([:: ssword ; ssword ], [:: ssword ])
  | Omulu => ([:: ssword ; ssword ], [:: ssword ; ssword ])
  | Oif => ([:: ssbool ; ssword ; ssword ], [:: ssword])
  | (Oaddcarry | Osubcarry) => ([:: ssword ; ssword ; ssbool ], [:: ssbool ; ssword ])
  | (Oleu | Oltu | Ogeu | Ogtu | Oles | Olts | Oges | Ogts | Oeqw) => ([:: ssword; ssword], [:: ssbool])
  | Ox86_cmp => ([:: ssword; ssword], [:: ssbool; ssbool; ssbool; ssbool; ssbool])
     *)
  | _ => ([::], [::])
  end.

Definition sopn_type_i op := fst (sopn_type op).
Definition sopn_type_o op := snd (sopn_type op).

Section STYPES_DENOTE.
  Context (f: sstype → Type).
  Fixpoint stypes_denote (ts: seq sstype) : Type :=
    match ts with
    | [::] => unit
    | [:: ty] => f ty
    | ty :: ts' => f ty * stypes_denote ts'
    end.

  Definition stype_cons ty tys (x: f ty)
    : stypes_denote tys → stypes_denote (ty :: tys) :=
    match tys with
    | [::] => λ _, x
    | _ => pair x
    end.

End STYPES_DENOTE.

Arguments stype_cons {f ty tys} _ _.

Section STYPES_DENOTE_MAP.
  Context (f g: sstype → Type).
  Context (q: ∀ t, f t → g t).

  Fixpoint stypes_denote_map_aux ty t {struct t}
    : stypes_denote f (ty :: t) → stypes_denote g (ty :: t) :=
    match t return stypes_denote f (ty :: t) → stypes_denote g (ty :: t) with
    | [::] => q ty
    | ty' :: tys => λ a, let '(x, xs) := a in (q ty x, stypes_denote_map_aux ty' tys xs)
    end.

  Definition stypes_denote_map t : stypes_denote f t → stypes_denote g t :=
    match t with
    | [::] => id
    | ty :: tys => stypes_denote_map_aux ty tys
    end.

End STYPES_DENOTE_MAP.

Section STYPES_DENOTE_MAP_M.
  Context (f g: sstype → Type).
  Context (q q': ∀ t, f t → g t).

  Context (E: ∀ t (x: f t), q t x = q' t x).

  Lemma stypes_denote_map_aux_m ty t args :
    stypes_denote_map_aux f g q ty t args = stypes_denote_map_aux f g q' ty t args.
  Proof.
    elim: t ty args => //= ty tys ih ty' [x xs] /=; f_equal; auto.
    case: tys ih xs => //=.
  Qed.

  Lemma stypes_denote_map_m tys args :
    stypes_denote_map f g q tys args = stypes_denote_map f g q' tys args.
  Proof.
    case: tys args => //. exact: stypes_denote_map_aux_m.
  Qed.

End STYPES_DENOTE_MAP_M.

Definition uncurry {A B C} (f: A → B → C) (p: A * B) : C :=
  let '(a, b) := p in f a b.

Definition eval_sopn (op: sopn) :
  stypes_denote ssem_t (sopn_type_i op) → stypes_denote ssem_t (sopn_type_o op) :=
  (*
  match op
  return stypes_denote _ (sopn_type_i op) → stypes_denote _ (sopn_type_o op)
  with
  | Olnot => I64.not
  | Oxor => uncurry I64.xor
  | Oland => uncurry I64.and
  | Olor => uncurry I64.or
  | Olsr => uncurry I64.shru
  | Olsl => uncurry I64.shl
  | Oif => λ a, let '(b, (x, y)) := a in if b then x else y
  | Omulu => uncurry word.wumul
  | Omuli => λ a, let '(x, y) := a in snd (word.wumul x y)
  | Oaddcarry => λ a, let '(x, (y, c)) := a in word.waddcarry x y c
  | Osubcarry => λ a, let '(x, (y, c)) := a in word.wsubcarry x y c
  | Oleu => uncurry (fun x y => I64.ltu x y || I64.eq x y)
  | Oltu => uncurry I64.ltu
  | Ogeu => uncurry (fun x y => I64.ltu y x || I64.eq x y)
  | Ogtu => uncurry (fun x y => I64.ltu y x)
  | Oles => uncurry (fun x y => I64.lt x y || I64.eq x y)
  | Olts => uncurry I64.lt
  | Oges => uncurry (fun x y => I64.lt y x || I64.eq x y)
  | Ogts => uncurry (fun x y => I64.lt y x)
  | Oeqw => uncurry I64.eq
  | Ox86_cmp => uncurry x86_cmp
  end.
*)
  λ x, x. (* FIXME *)

Fixpoint type_check_pexprs (pes: seq pexpr) (tys: seq sstype)
  : option (stypes_denote texpr tys) :=
  match pes, tys return option (stypes_denote texpr tys) with
  | [::], [::] => Some tt
  | pe :: pes', ty :: tys' =>
    match type_check_pexpr pe ty with
    | Some te =>
      match type_check_pexprs pes' tys' with
      | Some tes => Some (stype_cons te tes)
      | None => None end
    | None => None end
  | _, _ => None
  end.

Section WP_OPN.

  Context (m: mem) (vm: env).
  Context (op: sopn).

  Fixpoint wp_opn_aux_rec (ty: sstype) (tys: seq sstype) :
    (stypes_denote ssem_t (ty :: tys) → Prop) →
    Prop :=
    match tys
    return (stypes_denote ssem_t (ty :: tys) → Prop) → Prop
    with
    | [::] => λ P, ∀ v, P v
    | ty' :: tys' => λ P, ∀ v : ssem_t ty, wp_opn_aux_rec ty' tys' (λ q, P (v, q))
    end.

  Definition wp_opn_aux_aux spec :
    (stypes_denote ssem_t spec → Prop) →
    (stypes_denote ssem_t spec → Prop) → Prop :=
    match spec with
    | [::] => λ E P, P tt
    | ty :: tys => λ E P, wp_opn_aux_rec ty tys (λ e, E e → P e)
    end.

  Definition wp_opn_aux
    (vargs: stypes_denote ssem_t (sopn_type_i op)) :
    (stypes_denote ssem_t (sopn_type_o op) → Prop) →
    Prop :=
    wp_opn_aux_aux _ (λ e, eval_sopn op vargs = e).

  Fixpoint post_opn_aux (d: lval) (dst: lvals) ty tys
    : stypes_denote ssem_t (ty :: tys) → formula → formula.
    refine
    match dst, tys return stypes_denote _ (ty :: tys) → _ → _ with
    | [::], [::] => λ v, λ f, existT _ (post_assgn d v f) _
    | d' :: dst', ty' :: tys' =>
      λ a, let '(v, vs) := a in
           λ f,
           existT _ (post_assgn d v (post_opn_aux d' dst' ty' tys' vs f)) _
    | _, _ => λ _ _, ffalse
    end.
  Proof.
    clear; abstract (
    apply: formula_m => m s s' E;
    exact: post_assgn_m).
    clear; (
    apply: formula_m => m s s' E;
    exact: post_assgn_m).
  Defined.

  Definition post_opn dst tys : stypes_denote ssem_t tys → formula → formula :=
    match dst, tys return stypes_denote ssem_t tys → _ → _ with
    | [::], [::] => λ _, id
    | d :: dst, ty :: tys => post_opn_aux d dst ty tys
    | _, _ => λ _ _, ffalse
    end.

End WP_OPN.

Lemma wp_opn_aux_rec_m tys :
  ∀ ty
  (f f' : stypes_denote ssem_t (ty :: tys) → Prop),
  (∀ q : stypes_denote ssem_t (ty :: tys), f q ↔ f' q) →
  wp_opn_aux_rec ty tys f →
  wp_opn_aux_rec ty tys f'.
Proof.
  elim: tys => [ | ty' tys' ih ] ty f f' E X v.
  apply E, X.
  exact: (ih ty' (λ q, f (v, q)) (λ q, f' (v, q))).
Qed.

Lemma wp_opn_aux_aux_m spec :
  ∀ P (f f' : stypes_denote ssem_t spec → Prop),
  (∀ q : stypes_denote ssem_t spec, f q ↔ f' q) →
  wp_opn_aux_aux spec P f →
  wp_opn_aux_aux spec P f'.
Proof.
  case spec => [ | ty tys ] P f f' E.
  + apply E.
  apply: wp_opn_aux_rec_m.
  move=> q; split; move=> h p; apply E, h, p.
Qed.

Lemma wp_opn_aux_m op targs f f' :
  (∀ q, f q ↔ f' q) →
  wp_opn_aux op targs f →
  wp_opn_aux op targs f'.
Proof. exact: wp_opn_aux_aux_m. Qed.

Definition sem_texprs m vm tys tes : stypes_denote ssem_t tys :=
  stypes_denote_map texpr ssem_t (sem_texpr m vm) tys tes.

Definition wp_opn (dst: lvals) (op: sopn) (args: pexprs) (post: formula) : formula.
  refine
  match type_check_pexprs args (sopn_type_i op) with
  | Some targs =>
    existT _ (
    λ m vm,
    let vargs := sem_texprs m vm _ targs in
      wp_opn_aux op vargs (λ res, projT1 (post_opn dst _ res post) m vm)
    ) _
  | None => ffalse
  end.
Proof.
Admitted. (*
  abstract (
  apply: formula_m => /= m s s' E X;
  unfold sem_texprs;
  erewrite stypes_denote_map_m by (apply sem_texpr_m, env_ext_sym, E);
  apply: wp_opn_aux_m; [ | exact: X];
  move=> q /=;
  set f := post_opn _ _ _ _;
  rewrite (projT2 f m) => //;
  reflexivity).
Defined.
*)

Fixpoint of_svalues_rec ty tys (v: svalue) (vs: svalues) : exec (stypes_denote ssem_t (ty :: tys)) :=
    match tys return exec (stypes_denote ssem_t (ty :: tys)) with
    | [::] => match vs with [::] => of_sval ty v | _ => type_error end
    | ty' :: tys' =>
      match vs with
      | [::] => type_error
      | v' :: vs' =>
        Let w := of_sval ty v in
        Let ws := of_svalues_rec ty' tys' v' vs' in
        ok (w, ws)
      end
    end.

Definition of_svalues (tys: seq sstype) (vs: svalues) : exec (stypes_denote ssem_t tys) :=
  match tys return exec (stypes_denote ssem_t tys) with
  | [::] => match vs with [::] => ok tt | _ => type_error end
  | ty :: tys' => match vs with [::] => type_error | v :: vs' => of_svalues_rec ty tys' v vs' end
  end.

Definition pair_eq_inv {A B} (a a': A) (b b': B) (H: (a, b) = (a', b')) : a = a' ∧ b = b' :=
  let 'Logic.eq_refl := H in conj Logic.eq_refl Logic.eq_refl.

Lemma post_opn_sound xs oty res m vm s' f :
  swrite_lvals gd {| semem := m ; sevm := vm |} xs res = ok s' →
  ∀ res', of_svalues oty res = ok res' →
  projT1 (post_opn xs oty res' f) m (mv_of_fv vm) →
  ⟦f⟧ s'.
Proof.
  case: xs res => [ | x xs ] [ | v vs ] //.
  move=> H; apply ok_inj in H; subst s'.
  case: oty => //.
  apply: rbindP.
  case: oty => // ty tys. unfold post_opn, of_svalues.
  elim: tys m vm ty v vs x xs => [ | ty' tys' IH ] m vm ty v [ | v' vs] x [ | x' xs] // si Hsi.
  move=> REC res' H.
  apply of_sval_inv in H. subst v.
  apply ok_inj in REC. subst si.
  exact: post_assgn_sound.
  case: si Hsi => m' vm' Hsi.
  apply: rbindP => si' Hsi' REC [w res'] H.
  move: H. apply: rbindP => w' H.
  apply of_sval_inv in H. subst v.
  apply: rbindP => ws REC' H.
  apply ok_inj, pair_eq_inv in H; destruct H; subst w' ws.
  specialize (IH _ _ _ _ _ _ _ _ Hsi' REC _ REC').
  move=> H; eapply post_assgn_sound in H; eauto.
  exact: IH.
Qed.

Lemma type_check_pexprs_ok pes tys tes m vm vs :
  type_check_pexprs pes tys = Some tes →
  ssem_pexprs gd {| semem := m ; sevm := vm |} pes = ok vs →
  of_svalues tys vs = ok (sem_texprs m (mv_of_fv vm) _ tes).
Proof.
  case: pes tys tes vs => [ | pe pes ] [ | ty tys ] // tes.
  by move=> [] // H; apply Some_inj in H; subst.
  move=> [ _ | v vs ].
  apply: rbindP => v Hv.
  apply: rbindP => vs Hvs H; apply ok_inj in H; discriminate.
  unfold of_svalues.
  elim: pes pe ty tys tes v vs => [ | pe' pes IH ] pe ty tys tes' v vs' /=;
  generalize (type_check_pexprP m vm pe ty);
  case: type_check_pexpr => // te [v' [Hpe Hv']];
  case: tys tes' => //.
  move=> tes' H; apply Some_inj in H; subst tes'.
  apply: rbindP => w Hw H; apply ok_inj in H; inversion H; clear H. subst w vs'.
  simpl in *. congruence.
  move=> ty' tys tes'.
  generalize (type_check_pexprP m vm pe' ty').
  case_eq (type_check_pexpr pe' ty') => // te' Hte' [w [Hpe' Hw]].
  case_eq (type_check_pexprs pes tys) => // tes Htes H; apply Some_inj in H; subst tes'.
  unfold ssem_pexprs; unfold mapM. rewrite Hpe Hpe'. simpl.
  fold mapM. fold (ssem_pexprs gd {| semem := m ; sevm := vm |} pes).
  case_eq (ssem_pexprs gd {| semem := m ; sevm := vm |} pes) => // tes' Htes' H; apply ok_inj in H.
  inversion H; clear H; subst v' vs'.
  rewrite Hv'. simpl.
  specialize (IH pe' ty' tys (stype_cons te' tes) w).
  simpl in IH. rewrite Hte' Htes in IH.
  specialize (λ vs, IH vs Logic.eq_refl).
  unfold ssem_pexprs in IH. simpl in IH.
  fold (ssem_pexprs gd {| semem := m ; sevm := vm |} pes) in IH.
  rewrite Hpe' Htes' in IH. simpl in IH.
  specialize (IH _ Logic.eq_refl).
  rewrite IH. simpl. auto.
Qed.

Lemma wp_opn_aux_aux_sound tys P Q :
  wp_opn_aux_aux tys P Q →
  P ⊂ Q.
Proof.
  case: tys P Q => [ | ty tys ] P Q.
  move=> H [] _; exact: H.
  elim: tys ty P Q => [ | ty' tys IH ] ty P Q //.
  move=> H [v vs].
  exact: (IH ty' (λ q, P (v, q)) (λ q, Q (v, q))).
Qed.

Definition SVword_inj a b (H: SVword a = SVword b) : a = b :=
  let 'Logic.eq_refl := H in Logic.eq_refl.

Definition SVbool_inj a b (H: SVbool a = SVbool b) : a = b :=
  let 'Logic.eq_refl := H in Logic.eq_refl.

Lemma ssem_sopn_inv op vargs vargs' res :
  let ity := sopn_type_i op in
  let oty := sopn_type_o op in
  of_svalues ity vargs = ok vargs' →
  ssem_sopn op vargs = ok res →
  of_svalues oty res = ok (eval_sopn op vargs').
Proof.
Admitted. (*
  case: op vargs' => /=;
  repeat match goal with
  | |- _ → _ => intro
  | H : SVword ?a = SVword ?b |- _ => apply SVword_inj in H
  | H : SVbool ?a = SVbool ?b |- _ => apply SVbool_inj in H
  | H : type_error = ok _ |- _ => refine (let 'Logic.eq_refl := H in I)
  | H : sto_word _ = ok _ |- _ => apply sto_word_inv in H
  | H : sto_bool _ = ok _ |- _ => apply sto_bool_inv in H
  | H : Let _ := _ in _ = ok _ |- _ => apply bindW in H
  | H : match ?a with _ => _ end = ok _ |- _ => destruct a
  | H : ok _ = ok _ |- _ => apply ok_inj in H
  | H : ?a = ?b |- _ => subst a || subst b
  | H : ex2 _ _ |- _ => destruct H
  end; auto.
Qed.
*)

Lemma wp_opn_sound prg ii xs t op args f :
  hoare prg gd ⟦wp_opn xs op args f⟧ [:: MkI ii (Copn xs t op args)] ⟦f⟧.
Proof.
Admitted. (*
  move=> [m vm] s1 /ssem_inv[s' [/ssem_I_inv [i' [ii' [/MkI_inj [? <-]] /ssem_i_inv [vargs [res [Hargs [Hvs Hs']]]]]] /ssem_inv ->]]; subst ii'.
  unfold wp_opn.
  case (type_check_pexprs _ _) as [ targs | ] eqn: EQ. 2: apply ffalse_denote.
  move: (type_check_pexprs_ok _ _ _ _ _ _ EQ Hargs) => Htargs.
  simpl.
  unfold wp_opn_aux.
  set vm' := mv_of_fv _. fold vm' in Htargs.
  set ity := sopn_type_i _. fold ity in targs, Htargs, EQ.
  set oty := sopn_type_o _.
  set vargs' := sem_texprs _ _ _ _. fold vargs' in Htargs.
  move=> H.
  move: (ssem_sopn_inv _ _ _ _ Htargs Hvs) => X.
  fold oty in X.
  refine (post_opn_sound xs oty res m vm _ f Hs' _ X _).
  fold vm'.
  move: H.
  set f' :=(λ res : stypes_denote ssem_t oty, projT1 (post_opn xs oty res f) m vm').
  fold (f' (eval_sopn op vargs')).
  set res' := eval_sopn _ _.
  move=> H; exact: (wp_opn_aux_aux_sound _ (eq res') f' H).
Qed.
*)

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
  (∀ f, hoare prg gd ⟦wp_c1 f⟧ c1 ⟦f⟧) →
  (∀ f, hoare prg gd ⟦wp_c2 f⟧ c2 ⟦f⟧) →
  hoare prg gd ⟦wp_if e wp_c1 wp_c2 f ⟧ [:: MkI ii (Cif e c1 c2) ] ⟦f⟧.
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
  (∀ f, hoare prg gd ⟦wp_c1 f⟧ c1 ⟦f⟧) →
  (∀ f, hoare prg gd ⟦wp_c2 f⟧ c2 ⟦f⟧) →
  hoare prg gd ⟦wp_if' e wp_c1 wp_c2 f ⟧ [:: MkI ii (Cif e c1 c2) ] ⟦f⟧.
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

Definition wp_rec : cmd → formula → formula :=
  Eval lazy beta delta [cmd_rect instr_Rect list_rect wp_assgn (* wp_opn *) wp_opn_aux] in
  @cmd_rect
    (λ _, instr_info → formula → formula)
    (λ _, formula → formula)
    (λ _, formula → formula)
    (* instr_r *)
    (λ i ii wpi, wpi ii)
    (* nil *)
    (λ Q, Q)
    (* seq *)
    (λ i c wpi wpc Q, wpi (wpc Q))
    (* Cassgn *)
    (λ x _ e ii, wp_assgn x e)
    (* Copn *)
    (λ xs t o es ii, wp_opn xs o es)
    (* Cif *)
    (λ e c1 c2 wp1 wp2 ii, wp_if' e wp1 wp2)
    (* Cfor *)
    (λ v dr lo hi b wpb ii Q, ffalse)
    (* Cwhile *)
    (λ c e c' wpc wpc' ii Q, ffalse)
    (* Ccall *)
    (λ ii xs f es ii Q, ffalse).

Lemma wp_rec_sound prg c f :
  hoare prg gd ⟦wp_rec c f⟧ c ⟦f⟧.
Proof.
  set Pr := λ i : instr_r, ∀ ii f, hoare prg gd ⟦wp_rec [:: MkI ii i] f ⟧ [:: MkI ii i ] ⟦f⟧.
  set Pi := λ i : instr, ∀ f, hoare prg gd ⟦ wp_rec [:: i] f⟧ [:: i] ⟦f⟧.
  set Pc := λ c : cmd, ∀ f, hoare prg gd ⟦wp_rec c f⟧ c ⟦f⟧.
  refine (@cmd_rect Pr Pi Pc _ _ _ _ _ _ _ _ _ c f); clear.
  - by move=> i ii H //.
  - by move=> f; apply: hoare_skip_core.
  - move=> i c Hi Hc f.
    apply: hoare_cons.
    + 2: apply Hc.
    exact: Hi.
  - by move=> x t e ii f; apply: wp_assgn_sound.
  - by move=> xs op es ii f; apply: wp_opn_sound.
  - move=> e c1 c2 H1 H2 ii f.
    apply: wp_if'_sound.
    + exact: H1.
    exact: H2.
  - by move=> v dr lo hi c Hc ii f s s' H; apply: ffalse_denote.
  - by move=> c e c' Hc Hc' ii f s s' H; apply: ffalse_denote.
  - by move=> i xs fn es ii f s s' H; apply: ffalse_denote.
Qed.

Lemma hoare_by_wp prg (P: hpred) c Q :
  P ⊂ ⟦wp_rec c ⟨Q⟩⟧ →
  hoare prg gd P c Q.
Proof.
  move=> E.
  eapply hoare_conseq. exact E. 2: apply wp_rec_sound.
  apply formula_of_hpred_denote.
Qed.

End WEAKEST_PRECONDITION.

Ltac find_in_map_set m x :=
  match m with
  | @Mv.set _ ?m' ?y ?v =>
    let t := constr: (x == y) in
    let d := eval vm_compute in t in
    match d with
    | true => constr:(v)
    | false => find_in_map_set m' x
    end
  end.

Ltac mv_get_set :=
  repeat
  match goal with
  | H : context[ @Mv.get ?to ?m ?x ] |- _ =>
    let v := find_in_map_set m x in
    change (@Mv.get to m x) with v in H
  | |- context[ @Mv.get ?to ?m ?x ] =>
    let v := find_in_map_set m x in
    change (@Mv.get to m x) with v
  end.

Tactic Notation "post_wp" := simpl; unfold Fv.get; simpl; intros; mv_get_set.
