(* ** Imports and settings *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat.
From Coq Require Import ZArith Uint63.
Require Import values sopn pseudo_operator expr psem compiler_util word.

Require Export typing_new.
Import E.

Local Open Scope seq_scope.
Section PROOF.

Context `{asmop : asmOp}.
Context {syscall_state : Type}.
Context {ep : EstateParams syscall_state}.
Context {spp : SemPexprParams}.

Existing Instance nosubword.

(* Generic lemmas about the error monad *)

Lemma rbind_noerrty eT aT bT (m : result eT aT) (f : aT -> result eT bT) (e : eT) :
  m <> Error e ->
  (forall a, m = ok a -> f a <> Error e) ->
  (Let a := m in f a) <> Error e.
Proof.
  case: m => [a|e'] /= hm hf //=.
  - by apply hf.
  - congruence.
Qed.

Lemma mapM_noerrty {aT bT} (f : aT -> result error bT) l :
  (forall a, List.In a l -> f a <> Error ErrType) ->
  mapM f l <> Error ErrType.
Proof.
  elim: l => [|a l' ih] Hnoerr //=.
  apply rbind_noerrty => [|b _] //=.
  - apply Hnoerr, List.in_eq.
  - apply rbind_noerrty => [| _bs] //=.
    apply ih => a' HIn. by apply/Hnoerr/(List.in_cons a).
Qed.

Lemma fold2_Forall2 {aT bT eT : Type} (err : eT) (f : aT -> bT -> unit -> result eT unit) la lb :
  fold2 err f la lb tt = ok tt ->
  List.Forall2 (fun a b => f a b tt = ok tt) la lb.
Proof.
  elim: la lb => [|a la ih] [|b lb] //=.
  t_xrbindP => Hab /ih Hlalb //=. by apply: List.Forall2_cons.
Qed.

Lemma fold2_In {aT bT eT : Type} (err : eT) (f : aT -> bT -> unit -> result eT unit) la lb a :
  fold2 err f la lb tt = ok tt ->
  List.In a la ->
  exists2 b, List.In b lb & f a b tt = ok tt.
Proof.
  move=> Hforall.
  apply fold2_Forall2 in Hforall.
  elim: Hforall => [//| a' b' la' lb' Hfb' _ IH] /= -[<-|/IH [b HInb Hfb]].
  - by exists b'; [left|].
  - by exists b; [right|].
Qed.

(* Lemmas about values, conversions and primitive operations that never fail with ErrType *)

Lemma of_val_noerrty t v :
  subctype t (type_of_val v) ->
  of_val t v <> Error ErrType.
Proof.
  case: v => [b|z|len a|ws w|[||n|ws] ht'] /=; case: t => //=.
  - by move=> z /eqP [->]; rewrite WArray.castK.
  - by move=> s HCMP; rewrite (truncate_word_le _ HCMP).
Qed.

Lemma truncate_val_noerrty t v :
  subctype t (type_of_val v) ->
  truncate_val t v <> Error ErrType.
Proof.
  rewrite /truncate_val. move=> Hsub.
  apply: rbind_noerrty => //; by apply of_val_noerrty.
Qed.

Lemma read_noerrty {ptr : eqType} {P : pointer_op ptr} {cm : Type} {CM : coreMem ptr cm}
    (m : cm) al p ws :
  read m al p ws <> Error ErrType.
Proof.
  rewrite /read /assert.
  case: ifP => _ //.
  apply rbind_noerrty => [//| _ _].
  apply rbind_noerrty => [|//].
  apply: mapM_noerrty => k _ h; exact: (get_noerrty h).
Qed.

Lemma sem_sop1_typed_noerrty op (x : sem_t (eval_atype (type_of_op1 op).1)) :
  sem_sop1_typed op x <> Error ErrType.
Proof.
  case: op x => [ | | | | | | [] | ? [?|?|?|?|?|?]] x //=;
  rewrite /wint_of_int /in_wint_range /assert; by case: ifP.
Qed.

Lemma sem_sop1_noerrty op v :
  subctype (eval_atype (type_of_op1 op).1) (type_of_val v) ->
  sem_sop1 op v <> Error ErrType.
Proof.
  move=> Hsub; rewrite /sem_sop1.
  apply: rbind_noerrty => [|x _]; first exact: of_val_noerrty Hsub.
  apply: rbind_noerrty => [|_ _ //].
  exact: sem_sop1_typed_noerrty.
Qed.

Lemma sem_sop2_typed_noerrty op
    (x1 : sem_t (eval_atype (type_of_op2 op).1.1))
    (x2 : sem_t (eval_atype (type_of_op2 op).1.2)) :
  sem_sop2_typed op x1 x2 <> Error ErrType.
Proof.
  case: op x1 x2 =>
    [ (* Obeq Oand Oor *)           | |
    | (* Oadd Omul Osub *)          [] | [] | []
    | (* Odiv Omod *)               ? [|?] | ? [|?]
    | (* Oland Olor Olxor Olsr *)   | | |
    | (* Olsl Oasr *)               [] | []
    | (* Oror Orol *)               |
    | (* Oeq Oneq *)                [] | []
    | (* Olt Ole Ogt Oge *)         [] | [] | [] | []
    | (* Ovadd..Ovasr *)            | | | | |
    | (* Owi2 *)                    ?? [] ] x1 x2 //=;
  rewrite /mk_sem_divmod /mk_sem_wiop2 /mk_sem_wishift /wint_of_int /in_wint_range /assert; by case: ifP.
Qed.

Lemma sem_sop2_noerrty op v1 v2 :
  subctype (eval_atype (type_of_op2 op).1.1) (type_of_val v1) ->
  subctype (eval_atype (type_of_op2 op).1.2) (type_of_val v2) ->
  sem_sop2 op v1 v2 <> Error ErrType.
Proof.
  move=> hsub1 hsub2; rewrite /sem_sop2.
  apply: rbind_noerrty => [|x1 _]; first exact: of_val_noerrty hsub1.
  apply: rbind_noerrty => [|x2 _]; first exact: of_val_noerrty hsub2.
  apply rbind_noerrty => [|_ _ //].
  exact: sem_sop2_typed_noerrty.
Qed.

Lemma app_sopn_noerrty T ts (f : sem_prod ts (exec T)) vs :
  sem_forall (fun r => r <> Error ErrType) ts f ->
  List.Forall2 (fun t v => subctype t (type_of_val v)) ts vs ->
  app_sopn ts f vs <> Error ErrType.
Proof.
  move=> Hsemf HF.
  elim: HF f Hsemf => [| cty v ts' vs' Hsub HF' IH] f Hsemf //=.
  apply rbind_noerrty => [| t Hofv]; first by apply of_val_noerrty.
  by apply/IH.
Qed.

(* Inversion lemmas for the type checker *)

Lemma check_typeP te ty : check_type te ty = ok tt -> subatype ty te.
Proof. by rewrite /check_type; case: ifP => // /negbFE. Qed.

Lemma check_ptrP t :
  check_ptr t = ok tt ->
  exists2 ws, t = aword ws & (Uptr <= ws)%CMP.
Proof.
  by rewrite /check_ptr => /check_typeP;
  case: t => // ws ?; exists ws.
Qed.

Lemma check_arrayP t :
  check_array t = ok tt ->
  exists ws n, t = aarr ws n.
Proof.
  by rewrite /check_array;
  case: t => // ws n _ ; exists ws, n.
Qed.

Lemma check_global_declP (gd : glob_decl) :
  check_global_decl gd = ok tt ->
  type_of_val (gv2val gd.2) = eval_atype (vtype gd.1).
Proof.
  rewrite /check_global_decl. case: gd => x [ws w | len a] /=;
    by case: (vtype x) => //= >; case: ifP => // /eqP ->.
Qed.

(* Preservation *)

Lemma compat_val_defined ty v :
  is_defined v ->
  compat_val ty v = (type_of_val v == ty).
Proof. by rewrite /compat_val => ->. Qed.

Lemma ty_expr_preserves (gd : glob_decls) (s : estate) e ty v :
  ty_expr e = ok ty ->
  sem_pexpr true gd s e = ok v ->
  type_of_val v = eval_atype ty.
Proof.
  case: e =>
    [ z
    | b
    | ws n
    | x
    | al aa sz x e
    | al aa sz x e
    | al sz e
    | op e
    | op e1 e2
    | op es
    | t e e1 e2
    ] /=.
  - by move=> [<-] [<-].
  - by move=> [<-] [<-].
  - by move=> [<-] [<-].
  - by move=> [<-] /get_gvar_compat [] /compat_val_defined -> /eqP.
  - rewrite /ty_get_set; t_xrbindP=> _ _ _ _ ?; subst ty.
    rewrite /on_arr_var; t_xrbindP=> -[] // len a.
    by t_xrbindP=> _ _ _ _ _ ? _ <-.
  - rewrite /ty_get_set_sub; t_xrbindP=> _ _ _ _ ?; subst ty.
    rewrite /on_arr_var; t_xrbindP=> -[] // len a.
    by t_xrbindP=> _ _ _ _ _ ? _ <-.
  - by rewrite /ty_load_store; t_xrbindP=> _ _ _ ? _ _ _ _ ? _ ?; subst ty v.
  - rewrite /= /type_of_op1 /sem_sop1.
    by case: op => [ | | | | | | [] | ? []] //=; t_xrbindP => *; subst.
  - rewrite /= /sem_sop2 /type_of_op2.
    by case: op =>
      [ | | | [] | [] | [] | ? [] | ? [] | | | | | [] | [] | | | [] | [] | | |
      | | | | | | | | ?? [] ] //=; t_xrbindP => *; subst.
  - rewrite /= /sem_opN /type_of_opN.
    by case: op => //=; t_xrbindP => *; subst.
  - rewrite /= /check_expr.
    t_xrbindP=> ? _ _ ? _ _ ? _ _ ? b ? _ _ ? ? _ hv1 ? ? _ hv2 ?; subst.
    by case: b; [exact: truncate_val_has_type hv1 | exact: truncate_val_has_type hv2].
Qed.

(* Progress *)

Lemma sem_to_int_noerrty gd s e tye :
  ty_expr e = ok tye ->
  check_int tye = ok tt ->
  sem_pexpr true gd s e <> Error ErrType ->
  (Let x := sem_pexpr true gd s e in to_int x) <> Error ErrType.
Proof.
  move=> Hty /check_typeP/eqP Htyeint Hne.
  apply: rbind_noerrty => // v /(ty_expr_preserves Hty) Htv.
  by apply: (of_val_noerrty (t := cint)); rewrite Htv -Htyeint.
Qed.

Lemma sem_truncate_val_noerrty gd s e ty t :
  sem_pexpr true gd s e <> Error ErrType ->
  ty_expr e = ok ty ->
  check_type ty t = ok tt ->
  (Let v := sem_pexpr true gd s e in truncate_val (eval_atype t) v) <>
    Error ErrType.
Proof.
  move=> Hsem Hty /check_typeP Hsub.
  apply rbind_noerrty => [//| v /(ty_expr_preserves Hty) Hvty].
  apply/truncate_val_noerrty. rewrite Hvty. by apply subatype_subctype.
Qed.

Lemma check_exprs_subctype gd s es tins vs :
  check_exprs ty_expr es tins = ok tt ->
  mapM (sem_pexpr true gd s) es = ok vs ->
  List.Forall2 (fun t v => subctype t (type_of_val v)) (map eval_atype tins) vs.
Proof.
  elim: es tins vs => [|e es IH] [|tin tins'] vs; rewrite /check_exprs //=.
  - by move=> _ [<-].
  - rewrite /check_expr. t_xrbindP => tye Htye /check_typeP Hsub Hc v Hs vs' Hmap <-.
    apply List.Forall2_cons; last apply (IH _ _ Hc Hmap).
    rewrite (ty_expr_preserves Htye Hs).
    apply (subatype_subctype Hsub).
Qed.

Lemma on_arr_var_noerrty {T} gd vm x ws n (f : forall len, WArray.array len -> exec T) :
  (forall g, List.In g gd -> check_global_decl g = ok tt) ->
  ty_gvar x = aarr ws n ->
  (forall len (t : WArray.array len), f len t <> Error ErrType) ->
  on_arr_var (get_gvar true gd vm x) f <> Error ErrType.
Proof.
  rewrite /ty_gvar /ty_var /get_gvar /get_var /get_global /get_global_value => /=.
  move=> Hgd Htyx Hf.
  case Hassoc: (assoc gd (gv x)) => [p|].
  - move: (check_global_declP (Hgd _ (assoc_mem' Hassoc))) => /= ->.
    rewrite Htyx eqxx => //=.
    case: (is_lvar x); case: (is_defined vm.[gv x]) => //=.
    + move: (Vm.getP vm (v_var (gv x))) => //=.
      by rewrite Htyx => /compat_valEl [t ->] /Hf.
    1-2: by have := check_global_declP (Hgd _ (assoc_mem' Hassoc));
         rewrite Htyx => /type_of_valI [a ->].
  - case: (is_lvar x); case: (is_defined vm.[gv x]) => //=.
    move: (Vm.getP vm (v_var (gv x))).
    by rewrite Htyx => /compat_valEl [t ->].
Qed.

Lemma ty_expr_progress (gd : glob_decls) (s : estate) (e : pexpr) (ty : atype) :
  allM check_global_decl gd = ok tt ->
  ty_expr e = ok ty ->
  sem_pexpr true gd s e <> Error ErrType.
Proof.
  move=> /allMP Hgd.
  elim: e ty =>
    [ | | | x | ??? x e IH | ??? x e IH | ? ws e IH
    | op e IHe | op e1 IHe1 e2 IHe2 | op es H | t e1 IHe1 e2 IHe2 e3 IHe3 ] ty //=.
  - rewrite /= /get_gvar /get_var /get_global /get_global_value => _ /=.
    case: (is_lvar x).
    - by case: (is_defined (evm s).[gv x]).
    - case E: (assoc gd (gv x)) => [p|] //.
      by move: (check_global_declP (Hgd _ (assoc_mem' E))) => /= /eqP ->.
  - rewrite /ty_get_set.
    t_xrbindP => tye Htye /check_arrayP [ws [n Htyx]] HtyeInt _.
    apply (on_arr_var_noerrty Hgd Htyx) => len' t'.
    apply: rbind_noerrty => [|i _]; first exact: sem_to_int_noerrty Htye HtyeInt (IH _ Htye).
    apply: rbind_noerrty => [| _ _ //].
    exact: read_noerrty.
  - rewrite /ty_get_set_sub.
    t_xrbindP => tye Htye /check_arrayP [ws [n Htyx]] HtyeInt _.
    apply (on_arr_var_noerrty Hgd Htyx) => len' t'.
    apply: rbind_noerrty => [|i _]; first exact: sem_to_int_noerrty Htye HtyeInt (IH _ Htye).
    apply: rbind_noerrty => [| _ _ //].
    rewrite /WArray.get_sub.
    case: ifP => _ //.
  - rewrite /ty_load_store.
    t_xrbindP => tye Htye /check_ptrP [ws' Htyeword ?] _.
    apply: rbind_noerrty => [|w2 _].
    - apply: rbind_noerrty => [|v /(ty_expr_preserves Htye) Htv]; first exact: IH Htye.
      by apply: (of_val_noerrty (t := cword Uptr)); rewrite Htv Htyeword.
    apply: rbind_noerrty => [|_ _ //]; exact: read_noerrty.
  - rewrite /check_expr.
    case htop: (type_of_op1 op) => [tin tout].
    t_xrbindP => te hte /check_typeP hsub _.
    apply rbind_noerrty => [|v Hs]; first exact: IHe hte.
    apply sem_sop1_noerrty.
    rewrite htop /= (ty_expr_preserves hte Hs). apply: subatype_subctype hsub.
  - rewrite /check_expr.
    case htop: (type_of_op2 op) => [[tin1 tin2] tout].
    t_xrbindP => te1 hte1 /check_typeP hsub1 te2 hte2 /check_typeP hsub2 _.
    move: (IHe1 _ hte1) (IHe2 _ hte2) => Hs1 Hs2.
    apply: rbind_noerrty => //= v1 he1.
    apply: rbind_noerrty => //= v2 he2.
    apply sem_sop2_noerrty.
    - rewrite htop /= (ty_expr_preserves hte1 he1). apply (subatype_subctype hsub1).
    - rewrite htop /= (ty_expr_preserves hte2 he2). apply (subatype_subctype hsub2).
  - case htop: (type_of_opN op) => [tins touts].
    t_xrbindP => Hc _.
    apply: rbind_noerrty => [|vs Hmap].
    - apply mapM_noerrty => e HIn.
      have [tin _ Htyok] := fold2_In Hc HIn.
      move: Htyok. rewrite /check_expr. t_xrbindP => te hte _.
      apply (H e HIn te hte).
    - clear H Hgd.
      rewrite /sem_opN.
      apply rbind_noerrty => [/=|//].
      apply app_sopn_noerrty; first by apply/sem_forall_m/sem_opN_typed_ok => -[].
      - rewrite htop /=.
        exact: check_exprs_subctype Hc Hmap.
  - rewrite /check_expr.
    t_xrbindP => ty1 Hty1 /check_typeP/eqP Hbool ty2 Hty2 Hc2 ty3 Hty3 Hc3 _.
    apply rbind_noerrty => [|b _].
    - apply rbind_noerrty => [//|v1 /(ty_expr_preserves Hty1)]; first exact: IHe1 Hty1.
      rewrite -Hbool /=. case v1 => [ | | | | []] //.
    - apply rbind_noerrty => [|? _]; first by exact: sem_truncate_val_noerrty (IHe2 _ Hty2) Hty2 Hc2.
      apply rbind_noerrty => [|//].
      exact: sem_truncate_val_noerrty (IHe3 _ Hty3) Hty3 Hc3.
Qed.

End PROOF.
