(* ** Imports and settings *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat all_ssreflect.
From Coq Require Import ZArith Uint63.
Require Import values sopn pseudo_operator expr psem compiler_util word sem_op_typed_facts.

Require Export typing_new.
Import E.

Local Open Scope seq_scope.

(* -------------------------------------------------------------------------- *)
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
  elim: l => [|a l' IH] Hnoerr //=.
  apply rbind_noerrty => [|b _] //=.
  - apply Hnoerr, List.in_eq.
  - apply rbind_noerrty => [| _bs] //=.
    apply IH => a' HIn. by apply/Hnoerr/(List.in_cons a).
Qed.

Lemma foldM_noerrty {aT bT} (f : aT -> bT -> result error bT) l b0:
  (forall a b, f a b <> Error ErrType) ->
  foldM f b0 l <> Error ErrType.
Proof.
  elim: l b0 => [|a l IH b0 Hf] //=.
  apply rbind_noerrty => [|? _] //. by apply IH.
Qed.

Lemma foldM_oktt {eT aT : Type} a l (f : aT -> unit -> result eT unit ):
  foldM f tt l = ok tt ->
  List.In a l ->
  f a tt = ok tt.
Proof.
  elim: l => /= [//|x xs IH Hf Hin]; move: Hf. t_xrbindP => Hfx Hfold.
  case: Hin => [<- //| Hin'].
  by apply: IH.
Qed.

Lemma fold2P {aT bT eT : Type} (err : eT) (f : aT -> bT -> unit -> result eT unit) la lb :
  fold2 err f la lb tt = ok tt <->
  List.Forall2 (fun a b => f a b tt = ok tt) la lb.
Proof.
  split.
  - elim: la lb => [|a la ih] [|b lb] //=.
    t_xrbindP => Hab /ih Hlalb //=. by apply: List.Forall2_cons.
  - elim: la lb => [ |a la ih] [|b lb] //=.
    1-2: by move=> /List_Forall2_inv Hf.
    - move=> /List_Forall2_inv [Hf HF].
      rewrite Hf /=. exact: ih HF.
Qed.

Lemma fold2_noerrty {aT bT sT} (R : aT -> bT -> Prop)
      (f : aT -> bT -> sT -> result error sT) la lb s :
  List.Forall2 R la lb ->
  (forall a b s, R a b -> f a b s <> Error ErrType) ->
  fold2 ErrType f la lb s <> Error ErrType.
Proof.
  move=> hfor hf; elim: hfor s => {la lb} [|a b la lb hab _ ih] s //=.
  apply: rbind_noerrty => [|s' _]; first exact: hf _ _ _ hab.
  exact: ih.
Qed.

Lemma fold2_In {aT bT eT : Type} (err : eT) (f : aT -> bT -> unit -> result eT unit) la lb a :
  fold2 err f la lb tt = ok tt ->
  List.In a la ->
  exists2 b, List.In b lb & f a b tt = ok tt.
Proof.
  move=> /fold2P HForall2.
  elim: HForall2 => [//| a' b' la' lb' Hfb' _ IH] /= -[<-|/IH [b HInb Hfb]].
  - by exists b'; [left|].
  - by exists b; [right|].
Qed.

Lemma Forall2_mapM2_noerrty {aT bT cT} (R : aT -> bT -> Prop) (f : aT -> bT -> result error cT) la lb :
  List.Forall2 R la lb ->
  (forall a b, R a b -> f a b <> Error ErrType) ->
  mapM2 ErrType f la lb <> Error ErrType.
Proof.
  elim => {la lb} //= a b la lb hR _ ih hf.
  apply: rbind_noerrty => [| ? _]; first exact: hf.
  apply: rbind_noerrty => //; exact: ih.
Qed.

Lemma In_rev {A : Type} (x : A) (l : seq A) : List.In x l -> List.In x (rev l).
Proof.
  elim: l => //= a l ih [<- | /ih h]; rewrite rev_cons -cats1 List.in_app_iff.
  - by right; left.
  by left.
Qed.


Section WITH_PARAMS.

Existing Instance nosubword.
Existing Instance progUnit.
Existing Instance indirect_c.

Context
  {asm_op syscall_state : Type}
  {wa  : WithAssert}
  {ep  : EstateParams syscall_state}
  {spp : SemPexprParams}
  {sip : SemInstrParams asm_op syscall_state}
  {scP : semCallParams}.

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

Lemma check_exprsP es tys :
  check_exprs ty_expr es tys = ok tt <->
  List.Forall2 (fun e ty => check_expr ty_expr e ty = ok tt) es tys.
Proof. exact: fold2P. Qed.

Lemma check_lvalsP xs tys :
  check_lvals xs tys = ok tt <-> List.Forall2 (fun x ty => check_lval x ty = ok tt) xs tys.
Proof. exact: fold2P. Qed.

Lemma check_lvalP x ty :
  check_lval x ty = ok tt ->
  exists2 tx, ty_lval x = ok tx & subatype tx ty.
Proof.
  rewrite /check_lval/ty_lval.
  case: x => [? tx Hchk | v Hchk| ??? e | ????? | ?????] //=.
  - exists tx => //. exact: check_typeP.
  - exists (ty_var v) => //. exact: check_typeP.
  - t_xrbindP => te Htyls Hchkty. exists te => //. exact: check_typeP.
  - t_xrbindP => te Htygs Hchkty. exists te => //. exact: check_typeP.
  - t_xrbindP => te Htygs Hchkty. exists te => //. exact: check_typeP.
Qed.

Lemma check_lvals_vars_subctype (xs : seq var_i) tys :
  check_lvals (map Lvar xs) tys = ok tt ->
  List.Forall2 (fun x cty => subctype (eval_atype (ty_var x)) cty) xs (map eval_atype tys).
Proof.
  move=> /check_lvalsP HF.
  have HF' : List.Forall2 (fun x ty => subatype (ty_var x) ty) xs tys.
  - apply: (Forall2_trans _ (map_Forall2 Lvar xs) HF).
    by move=> x v ty <- /check_lvalP [tx [-> ?]].
  apply: (Forall2_trans _ HF' (map_Forall2 eval_atype tys)) => aty v cty Hsuba <-.
  by apply: subatype_subctype.
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

Lemma mapM2_truncate_val_type tys vs vs' :
  mapM2 ErrType truncate_val tys vs = ok vs' ->
  List.Forall2 (fun cty v => type_of_val v = cty) tys vs'.
Proof.
  elim: tys vs vs' => [|t ts IH] [|v vs] vs' //=.
  - by move=> [<-].
  - t_xrbindP=> v' /truncate_val_has_type Htyv vs'' /IH Hmap <-.
    by apply: List.Forall2_cons.
Qed.

Lemma compat_val_defined ty v :
  is_defined v ->
  compat_val ty v = (type_of_val v == ty).
Proof. by rewrite /compat_val => ->. Qed.

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

Lemma write_noerrty {ptr : eqType} {P : pointer_op ptr} {cm : Type} {CM : coreMem ptr cm}
  (m : cm) al ptr' sz (w : word sz):
  write m al ptr' w <> Error ErrType.
Proof.
  rewrite /write /assert.
  case: ifP => _ //.
  apply: foldM_noerrty => a b h; exact: (set_noerrty h).
Qed.

Lemma sem_sop1_typed_noerrty op (x : sem_t (eval_atype (type_of_op1 op).1)) :
  sem_sop1_typed op x <> Error ErrType.
Proof.
  case: op x => [ | | | | | | [] | ? [?|?|?|?|?|?]] x //=;
  rewrite /sem_sop1_typed /mk_sem_op /check_safe => /=; by case: ifP.
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
  rewrite /sem_sop2_typed /mk_sem_op /check_safe => /=; by case: ifP.
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

Lemma on_arr_var_noerrty {T} vm x ws n (f : forall len, WArray.array len -> exec T) :
  ty_var x = aarr ws n ->
  (forall (t : WArray.array (arr_size ws n)), f _ t <> Error ErrType) ->
  on_arr_var (get_var true vm x) f <> Error ErrType.
Proof.
  rewrite /ty_var /get_gvar /get_var => /= Htyx Hf.
  case: (is_defined vm.[x]) => //=.
  move: (Vm.getP vm (v_var x)).
  by rewrite Htyx => /compat_valEl [t ->].
Qed.

Lemma on_arr_gvar_noerrty {T} gd vm x ws n (f : forall len, WArray.array len -> exec T) :
  (forall g, List.In g gd -> check_global_decl g = ok tt) ->
  ty_gvar x = aarr ws n ->
  (forall (t : WArray.array (arr_size ws n)), f _ t <> Error ErrType) ->
  on_arr_var (get_gvar true gd vm x) f <> Error ErrType.
Proof.
  move=> Hgd Htyx Hf; rewrite /get_gvar; case: ifP => _.
  - exact: on_arr_var_noerrty Htyx Hf.
  rewrite /get_global /get_global_value /=.
  case Hassoc: (assoc gd (gv x)) => [p|] //=.
  have Hp := check_global_declP (Hgd _ (assoc_mem' Hassoc)).
  move: Hp; rewrite /ty_gvar /ty_var in Htyx; rewrite Htyx => /= Hp.
  rewrite Hp eqxx /=.
  by move: Hp => /type_of_valI [a ->]; exact: Hf.
Qed.

Section EXPR.
(* Expr Preservation *)

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
  1-3: by move=> [<-] [<-].
  2-3: by rewrite /ty_get_set /ty_get_set_sub; t_xrbindP=> _ _ _ _ <-;
       rewrite /on_arr_var; t_xrbindP=> -[] // len a; t_xrbindP=> _ _ _ _ _ ? _ <-.
  - by move=> [<-] /get_gvar_compat [] /compat_val_defined -> /eqP.
  - by rewrite /ty_load_store; t_xrbindP=> _ _ _ <- _ _ _ _ ? _ <-.
  - rewrite /= /type_of_op1 /sem_sop1.
    by case: op => [ | | | | | | [] | ? []] //=; t_xrbindP => *; subst.
  - rewrite /= /sem_sop2 /type_of_op2.
    by case: op =>
      [ | | | [] | [] | [] | ? [] | ? [] | | | | | [] | [] | | | [] | [] | | |
      | | | | | | | | ?? [] ] //=; t_xrbindP => *; subst.
  - rewrite /= /sem_opN /type_of_opN.
    by case: op => //=; t_xrbindP => *; subst.
  - rewrite /= /check_expr.
    t_xrbindP=> ? _ _ ? _ _ ? _ _ <- b ? _ _ ? ? _
      /truncate_val_has_type hv1 ? ? _ /truncate_val_has_type hv2 <-.
    by case: b.
Qed.

(* Expr Progress *)
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

Lemma sem_to_bool_noerrty gd s e tye :
  ty_expr e = ok tye ->
  check_type tye abool = ok tt ->
  sem_pexpr true gd s e <> Error ErrType ->
  (Let x := sem_pexpr true gd s e in to_bool x) <> Error ErrType.
Proof.
  move=> Hty /check_typeP/eqP Htyebool Hne.
  apply: rbind_noerrty => // v /(ty_expr_preserves Hty) Htv.
  by apply: (of_val_noerrty (t := cbool)); rewrite Htv -Htyebool.
Qed.

Lemma sem_to_pointer_noerrty gd s e tye:
  ty_expr e = ok tye ->
  check_type tye (aword Uptr) = ok tt ->
  sem_pexpr true gd s e <> Error ErrType ->
  (Let x := sem_pexpr true gd s e in to_pointer x) <> Error ErrType.
Proof.
  move=> Htye /check_typeP/subatype_subctype Hsub Hsem.
  apply: rbind_noerrty => // v /(ty_expr_preserves Htye) Htv.
  by apply: (of_val_noerrty (t := (cword Uptr))); rewrite Htv Hsub.
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
    apply (on_arr_gvar_noerrty Hgd Htyx) => t'.
    apply: rbind_noerrty => [|i _]; first exact: sem_to_int_noerrty Htye HtyeInt (IH _ Htye).
    apply: rbind_noerrty => [| _ _ //].
    exact: read_noerrty.
  - rewrite /ty_get_set_sub.
    t_xrbindP => tye Htye /check_arrayP [ws [n Htyx]] HtyeInt _.
    apply (on_arr_gvar_noerrty Hgd Htyx) => t'.
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

End EXPR.

(* Lvalues: progress *)

Lemma write_var_noerrty (x : var_i) v s :
  subctype (eval_atype (vtype x)) (type_of_val v) ->
  write_var true x v s <> Error ErrType.
Proof.
  rewrite /write_var /set_var /assert => /(subctype_truncatable true) ->.
  by case: ifP.
Qed.

Lemma write_lval_progress x v s gd ty :
  allM check_global_decl gd = ok tt ->
  type_of_val v = eval_atype ty ->
  check_lval x ty = ok tt ->
  write_lval true gd x v s <> Error ErrType.
Proof.
  move=> Hgd Hvty. rewrite /check_lval /ty_lval /=.
  case: x => [?? | ? | ???? | ????? | ?????] //=.
  - rewrite /write_none /assert => /check_typeP/subatype_subctype.
    by rewrite -Hvty => /(subctype_truncatable true) ->; case: ifP.
  - move=> /check_typeP/subatype_subctype; rewrite -Hvty.
    exact: write_var_noerrty.
  - rewrite /ty_load_store.
    t_xrbindP => _ tye Htye /check_ptrP [???] <- /check_typeP/subatype_subctype.
    rewrite -Hvty => Hsubc; subst tye.
    apply: rbind_noerrty => [|?].
    + apply: rbind_noerrty => [/(ty_expr_progress Hgd Htye) //| ? Hsem].
      apply: (of_val_noerrty (t := cword Uptr)).
      by rewrite (ty_expr_preserves Htye Hsem).
    t_xrbindP => ve Hsem Htoptr.
    apply: rbind_noerrty => [/(of_val_noerrty Hsubc) //| ??].
    by apply: rbind_noerrty => [|//]; exact: write_noerrty.
  - rewrite /ty_get_set.
    t_xrbindP => ?? Hty2 /check_arrayP [ws' [n Htyarr]] Hcint <- /check_typeP/subatype_subctype.
    rewrite -Hvty => Hsubc /=.
    apply: (on_arr_var_noerrty Htyarr) => t.
    apply: rbind_noerrty => [|??].
    + by apply: (sem_to_int_noerrty Hty2 Hcint); apply: (ty_expr_progress Hgd Hty2).
    apply: rbind_noerrty => [|??]; first exact: of_val_noerrty Hsubc.
    apply: rbind_noerrty => [|t0 _]; first by rewrite /WArray.set; exact: write_noerrty.
    apply: write_var_noerrty.
    by move: Htyarr; rewrite /ty_gvar /ty_var /= => -> /=; rewrite eqxx.
  - rewrite /ty_get_set_sub.
    t_xrbindP => ?? Hty2 /check_arrayP [ws' [n Htyarr]] Hcint <- /check_typeP/subatype_subctype.
    rewrite -Hvty => Hsubc /=.
    apply: (on_arr_var_noerrty Htyarr) => t.
    apply: rbind_noerrty => [|??].
    + by apply: (sem_to_int_noerrty Hty2 Hcint); apply: (ty_expr_progress Hgd Hty2).
    apply: rbind_noerrty => [|??]; first exact: of_val_noerrty Hsubc.
    apply: rbind_noerrty => [|t0 _]; first by rewrite /WArray.set_sub; case: ifP.
    apply: write_var_noerrty.
    by move: Htyarr; rewrite /ty_gvar /ty_var /= => -> /=; rewrite eqxx.
Qed.


Section IT.

Context
  {E E0 : Type -> Type}
  {wE : with_Error E E0}
  {p  : prog}
  {ev : extra_val_t}.

Definition noerrty err : Prop :=
  err <> ErrType.

#[local] Instance typing_invErr : InvErr :=
  {| invErr_ := noerrty |}.

Lemma rhoare_noerrty {I O} (P : Pred I) (F : fresult error I O) (Q : Pred O) :
  (forall i, P i -> F i <> Error ErrType) ->
  (forall i o, P i -> F i = ok o -> Q o) ->
  rhoare P F Q noerrty.
Proof.
  move=> Herr HQ. rewrite /rhoare /rhoare_io => i HP.
  case HF: (F i) => [o|err].
  - exact: (HQ i o HP HF).
  - move => ?. subst err. by apply (Herr i HP).
Qed.

Context {iE0 : InvEvent E0}.

#[local] Instance spec : HoareSpec :=
  {|
    preF_ := fun fn fs =>
            (exists fd, get_fun (p_funcs p) fn = ok fd /\
              List.Forall2 (fun t v => subctype t (type_of_val v))
                                      (map eval_atype (f_tyin fd)) (fvals fs))
            /\ sem_pre p fn fs = ok tt ;
    postF_ := fun fn fs fs' =>
            (exists fd, get_fun (p_funcs p) fn = ok fd /\
              List.Forall2 (fun t v => subctype t (type_of_val v))
                                      (map eval_atype (f_tyout fd)) (fvals fs'))
            /\ sem_post p fn (fvals fs) fs' = ok tt ;
  |}.

Lemma get_fun_In (fds : ufun_decls) fn f :
  get_fun fds fn = ok f -> List.In (fn, f) fds.
Proof.
  rewrite /get_fun/o2r/get_fundef.
  case Hf: (assoc _ _) => [g | ] // [<-].
  apply: assoc_mem' Hf.
Qed.

Lemma get_funP fds fn f:
  get_fun fds fn = ok f ->
  get_fundef fds fn = Some f.
Proof.
  rewrite /get_fun/o2r. by case: get_fundef => // a [<-].
Qed.

Section CMD.
Context {Ec E0c : Type -> Type}
        {wEc : with_Error Ec E0c}
        {iE0c : InvEvent E0c}
        {sem_Fc : sem_Fun Ec}.

Context (Hgd: allM check_global_decl (p_globs p) = ok tt)
        (Hfns: allM (check_fun (p_funcs p)) (rev (p_funcs p)) = ok tt).

Lemma check_funsP fn fd :
  get_fun (p_funcs p) fn = ok fd ->
  [/\ check_lvals (map Lvar (f_params fd)) (f_tyin fd) = ok tt,
       check_exprs ty_expr (map (Pvar \o mk_gvar) (f_res fd)) (f_tyout fd) = ok tt,
       check_cmd check_instr (p_funcs p) (f_body fd) = ok tt
     & oapp (check_contract (f_tyin fd) (f_tyout fd)) (ok tt) (f_contract fd) = ok tt ].
Proof using Hfns.
  move=> hget. move: (allMP (In_rev (get_fun_In hget)) Hfns). rewrite /check_fun.
  by t_xrbindP => h1 h2 h3 h4 _.
Qed.

Lemma sem_eassert_progress a s :
  check_eassert a = ok tt ->
  sem_eassert (p_globs p) s a <> Error ErrType.
Proof using Hgd.
  elim: a => [e | o es | | e1 e2 | a1 IH1 a2 IH2] => //=.
  - rewrite /check_expr. t_xrbindP => tye Htye Hchk.
    apply: sem_to_bool_noerrty Htye Hchk (ty_expr_progress Hgd Htye).
  - move=> Hchkes.
    apply rbind_noerrty => [|vs HmapM].
    - apply mapM_noerrty => e HIn.
      have [tin _ Htyok] := fold2_In Hchkes HIn.
      move: Htyok. rewrite /check_expr. t_xrbindP => te Hte _.
      apply: (ty_expr_progress Hgd Hte).
    - apply: app_sopn_noerrty; first by apply/sem_forall_m/sem_opN_safety_typed_ok => -[].
      exact: (check_exprs_subctype Hchkes HmapM).
  - rewrite /check_expr. t_xrbindP => te1 Hte1 Hce1 te2 Hte2 Hce2.
    apply: rbind_noerrty => [| w ]; first apply: sem_to_pointer_noerrty Hte1 Hce1 (ty_expr_progress Hgd Hte1).
    t_xrbindP => v1 Hsem1 Hto_pointer1.
    apply: rbind_noerrty => //; apply: sem_to_int_noerrty Hte2 Hce2 (ty_expr_progress Hgd Hte2).
  - t_xrbindP => /IH1 Hchk1 /IH2 Hchk2.
    apply: rbind_noerrty => [//| b Hsem].
    apply: rbind_noerrty => //.
Qed.

Let Pc (c:cmd) :=
  (check_cmd check_instr (p_funcs p) c) = ok tt ->
  hoare p ev PredT c PredT.
Let Pi (i: instr) :=
  Pc [::i].
Let Pi_r (i: instr_r) :=
  forall ii, Pi (MkI ii i).

Lemma check_cmdP:
  (forall ii fn, hoare_f_ii p ev preF ii fn postF) ->
  (forall c, (check_cmd check_instr (p_funcs p) c) = ok tt ->
  hoare p ev PredT c PredT).
Proof using Hgd.
  move=> Hp.
  rewrite /check_cmd /allM.
  apply (cmd_rect (Pr := Pi_r) (Pi:=Pi) (Pc:=Pc)) => //; subst Pi_r Pi Pc => /=.
  by move=> ? ; apply hoare_skip.
  move=> /= i c0 Hi Hc  Hcheck .
  move: Hcheck. rewrite /check_cmd /allM. rewrite -cat1s. rewrite foldM_cat. t_xrbindP=>*.
  apply hoare_cons with (R:=PredT) => //=; first by apply Hi => //=.
  by apply Hc.
  - (*Cassgn*)
    move => x a ty e ? //=.
    rewrite  /check_cmd /allM  /= /check_expr => /=.
    t_xrbindP => tye Htye /check_typeP /subatype_subctype Hsub Htyx _.
    apply hoare_assgn with (Rv:=fun v=>(type_of_val v = eval_atype tye)) (Rtr:=fun v=> (type_of_val v = eval_atype ty)) (Qerr:=noerrty) => [//| |s _ | v Hvty ].
    - apply: rhoare_noerrty => [s _ | s v _ Hsem ].
      - by apply: ty_expr_progress Hgd Htye.
      exact: (ty_expr_preserves Htye Hsem).
    - apply: rhoare_noerrty => [v Hvtye | v v' _ Hvv'].
      + apply: truncate_val_noerrty. by rewrite Hvtye.
      + apply: (truncate_val_has_type Hvv').
    - apply: rhoare_noerrty => [s _ | //].
      apply: (write_lval_progress Hgd Hvty Htyx).
  - (*Copn*) admit.
  - (*Csyscall*) admit.
  - (*Cassert*) admit.
  - (*Cif)*)
    move => e c1 c2 Hc1 Hc2 ii.
    rewrite  /check_cmd /allM /= /check_expr. t_xrbindP => tye Htye /check_typeP /= /eqP ?.
    subst tye. move=> /Hc1 Hcheck_c1 /Hc2 Hcheck_c2 _.
    apply: (hoare_if (Qerr:=noerrty)) => //.
    rewrite /sem_cond. apply rhoare_noerrty => [s _ | //].
    apply rbind_noerrty => [|v Hsem]; first exact: ty_expr_progress Hgd Htye.
    apply: (of_val_noerrty (t:=cbool)).
    by rewrite (ty_expr_preserves Htye Hsem).
    by case.
  - (*Cfor*) admit.
  - (*Cwhile*) admit.
  - (*Ccall*)
    move=> xs fn es ii.
    rewrite /check_cmd /allM /=. t_xrbindP => f Hgetfun Hes Hxs _.
    apply (hoare_call (Qerr:=noerrty) (Pf:=preF) (Qf:=postF)
                      (Rv:=List.Forall2 (fun t v => subctype t (type_of_val v)) (map eval_atype (f_tyin f)))) => //.

    - apply: rhoare_noerrty => [s _ | /= s vs _ Hsem].
      - rewrite /sem_pexprs. apply: mapM_noerrty => e HIn.
        rewrite /check_exprs /check_expr in Hes. have [ty Hty]:= (fold2_In Hes HIn).
        t_xrbindP => tye Htye /check_typeP /subatype_subctype Hsub /=.
        apply: (ty_expr_progress Hgd Htye) => //.
      - apply: (check_exprs_subctype Hes Hsem).
    - move=> s vs _ Hvs. split. exists f. by split. admit.
    - move=> vs Hvs. apply rhoare_noerrty => [s _ | ] //.
      rewrite /sem_pre/dc_truncate_val.
      case: ifP => Haa //.
      move: (allMP (In_rev (get_fun_In Hgetfun)) Hfns).
      rewrite /check_fun/oapp. t_xrbindP => /= Hchk_params Hchk_res Hchk_body Hoapp _.
      move: Hgetfun => /get_funP ->.
      move: Hoapp.
      case Hf_contract: f_contract => [f_contr |] //.
      rewrite /check_contract. t_xrbindP => /check_lvals_vars_subctype Hchk_iparams Hchk_ires Hpre Hpost.
      apply: rbind_noerrty => [|vs' /=]; first exact: (Forall2_mapM2_noerrty Hvs truncate_val_noerrty).
      move=> /mapM2_truncate_val_type Hvs'ty.
      apply: rbind_noerrty => [| s' _].
      - rewrite /write_vars.
        apply: (fold2_noerrty (R:=fun x v => subctype (eval_atype (ty_var x)) (type_of_val v))).
        apply: (Forall2_trans _ Hchk_iparams Hvs'ty) => ty x v Hsub -> //.
        move=> x v ?. apply: write_var_noerrty.
      - apply: rbind_noerrty => //.
        apply: mapM_noerrty => -[lbl ea] HIn.
        move: (allMP HIn Hpre) => /= Hchk.
        rewrite /sem_assert/assert.
        apply rbind_noerrty => [| ? _]; first by rewrite (negbFE Haa).
        apply rbind_noerrty => [| b _]; first apply: sem_eassert_progress Hchk.
        apply rbind_noerrty => //; by case: b.
Admitted.

End CMD.

Notation fun_safe fn := (khoare_io (preF fn) (isem_fun p ev fn) (postF fn)).

Lemma ty_prog_safe:
  check_prog p = ok tt ->
  forall fn, fun_safe fn.
Proof.
  rewrite /check_prog.
  t_xrbindP=>Hgd /check_funsP Hfns _ fn Hfn_in_p.
  apply (ihoare_fun (Qerr := noerrty)) => hrec.
  rewrite /hoare_fun_body_hyp_rec.
  move=> fn0 fs [[fd0 [/get_funP Hfn0p Hargs]] Hpre]; split; move=> //.
  rewrite Hfn0p.
  split=> // [fs' HpostF|].
  admit.
  exists PredT , PredT.
  split => //.
  admit.
  apply: (check_cmdP Hgd).
Admitted.


End IT.

End WITH_PARAMS.
