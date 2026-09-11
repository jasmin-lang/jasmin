(* * Building blocks for the semantics of [sopn]-like operators.

   An operator is described by four independent pieces of data:
   - a total semantics, whose boolean results are plain [bool];
   - a list of safety conditions [safe_cond] under which it does not fail;
   - the error it raises when one of them does not hold;
   - a list of conditions, one per output, telling when that output is defined.
   [mk_semi] assembles them into the usual
   [sem_prod tin (exec (sem_tuple tout))]. *)

(* ** Imports and settings *)
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq eqtype ssralg.
From mathcomp Require Import word_ssrZ.
From elpi.apps Require Import derive.std.
From HB Require Import structures.
Require Export sem_op_typed values.
Import Utf8.

(* -------------------------------------------------------------------- *)
(* Auxiliary facts about [of_val] and [truncate_val].                     *)

(* Truncating at [t] does not change how the value is read at any smaller
   type [t']: this is what makes the interpretation of a [safe_cond] on the
   original arguments agree with its interpretation on the truncated ones. *)
Lemma of_val_truncate_val t t' v v' :
  subctype t' t -> truncate_val t v = ok v' -> of_val t' v' = of_val t' v.
Proof.
case: t t' => [||len|ws] [||len'|ws'] //= hsub.
1,2: by move=> /truncate_val_typeE [x -> ->].
+ by move: hsub => /eqP [->] /truncate_val_typeE [a -> ->].
move=> /truncate_val_typeE [w [ws1 [w1 [/truncate_wordP [hle ->] -> ->]]]] /=.
by rewrite !truncate_word_le ?zero_extend_idem // (cmp_le_trans hsub hle).
Qed.

Lemma truncate_val_to_val t (x : sem_t t) : truncate_val t (to_val x) = ok (to_val x).
Proof. by rewrite /truncate_val of_val_to_val. Qed.

Lemma of_val_subctype_ok t t' (x : sem_t t) :
  subctype t' t -> exists y : sem_t t', of_val t' (to_val x) = ok y.
Proof.
move=> hsub; have [v2] := subctype_truncate_val hsub (truncate_val_to_val x).
by rewrite /truncate_val; case hof: (of_val t' (to_val x)) => [y|e] //= _; exists y.
Qed.

(* -------------------------------------------------------------------- *)
(* Semantics of the unary and binary operators on [value].                *)

Definition sem_sop1 (o: sop1) (v: value) : exec value :=
  Let x := of_val _ v in
  Let r := sem_sop1_typed o x in
  ok (to_val r).

Definition sem_sop2 (o: sop2) (v1 v2: value) : exec value :=
  Let x1 := of_val _ v1 in
  Let x2 := of_val _ v2 in
  Let r  := sem_sop2_typed o x1 x2 in
  ok (to_val r).

(* -------------------------------------------------------------------- *)
(* ** Conditions on the arguments of an operator                          *)

(* A boolean expression on the arguments of an operator. [IVar n] refers to
   the n-th argument. The same language describes the safety conditions of an
   operator and the conditions under which each of its outputs is defined. *)
#[only(eqbOK)] derive
Inductive safe_cond :=
  | IBool of bool
  | IConst of Z
  | IVar of nat
  | IOp1 of sop1 & safe_cond
  | IOp2 of sop2 & safe_cond & safe_cond
  | IAppN_safety of opN_safety & seq safe_cond.

HB.instance Definition _ := hasDecEq.Build safe_cond safe_cond_eqb_OK.

(* The generated scheme does not go under the list of [IAppN_safety]. *)
Section SAFE_COND_IND.
  Context
    (P : safe_cond -> Prop)
    (Hbool : forall b, P (IBool b))
    (Hconst : forall z, P (IConst z))
    (Hvar : forall k, P (IVar k))
    (Hop1 : forall o c, P c -> P (IOp1 o c))
    (Hop2 : forall o c1, P c1 -> forall c2, P c2 -> P (IOp2 o c1 c2))
    (HappN : forall o cs, List.Forall P cs -> P (IAppN_safety o cs)).

  Fixpoint safe_cond_ind_s (c : safe_cond) : P c :=
    match c with
    | IBool b => Hbool b
    | IConst z => Hconst z
    | IVar k => Hvar k
    | IOp1 o c => Hop1 o (safe_cond_ind_s c)
    | IOp2 o c1 c2 => Hop2 o (safe_cond_ind_s c1) (safe_cond_ind_s c2)
    | IAppN_safety o cs =>
      HappN o ((fix loop (l : seq safe_cond) : List.Forall P l :=
                  match l with
                  | [::] => List.Forall_nil P
                  | c :: l => List.Forall_cons c (safe_cond_ind_s c) (loop l)
                  end) cs)
    end.
End SAFE_COND_IND.

(* The interpretation goes through the *total* semantics of the operators, so
   that it does not depend on [sem_sop1_typed]/[sem_sop2_typed] failing. *)
Fixpoint interp_safe_cond (vs : values) (c : safe_cond) : exec value :=
  match c with
  | IBool b => ok (Vbool b)
  | IConst z => ok (Vint z)
  | IVar n => ok (nth undef_b vs n)
  | IOp1 o c =>
    Let v := interp_safe_cond vs c in
    Let x := of_val _ v in
    ok (to_val (sem_sop1_total o x))
  | IOp2 o c1 c2 =>
    Let v1 := interp_safe_cond vs c1 in
    Let v2 := interp_safe_cond vs c2 in
    Let x1 := of_val _ v1 in
    Let x2 := of_val _ v2 in
    ok (to_val (sem_sop2_total o x1 x2))
  | IAppN_safety o cs =>
    Let l := mapM (interp_safe_cond vs) cs in
    Let b := app_sopn _ (sem_opN_safety_typed o) l in
    ok (Vbool b)
  end.

(* A condition that is not a boolean (in particular an ill-typed one, whose
   interpretation is an error) counts as false. *)
Definition safe_cond_b (vs : values) (c : safe_cond) : bool :=
  if interp_safe_cond vs c is Ok (Vbool b) then b else false.

(* ** Typing *)

(* [sc_type tin c] is the type of [c] when the arguments have types [tin].
   An operator expecting an argument of type [t] accepts a sub-condition of
   type [t'] as soon as [subctype t t'], which is exactly what [of_val]
   accepts (for words: a word of at least that size). *)
Definition sub_octype (t : ctype) (ot : option ctype) : bool :=
  if ot is Some t' then subctype t t' else false.

Fixpoint sc_type (tin : seq ctype) (c : safe_cond) : option ctype :=
  match c with
  | IBool _ => Some cbool
  | IConst _ => Some cint
  | IVar n => if (n < size tin)%nat then Some (nth cbool tin n) else None
  | IOp1 o c =>
    let t := type_of_op1 o in
    if sc_type tin c is Some t1 then
      if subctype (eval_atype t.1) t1 then Some (eval_atype t.2) else None
    else None
  | IOp2 o c1 c2 =>
    let t := type_of_op2 o in
    if sc_type tin c1 is Some t1 then
      if sc_type tin c2 is Some t2 then
        if subctype (eval_atype t.1.1) t1 && subctype (eval_atype t.1.2) t2
        then Some (eval_atype t.2) else None
      else None
    else None
  | IAppN_safety o cs =>
    if all2 sub_octype (map eval_atype (type_of_opN_safety o).1) (map (sc_type tin) cs)
    then Some cbool else None
  end.

(* [sc_types tin ts cs]: the conditions [cs] have the types [ts], up to
   [subctype]. *)
Definition sc_types (tin ts : seq ctype) (cs : seq safe_cond) : bool :=
  all2 sub_octype ts (map (sc_type tin) cs).

Lemma sc_type_appN tin o cs :
  sc_type tin (IAppN_safety o cs) =
  if sc_types tin (map eval_atype (type_of_opN_safety o).1) cs then Some cbool else None.
Proof. by []. Qed.

(* A well-typed condition is one that evaluates to a boolean. *)
Definition sc_wt (tin : seq ctype) (c : safe_cond) : bool :=
  sc_type tin c == Some cbool.

(* The variables of a condition are among the first [n] arguments. *)
Fixpoint sc_below (n : nat) (c : safe_cond) : bool :=
  match c with
  | IBool _ | IConst _ => true
  | IVar k => (k < n)%nat
  | IOp1 _ c => sc_below n c
  | IOp2 _ c1 c2 => sc_below n c1 && sc_below n c2
  | IAppN_safety _ cs => all (sc_below n) cs
  end.

(* The number of arguments a condition reads: one more than the largest [IVar]
   it mentions, [0] if it mentions none. *)
Fixpoint sc_max_var (c : safe_cond) : nat :=
  match c with
  | IBool _ | IConst _ => 0
  | IVar k => S k
  | IOp1 _ c => sc_max_var c
  | IOp2 _ c1 c2 => ssrnat.maxn (sc_max_var c1) (sc_max_var c2)
  | IAppN_safety _ cs => foldr (fun c n => ssrnat.maxn (sc_max_var c) n) 0 cs
  end.

Lemma sc_max_var_appN_le o cs n :
  ssrnat.leq (sc_max_var (IAppN_safety o cs)) n
  = all (fun c => ssrnat.leq (sc_max_var c) n) cs.
Proof. by elim: cs => //= c cs ih; rewrite ssrnat.geq_max ih. Qed.

Lemma sc_max_var_below n c : ssrnat.leq (sc_max_var c) n = sc_below n c.
Proof.
elim/safe_cond_ind_s: c => //=.
+ by move=> o c1 ih1 c2 ih2; rewrite ssrnat.geq_max ih1 ih2.
move=> o cs; elim => //= c l ih1 _ ih2.
by rewrite ssrnat.geq_max ih1 ih2.
Qed.

(* ** Total conditions *)

(* The unary operators whose typed semantics cannot fail. *)
Definition op1_total (o : sop1) : bool :=
  if o is Owi1 _ _ then false else true.

(* The binary operators whose typed semantics cannot fail: word division and
   modulo fail on a null divisor, the [wint] operators on overflow. *)
Definition op2_total (o : sop2) : bool :=
  match o with
  | Odiv _ (Op_w _) | Omod _ (Op_w _) | Owi2 _ _ _ => false
  | _ => true
  end.

Lemma sem_sop1_typed_total o :
  op1_total o -> forall x, exists y, sem_sop1_typed o x = ok y.
Proof. by case: o => [?|??|??|??||?|[|?]|??] //= *; eexists; reflexivity. Qed.

Lemma sem_sop2_typed_total o :
  op2_total o -> forall x1 x2, exists y, sem_sop2_typed o x1 x2 = ok y.
Proof.
by case: o => [|||[|?]|[|?]|[|?]|?[|?]|?[|?]|?|?|?|?|[|?]|[|?]|?|?|[|?]|[|?]
              |[|??]|[|??]|[|??]|[|??]|??|??|??|??|??|??|???] //= *;
   eexists; reflexivity.
Qed.

(* On the white list, the typed semantics is the total one wrapped in [ok]. *)
Lemma sem_sop1_typed_totalE o :
  op1_total o -> forall x, sem_sop1_typed o x = ok (sem_sop1_total o x).
Proof. by case: o => [?|??|??|??||?|[|?]|??] //= *. Qed.

Lemma sem_sop2_typed_totalE o :
  op2_total o -> forall x1 x2, sem_sop2_typed o x1 x2 = ok (sem_sop2_total o x1 x2).
Proof.
by case: o => [|||[|?]|[|?]|[|?]|?[|?]|?[|?]|?|?|?|?|[|?]|[|?]|?|?|[|?]|[|?]
              |[|??]|[|??]|[|??]|[|??]|??|??|??|??|??|??|???] //= *.
Qed.

(* The safety operators are total. *)
Lemma sem_opN_safety_typed_ok o :
  sem_forall (fun r : exec bool => is_ok r)
    (map eval_atype (type_of_opN_safety o).1) (sem_opN_safety_typed o).
Proof. by case: o => len a lo l. Qed.

(* Conditions built from operators whose typed semantics cannot fail: their
   interpretation on arguments of the announced types is always a value. *)
Fixpoint sc_total (c : safe_cond) : bool :=
  match c with
  | IBool _ | IConst _ | IVar _ => true
  | IOp1 o c => op1_total o && sc_total c
  | IOp2 o c1 c2 => [&& op2_total o, sc_total c1 & sc_total c2]
  | IAppN_safety _ cs => all sc_total cs
  end.

(* The conditions that are translated into a [pexpr] by [sc_to_e]
   (safety_common.v): those built from the operators of the white list, with no
   [IAppN_safety], which the expression language does not have. *)
Fixpoint sc_expr (c : safe_cond) : bool :=
  match c with
  | IBool _ | IConst _ | IVar _ => true
  | IOp1 o c => op1_total o && sc_expr c
  | IOp2 o c1 c2 => [&& op2_total o, sc_expr c1 & sc_expr c2]
  | IAppN_safety _ _ => false
  end.

Lemma sc_expr_total c : sc_expr c -> sc_total c.
Proof.
elim/safe_cond_ind_s: c => //=.
+ by move=> o c ih /andP [-> /ih ->].
by move=> o c1 ih1 c2 ih2 /and3P [-> /ih1 -> /ih2 ->].
Qed.

(* Well-formedness of a condition: well typed and total. *)
Definition sc_ok (tin : seq ctype) (c : safe_cond) : bool :=
  sc_wt tin c && sc_total c.

Lemma sc_ok_wt tin c : sc_ok tin c -> sc_wt tin c.
Proof. by move=> /andP []. Qed.

Lemma sc_ok_total tin c : sc_ok tin c -> sc_total c.
Proof. by move=> /andP []. Qed.

Lemma all_sc_ok_wt tin l : all (sc_ok tin) l -> all (sc_wt tin) l.
Proof. by apply: sub_all; apply: sc_ok_wt. Qed.

Lemma all_sc_ok_total tin l : all (sc_ok tin) l -> all sc_total l.
Proof. by apply: sub_all; apply: sc_ok_total. Qed.

(* ** Basic properties of the interpretation *)

Lemma sc_type_below tin c t : sc_type tin c = Some t -> sc_below (size tin) c.
Proof.
elim/safe_cond_ind_s: c t => //=.
+ by move=> k t; case: ifP.
+ move=> o c ih t; case heq: (sc_type tin c) => [t1|] //=; case: ifP => // _ _.
  by apply: ih heq.
+ move=> o c1 ih1 c2 ih2 t.
  case heq1: (sc_type tin c1) => [t1|] //=; case heq2: (sc_type tin c2) => [t2|] //=.
  case: ifP => // _ _.
  by rewrite (ih1 _ heq1) (ih2 _ heq2).
move=> o cs hall t; case: ifP => // + _.
elim: cs hall (map eval_atype (type_of_opN_safety o).1) => [ | c cs ih] hall [ | t0 ts] //=.
move=> /andP [h1 h2]; move/List_Forall_inv: hall => [hc hcs].
rewrite (ih hcs ts h2) andbT.
by move: h1; rewrite /sub_octype; case heq: (sc_type tin c) => [t1|] // _; apply: (hc _ heq).
Qed.

Lemma sc_type_cat tin tin' c t :
  sc_type tin c = Some t -> sc_type (tin ++ tin') c = Some t.
Proof.
elim/safe_cond_ind_s: c t => //=.
+ move=> k t; case: ifP => // hk [<-].
  by rewrite nth_cat hk size_cat (ltn_addr _ hk).
+ move=> o c ih t; case heq: (sc_type tin c) => [t1|] //=; case: ifP => // hsub [<-].
  by rewrite (ih _ heq) /= hsub.
+ move=> o c1 ih1 c2 ih2 t.
  case heq1: (sc_type tin c1) => [t1|] //=; case heq2: (sc_type tin c2) => [t2|] //=.
  case: ifP => // hsub [<-].
  by rewrite (ih1 _ heq1) (ih2 _ heq2) /= hsub.
move=> o cs hall t; case: ifP => // + [<-].
have haux : forall ts, all2 sub_octype ts (map (sc_type tin) cs) ->
                       all2 sub_octype ts (map (sc_type (tin ++ tin')) cs).
+ elim: cs hall => [ | c cs ih] hall [ | t0 ts] //=.
  move/List_Forall_inv: hall => [hc hcs] /andP [h1 h2]; rewrite (ih hcs ts h2) andbT.
  by move: h1; rewrite /sub_octype; case heq: (sc_type tin c) => [t1|] // hsub; rewrite (hc _ heq).
by move=> /haux ->.
Qed.

Lemma sc_wt_cat tin tin' c : sc_wt tin c -> sc_wt (tin ++ tin') c.
Proof. by rewrite /sc_wt => /eqP /sc_type_cat ->. Qed.

Lemma sc_ok_cat tin tin' c : sc_ok tin c -> sc_ok (tin ++ tin') c.
Proof. by move=> /andP [h1 h2]; rewrite /sc_ok (sc_wt_cat tin' h1). Qed.

Lemma all_sc_ok_cat tin tin' l : all (sc_ok tin) l -> all (sc_ok (tin ++ tin')) l.
Proof. by apply: sub_all => c; apply: sc_ok_cat. Qed.

(* The interpretation only depends on the arguments the condition reads. *)
Lemma interp_safe_cond_cat (vs vs' : values) c :
  sc_below (size vs) c -> interp_safe_cond (vs ++ vs') c = interp_safe_cond vs c.
Proof.
elim/safe_cond_ind_s: c => //=.
+ by move=> k hk; rewrite nth_cat hk.
+ by move=> o c ih h; rewrite ih.
+ by move=> o c1 ih1 c2 ih2 /andP [h1 h2]; rewrite ih1 // ih2.
move=> o cs hall hb.
suff -> : mapM (interp_safe_cond (vs ++ vs')) cs = mapM (interp_safe_cond vs) cs by [].
elim: cs hall hb => //= c cs ih /List_Forall_inv [hc hcs] /andP [h1 h2].
by rewrite hc // (ih hcs h2).
Qed.

Lemma safe_cond_b_cat (vs vs' : values) c :
  ssrnat.leq (sc_max_var c) (size vs) -> safe_cond_b (vs ++ vs') c = safe_cond_b vs c.
Proof. by rewrite sc_max_var_below => h; rewrite /safe_cond_b interp_safe_cond_cat. Qed.

(* A well-typed total condition evaluates to a value on arguments of the
   announced types. *)
Lemma sc_type_ok tin (vs : values) c t :
  List.Forall2 (fun (t : ctype) v => exists x : sem_t t, v = to_val x) tin vs ->
  sc_total c ->
  sc_type tin c = Some t ->
  exists x : sem_t t, interp_safe_cond vs c = ok (to_val x).
Proof.
move=> hall; elim/safe_cond_ind_s: c t => /=.
1,2: by move=> x t _ [<-]; eexists.
+ move=> k t _; case: ifP => // hk [<-].
  by have [x hx] := Forall2_nth hall cbool undef_b hk; exists x; rewrite hx.
+ move=> o c ih t /andP [hto htot].
  case heq: (sc_type tin c) => [t1|] //=; case: ifP => // hsub [<-].
  have [x1 ->] := ih _ htot heq.
  have [y hy] := of_val_subctype_ok x1 hsub.
  by rewrite /= hy /=; eexists.
+ move=> o c1 ih1 c2 ih2 t /and3P [hto ht1 ht2].
  case heq1: (sc_type tin c1) => [t1|] //=; case heq2: (sc_type tin c2) => [t2|] //=.
  case: ifP => // /andP [hsub1 hsub2] [<-].
  have [x1 ->] := ih1 _ ht1 heq1; have [x2 ->] := ih2 _ ht2 heq2.
  have [y1 hy1] := of_val_subctype_ok x1 hsub1.
  have [y2 hy2] := of_val_subctype_ok x2 hsub2.
  by rewrite /= hy1 /= hy2 /=; eexists.
move=> o cs hall2 t htot; case: ifP => // hall3 [<-].
have {}htot : all sc_total cs by move: htot.
have haux : forall (ts : seq ctype) A (f : sem_prod ts (exec A)),
    sem_forall (fun r : exec A => is_ok r) ts f ->
    all2 sub_octype ts (map (sc_type tin) cs) ->
    exists2 l, mapM (interp_safe_cond vs) cs = ok l & exists a, app_sopn ts f l = ok a.
+ move: hall3 => _; elim: cs hall2 htot => /= [ | c cs ih] hall2 htot [ | t0 ts] //= A f hf.
  + by move=> _; exists [::] => //; move/is_okP: hf.
  move/List_Forall_inv: hall2 => [hc hcs]; move: htot => /andP [htc htcs].
  move=> /andP [h1 h2].
  move: h1; rewrite /sub_octype; case heq: (sc_type tin c) => [t1|] // hsub.
  have [x ->] := hc _ htc heq.
  have [y hy] := of_val_subctype_ok x hsub.
  have [l -> [a ha]] := ih hcs htcs ts _ (f y) (hf y) h2.
  by exists (to_val x :: l) => //=; exists a; rewrite hy /=.
have [l -> [a ha]] := haux _ _ _ (sem_opN_safety_typed_ok o) hall3.
by rewrite /= ha /=; exists a.
Qed.

(* Interpreting a well-typed condition on the arguments or on their truncation
   at [tin] gives the same result (up to truncation of the result). *)
Lemma interp_safe_cond_truncate tin vs vs' :
  mapM2 ErrType truncate_val tin vs = ok vs' ->
  forall c t, sc_type tin c = Some t ->
  match interp_safe_cond vs c with
  | Ok v => exists2 v'', interp_safe_cond vs' c = ok v'' & truncate_val t v = ok v''
  | Error e => interp_safe_cond vs' c = Error e
  end.
Proof.
move=> /mapM2_Forall3 htr c.
elim/safe_cond_ind_s: c => /=.
1,2: by move=> x t [<-]; eexists.
+ move=> n t; case: ifP => // hn [<-]; eexists; first reflexivity.
  by apply: (Forall3_nth htr).
+ move=> o c ih t; case heq: (sc_type tin c) => [t1|] //; case: ifP => // hsub [<-].
  have {ih} := ih _ heq; case: (interp_safe_cond vs c) => [v | e] /=; last by move=> ->.
  move=> [v'' -> htr'] /=; rewrite (of_val_truncate_val hsub htr').
  by case: (of_val _ v) => //= x; eexists; first reflexivity; apply truncate_val_to_val.
+ move=> o c1 ih1 c2 ih2 t.
  case heq1: (sc_type tin c1) => [t1|] //; case heq2: (sc_type tin c2) => [t2|] //.
  case: ifP => // /andP [hsub1 hsub2] [<-].
  have {ih1} := ih1 _ heq1; case: (interp_safe_cond vs c1) => [v1 | e] /=; last by move=> ->.
  move=> [v1'' -> htr1] /=.
  have {ih2} := ih2 _ heq2; case: (interp_safe_cond vs c2) => [v2 | e] /=; last by move=> ->.
  move=> [v2'' -> htr2] /=.
  rewrite (of_val_truncate_val hsub1 htr1) (of_val_truncate_val hsub2 htr2).
  case: (of_val _ v1) => //= x1; case: (of_val _ v2) => //= x2.
  by eexists; first reflexivity; apply truncate_val_to_val.
move=> o cs hall t; case: ifP => // hall2 [<-].
have haux : forall (ts : seq ctype),
    all2 sub_octype ts (map (sc_type tin) cs) ->
    match mapM (interp_safe_cond vs) cs with
    | Ok l => exists2 l', mapM (interp_safe_cond vs') cs = ok l' &
              forall A (f : sem_prod ts (exec A)), app_sopn ts f l' = app_sopn ts f l
    | Error e => mapM (interp_safe_cond vs') cs = Error e
    end.
+ move: hall2 => _; elim: cs hall => /= [ | c cs ih] hall [ | t0 ts] //=.
  + by move=> _; exists [::].
  move/List_Forall_inv: hall => [hc hcs] /andP [h1 h2].
  move: h1; rewrite /sub_octype; case heq: (sc_type tin c) => [t1|] // hsub.
  have {hc} := hc _ heq; case: (interp_safe_cond vs c) => [v | e] /=; last by move=> ->.
  move=> [v'' -> htr'] /=.
  have {ih} := ih hcs ts h2.
  case: (mapM (interp_safe_cond vs) cs) => [l | e] /=; last by move=> ->.
  move=> [l' -> hap]; exists (v'' :: l') => // A f /=.
  by rewrite (of_val_truncate_val hsub htr'); case: (of_val t0 v) => //= x; apply hap.
have {haux} := haux _ hall2.
case: (mapM (interp_safe_cond vs) cs) => [l | e] /=; last by move=> ->.
move=> [l' -> hap] /=; rewrite (hap _ (sem_opN_safety_typed o)).
by case: (app_sopn _ _ l) => //= b; eexists.
Qed.

Lemma safe_cond_truncate tin vs vs' c :
  mapM2 ErrType truncate_val tin vs = ok vs' ->
  sc_wt tin c ->
  interp_safe_cond vs' c = interp_safe_cond vs c.
Proof.
move=> htr /eqP hwt; have := interp_safe_cond_truncate htr hwt.
case: (interp_safe_cond vs c) => [v | e] //=.
by move=> [v'' -> /truncate_val_typeE [b -> ->]].
Qed.

Lemma safe_cond_b_truncate tin vs vs' c :
  sc_ok tin c -> mapM2 ErrType truncate_val tin vs = ok vs' ->
  safe_cond_b vs' c = safe_cond_b vs c.
Proof. by move=> /sc_ok_wt h2 h1; rewrite /safe_cond_b (safe_cond_truncate h1 h2). Qed.

(* -------------------------------------------------------------------- *)
(* ** Building conditions                                                *)

(* Some of the functions below are matched by shape in
   safetylib/safetyInterpreter.ml; each of them carries a comment saying so. *)

Definition sc_toint sg ws k    := IOp1 (Oint_of_word sg ws) (IVar k).
Definition sc_not c            := IOp1 Onot c.
Definition sc_and c1 c2        := IOp2 Oand c1 c2.
Definition sc_or c1 c2         := IOp2 Oor c1 c2.
Definition sc_eqi c1 c2        := IOp2 (Oeq Op_int) c1 c2.
Definition sc_neqi c1 c2       := IOp2 (Oneq Op_int) c1 c2.
Definition sc_lei c1 c2        := IOp2 (Ole Cmp_int) c1 c2.
Definition sc_lti c1 c2        := IOp2 (Olt Cmp_int) c1 c2.
Definition sc_addi c1 c2       := IOp2 (Oadd Op_int) c1 c2.
Definition sc_muli c1 c2       := IOp2 (Omul Op_int) c1 c2.
Definition sc_divi sg c1 c2    := IOp2 (Odiv sg Op_int) c1 c2.
Definition sc_modi sg c1 c2    := IOp2 (Omod sg Op_int) c1 c2.

(* This shape is recognised by safetylib/safetyInterpreter.ml;
   if it changes, its recognition there must change too. *)
Definition sc_in_range lo hi c := sc_and (sc_lei (IConst lo) c) (sc_lei c (IConst hi)).

(* This shape is recognised by safetylib/safetyInterpreter.ml;
   if it changes, its recognition there must change too. *)
Definition sc_false : safe_cond := IBool false.

(* This shape is recognised by safetylib/safetyInterpreter.ml;
   if it changes, its recognition there must change too. *)
Definition sc_not_zero ws k    := sc_neqi (sc_toint Unsigned ws k) (IConst 0).

(* This shape is recognised by safetylib/safetyInterpreter.ml;
   if it changes, its recognition there must change too. *)
Definition sc_is_zero ws k     := sc_eqi (sc_toint Unsigned ws k) (IConst 0).

(* This shape is recognised by safetylib/safetyInterpreter.ml;
   if it changes, its recognition there must change too. *)
Definition sc_ult ws k z       := sc_lti (sc_toint Unsigned ws k) (IConst z).

(* This shape is recognised by safetylib/safetyInterpreter.ml;
   if it changes, its recognition there must change too. *)
Definition sc_uge ws z k       := sc_lei (IConst z) (sc_toint Unsigned ws k).

(* This shape is recognised by safetylib/safetyInterpreter.ml;
   if it changes, its recognition there must change too. *)
Definition sc_uadd_le ws k1 k2 z :=
  sc_lei (sc_addi (sc_toint Unsigned ws k1) (sc_toint Unsigned ws k2)) (IConst z).

(* Recognised by safetylib/safetyInterpreter.ml through [sc_in_range]. *)
Definition sc_in_range_mod32 ws i j k :=
  sc_in_range i j (sc_modi Unsigned (sc_toint Unsigned ws k) (IConst 32)).

(* [sc_is_arr_init len ka start size]: the [size] cells of the array argument
   [ka] (of length [len]) starting at [start] are initialised. *)
Definition sc_is_arr_init (len : Z) (ka : nat) (start : safe_cond) (size : Z) : safe_cond :=
  IAppN_safety (Ois_arr_init len) [:: IVar ka; start; IConst size].

(* This shape is recognised by safetylib/safetyInterpreter.ml;
   if it changes, its recognition there must change too. *)
Definition sc_all_init ws len k :=
  sc_is_arr_init (arr_size ws len) k (IConst 0) (arr_size ws len).

(* This shape is recognised by safetylib/safetyInterpreter.ml;
   if it changes, its recognition there must change too. *)
Definition sc_guarded (g : nat) (c : safe_cond) : safe_cond :=
  sc_or (sc_not (IVar g)) c.

(* This shape is recognised by safetylib/safetyInterpreter.ml;
   if it changes, its recognition there must change too. *)
Definition sc_x86_division (sz : wsize) (sg : signedness) : safe_cond :=
  match sg with
  | Signed =>
    let hi := sc_toint Signed sz 0 in
    let lo := sc_toint Unsigned sz 1 in
    let dd := sc_addi (sc_muli (IConst (wbase sz)) hi) lo in
    let dv := sc_toint Signed sz 2 in
    let q  := sc_divi Signed dd dv in
    let ov := sc_or (sc_lti q (IConst (wmin_signed sz)))
                    (sc_lti (IConst (wmax_signed sz)) q) in
    sc_and (sc_neqi dv (IConst 0)) (sc_not ov)
  | Unsigned =>
    let hi := sc_toint Unsigned sz 0 in
    let lo := sc_toint Unsigned sz 1 in
    let dd := sc_addi (sc_muli (IConst (wbase sz)) hi) lo in
    let dv := sc_toint Unsigned sz 2 in
    let q  := sc_divi Unsigned dd dv in
    let ov := sc_lti (IConst (wmax_unsigned sz)) q in
    sc_and (sc_neqi dv (IConst 0)) (sc_not ov)
  end.

(* The result of a [wint] operation fits in its type. *)
Definition sc_wi_range sg sz (c : safe_cond) : safe_cond :=
  signed (sc_in_range 0 (wmax_unsigned sz) c)
         (sc_in_range (wmin_signed sz) (wmax_signed sz) c) sg.

(* The divisor is not zero and, in the signed case, the division does not
   overflow. *)
Definition sc_divmod sg sz (k1 k2 : nat) : seq safe_cond :=
  sc_not_zero sz k2 ::
  signed [::]
    [:: sc_not (sc_and (sc_eqi (sc_toint sg sz k1) (IConst (wmin_signed sz)))
                       (sc_eqi (sc_toint sg sz k2) (IConst (-1)))) ] sg.

(* ** Bridging lemmas: what the conditions above compute *)

Lemma Z_eqbE (x y : Z) : (x =? y)%Z = (x == y).
Proof. by apply/idP/idP => [/ZeqbP /eqP | /eqP /ZeqbP]. Qed.

Lemma wunsigned_eqb0 ws (w : word ws) : (wunsigned w =? 0)%Z = (w == 0%w).
Proof.
apply/idP/idP => [/ZeqbP h1 | /eqP ->]; last by rewrite wunsigned0; apply/ZeqbP.
by apply/eqP/wunsigned_inj; rewrite h1 wunsigned0.
Qed.

Lemma safe_cond_b_false vs : safe_cond_b vs sc_false = false.
Proof. by []. Qed.

Lemma safe_cond_b_not_zero ws k (vs : values) (w : word ws) :
  nth undef_b vs k = Vword w -> safe_cond_b vs (sc_not_zero ws k) = (w != 0%w).
Proof.
by move=> h;
  rewrite /safe_cond_b /sc_not_zero /sc_neqi /sc_toint /= h /= truncate_word_u /=
          wunsigned_eqb0.
Qed.

Lemma safe_cond_b_is_zero ws k (vs : values) (w : word ws) :
  nth undef_b vs k = Vword w -> safe_cond_b vs (sc_is_zero ws k) = (w == 0%w).
Proof.
by move=> h;
  rewrite /safe_cond_b /sc_is_zero /sc_eqi /sc_toint /= h /= truncate_word_u /=
          wunsigned_eqb0.
Qed.

Lemma safe_cond_b_ult ws k z (vs : values) (w : word ws) :
  nth undef_b vs k = Vword w ->
  safe_cond_b vs (sc_ult ws k z) = (wunsigned w <? z)%Z.
Proof.
by move=> h; rewrite /safe_cond_b /sc_ult /sc_lti /sc_toint /= h /= truncate_word_u.
Qed.

Lemma safe_cond_b_uge ws z k (vs : values) (w : word ws) :
  nth undef_b vs k = Vword w ->
  safe_cond_b vs (sc_uge ws z k) = (z <=? wunsigned w)%Z.
Proof.
by move=> h; rewrite /safe_cond_b /sc_uge /sc_lei /sc_toint /= h /= truncate_word_u.
Qed.

Lemma safe_cond_b_uadd_le ws k1 k2 z (vs : values) (w1 w2 : word ws) :
  nth undef_b vs k1 = Vword w1 -> nth undef_b vs k2 = Vword w2 ->
  safe_cond_b vs (sc_uadd_le ws k1 k2 z)
  = (wunsigned w1 + wunsigned w2 <=? z)%Z.
Proof.
move=> h1 h2; rewrite /safe_cond_b /sc_uadd_le /sc_lei /sc_addi /sc_toint /=.
by rewrite h1 h2 /= !truncate_word_u.
Qed.

Lemma safe_cond_b_in_range_mod32 ws i j k (vs : values) (w : word ws) :
  nth undef_b vs k = Vword w ->
  safe_cond_b vs (sc_in_range_mod32 ws i j k)
  = (i <=? (wunsigned w) mod 32)%Z && ((wunsigned w) mod 32 <=? j)%Z.
Proof.
move=> h.
by rewrite /safe_cond_b /sc_in_range_mod32 /sc_in_range /sc_and /sc_lei /sc_modi
           /sc_toint /= h /= truncate_word_u.
Qed.

Lemma safe_cond_b_all_init ws len k (vs : values) (t : WArray.array (arr_size ws len)) :
  nth undef_b vs k = Varr t ->
  safe_cond_b vs (sc_all_init ws len k)
  = all (WArray.is_init t) (ziota 0 (arr_size ws len)).
Proof.
by move=> h;
  rewrite /safe_cond_b /sc_all_init /= h /= arr_sizeE wsize8 Z.mul_1_l WArray.castK.
Qed.

Local Opaque wbase.
Lemma safe_cond_b_x86_division sz sg (vs : values) (hi lo dv : word sz) :
  nth undef_b vs 0 = Vword hi ->
  nth undef_b vs 1 = Vword lo ->
  nth undef_b vs 2 = Vword dv ->
  safe_cond_b vs (sc_x86_division sz sg) =
  ~~ match sg with
     | Signed =>
       let dd := wdwords hi lo in
       let d  := wsigned dv in
       let q  := Z.quot dd d in
       ((d == 0)%Z || ((q <? wmin_signed sz)%Z || (q >? wmax_signed sz)%Z))
     | Unsigned =>
       let dd := wdwordu hi lo in
       let d  := wunsigned dv in
       let q  := (dd / d)%Z in
       ((d == 0)%Z || (q >? wmax_unsigned sz)%Z)
     end.
Proof.
move=> h0 h1 h2; rewrite /safe_cond_b /sc_x86_division /wdwordu /wdwords.
case: sg => /=;
  rewrite /sc_and /sc_not /sc_or /sc_neqi /sc_lti /sc_addi /sc_muli /sc_divi /sc_toint /=
          h0 h1 h2 /= !truncate_word_u /=.
+ by rewrite !negb_or !Z.gtb_ltb.
by rewrite !negb_or !Z.gtb_ltb.
Qed.
Local Transparent wbase.

(* ** Well-formedness of the conditions above *)

Lemma sc_type_op1E tin o c :
  sc_type tin (IOp1 o c) =
  if sc_type tin c is Some t1 then
    if subctype (eval_atype (type_of_op1 o).1) t1 then Some (eval_atype (type_of_op1 o).2)
    else None
  else None.
Proof. by []. Qed.

Lemma sc_type_op2E tin o c1 c2 :
  sc_type tin (IOp2 o c1 c2) =
  if sc_type tin c1 is Some t1 then
    if sc_type tin c2 is Some t2 then
      if subctype (eval_atype (type_of_op2 o).1.1) t1
         && subctype (eval_atype (type_of_op2 o).1.2) t2
      then Some (eval_atype (type_of_op2 o).2) else None
    else None
  else None.
Proof. by []. Qed.

Lemma sc_type_toint tin sg ws k :
  ssrnat.leq (S k) (size tin) -> nth cbool tin k = cword ws ->
  sc_type tin (sc_toint sg ws k) = Some cint.
Proof. by move=> h1 h2; rewrite /sc_toint sc_type_op1E /= h1 h2 /= cmp_le_refl. Qed.

Lemma sc_ok_not_zero tin ws k :
  ssrnat.leq (S k) (size tin) -> nth cbool tin k = cword ws ->
  sc_ok tin (sc_not_zero ws k).
Proof.
by move=> h1 h2; rewrite /sc_ok /sc_wt /sc_not_zero /sc_neqi sc_type_op2E
  (sc_type_toint Unsigned h1 h2) /=.
Qed.

Lemma sc_ok_is_zero tin ws k :
  ssrnat.leq (S k) (size tin) -> nth cbool tin k = cword ws ->
  sc_ok tin (sc_is_zero ws k).
Proof.
by move=> h1 h2; rewrite /sc_ok /sc_wt /sc_is_zero /sc_eqi sc_type_op2E
  (sc_type_toint Unsigned h1 h2) /=.
Qed.

Lemma sc_ok_ult tin ws k z :
  ssrnat.leq (S k) (size tin) -> nth cbool tin k = cword ws ->
  sc_ok tin (sc_ult ws k z).
Proof.
by move=> h1 h2; rewrite /sc_ok /sc_wt /sc_ult /sc_lti sc_type_op2E
  (sc_type_toint Unsigned h1 h2) /=.
Qed.

Lemma sc_ok_uge tin ws z k :
  ssrnat.leq (S k) (size tin) -> nth cbool tin k = cword ws ->
  sc_ok tin (sc_uge ws z k).
Proof.
by move=> h1 h2; rewrite /sc_ok /sc_wt /sc_uge /sc_lei sc_type_op2E
  (sc_type_toint Unsigned h1 h2) /=.
Qed.

Lemma sc_ok_uadd_le tin ws k1 k2 z :
  ssrnat.leq (S k1) (size tin) -> nth cbool tin k1 = cword ws ->
  ssrnat.leq (S k2) (size tin) -> nth cbool tin k2 = cword ws ->
  sc_ok tin (sc_uadd_le ws k1 k2 z).
Proof.
move=> h1 h2 h3 h4.
by rewrite /sc_ok /sc_wt /sc_uadd_le /sc_lei /sc_addi !sc_type_op2E
  (sc_type_toint Unsigned h1 h2) (sc_type_toint Unsigned h3 h4) /=.
Qed.

Lemma sc_ok_in_range_mod32 tin ws i j k :
  ssrnat.leq (S k) (size tin) -> nth cbool tin k = cword ws ->
  sc_ok tin (sc_in_range_mod32 ws i j k).
Proof.
move=> h1 h2.
by rewrite /sc_ok /sc_wt /sc_in_range_mod32 /sc_in_range /sc_and /sc_lei /sc_modi
  !sc_type_op2E (sc_type_toint Unsigned h1 h2) /=.
Qed.

Lemma sc_ok_x86_division tin sz sg :
  ssrnat.leq 3 (size tin) ->
  nth cbool tin 0 = cword sz -> nth cbool tin 1 = cword sz -> nth cbool tin 2 = cword sz ->
  sc_ok tin (sc_x86_division sz sg).
Proof.
move=> hs h0 h1 h2.
have l0 : ssrnat.leq 1 (size tin) by apply: leq_trans hs.
have l1 : ssrnat.leq 2 (size tin) by apply: leq_trans hs.
by rewrite /sc_ok /sc_wt /sc_x86_division; case: sg => /=;
  rewrite l0 l1 hs h0 h1 h2 /= !cmp_le_refl.
Qed.

Lemma sc_ok_all_init tin ws len k :
  ssrnat.leq (S k) (size tin) -> nth cbool tin k = carr (arr_size ws len) ->
  sc_ok tin (sc_all_init ws len k).
Proof.
move=> h1 h2; rewrite /sc_ok /sc_wt /sc_all_init /= h1 h2.
have -> : arr_size U8 (arr_size ws len) = arr_size ws len.
+ by rewrite arr_sizeE wsize8 Z.mul_1_l.
by rewrite /sub_octype /= !eqxx.
Qed.

(* -------------------------------------------------------------------- *)
(* ** Guarding a condition                                               *)

(* A condition guarded by the [g]-th argument: it is required only when the
   guard is true. For an output, it says that the output is defined when the
   guard is false — it is then the old value, which is defined — or when its
   own condition holds. *)
Definition cond_init (g : nat) (c : safe_cond) : safe_cond := sc_guarded g c.

Lemma sc_wt_guarded tin tin' c :
  sc_wt tin c -> sc_wt (tin ++ cbool :: tin') (sc_guarded (size tin) c).
Proof.
rewrite /sc_wt /sc_guarded /sc_or /sc_not /= => /eqP /sc_type_cat -> /=.
rewrite size_cat /= nth_cat ltnn subnn /=.
by have -> : (size tin < size tin + (size tin').+1)%nat by rewrite -addn1 leq_add2l.
Qed.

Lemma sc_total_guarded g c : sc_total c -> sc_total (sc_guarded g c).
Proof. by move=> h; rewrite /sc_guarded /= h. Qed.

Lemma safe_cond_b_guarded (vs0 vs2 : values) (b : bool) (c : safe_cond) (bb : bool) :
  sc_below (size vs0) c ->
  interp_safe_cond vs0 c = ok (Vbool bb) ->
  safe_cond_b (vs0 ++ Vbool b :: vs2) (sc_guarded (size vs0) c) = (~~ b) || bb.
Proof.
move=> hb hev; rewrite /safe_cond_b /sc_guarded /sc_or /sc_not /=.
rewrite nth_cat ltnn subnn /=.
by rewrite (interp_safe_cond_cat (Vbool b :: vs2) hb) hev /=.
Qed.

Lemma sc_guarded_val (ts : seq ctype) (vs0 vs2 : values) (b : bool) (c : safe_cond) :
  List.Forall2 (fun t v => exists x : sem_t t, v = to_val x) ts vs0 ->
  sc_total c -> sc_wt ts c ->
  safe_cond_b (vs0 ++ Vbool b :: vs2) (sc_guarded (size ts) c)
  = (~~ b) || safe_cond_b vs0 c.
Proof.
move=> hall htot hwt.
have hsz : size ts = size vs0 by apply: Forall2_size hall.
have [x hx] := sc_type_ok hall htot (eqP hwt).
have hbelow : sc_below (size vs0) c.
+ by rewrite -hsz; apply: (sc_type_below (eqP hwt)).
have -> : safe_cond_b vs0 c = x by rewrite /safe_cond_b hx.
by rewrite hsz; apply: (@safe_cond_b_guarded vs0 vs2 b c x hbelow hx).
Qed.

Lemma map_const_seq {A B : Type} (s : seq A) (c : B) :
  map (fun _ => c) s = nseq (size s) c.
Proof. by elim: s => //= x s ->. Qed.

(* The mask seen by the generic construction under a guard: everything is
   defined when the guard is false, and the original mask otherwise. *)
Lemma cond_init_mask (ts : seq ctype) (vs0 : values) (init : seq safe_cond) (b : bool)
    (vs2 : values) (n : nat) :
  List.Forall2 (fun t v => exists x : sem_t t, v = to_val x) ts vs0 ->
  all sc_total init -> all (sc_wt ts) init ->
  size init = n ->
  map (safe_cond_b (rcons vs0 (Vbool b) ++ vs2)) (map (cond_init (size ts)) init)
  = (if b then map (safe_cond_b vs0) init else nseq n true).
Proof.
move=> hall htot hwt hsz.
rewrite cat_rcons -map_comp.
have hpt : forall c, c \in init ->
    (safe_cond_b (vs0 ++ Vbool b :: vs2) \o cond_init (size ts)) c
    = (~~ b) || safe_cond_b vs0 c.
+ by move=> c hc; apply: (sc_guarded_val _ _ hall (allP htot _ hc) (allP hwt _ hc)).
case: b hpt => hpt.
+ by apply/eq_in_map => c hc; rewrite hpt.
by rewrite -hsz -map_const_seq; apply/eq_in_map => c hc; rewrite hpt.
Qed.

(* The same, for the safety conditions: under a false guard they all hold. *)
Lemma cond_init_all (ts : seq ctype) (vs0 : values) (safe : seq safe_cond) (b : bool)
    (vs2 : values) :
  List.Forall2 (fun t v => exists x : sem_t t, v = to_val x) ts vs0 ->
  all sc_total safe -> all (sc_wt ts) safe ->
  all (safe_cond_b (rcons vs0 (Vbool b) ++ vs2)) (map (cond_init (size ts)) safe)
  = (if b then all (safe_cond_b vs0) safe else true).
Proof.
move=> hall htot hwt; rewrite all_map.
have hpt : forall c, c \in safe ->
    preim (cond_init (size ts)) (safe_cond_b (rcons vs0 (Vbool b) ++ vs2)) c
    = (~~ b) || safe_cond_b vs0 c.
+ move=> c hc; rewrite /preim /= cat_rcons.
  by apply: (sc_guarded_val _ _ hall (allP htot _ hc) (allP hwt _ hc)).
rewrite (eq_in_all hpt) => {hpt}; case: b => /=; first by [].
by apply: all_predT.
Qed.

(* -------------------------------------------------------------------- *)
(* ** Total tuples and filtering                                         *)

(* Like [sem_tuple], but boolean components are [bool] instead of
   [option bool]: the result of a total semantics. *)
Definition sem_tuple_t (ts : seq ctype) := ltuple (map sem_t ts).

(* A boolean component is kept when the mask says so, every other component is
   left untouched. *)
Definition filter_ot (b : bool) (t : ctype) : sem_t t -> sem_ot t :=
  if t is cbool then (fun x => if b then Some x else None) else id.

(* A component whose condition holds is the value itself. *)
Lemma filter_ot_true t (x : sem_t t) : filter_ot true x = sem_prod_id x.
Proof. by case: t x. Qed.

Fixpoint filter_tuple (ts : seq ctype) (mask : seq bool) : sem_tuple_t ts -> sem_tuple ts :=
  match ts return sem_tuple_t ts -> sem_tuple ts with
  | [::] => fun _ => tt
  | t :: ts =>
    let rec := @filter_tuple ts (behead mask) in
    match ts return (sem_tuple_t ts -> sem_tuple ts) ->
                    sem_tuple_t (t :: ts) -> sem_tuple (t :: ts) with
    | [::] => fun _ (x : sem_t t) => filter_ot (head false mask) x
    | t1 :: ts' => fun rec (p : sem_t t * sem_tuple_t (t1 :: ts')) =>
        (filter_ot (head false mask) p.1, rec p.2)
    end rec
  end.
Arguments filter_tuple : clear implicits.

(* A default total tuple, for the operators that have no semantics. *)
Definition dflt_t (t : ctype) : sem_t t :=
  match t return sem_t t with
  | cbool => false
  | cint => 0%Z
  | carr n => WArray.empty n
  | cword ws => 0%R
  end.

Fixpoint dflt_tuple (ts : seq ctype) : sem_tuple_t ts :=
  match ts return sem_tuple_t ts with
  | [::] => tt
  | t :: ts =>
    match ts return sem_tuple_t ts -> sem_tuple_t (t :: ts) with
    | [::] => fun _ => dflt_t t
    | t1 :: ts' => fun r => (dflt_t t, r)
    end (dflt_tuple ts)
  end.

(* [defined_as b v] : [v] is defined exactly when [b] holds, for a boolean
   component; a component of any other type is always defined. *)
Definition defined_as (b : bool) (v : value) : Prop :=
  if type_of_val v is cbool then is_defined v = b else is_defined v.

Lemma defined_as_filter_ot b t (x : sem_t t) : defined_as b (oto_val (filter_ot b x)).
Proof. by rewrite /defined_as; case: t x => //= x; case: b. Qed.

Lemma filter_tuple_defined ts mask (t : sem_tuple_t ts) :
  size mask = size ts ->
  List.Forall2 defined_as mask (list_ltuple (filter_tuple ts mask t)).
Proof.
elim: ts mask t => /= [ | ty1 [ | ty2 ts] ih] mask t.
+ by case: mask => //= _; constructor.
+ by case: mask => [ | b [ | ??]] //= _; constructor => //; apply: defined_as_filter_ot.
case: mask => [ | b mask] //= [] hsize; case: t => x xs /=.
by constructor; [apply: defined_as_filter_ot | apply: ih].
Qed.

Lemma filter_add_tuple (t : ctype) (lt : seq ctype) (b : bool) (mask : seq bool)
   (v : sem_t t) (xs : sem_tuple_t lt) :
  filter_tuple (t :: lt) (b :: mask) (add_tuple v xs)
  = add_tuple (filter_ot b v) (filter_tuple lt mask xs).
Proof. by case: lt xs => [ | t1 lt] xs //=; case: xs. Qed.

(* Total counterpart of [sem_prod_tuple]: the identity on a tuple of
   arguments, without wrapping the booleans in [Some]. *)
Fixpoint sem_prod_tuple_t (lt : seq ctype) : sem_prod lt (sem_tuple_t lt) :=
  match lt return sem_prod lt (sem_tuple_t lt) with
  | [::] => tt
  | t :: lt' =>
      fun v => sem_prod_app (sem_prod_tuple_t lt') (fun xs => add_tuple v xs)
  end.

(* -------------------------------------------------------------------- *)
(* ** The construction                                                   *)

(* The safety check: if one of the conditions fails, the operator raises the
   error it declares. *)
Definition check_safe (vs : values) (safe : seq safe_cond) (err : error) : exec unit :=
  if all (safe_cond_b vs) safe then ok tt else Error err.

Lemma check_safe_ok vs safe err : all (safe_cond_b vs) safe -> check_safe vs safe err = ok tt.
Proof. by rewrite /check_safe => ->. Qed.

Lemma check_safe_okE vs safe err u : check_safe vs safe err = ok u -> all (safe_cond_b vs) safe.
Proof. by rewrite /check_safe; case: ifP. Qed.

(* Conditions checked in order, each with its own error: an array read raises
   [ErrAddrInvalid], [ErrOob] or [ErrAddrUndef] depending on which guard fails,
   so the single error of [check_safe] does not suffice for the accesses. *)
Fixpoint check_safe_seq (vs : values) (scs : seq (safe_cond * error)) : exec unit :=
  match scs with
  | [::] => ok tt
  | (c, e) :: scs => if safe_cond_b vs c then check_safe_seq vs scs else Error e
  end.

Lemma check_safeE vs safe err :
  check_safe vs safe err = check_safe_seq vs (map (fun c => (c, err)) safe).
Proof.
rewrite /check_safe; elim: safe => //= c safe <-.
by case: safe_cond_b.
Qed.

(* Same accumulation scheme as [interp_safe_cond_ty_aux]: the arguments are
   collected, as values, in [vs]. *)
Fixpoint mk_semi_aux {T T'} (P : values -> T -> exec T') (vs : values) (tin : seq ctype) :
  sem_prod tin T -> sem_prod tin (exec T') :=
  match tin return sem_prod tin T -> sem_prod tin (exec T') with
  | [::] => fun t => P vs t
  | t :: tin => fun o v => @mk_semi_aux T T' P (rcons vs (to_val v)) tin (o v)
  end.
Arguments mk_semi_aux {T T'} P vs tin _ : assert.

Definition mk_semi (tin tout : seq ctype) (safe : seq safe_cond) (err : error)
    (init : seq safe_cond)
    (f : sem_prod tin (sem_tuple_t tout)) : sem_prod tin (exec (sem_tuple tout)) :=
  mk_semi_aux
    (fun vs t => Let _ := check_safe vs safe err in
                 ok (filter_tuple tout (map (safe_cond_b vs) init) t))
    [::] tin f.
Arguments mk_semi {tin tout} safe err init f : assert.

(* An operator has exactly one output and no undefined result: [mk_semi]
   without [init] nor [filter_tuple]. *)
Definition mk_sem_op (tin : seq ctype) (t : ctype) (safe : seq safe_cond) (err : error)
    (f : sem_prod tin (sem_t t)) : sem_prod tin (exec (sem_t t)) :=
  mk_semi_aux (fun vs r => Let _ := check_safe vs safe err in ok r) [::] tin f.
Arguments mk_sem_op {tin t} safe err f : assert.

(* Extensional equality on [sem_prod], by recursion on [tin]: no functional
   extensionality needed. *)
Fixpoint sem_prod_eq {T} (tin : seq ctype) : sem_prod tin T -> sem_prod tin T -> Prop :=
  match tin return sem_prod tin T -> sem_prod tin T -> Prop with
  | [::] => fun f g => f = g
  | t :: tin => fun f g => forall v : sem_t t, @sem_prod_eq T tin (f v) (g v)
  end.
Arguments sem_prod_eq {T} tin f g : assert.

Lemma sem_prod_eq_refl {T} tin (f : sem_prod tin T) : sem_prod_eq tin f f.
Proof. by elim: tin f => //= t tin ih f v; apply ih. Qed.

Lemma sem_prod_eq_sym {T} tin (f g : sem_prod tin T) :
  sem_prod_eq tin f g -> sem_prod_eq tin g f.
Proof. by elim: tin f g => /= [f g -> // | t tin ih f g h v]; apply: ih (h v). Qed.

Lemma sem_prod_eq_trans {T} tin (f g h : sem_prod tin T) :
  sem_prod_eq tin f g -> sem_prod_eq tin g h -> sem_prod_eq tin f h.
Proof.
by elim: tin f g h => /= [f g h -> // | t tin ih f g h h1 h2 v]; apply: ih (h1 v) (h2 v).
Qed.

Lemma sem_prod_eq_app {A B} tin (g : A -> B) (f1 f2 : sem_prod tin A) :
  sem_prod_eq tin f1 f2 -> sem_prod_eq tin (sem_prod_app f1 g) (sem_prod_app f2 g).
Proof. by elim: tin f1 f2 => /= [f1 f2 -> // | t tin ih f1 f2 h v]; apply: ih (h v). Qed.

(* Two pointwise equal post-treatments give two equal semantics. *)
Lemma mk_semi_aux_eq {T T'} (P Q : values -> T -> exec T') vs tin (f : sem_prod tin T) :
  (forall vs t, P vs t = Q vs t) ->
  sem_prod_eq tin (mk_semi_aux P vs tin f) (mk_semi_aux Q vs tin f).
Proof. by move=> h; elim: tin vs f => /= [vs f | t tin ih vs f v]; [apply h | apply ih]. Qed.

(* Post-composing the result is the same as post-composing the post-treatment. *)
Lemma sem_prod_app_mk_semi_aux {T T' T''} (P : values -> T -> exec T')
    (g : exec T' -> exec T'') vs tin (f : sem_prod tin T) :
  sem_prod_eq tin (sem_prod_app (mk_semi_aux P vs tin f) g)
                  (mk_semi_aux (fun vs t => g (P vs t)) vs tin f).
Proof. by elim: tin vs f => //= t tin ih vs f v; apply ih. Qed.

(* Pre-composing the total semantics is the same as pre-composing the
   post-treatment. *)
Lemma mk_semi_aux_sem_prod_app {T T' T''} (Q : values -> T'' -> exec T')
    (h : T -> T'') vs tin (f : sem_prod tin T) :
  sem_prod_eq tin (mk_semi_aux Q vs tin (sem_prod_app f h))
                  (mk_semi_aux (fun vs t => Q vs (h t)) vs tin f).
Proof. by elim: tin vs f => //= t tin ih vs f v; apply ih. Qed.

(* Two extensionally equal semantics satisfy the same properties. *)
Lemma sem_forall_eq {T} (P : T -> Prop) tin (f g : sem_prod tin T) :
  sem_prod_eq tin f g -> sem_forall P tin g -> sem_forall P tin f.
Proof.
by elim: tin f g => /= [f g -> // | t tin ih f g heq hg v]; apply: (ih _ _ (heq v) (hg v)).
Qed.

(* The safety conditions of an operator are sufficient for its semantics to
   succeed. *)
Definition safe_cond_ty tin T (safe : seq safe_cond) (semi : sem_prod tin (exec T)) :=
  interp_safe_cond_ty_aux
    (fun vs r => all (safe_cond_b vs) safe -> exists t, r = ok t) [::] semi.

Lemma sem_prod_ok_safe_aux {T:Type} (tin : seq ctype) (o: sem_prod tin T) safe vs :
   interp_safe_cond_ty_aux
     (fun (vs : values) (r : result error T) =>
        all (safe_cond_b vs) safe -> exists t : T, r = ok t) vs
      (sem_prod_ok tin o).
Proof. elim: tin vs o => //=; eauto. Qed.

Lemma sem_prod_ok_safe {T:Type} (tin : seq ctype) (o: sem_prod tin T) :
   safe_cond_ty [::] (sem_prod_ok tin o).
Proof. apply sem_prod_ok_safe_aux. Qed.

Lemma safe_cond_ty_aux_eq {T} (P : values -> exec T -> Prop) tin vs
    (f g : sem_prod tin (exec T)) :
  sem_prod_eq tin f g -> interp_safe_cond_ty_aux P vs g -> interp_safe_cond_ty_aux P vs f.
Proof.
by elim: tin vs f g => /= [vs f g -> // | t tin ih vs f g heq hg v]; apply: (ih _ _ _ (heq v) (hg v)).
Qed.

Lemma safe_cond_ty_eq {T} tin safe (f g : sem_prod tin (exec T)) :
  sem_prod_eq tin f g -> safe_cond_ty safe g -> safe_cond_ty safe f.
Proof. apply: safe_cond_ty_aux_eq. Qed.

Lemma sem_prod_eq_app_sopn {A} tin (f g : sem_prod tin (exec A)) vs :
  sem_prod_eq tin f g -> app_sopn tin f vs = app_sopn tin g vs.
Proof.
elim: tin f g vs => /= [f g vs -> // | t tin ih f g [ | v vs] //= heq].
by case: of_val => //= x; apply ih.
Qed.

Lemma sem_prod_eq_app_sopn_v tin tout (f g : sem_prod tin (exec (sem_tuple tout))) vs :
  sem_prod_eq tin f g -> app_sopn_v f vs = app_sopn_v g vs.
Proof. by move=> heq; rewrite /app_sopn_v (sem_prod_eq_app_sopn vs heq). Qed.

(* -------------------------------------------------------------------- *)
(* ** Generic properties of [mk_semi]                                    *)

Lemma mk_semi_aux_errty {T T'} (P : values -> T -> exec T') e vs tin (f : sem_prod tin T) :
  (forall vs t, P vs t <> Error e) ->
  sem_forall (fun r => r <> Error e) tin (mk_semi_aux P vs tin f).
Proof. by move=> h; elim: tin vs f => //= t tin ih vs f v; apply ih. Qed.

(* [mk_semi] never raises a type error, as long as the declared error is not
   one. *)
Lemma mk_semi_errty tin tout safe err init f :
  err <> ErrType ->
  sem_forall (fun r => r <> Error ErrType) tin (@mk_semi tin tout safe err init f).
Proof.
move=> herr; apply: mk_semi_aux_errty => vs t.
by rewrite /check_safe; case: ifP => //= _ [].
Qed.

Lemma mk_semi_aux_safe {T T'} (P : values -> T -> exec T') (Q : values -> Prop) vs tin
    (f : sem_prod tin T) :
  (forall vs t, Q vs -> exists t', P vs t = ok t') ->
  interp_safe_cond_ty_aux (fun vs r => Q vs -> exists t, r = ok t) vs (mk_semi_aux P vs tin f).
Proof. by move=> h; elim: tin vs f => //= t tin ih vs f v; apply ih. Qed.

(* If the safety conditions hold, [mk_semi] succeeds. *)
Lemma mk_semi_safe tin tout safe err init f :
  safe_cond_ty safe (@mk_semi tin tout safe err init f).
Proof.
apply: mk_semi_aux_safe => vs t hall.
by rewrite (check_safe_ok err hall) /=; eexists; reflexivity.
Qed.

(* The values [mk_semi] sees are the truncations of the arguments at [tin]. *)
Lemma mk_semi_auxP {T T'} (P : values -> T -> exec T') tin (f : sem_prod tin T) vs vs0 r :
  app_sopn tin (mk_semi_aux P vs0 tin f) vs = ok r ->
  exists2 vs', mapM2 ErrType truncate_val tin vs = ok vs' &
    exists2 t, app_sopn tin (sem_prod_ok tin f) vs = ok t & P (vs0 ++ vs') t = ok r.
Proof.
elim: tin f vs vs0 => /= [f [|//] vs0 h | t tin ih f [|v vs] // vs0].
+ by exists [::] => //; exists f => //; rewrite cats0.
t_xrbindP => x hx /ih [vs' hvs' [t0 ht0 hP]].
rewrite /truncate_val hx /= hvs' /= ht0.
by exists (to_val x :: vs') => //; exists t0 => //; rewrite -cat_rcons.
Qed.

(* Complete description of a successful application of [mk_semi]. *)
Lemma mk_semiP tin tout safe err init f vs r :
  app_sopn tin (@mk_semi tin tout safe err init f) vs = ok r ->
  exists2 vs', mapM2 ErrType truncate_val tin vs = ok vs' &
    exists2 t, app_sopn tin (sem_prod_ok tin f) vs = ok t &
      all (safe_cond_b vs') safe /\
      r = filter_tuple tout (map (safe_cond_b vs') init) t.
Proof.
rewrite /mk_semi => h; case: (mk_semi_auxP h) => vs' h1 [t h2]; rewrite cat0s.
case hu: (check_safe vs' safe err) => [u|e] //= [<-].
by exists vs' => //; exists t => //; split => //; apply: check_safe_okE hu.
Qed.

(* Conversely, success implies that the safety conditions hold on the
   truncated arguments. *)
Lemma mk_semi_safe_rev tin tout safe err init f vs r :
  app_sopn tin (@mk_semi tin tout safe err init f) vs = ok r ->
  exists2 vs', mapM2 ErrType truncate_val tin vs = ok vs' & all (safe_cond_b vs') safe.
Proof. by move=> h; case: (mk_semiP h) => vs' h1 [t _ [h3 _]]; exists vs'. Qed.

Lemma Forall2_map_l A B C (f : A -> B) (R : B -> C -> Prop) l1 l2 :
  List.Forall2 R (map f l1) l2 -> List.Forall2 (fun a c => R (f a) c) l1 l2.
Proof.
elim: l1 l2 => /= [ | a l1 ih] l2 /List_Forall2_inv_l; first by move=> ->.
by move=> [c [l2' [-> [hr /ih h]]]]; constructor.
Qed.

(* An output is defined exactly when its condition, evaluated on the truncated
   arguments, holds. *)
Lemma mk_semi_init tin tout safe err init f vs r :
  size init = size tout ->
  app_sopn tin (@mk_semi tin tout safe err init f) vs = ok r ->
  exists2 vs', mapM2 ErrType truncate_val tin vs = ok vs' &
    List.Forall2 (fun c v => defined_as (safe_cond_b vs' c) v) init (list_ltuple r).
Proof.
move=> hsize h; case: (mk_semiP h) => vs' h1 [t _ [_ ->]].
exists vs' => //; apply: Forall2_map_l.
by apply: filter_tuple_defined; rewrite size_map.
Qed.

Lemma mk_semi_aux_ok {T T'} (P : values -> T -> exec T') (g : T -> T') vs tin
    (f : sem_prod tin T) :
  (forall vs t, P vs t = ok (g t)) ->
  sem_prod_eq tin (mk_semi_aux P vs tin f) (sem_prod_ok tin (sem_prod_app f g)).
Proof.
move=> h; elim: tin vs f => /= [vs f | t tin ih vs f v].
+ by apply: h.
by apply: ih.
Qed.

(* Same, when the post-treatment is only known on the arguments prefixed by
   [vs1]. *)
Lemma mk_semi_aux_ok_cat {T T'} (P : values -> T -> exec T') (g : T -> T') vs1
    (tin : seq ctype) (f : sem_prod tin T) :
  (forall vs2 t, P (vs1 ++ vs2) t = ok (g t)) ->
  sem_prod_eq tin (mk_semi_aux P vs1 tin f) (sem_prod_ok tin (sem_prod_app f g)).
Proof.
elim: tin vs1 f => /= [vs1 f h | t tin ih vs1 f h v].
+ by have := h [::] f; rewrite cats0.
by apply: ih => vs2 t2; rewrite cat_rcons h.
Qed.

(* Same, when the total semantics is a constant. *)
Lemma mk_semi_aux_const {T T'} (P : values -> T -> exec T') vs1
    (tin : seq ctype) (t0 : T) (r : exec T') :
  (forall vs2, P (vs1 ++ vs2) t0 = r) ->
  sem_prod_eq tin (mk_semi_aux P vs1 tin (sem_prod_const tin t0)) (sem_prod_const tin r).
Proof.
elim: tin vs1 => /= [vs1 h | t tin ih vs1 h v].
+ by have := h [::]; rewrite cats0.
by apply: ih => vs2; rewrite cat_rcons h.
Qed.

Lemma sem_prod_ok_app {A} (lt : seq ctype) (X : sem_prod lt A) :
  sem_prod_eq lt (sem_prod_ok lt X) (sem_prod_app X (fun a : A => ok a)).
Proof. by elim: lt X => //= t lt ih X v. Qed.

Lemma sem_prod_app_comp {A B C} (lt : seq ctype) (f : sem_prod lt A)
    (g : A -> B) (h : B -> C) :
  sem_prod_eq lt (sem_prod_app (sem_prod_app f g) h) (sem_prod_app f (fun x => h (g x))).
Proof. by elim: lt f => //= t lt ih f v. Qed.

Lemma sem_prod_const_app {A B} (lt : seq ctype) (r : A) (c : A -> B) :
  sem_prod_eq lt (sem_prod_app (sem_prod_const lt r) c) (sem_prod_const lt (c r)).
Proof. by elim: lt => //= t lt ih v. Qed.

(* Building a tuple out of the arguments and filtering it with an all-true
   mask is building the tuple of the semantics. *)
Lemma sem_prod_tuple_filter {A} (lt : seq ctype) (mask : seq bool)
      (K : sem_tuple lt -> A) (K' : sem_tuple_t lt -> A) :
  all id mask -> size mask = size lt ->
  (forall t, K' t = K (filter_tuple lt mask t)) ->
  sem_prod_eq lt (sem_prod_app (sem_prod_tuple_t lt) K') (sem_prod_app (sem_prod_tuple lt) K).
Proof.
elim: lt mask K K'.
+ by move=> mask K K' _ _ h /=; rewrite h.
move=> t lt ih [ | b mask] // K K' /andP [hb hall] [hsz] h v /=.
apply: sem_prod_eq_trans; first by apply: sem_prod_app_comp.
apply: sem_prod_eq_trans; last by apply: sem_prod_eq_sym; apply: sem_prod_app_comp.
apply: (ih mask _ _ hall hsz) => t2.
by rewrite h filter_add_tuple hb filter_ot_true.
Qed.

(* No safety condition and every output defined: [mk_semi] is the total
   semantics, with [Some] added on the boolean components. *)
Lemma mk_semi_all_true tin tout err f :
  sem_prod_eq tin (@mk_semi tin tout [::] err (nseq (size tout) (IBool true)) f)
                  (sem_prod_ok tin (sem_prod_app f (filter_tuple tout (nseq (size tout) true)))).
Proof. by apply: mk_semi_aux_ok => vs t; rewrite /= map_nseq. Qed.

(* [mk_semi] reduces on a concrete signature: this is what makes the
   instruction-by-instruction equality proofs provable by [reflexivity]. *)
Lemma mk_semi_reduces_example :
  sem_prod_eq [:: cword U64; cword U8]
    (sem_prod_ok [:: cword U64; cword U8]
       (fun (v : word U64) (i : word U8) =>
          ((Some (msb v), v) : sem_tuple [:: cbool; cword U64])))
    (@mk_semi [:: cword U64; cword U8] [:: cbool; cword U64] [::] ErrArith
       [:: IBool true; IBool true]
       (fun (v : word U64) (i : word U8) => (msb v, v))).
Proof. by move=> v i. Qed.

(* -------------------------------------------------------------------- *)
(* ** Generic properties of [mk_sem_op]                                  *)

(* [mk_sem_op] never raises a type error. *)
Lemma mk_sem_op_errty tin t safe err f :
  err <> ErrType ->
  sem_forall (fun r => r <> Error ErrType) tin (@mk_sem_op tin t safe err f).
Proof.
move=> herr; apply: mk_semi_aux_errty => vs r.
by rewrite /check_safe; case: ifP => //= _ [].
Qed.

(* If the safety conditions hold, [mk_sem_op] succeeds. *)
Lemma mk_sem_op_safe tin t safe err f :
  safe_cond_ty safe (@mk_sem_op tin t safe err f).
Proof.
apply: mk_semi_aux_safe => vs r hall.
by rewrite (check_safe_ok err hall) /=; eexists; reflexivity.
Qed.

(* Complete description of a successful application of [mk_sem_op]. *)
Lemma mk_sem_opP tin t safe err f vs r :
  app_sopn tin (@mk_sem_op tin t safe err f) vs = ok r ->
  exists2 vs', mapM2 ErrType truncate_val tin vs = ok vs' &
    all (safe_cond_b vs') safe /\ app_sopn tin (sem_prod_ok tin f) vs = ok r.
Proof.
rewrite /mk_sem_op => h; case: (mk_semi_auxP h) => vs' h1 [r0 h2]; rewrite cat0s.
case hu: (check_safe vs' safe err) => [u|e] //= [?]; subst r0.
by exists vs' => //; split => //; apply: check_safe_okE hu.
Qed.

Lemma mk_sem_op_safe_rev tin t safe err f vs r :
  app_sopn tin (@mk_sem_op tin t safe err f) vs = ok r ->
  exists2 vs', mapM2 ErrType truncate_val tin vs = ok vs' & all (safe_cond_b vs') safe.
Proof. by move=> h; case: (mk_sem_opP h) => vs' h1 [h2 _]; exists vs'. Qed.

Lemma mk_semi_aux_id {T} (P : values -> T -> exec T) vs tin (f : sem_prod tin T) :
  (forall vs r, P vs r = ok r) ->
  sem_prod_eq tin (mk_semi_aux P vs tin f) (sem_prod_ok tin f).
Proof. by move=> h; elim: tin vs f => /= [vs f | t tin ih vs f v]; [apply h | apply ih]. Qed.

(* Without safety condition, [mk_sem_op] is the total semantics. *)
Lemma mk_sem_op_nil tin t err f :
  sem_prod_eq tin (@mk_sem_op tin t [::] err f) (sem_prod_ok tin f).
Proof. by apply: mk_semi_aux_id. Qed.

(* [mk_sem_op] reduces on a concrete signature. *)
Lemma mk_sem_op_reduces_example :
  sem_prod_eq [:: cint; cint]
    (@mk_sem_op [:: cint; cint] cint [::] ErrArith (fun v1 v2 => (v1 + v2)%Z))
    (sem_prod_ok [:: cint; cint] (fun v1 v2 => (v1 + v2)%Z)).
Proof. by move=> v1 v2. Qed.

(* -------------------------------------------------------------------- *)
(* ** Safety conditions of the array and memory accesses                  *)

(* Unlike the conditions of the operators above, the conditions of this section
   are not matched by safetylib/safetyInterpreter.ml: the OCaml checker builds
   its own conditions for the accesses ([AlignedExpr], [InBound], [Initai],
   [Valid]). These are the conditions of the semantics itself. *)

(* The scaled index of an array access: [i * mk_scale aa ws]. *)
Definition sc_arr_scaled (aa : arr_access) ws (k : nat) : safe_cond :=
  sc_muli (IVar k) (IConst (mk_scale aa ws)).

(* [is_aligned_if al (i * mk_scale aa ws) ws]: a scaled access is always
   aligned, and an unaligned access has nothing to check. *)
Definition sc_arr_aligned (al : aligned) (aa : arr_access) ws (k : nat) : safe_cond :=
  if (al == Unaligned) || (aa == AAscale) then IBool true
  else sc_eqi (sc_modi Unsigned (sc_arr_scaled aa ws k) (IConst (wsize_size ws))) (IConst 0).

(* The [size] bytes read or written at [i * mk_scale aa ws] are inside an array
   of length [len]. *)
Definition sc_arr_in_bound (len : Z) (aa : arr_access) ws (k : nat) (size : Z) : safe_cond :=
  sc_and (sc_lei (IConst 0) (sc_arr_scaled aa ws k))
         (sc_lei (sc_addi (sc_arr_scaled aa ws k) (IConst size)) (IConst len)).

(* They are moreover initialised, in the array argument [ka]. *)
Definition sc_arr_init (len : Z) (aa : arr_access) ws (ka k : nat) (size : Z) : safe_cond :=
  sc_is_arr_init len ka (sc_arr_scaled aa ws k) size.

(* The conditions of the four array accesses, on the arguments
   [:: Varr a; Vint i] (plus the written value, which no condition mentions). *)
Definition sc_get (len : Z) al aa ws : seq (safe_cond * error) :=
  [:: (sc_arr_aligned al aa ws 1, ErrAddrInvalid);
      (sc_arr_in_bound len aa ws 1 (wsize_size ws), ErrOob);
      (sc_arr_init len aa ws 0 1 (wsize_size ws), ErrAddrUndef) ].

Definition sc_set (len : Z) al aa ws : seq (safe_cond * error) :=
  [:: (sc_arr_aligned al aa ws 1, ErrAddrInvalid);
      (sc_arr_in_bound len aa ws 1 (wsize_size ws), ErrOob) ].

Definition sc_get_sub (len : Z) aa ws n : seq (safe_cond * error) :=
  [:: (sc_arr_in_bound len aa ws 1 (arr_size ws n), ErrOob) ].

Definition sc_set_sub (len : Z) aa ws n : seq (safe_cond * error) :=
  [:: (sc_arr_in_bound len aa ws 1 (arr_size ws n), ErrOob) ].

(* ** What these conditions compute *)

Lemma safe_cond_b_arr_aligned al aa ws k (vs : values) (i : Z) :
  nth undef_b vs k = Vint i ->
  safe_cond_b vs (sc_arr_aligned al aa ws k) = is_aligned_if al (i * mk_scale aa ws)%Z ws.
Proof.
move=> h; rewrite /sc_arr_aligned.
case: ifPn => [ | ]; last first.
+ rewrite negb_or => /andP [hal haa].
  case: al hal => [// | _]; case: aa haa => [_ | //].
  rewrite /safe_cond_b /sc_eqi /sc_modi /sc_arr_scaled /sc_muli /= h /=.
  by rewrite is_alignE WArray.p_to_zE Z_eqbE.
case: al => [_ | ] /=; first by [].
by move=> /eqP ->; rewrite WArray.is_align_scale.
Qed.

Lemma safe_cond_b_arr_in_bound len aa ws k size (vs : values) (i : Z) :
  nth undef_b vs k = Vint i ->
  safe_cond_b vs (sc_arr_in_bound len aa ws k size)
  = ((0 <=? i * mk_scale aa ws) && (i * mk_scale aa ws + size <=? len))%Z.
Proof.
by move=> h;
  rewrite /safe_cond_b /sc_arr_in_bound /sc_and /sc_lei /sc_addi /sc_arr_scaled
          /sc_muli /= h.
Qed.

Lemma safe_cond_b_arr_init len aa ws ka k size (vs : values)
    (a : WArray.array len) (i : Z) :
  nth undef_b vs ka = Varr a ->
  nth undef_b vs k = Vint i ->
  safe_cond_b vs (sc_arr_init len aa ws ka k size)
  = all (WArray.is_init a) (ziota (i * mk_scale aa ws)%Z size).
Proof.
move=> ha hi.
by rewrite /safe_cond_b /sc_arr_init /sc_is_arr_init /sc_arr_scaled /sc_muli /=
           ha hi /= arr_sizeE wsize8 Z.mul_1_l WArray.castK.
Qed.

(* ** The accesses as "conditions + total function" *)

Lemma getE (len : Z) al aa ws (a : WArray.array len) (i : Z) :
  eq_ok (WArray.get al aa ws a i)
        (Let _ := check_safe_seq [:: Varr a; Vint i] (sc_get len al aa ws) in
         ok (WArray.get_total aa ws a i)).
Proof.
rewrite /WArray.get /WArray.get_total.
apply: (eq_ok_trans (@readE _ _ _ _ a al (i * mk_scale aa ws)%Z ws)).
rewrite [X in eq_ok _ X]/=.
rewrite WArray.validr_validw_init WArray.validw_in_range /WArray.in_range.
rewrite (@safe_cond_b_arr_aligned al aa ws 1 [:: Varr a; Vint i] i erefl)
        (@safe_cond_b_arr_in_bound len aa ws 1 (wsize_size ws) [:: Varr a; Vint i] i erefl)
        (@safe_cond_b_arr_init len aa ws 0 1 (wsize_size ws) [:: Varr a; Vint i] a i erefl erefl).
by case: is_aligned_if; case: (0 <=? i * mk_scale aa ws)%Z;
   case: (i * mk_scale aa ws + wsize_size ws <=? len)%Z;
   case: (all (WArray.is_init a) (ziota (i * mk_scale aa ws)%Z (wsize_size ws))).
Qed.

Lemma setE (len : Z) al aa ws (a : WArray.array len) (i : Z) (v : word ws) :
  eq_ok (WArray.set a al aa i v)
        (Let _ := check_safe_seq [:: Varr a; Vint i; Vword v] (sc_set len al aa ws) in
         ok (WArray.set_total a aa i v)).
Proof.
rewrite /WArray.set /WArray.set_total.
apply: (eq_ok_trans (@writeE _ _ _ _ a al (i * mk_scale aa ws)%Z ws v)).
rewrite [X in eq_ok _ X]/=.
rewrite WArray.validw_in_range /WArray.in_range.
rewrite (@safe_cond_b_arr_aligned al aa ws 1 [:: Varr a; Vint i; Vword v] i erefl)
        (@safe_cond_b_arr_in_bound len aa ws 1 (wsize_size ws)
           [:: Varr a; Vint i; Vword v] i erefl).
by case: is_aligned_if; case: (0 <=? i * mk_scale aa ws)%Z;
   case: (i * mk_scale aa ws + wsize_size ws <=? len)%Z.
Qed.

Lemma get_subE (lena : Z) aa ws n (a : WArray.array lena) (i : Z) :
  eq_ok (WArray.get_sub aa ws n a i)
        (Let _ := check_safe_seq [:: Varr a; Vint i] (sc_get_sub lena aa ws n) in
         ok (WArray.get_sub_total aa ws n a i)).
Proof.
rewrite /WArray.get_sub /WArray.get_sub_total /=.
rewrite (@safe_cond_b_arr_in_bound lena aa ws 1 (arr_size ws n)
           [:: Varr a; Vint i] i erefl).
by case: (_ && _).
Qed.

Lemma set_subE (lena : Z) aa ws n (a : WArray.array lena) (i : Z)
    (b : WArray.array (arr_size ws n)) :
  eq_ok (WArray.set_sub aa a i b)
        (Let _ := check_safe_seq [:: Varr a; Vint i; Varr b] (sc_set_sub lena aa ws n) in
         ok (WArray.set_sub_total aa a i b)).
Proof.
rewrite /WArray.set_sub /WArray.set_sub_total /=.
rewrite (@safe_cond_b_arr_in_bound lena aa ws 1 (arr_size ws n)
           [:: Varr a; Vint i; Varr b] i erefl).
by case: (_ && _).
Qed.

(* ** The alignment condition of a memory access *)

Section MEM_COND.

Context {pd : PointerData}.

(* The validity of a memory access depends on the memory, not only on the
   arguments: it stays an assertion ([Pis_mem_init]). Only the alignment of the
   pointer is a condition on the value of an argument. *)
Definition sc_mem_aligned (al : aligned) sz (k : nat) : safe_cond :=
  if al == Unaligned then IBool true
  else sc_eqi (sc_modi Unsigned (sc_toint Unsigned Uptr k) (IConst (wsize_size sz)))
              (IConst 0).

Lemma safe_cond_b_mem_aligned al sz k (vs : values) (p : pointer) :
  nth undef_b vs k = Vword p ->
  safe_cond_b vs (sc_mem_aligned al sz k) = is_aligned_if al p sz.
Proof.
move=> h; rewrite /sc_mem_aligned; case: al => //=.
rewrite /safe_cond_b /sc_eqi /sc_modi /sc_toint /= h /= truncate_word_u /=.
by rewrite is_alignE memory_model.p_to_zE Z_eqbE.
Qed.

End MEM_COND.
