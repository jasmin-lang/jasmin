(* * Building blocks for the semantics of the operators.

   An operator is described by three independent pieces of data:
   - a total semantics, of type [sem_prod tin (sem_t tout)] ([sem_op_total.v]);
   - a list of conditions on its arguments, [seq acond], under which the usual
     (partial) semantics does not fail;
   - the error it raises when one of them does not hold.
   [mk_sem_op] assembles them into the usual [sem_prod tin (exec (sem_t tout))].

   The conditions of the operators themselves are in [op_semi.v]; this file
   only defines the language of conditions and the generic construction. *)

(* ** Imports and settings *)
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq eqtype ssralg.
From mathcomp Require Import word_ssrZ.
From elpi.apps Require Import derive.std.
From HB Require Import structures.
Require Export sem_op_total values.
Import Utf8.

(* -------------------------------------------------------------------- *)
(* Auxiliary facts about [of_val] and [truncate_val].                     *)

(* Truncating at [t] does not change how the value is read at any smaller
   type [t']: this is what makes the interpretation of a condition on the
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
(* ** Conditions on the arguments of an operator                          *)

(* A boolean expression on the arguments of an operator. [IVar n] refers to
   the n-th argument. *)
#[only(eqbOK)] derive
Inductive acond :=
  | IBool of bool
  | IConst of Z
  | IVar of nat
  | IOp1 of sop1 & acond
  | IOp2 of sop2 & acond & acond
  | IAppN_safety of opN_safety & seq acond.

HB.instance Definition _ := hasDecEq.Build acond acond_eqb_OK.

(* The generated scheme does not go under the list of [IAppN_safety]. *)
Section ACOND_IND.
  Context
    (P : acond -> Prop)
    (Hbool : forall b, P (IBool b))
    (Hconst : forall z, P (IConst z))
    (Hvar : forall k, P (IVar k))
    (Hop1 : forall o c, P c -> P (IOp1 o c))
    (Hop2 : forall o c1, P c1 -> forall c2, P c2 -> P (IOp2 o c1 c2))
    (HappN : forall o cs, List.Forall P cs -> P (IAppN_safety o cs)).

  Fixpoint acond_ind_s (c : acond) : P c :=
    match c with
    | IBool b => Hbool b
    | IConst z => Hconst z
    | IVar k => Hvar k
    | IOp1 o c => Hop1 o (acond_ind_s c)
    | IOp2 o c1 c2 => Hop2 o (acond_ind_s c1) (acond_ind_s c2)
    | IAppN_safety o cs =>
      HappN o ((fix loop (l : seq acond) : List.Forall P l :=
                  match l with
                  | [::] => List.Forall_nil P
                  | c :: l => List.Forall_cons c (acond_ind_s c) (loop l)
                  end) cs)
    end.
End ACOND_IND.

(* The interpretation goes through the *total* semantics of the operators, so
   that it does not depend on [sem_sop1_typed]/[sem_sop2_typed] failing. *)
Fixpoint interp_acond (vs : values) (c : acond) : exec value :=
  match c with
  | IBool b => ok (Vbool b)
  | IConst z => ok (Vint z)
  | IVar n => ok (nth undef_b vs n)
  | IOp1 o c =>
    Let v := interp_acond vs c in
    Let x := of_val _ v in
    ok (to_val (sem_sop1_total o x))
  | IOp2 o c1 c2 =>
    Let v1 := interp_acond vs c1 in
    Let v2 := interp_acond vs c2 in
    Let x1 := of_val _ v1 in
    Let x2 := of_val _ v2 in
    ok (to_val (sem_sop2_total o x1 x2))
  | IAppN_safety o cs =>
    Let l := mapM (interp_acond vs) cs in
    Let b := app_sopn _ (sem_opN_safety_typed o) l in
    ok (Vbool b)
  end.

(* A condition that is not a boolean (in particular an ill-typed one, whose
   interpretation is an error) counts as false. *)
Definition acond_b (vs : values) (c : acond) : bool :=
  if interp_acond vs c is Ok (Vbool b) then b else false.

(* ** Typing *)

(* [ac_type tin c] is the type of [c] when the arguments have types [tin].
   An operator expecting an argument of type [t] accepts a sub-condition of
   type [t'] as soon as [subctype t t'], which is exactly what [of_val]
   accepts (for words: a word of at least that size). *)
Definition sub_octype (t : ctype) (ot : option ctype) : bool :=
  if ot is Some t' then subctype t t' else false.

Fixpoint ac_type (tin : seq ctype) (c : acond) : option ctype :=
  match c with
  | IBool _ => Some cbool
  | IConst _ => Some cint
  | IVar n => if (n < size tin)%nat then Some (nth cbool tin n) else None
  | IOp1 o c =>
    let t := type_of_op1 o in
    if ac_type tin c is Some t1 then
      if subctype (eval_atype t.1) t1 then Some (eval_atype t.2) else None
    else None
  | IOp2 o c1 c2 =>
    let t := type_of_op2 o in
    if ac_type tin c1 is Some t1 then
      if ac_type tin c2 is Some t2 then
        if subctype (eval_atype t.1.1) t1 && subctype (eval_atype t.1.2) t2
        then Some (eval_atype t.2) else None
      else None
    else None
  | IAppN_safety o cs =>
    if all2 sub_octype (map eval_atype (type_of_opN_safety o).1) (map (ac_type tin) cs)
    then Some cbool else None
  end.

(* [ac_types tin ts cs]: the conditions [cs] have the types [ts], up to
   [subctype]. *)
Definition ac_types (tin ts : seq ctype) (cs : seq acond) : bool :=
  all2 sub_octype ts (map (ac_type tin) cs).

Lemma ac_type_appN tin o cs :
  ac_type tin (IAppN_safety o cs) =
  if ac_types tin (map eval_atype (type_of_opN_safety o).1) cs then Some cbool else None.
Proof. by []. Qed.

(* A well-typed condition is one that evaluates to a boolean. *)
Definition ac_wt (tin : seq ctype) (c : acond) : bool :=
  ac_type tin c == Some cbool.

(* The variables of a condition are among the first [n] arguments. *)
Fixpoint ac_below (n : nat) (c : acond) : bool :=
  match c with
  | IBool _ | IConst _ => true
  | IVar k => (k < n)%nat
  | IOp1 _ c => ac_below n c
  | IOp2 _ c1 c2 => ac_below n c1 && ac_below n c2
  | IAppN_safety _ cs => all (ac_below n) cs
  end.

(* The number of arguments a condition reads: one more than the largest [IVar]
   it mentions, [0] if it mentions none. *)
Fixpoint ac_max_var (c : acond) : nat :=
  match c with
  | IBool _ | IConst _ => 0
  | IVar k => S k
  | IOp1 _ c => ac_max_var c
  | IOp2 _ c1 c2 => ssrnat.maxn (ac_max_var c1) (ac_max_var c2)
  | IAppN_safety _ cs => foldr (fun c n => ssrnat.maxn (ac_max_var c) n) 0 cs
  end.

Lemma ac_max_var_appN_le o cs n :
  ssrnat.leq (ac_max_var (IAppN_safety o cs)) n
  = all (fun c => ssrnat.leq (ac_max_var c) n) cs.
Proof. by elim: cs => //= c cs ih; rewrite ssrnat.geq_max ih. Qed.

Lemma ac_max_var_below n c : ssrnat.leq (ac_max_var c) n = ac_below n c.
Proof.
elim/acond_ind_s: c => //=.
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

(* The safety operators are total. *)
Lemma sem_opN_safety_typed_ok o :
  sem_forall (fun r : exec bool => is_ok r)
    (map eval_atype (type_of_opN_safety o).1) (sem_opN_safety_typed o).
Proof. by case: o => len a lo l. Qed.

(* Conditions built from operators whose typed semantics cannot fail: their
   interpretation on arguments of the announced types is always a value. *)
Fixpoint ac_total (c : acond) : bool :=
  match c with
  | IBool _ | IConst _ | IVar _ => true
  | IOp1 o c => op1_total o && ac_total c
  | IOp2 o c1 c2 => [&& op2_total o, ac_total c1 & ac_total c2]
  | IAppN_safety _ cs => all ac_total cs
  end.

(* Well-formedness of a condition: well typed and total. *)
Definition ac_ok (tin : seq ctype) (c : acond) : bool :=
  ac_wt tin c && ac_total c.

Lemma ac_ok_wt tin c : ac_ok tin c -> ac_wt tin c.
Proof. by move=> /andP []. Qed.

Lemma ac_ok_total tin c : ac_ok tin c -> ac_total c.
Proof. by move=> /andP []. Qed.

Lemma all_ac_ok_wt tin l : all (ac_ok tin) l -> all (ac_wt tin) l.
Proof. by apply: sub_all; apply: ac_ok_wt. Qed.

Lemma all_ac_ok_total tin l : all (ac_ok tin) l -> all ac_total l.
Proof. by apply: sub_all; apply: ac_ok_total. Qed.

(* ** Basic properties of the interpretation *)

Lemma ac_type_below tin c t : ac_type tin c = Some t -> ac_below (size tin) c.
Proof.
elim/acond_ind_s: c t => //=.
+ by move=> k t; case: ifP.
+ move=> o c ih t; case heq: (ac_type tin c) => [t1|] //=; case: ifP => // _ _.
  by apply: ih heq.
+ move=> o c1 ih1 c2 ih2 t.
  case heq1: (ac_type tin c1) => [t1|] //=; case heq2: (ac_type tin c2) => [t2|] //=.
  case: ifP => // _ _.
  by rewrite (ih1 _ heq1) (ih2 _ heq2).
move=> o cs hall t; case: ifP => // + _.
elim: cs hall (map eval_atype (type_of_opN_safety o).1) => [ | c cs ih] hall [ | t0 ts] //=.
move=> /andP [h1 h2]; move/List_Forall_inv: hall => [hc hcs].
rewrite (ih hcs ts h2) andbT.
by move: h1; rewrite /sub_octype; case heq: (ac_type tin c) => [t1|] // _; apply: (hc _ heq).
Qed.

Lemma ac_type_cat tin tin' c t :
  ac_type tin c = Some t -> ac_type (tin ++ tin') c = Some t.
Proof.
elim/acond_ind_s: c t => //=.
+ move=> k t; case: ifP => // hk [<-].
  by rewrite nth_cat hk size_cat (ltn_addr _ hk).
+ move=> o c ih t; case heq: (ac_type tin c) => [t1|] //=; case: ifP => // hsub [<-].
  by rewrite (ih _ heq) /= hsub.
+ move=> o c1 ih1 c2 ih2 t.
  case heq1: (ac_type tin c1) => [t1|] //=; case heq2: (ac_type tin c2) => [t2|] //=.
  case: ifP => // hsub [<-].
  by rewrite (ih1 _ heq1) (ih2 _ heq2) /= hsub.
move=> o cs hall t; case: ifP => // + [<-].
have haux : forall ts, all2 sub_octype ts (map (ac_type tin) cs) ->
                       all2 sub_octype ts (map (ac_type (tin ++ tin')) cs).
+ elim: cs hall => [ | c cs ih] hall [ | t0 ts] //=.
  move/List_Forall_inv: hall => [hc hcs] /andP [h1 h2]; rewrite (ih hcs ts h2) andbT.
  by move: h1; rewrite /sub_octype; case heq: (ac_type tin c) => [t1|] // hsub; rewrite (hc _ heq).
by move=> /haux ->.
Qed.

Lemma ac_wt_cat tin tin' c : ac_wt tin c -> ac_wt (tin ++ tin') c.
Proof. by rewrite /ac_wt => /eqP /ac_type_cat ->. Qed.

Lemma ac_ok_cat tin tin' c : ac_ok tin c -> ac_ok (tin ++ tin') c.
Proof. by move=> /andP [h1 h2]; rewrite /ac_ok (ac_wt_cat tin' h1). Qed.

Lemma all_ac_ok_cat tin tin' l : all (ac_ok tin) l -> all (ac_ok (tin ++ tin')) l.
Proof. by apply: sub_all => c; apply: ac_ok_cat. Qed.

(* The interpretation only depends on the arguments the condition reads. *)
Lemma interp_acond_cat (vs vs' : values) c :
  ac_below (size vs) c -> interp_acond (vs ++ vs') c = interp_acond vs c.
Proof.
elim/acond_ind_s: c => //=.
+ by move=> k hk; rewrite nth_cat hk.
+ by move=> o c ih h; rewrite ih.
+ by move=> o c1 ih1 c2 ih2 /andP [h1 h2]; rewrite ih1 // ih2.
move=> o cs hall hb.
suff -> : mapM (interp_acond (vs ++ vs')) cs = mapM (interp_acond vs) cs by [].
elim: cs hall hb => //= c cs ih /List_Forall_inv [hc hcs] /andP [h1 h2].
by rewrite hc // (ih hcs h2).
Qed.

Lemma acond_b_cat (vs vs' : values) c :
  ssrnat.leq (ac_max_var c) (size vs) -> acond_b (vs ++ vs') c = acond_b vs c.
Proof. by rewrite ac_max_var_below => h; rewrite /acond_b interp_acond_cat. Qed.

(* A well-typed total condition evaluates to a value on arguments of the
   announced types. *)
Lemma ac_type_ok tin (vs : values) c t :
  List.Forall2 (fun (t : ctype) v => exists x : sem_t t, v = to_val x) tin vs ->
  ac_total c ->
  ac_type tin c = Some t ->
  exists x : sem_t t, interp_acond vs c = ok (to_val x).
Proof.
move=> hall; elim/acond_ind_s: c t => /=.
1,2: by move=> x t _ [<-]; eexists.
+ move=> k t _; case: ifP => // hk [<-].
  by have [x hx] := Forall2_nth hall cbool undef_b hk; exists x; rewrite hx.
+ move=> o c ih t /andP [hto htot].
  case heq: (ac_type tin c) => [t1|] //=; case: ifP => // hsub [<-].
  have [x1 ->] := ih _ htot heq.
  have [y hy] := of_val_subctype_ok x1 hsub.
  by rewrite /= hy /=; eexists.
+ move=> o c1 ih1 c2 ih2 t /and3P [hto ht1 ht2].
  case heq1: (ac_type tin c1) => [t1|] //=; case heq2: (ac_type tin c2) => [t2|] //=.
  case: ifP => // /andP [hsub1 hsub2] [<-].
  have [x1 ->] := ih1 _ ht1 heq1; have [x2 ->] := ih2 _ ht2 heq2.
  have [y1 hy1] := of_val_subctype_ok x1 hsub1.
  have [y2 hy2] := of_val_subctype_ok x2 hsub2.
  by rewrite /= hy1 /= hy2 /=; eexists.
move=> o cs hall2 t htot; case: ifP => // hall3 [<-].
have {}htot : all ac_total cs by move: htot.
have haux : forall (ts : seq ctype) A (f : sem_prod ts (exec A)),
    sem_forall (fun r : exec A => is_ok r) ts f ->
    all2 sub_octype ts (map (ac_type tin) cs) ->
    exists2 l, mapM (interp_acond vs) cs = ok l & exists a, app_sopn ts f l = ok a.
+ move: hall3 => _; elim: cs hall2 htot => /= [ | c cs ih] hall2 htot [ | t0 ts] //= A f hf.
  + by move=> _; exists [::] => //; move/is_okP: hf.
  move/List_Forall_inv: hall2 => [hc hcs]; move: htot => /andP [htc htcs].
  move=> /andP [h1 h2].
  move: h1; rewrite /sub_octype; case heq: (ac_type tin c) => [t1|] // hsub.
  have [x ->] := hc _ htc heq.
  have [y hy] := of_val_subctype_ok x hsub.
  have [l -> [a ha]] := ih hcs htcs ts _ (f y) (hf y) h2.
  by exists (to_val x :: l) => //=; exists a; rewrite hy /=.
have [l -> [a ha]] := haux _ _ _ (sem_opN_safety_typed_ok o) hall3.
by rewrite /= ha /=; exists a.
Qed.

(* Interpreting a well-typed condition on the arguments or on their truncation
   at [tin] gives the same result (up to truncation of the result). *)
Lemma interp_acond_truncate tin vs vs' :
  mapM2 ErrType truncate_val tin vs = ok vs' ->
  forall c t, ac_type tin c = Some t ->
  match interp_acond vs c with
  | Ok v => exists2 v'', interp_acond vs' c = ok v'' & truncate_val t v = ok v''
  | Error e => interp_acond vs' c = Error e
  end.
Proof.
move=> /mapM2_Forall3 htr c.
elim/acond_ind_s: c => /=.
1,2: by move=> x t [<-]; eexists.
+ move=> n t; case: ifP => // hn [<-]; eexists; first reflexivity.
  by apply: (Forall3_nth htr).
+ move=> o c ih t; case heq: (ac_type tin c) => [t1|] //; case: ifP => // hsub [<-].
  have {ih} := ih _ heq; case: (interp_acond vs c) => [v | e] /=; last by move=> ->.
  move=> [v'' -> htr'] /=; rewrite (of_val_truncate_val hsub htr').
  by case: (of_val _ v) => //= x; eexists; first reflexivity; apply truncate_val_to_val.
+ move=> o c1 ih1 c2 ih2 t.
  case heq1: (ac_type tin c1) => [t1|] //; case heq2: (ac_type tin c2) => [t2|] //.
  case: ifP => // /andP [hsub1 hsub2] [<-].
  have {ih1} := ih1 _ heq1; case: (interp_acond vs c1) => [v1 | e] /=; last by move=> ->.
  move=> [v1'' -> htr1] /=.
  have {ih2} := ih2 _ heq2; case: (interp_acond vs c2) => [v2 | e] /=; last by move=> ->.
  move=> [v2'' -> htr2] /=.
  rewrite (of_val_truncate_val hsub1 htr1) (of_val_truncate_val hsub2 htr2).
  case: (of_val _ v1) => //= x1; case: (of_val _ v2) => //= x2.
  by eexists; first reflexivity; apply truncate_val_to_val.
move=> o cs hall t; case: ifP => // hall2 [<-].
have haux : forall (ts : seq ctype),
    all2 sub_octype ts (map (ac_type tin) cs) ->
    match mapM (interp_acond vs) cs with
    | Ok l => exists2 l', mapM (interp_acond vs') cs = ok l' &
              forall A (f : sem_prod ts (exec A)), app_sopn ts f l' = app_sopn ts f l
    | Error e => mapM (interp_acond vs') cs = Error e
    end.
+ move: hall2 => _; elim: cs hall => /= [ | c cs ih] hall [ | t0 ts] //=.
  + by move=> _; exists [::].
  move/List_Forall_inv: hall => [hc hcs] /andP [h1 h2].
  move: h1; rewrite /sub_octype; case heq: (ac_type tin c) => [t1|] // hsub.
  have {hc} := hc _ heq; case: (interp_acond vs c) => [v | e] /=; last by move=> ->.
  move=> [v'' -> htr'] /=.
  have {ih} := ih hcs ts h2.
  case: (mapM (interp_acond vs) cs) => [l | e] /=; last by move=> ->.
  move=> [l' -> hap]; exists (v'' :: l') => // A f /=.
  by rewrite (of_val_truncate_val hsub htr'); case: (of_val t0 v) => //= x; apply hap.
have {haux} := haux _ hall2.
case: (mapM (interp_acond vs) cs) => [l | e] /=; last by move=> ->.
move=> [l' -> hap] /=; rewrite (hap _ (sem_opN_safety_typed o)).
by case: (app_sopn _ _ l) => //= b; eexists.
Qed.

Lemma acond_truncate tin vs vs' c :
  mapM2 ErrType truncate_val tin vs = ok vs' ->
  ac_wt tin c ->
  interp_acond vs' c = interp_acond vs c.
Proof.
move=> htr /eqP hwt; have := interp_acond_truncate htr hwt.
case: (interp_acond vs c) => [v | e] //=.
by move=> [v'' -> /truncate_val_typeE [b -> ->]].
Qed.

Lemma acond_b_truncate tin vs vs' c :
  ac_ok tin c -> mapM2 ErrType truncate_val tin vs = ok vs' ->
  acond_b vs' c = acond_b vs c.
Proof. by move=> /ac_ok_wt h2 h1; rewrite /acond_b (acond_truncate h1 h2). Qed.

Lemma all_acond_b_truncate tin vs vs' safe :
  all (ac_ok tin) safe -> mapM2 ErrType truncate_val tin vs = ok vs' ->
  all (acond_b vs') safe = all (acond_b vs) safe.
Proof.
move=> hall htr; apply/eq_in_all => c hc.
by apply: (acond_b_truncate (allP hall _ hc) htr).
Qed.

(* -------------------------------------------------------------------- *)
(* ** Building conditions                                                *)

Definition sc_toint sg ws k    := IOp1 (Oint_of_word sg ws) (IVar k).
Definition sc_not c            := IOp1 Onot c.
Definition sc_and c1 c2        := IOp2 Oand c1 c2.
Definition sc_eqi c1 c2        := IOp2 (Oeq Op_int) c1 c2.
Definition sc_neqi c1 c2       := IOp2 (Oneq Op_int) c1 c2.
Definition sc_lei c1 c2        := IOp2 (Ole Cmp_int) c1 c2.
Definition sc_addi c1 c2       := IOp2 (Oadd Op_int) c1 c2.
Definition sc_muli c1 c2       := IOp2 (Omul Op_int) c1 c2.

Definition sc_in_range lo hi c := sc_and (sc_lei (IConst lo) c) (sc_lei c (IConst hi)).

Definition sc_not_zero ws k    := sc_neqi (sc_toint Unsigned ws k) (IConst 0).

(* The result of a [wint] operation fits in its type. *)
Definition sc_wi_range sg sz (c : acond) : acond :=
  signed (sc_in_range 0 (wmax_unsigned sz) c)
         (sc_in_range (wmin_signed sz) (wmax_signed sz) c) sg.

(* The divisor is not zero and, in the signed case, the division does not
   overflow. *)
Definition sc_divmod sg sz (k1 k2 : nat) : seq acond :=
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

Lemma acond_b_not_zero ws k (vs : values) (w : word ws) :
  nth undef_b vs k = Vword w -> acond_b vs (sc_not_zero ws k) = (w != 0%w).
Proof.
by move=> h;
  rewrite /acond_b /sc_not_zero /sc_neqi /sc_toint /= h /= truncate_word_u /=
          wunsigned_eqb0.
Qed.

Lemma acond_b_in_range vs lo hi c z :
  interp_acond vs c = ok (Vint z) ->
  acond_b vs (sc_in_range lo hi c) = (lo <=? z)%Z && (z <=? hi)%Z.
Proof. by rewrite /acond_b /sc_in_range /sc_and /sc_lei /= => ->. Qed.

Lemma acond_b_wi_range vs sg sz c z :
  interp_acond vs c = ok (Vint z) ->
  acond_b vs (sc_wi_range sg sz c) = signed in_uint_range in_sint_range sg sz z.
Proof.
by rewrite /sc_wi_range; case: sg => /= h; rewrite (acond_b_in_range _ _ h).
Qed.

(* ** Well-formedness of the conditions above *)

Lemma ac_type_op1E tin o c :
  ac_type tin (IOp1 o c) =
  if ac_type tin c is Some t1 then
    if subctype (eval_atype (type_of_op1 o).1) t1 then Some (eval_atype (type_of_op1 o).2)
    else None
  else None.
Proof. by []. Qed.

Lemma ac_type_op2E tin o c1 c2 :
  ac_type tin (IOp2 o c1 c2) =
  if ac_type tin c1 is Some t1 then
    if ac_type tin c2 is Some t2 then
      if subctype (eval_atype (type_of_op2 o).1.1) t1
         && subctype (eval_atype (type_of_op2 o).1.2) t2
      then Some (eval_atype (type_of_op2 o).2) else None
    else None
  else None.
Proof. by []. Qed.

Lemma ac_type_toint tin sg ws k :
  ssrnat.leq (S k) (size tin) -> nth cbool tin k = cword ws ->
  ac_type tin (sc_toint sg ws k) = Some cint.
Proof. by move=> h1 h2; rewrite /sc_toint ac_type_op1E /= h1 h2 /= cmp_le_refl. Qed.

Lemma ac_ok_not_zero tin ws k :
  ssrnat.leq (S k) (size tin) -> nth cbool tin k = cword ws ->
  ac_ok tin (sc_not_zero ws k).
Proof.
by move=> h1 h2; rewrite /ac_ok /ac_wt /sc_not_zero /sc_neqi ac_type_op2E
  (ac_type_toint Unsigned h1 h2) /=.
Qed.

(* -------------------------------------------------------------------- *)
(* ** The construction                                                   *)

(* The safety check: if one of the conditions fails, the operator raises the
   error it declares. *)
Definition check_safe (vs : values) (safe : seq acond) (err : error) : exec unit :=
  if all (acond_b vs) safe then ok tt else Error err.

Lemma check_safe_ok vs safe err : all (acond_b vs) safe -> check_safe vs safe err = ok tt.
Proof. by rewrite /check_safe => ->. Qed.

Lemma check_safe_okE vs safe err u : check_safe vs safe err = ok u -> all (acond_b vs) safe.
Proof. by rewrite /check_safe; case: ifP. Qed.

(* Computational analogue of [values.interp_safe_cond_ty_aux]: the arguments
   are collected, as values, in [vs] along the [sem_prod], and [P] is applied
   to them and to the result. *)
Fixpoint mk_semi_aux {T T'} (P : values -> T -> exec T') (vs : values) (tin : seq ctype) :
  sem_prod tin T -> sem_prod tin (exec T') :=
  match tin return sem_prod tin T -> sem_prod tin (exec T') with
  | [::] => fun t => P vs t
  | t :: tin => fun o v => @mk_semi_aux T T' P (rcons vs (to_val v)) tin (o v)
  end.
Arguments mk_semi_aux {T T'} P vs tin _ : assert.

(* An operator has exactly one output: the conditions are checked on the
   arguments, then the total semantics is returned. *)
Definition mk_sem_op (tin : seq ctype) (t : ctype) (safe : seq acond) (err : error)
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

Lemma sem_prod_ok_app_g {A B} tin (x : sem_prod tin A) (g : A -> B) :
  sem_prod_eq tin (sem_prod_ok tin (sem_prod_app x g))
                  (sem_prod_app x (fun a => ok (g a))).
Proof. by elim: tin x => //= t ts ih x v; apply: ih. Qed.

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
(* ** Generic properties of [mk_sem_op]                                  *)

(* The conditions of an operator are sufficient for its semantics to
   succeed. *)
Definition acond_ty tin T (safe : seq acond) (semi : sem_prod tin (exec T)) :=
  interp_safe_cond_ty_aux
    (fun vs r => all (acond_b vs) safe -> exists t, r = ok t) [::] semi.

Lemma mk_semi_aux_errty {T T'} (P : values -> T -> exec T') e vs tin (f : sem_prod tin T) :
  (forall vs t, P vs t <> Error e) ->
  sem_forall (fun r => r <> Error e) tin (mk_semi_aux P vs tin f).
Proof. by move=> h; elim: tin vs f => //= t tin ih vs f v; apply ih. Qed.

Lemma mk_semi_aux_safe {T T'} (P : values -> T -> exec T') (Q : values -> Prop) vs tin
    (f : sem_prod tin T) :
  (forall vs t, Q vs -> exists t', P vs t = ok t') ->
  interp_safe_cond_ty_aux (fun vs r => Q vs -> exists t, r = ok t) vs (mk_semi_aux P vs tin f).
Proof. by move=> h; elim: tin vs f => //= t tin ih vs f v; apply ih. Qed.

(* The values [mk_semi_aux] sees are the truncations of the arguments at
   [tin]. *)
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

(* [mk_sem_op] never raises a type error. *)
Lemma mk_sem_op_errty tin t safe err f :
  err <> ErrType ->
  sem_forall (fun r => r <> Error ErrType) tin (@mk_sem_op tin t safe err f).
Proof.
move=> herr; apply: mk_semi_aux_errty => vs r.
by rewrite /check_safe; case: ifP => //= _ [].
Qed.

(* If the conditions hold, [mk_sem_op] succeeds. *)
Lemma mk_sem_op_safe tin t safe err f :
  acond_ty safe (@mk_sem_op tin t safe err f).
Proof.
apply: mk_semi_aux_safe => vs r hall.
by rewrite (check_safe_ok err hall) /=; eexists; reflexivity.
Qed.

(* Complete description of a successful application of [mk_sem_op]. *)
Lemma mk_sem_opP tin t safe err f vs r :
  app_sopn tin (@mk_sem_op tin t safe err f) vs = ok r ->
  exists2 vs', mapM2 ErrType truncate_val tin vs = ok vs' &
    all (acond_b vs') safe /\ app_sopn tin (sem_prod_ok tin f) vs = ok r.
Proof.
rewrite /mk_sem_op => h; case: (mk_semi_auxP h) => vs' h1 [r0 h2]; rewrite cat0s.
case hu: (check_safe vs' safe err) => [u|e] //= [?]; subst r0.
by exists vs' => //; split => //; apply: check_safe_okE hu.
Qed.

Lemma mk_sem_op_safe_rev tin t safe err f vs r :
  app_sopn tin (@mk_sem_op tin t safe err f) vs = ok r ->
  exists2 vs', mapM2 ErrType truncate_val tin vs = ok vs' & all (acond_b vs') safe.
Proof. by move=> h; case: (mk_sem_opP h) => vs' h1 [h2 _]; exists vs'. Qed.

Lemma mk_semi_aux_id {T} (P : values -> T -> exec T) vs tin (f : sem_prod tin T) :
  (forall vs r, P vs r = ok r) ->
  sem_prod_eq tin (mk_semi_aux P vs tin f) (sem_prod_ok tin f).
Proof. by move=> h; elim: tin vs f => /= [vs f | t tin ih vs f v]; [apply h | apply ih]. Qed.

(* Without condition, [mk_sem_op] is the total semantics. *)
Lemma mk_sem_op_nil tin t err f :
  sem_prod_eq tin (@mk_sem_op tin t [::] err f) (sem_prod_ok tin f).
Proof. by apply: mk_semi_aux_id. Qed.

(* [mk_sem_op] reduces on a concrete signature: this is what makes the
   equality proofs provable by [reflexivity]. *)
Lemma mk_sem_op_reduces_example :
  sem_prod_eq [:: cint; cint]
    (@mk_sem_op [:: cint; cint] cint [::] ErrArith (fun v1 v2 => (v1 + v2)%Z))
    (sem_prod_ok [:: cint; cint] (fun v1 v2 => (v1 + v2)%Z)).
Proof. by move=> v1 v2. Qed.
