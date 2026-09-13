(* * Building blocks for the semantics of the operators.

   An operator is described by three independent pieces of data:
   - a total semantics, of type [sem_prod tin (sem_t tout)] ([sem_op_total.v]);
   - a list of conditions on its arguments, [seq acond], under which the usual
     (partial) semantics does not fail;
   - the error it raises when one of them does not hold.
   [mk_sem_op] assembles them into the usual [sem_prod tin (exec (sem_t tout))].

   The conditions of the operators themselves are in [op_semi.v]; this file
   only defines the language of conditions and the generic construction.

   An instruction is described the same way, by [mk_semi], with two
   differences: it has several outputs, some of which may be left undefined
   (one condition of [seq acond] per output says when an output is defined),
   and its safety conditions are the ones of [wsize.safe_cond], decided by
   [values.check_safe_cond]. *)

(* ** Imports and settings *)
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq eqtype ssralg.
From mathcomp Require Import word_ssrZ.
From elpi.apps Require Import derive.std.
From HB Require Import structures.
Require Export sem_op_total.
Require Import values.
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
  mapM2 ErrType truncate_val tin vs = ok vs' ->
  ac_ok tin c ->
  acond_b vs' c = acond_b vs c.
Proof. by move=> h1 /ac_ok_wt h2; rewrite /acond_b (acond_truncate h1 h2). Qed.

Lemma all_acond_b_truncate tin vs vs' safe :
  mapM2 ErrType truncate_val tin vs = ok vs' ->
  all (ac_ok tin) safe ->
  all (acond_b vs') safe = all (acond_b vs) safe.
Proof.
move=> htr hall; apply/eq_in_all => c hc.
by apply: (acond_b_truncate htr (allP hall _ hc)).
Qed.

(* -------------------------------------------------------------------- *)
(* ** Building conditions                                                *)

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

(* The condition that never holds. *)
Definition sc_false : acond := IBool false.

Definition sc_in_range lo hi c := sc_and (sc_lei (IConst lo) c) (sc_lei c (IConst hi)).

Definition sc_not_zero ws k    := sc_neqi (sc_toint Unsigned ws k) (IConst 0).

(* The [k]-th argument, a word of size [ws], is zero. *)
Definition sc_is_zero ws k     := sc_eqi (sc_toint Unsigned ws k) (IConst 0).

(* The [k]-th argument, read as an unsigned word of size [ws], is below [z]. *)
Definition sc_ult ws k z       := sc_lti (sc_toint Unsigned ws k) (IConst z).

(* The [k]-th argument, read as an unsigned word of size [ws], is at least [z]. *)
Definition sc_uge ws z k       := sc_lei (IConst z) (sc_toint Unsigned ws k).

(* The sum of the arguments [k1] and [k2], read as unsigned words of size
   [ws], is at most [z]. *)
Definition sc_uadd_le ws k1 k2 z :=
  sc_lei (sc_addi (sc_toint Unsigned ws k1) (sc_toint Unsigned ws k2)) (IConst z).

(* The [k]-th argument, read as an unsigned word of size [ws] modulo 32, is
   between [i] and [j]. *)
Definition sc_in_range_mod32 ws i j k :=
  sc_in_range i j (sc_modi Unsigned (sc_toint Unsigned ws k) (IConst 32)).

(* Every cell of the [k]-th argument, an array of [len] words of size [ws],
   is initialised. *)
Definition sc_all_init ws len k :=
  IAppN_safety (Ois_arr_init (arr_size ws len))
               [:: IVar k; IConst 0; IConst (arr_size ws len)].

(* The condition [c] is required only when the [g]-th argument, a boolean,
   is true. *)
Definition sc_guarded (g : nat) (c : acond) : acond := sc_or (sc_not (IVar g)) c.

(* The x86 division of the double word made of the arguments 0 (high part)
   and 1 (low part) by the argument 2: the divisor is not zero and the
   quotient fits in a word of size [sz]. *)
Definition sc_x86_division (sz : wsize) (sg : signedness) : acond :=
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

Lemma acond_b_is_zero ws k (vs : values) (w : word ws) :
  nth undef_b vs k = Vword w -> acond_b vs (sc_is_zero ws k) = (w == 0%w).
Proof.
by move=> h;
  rewrite /acond_b /sc_is_zero /sc_eqi /sc_toint /= h /= truncate_word_u /=
          wunsigned_eqb0.
Qed.

Lemma is_ok_mapM (eT aT bT : Type) (f : aT -> result eT bT) l :
  is_ok (mapM f l) = all (fun a => is_ok (f a)) l.
Proof.
elim: l => //= a l ih; case: (f a) => //= b.
by rewrite -ih; case: mapM.
Qed.

Lemma is_ok_get8 len (t : WArray.array len) i :
  is_ok (WArray.get8 t i) = WArray.in_bound t i && WArray.is_init t i.
Proof. by rewrite /WArray.get8; case: WArray.in_bound; case: WArray.is_init. Qed.

(* An array read succeeds exactly when all the cells it reads are in bounds
   and initialised. *)
Lemma is_ok_get ws len (t : WArray.array len) i :
  is_ok (WArray.get Unaligned AAscale ws t i)
  = all (fun k => WArray.in_bound t (i * wsize_size ws + k)%Z
                  && WArray.is_init t (i * wsize_size ws + k)%Z)
        (ziota 0 (wsize_size ws)).
Proof.
rewrite /WArray.get /CoreMem.read /assert /is_aligned_if /mk_scale.
have heq : forall k,
  get t (add (i * wsize_size ws)%Z k) = WArray.get8 t (i * wsize_size ws + k)%Z.
+ by move=> k; rewrite WArray.addE.
have -> :
  all (fun k => WArray.in_bound t (i * wsize_size ws + k)%Z
                && WArray.is_init t (i * wsize_size ws + k)%Z)
      (ziota 0 (wsize_size ws))
  = is_ok (mapM (fun k => get t (add (i * wsize_size ws)%Z k))
                (ziota 0 (wsize_size ws))).
+ by rewrite is_ok_mapM; apply: eq_all => k; rewrite heq is_ok_get8.
by case: mapM.
Qed.

(* The cells of an array of [len] words of size [ws] are all initialised
   exactly when each of the [len] words can be read. *)
Lemma all_init_getE ws len (t : WArray.array (arr_size ws len)) :
  all (WArray.is_init t) (ziota 0 (arr_size ws len))
  = all (fun i => is_ok (WArray.get Unaligned AAscale ws t i)) (ziota 0 len).
Proof.
have hws := wsize_size_pos ws.
apply/idP/idP => [/allP h | /allP h]; apply/allP.
+ move=> i; rewrite in_ziota !zify => hi.
  rewrite is_ok_get; apply/allP => k; rewrite in_ziota !zify => hk.
  split; first by rewrite arr_sizeE; Lia.nia.
  by apply: h; rewrite in_ziota !zify arr_sizeE; Lia.nia.
move=> j; rewrite in_ziota !zify => hj; rewrite arr_sizeE in hj.
have hq : (0 <= j / wsize_size ws < len)%Z.
+ by split; [apply: Z.div_pos | apply: Z.div_lt_upper_bound]; Lia.lia.
have hin : ((j / wsize_size ws)%Z \in ziota 0 len).
+ by rewrite in_ziota !zify; Lia.lia.
have hr := Z.mod_pos_bound j _ hws.
have hin2 : ((j mod wsize_size ws)%Z \in ziota 0 (wsize_size ws)).
+ by rewrite in_ziota !zify; Lia.lia.
move: (h _ hin); rewrite is_ok_get => /allP /(_ _ hin2) /andP [] _.
rewrite Z.mul_comm -Z.div_mod.
+ by [].
by Lia.lia.
Qed.

Lemma acond_b_all_init ws len k (vs : values) (t : WArray.array (arr_size ws len)) :
  nth undef_b vs k = Varr t ->
  acond_b vs (sc_all_init ws len k)
  = all (fun i => is_ok (WArray.get Unaligned AAscale ws t i)) (ziota 0 len).
Proof.
move=> h.
rewrite /acond_b /sc_all_init /= h /= arr_sizeE wsize8 Z.mul_1_l WArray.castK.
exact: all_init_getE.
Qed.

Local Opaque wbase.
Lemma acond_b_x86_division sz sg (vs : values) (hi lo dv : word sz) :
  nth undef_b vs 0 = Vword hi ->
  nth undef_b vs 1 = Vword lo ->
  nth undef_b vs 2 = Vword dv ->
  acond_b vs (sc_x86_division sz sg) =
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
move=> h0 h1 h2; rewrite /acond_b /sc_x86_division /wdwordu /wdwords.
case: sg => /=;
  rewrite /sc_and /sc_not /sc_or /sc_neqi /sc_lti /sc_addi /sc_muli /sc_divi /sc_toint /=
          h0 h1 h2 /= !truncate_word_u /=.
+ by rewrite !negb_or !Z.gtb_ltb.
by rewrite !negb_or !Z.gtb_ltb.
Qed.
Local Transparent wbase.

(* A guarded condition: when the guard is false the condition is not
   required, when it is true it amounts to the guarded condition. *)
Lemma acond_b_guarded (vs0 vs2 : values) (b : bool) (c : acond) (bb : bool) :
  ac_below (size vs0) c ->
  interp_acond vs0 c = ok (Vbool bb) ->
  acond_b (vs0 ++ Vbool b :: vs2) (sc_guarded (size vs0) c) = (~~ b) || bb.
Proof.
move=> hb hev; rewrite /acond_b /sc_guarded /sc_or /sc_not /=.
rewrite nth_cat ltnn subnn /=.
by rewrite (interp_acond_cat (Vbool b :: vs2) hb) hev /=.
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

Lemma ac_ok_is_zero tin ws k :
  ssrnat.leq (S k) (size tin) -> nth cbool tin k = cword ws ->
  ac_ok tin (sc_is_zero ws k).
Proof.
by move=> h1 h2; rewrite /ac_ok /ac_wt /sc_is_zero /sc_eqi ac_type_op2E
  (ac_type_toint Unsigned h1 h2) /=.
Qed.

Lemma ac_ok_all_init tin ws len k :
  ssrnat.leq (S k) (size tin) -> nth cbool tin k = carr (arr_size ws len) ->
  ac_ok tin (sc_all_init ws len k).
Proof.
move=> h1 h2; rewrite /ac_ok /ac_wt /sc_all_init /= h1 h2.
have -> : arr_size U8 (arr_size ws len) = arr_size ws len.
+ by rewrite arr_sizeE wsize8 Z.mul_1_l.
by rewrite /sub_octype /= !eqxx.
Qed.

Lemma ac_ok_x86_division tin sz sg :
  ssrnat.leq 3 (size tin) ->
  nth cbool tin 0 = cword sz -> nth cbool tin 1 = cword sz -> nth cbool tin 2 = cword sz ->
  ac_ok tin (sc_x86_division sz sg).
Proof.
move=> hs h0 h1 h2.
have l0 : ssrnat.leq 1 (size tin) by apply: ssrnat.leq_trans hs.
have l1 : ssrnat.leq 2 (size tin) by apply: ssrnat.leq_trans hs.
by rewrite /ac_ok /ac_wt /sc_x86_division; case: sg => /=;
  rewrite l0 l1 hs h0 h1 h2 /= !cmp_le_refl.
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

(* Two pointwise equal post-treatments give two equal semantics. *)
Lemma mk_semi_aux_eq {T T'} (P Q : values -> T -> exec T') vs tin (f : sem_prod tin T) :
  (forall vs t, P vs t = Q vs t) ->
  sem_prod_eq tin (mk_semi_aux P vs tin f) (mk_semi_aux Q vs tin f).
Proof. by move=> h; elim: tin vs f => /= [vs f | t tin ih vs f v]; [apply h | apply ih]. Qed.

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

Lemma mk_semi_aux_id {T} (P : values -> T -> exec T) vs tin (f : sem_prod tin T) :
  (forall vs r, P vs r = ok r) ->
  sem_prod_eq tin (mk_semi_aux P vs tin f) (sem_prod_ok tin f).
Proof. by move=> h; elim: tin vs f => /= [vs f | t tin ih vs f v]; [apply h | apply ih]. Qed.

(* Without condition, [mk_sem_op] is the total semantics. *)
Lemma mk_sem_op_nil tin t err f :
  sem_prod_eq tin (@mk_sem_op tin t [::] err f) (sem_prod_ok tin f).
Proof. by apply: mk_semi_aux_id. Qed.

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
(* ** The construction for the instructions                              *)

Definition is_ErrType (e : error) : bool := if e is ErrType then true else false.

(* The safety check of an instruction: its conditions are the old
   [wsize.safe_cond], decided by [values.check_safe_cond]; if one of them
   fails, the instruction raises the error it declares. *)
Definition check_safe_old (vs : values) (safe : seq safe_cond) (err : error) : exec unit :=
  if all (check_safe_cond vs) safe then ok tt else Error err.

(* The semantics of an instruction: the safety conditions are checked on the
   arguments, then the total semantics is filtered by the initialisation
   conditions, one per output. *)
Definition mk_semi (tin tout : seq ctype) (safe : seq acond) (err : error)
    (init : seq acond)
    (f : sem_prod tin (sem_tuple_t tout)) : sem_prod tin (exec (sem_tuple tout)) :=
  mk_semi_aux
    (fun vs t => Let _ := check_safe vs safe err in
                 ok (filter_tuple tout (map (acond_b vs) init) t))
    [::] tin f.
Arguments mk_semi {tin tout} safe err init f : assert.

(* -------------------------------------------------------------------- *)
(* ** Generic properties of [mk_semi]                                    *)

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

Lemma map_const_seq {A B : Type} (s : seq A) (c : B) :
  map (fun _ => c) s = nseq (size s) c.
Proof. by elim: s => //= x s ->. Qed.

(* -------------------------------------------------------------------- *)
(* ** Guarded conditions                                                 *)

(* The initialisation condition of a conditional instruction: the output keeps
   its previous value when the guard (the argument [g]) is false, so it is
   defined in that case too. *)
Definition cond_init (g : nat) (c : acond) : acond := sc_guarded g c.

Lemma ac_wt_cond_init tin tin' c :
  ac_wt tin c -> ac_wt (tin ++ cbool :: tin') (cond_init (size tin) c).
Proof.
rewrite /ac_wt /cond_init /sc_guarded /sc_or /sc_not /= => /eqP /ac_type_cat -> /=.
rewrite size_cat /= nth_cat ltnn subnn /=.
by have -> : (size tin < size tin + (size tin').+1)%nat by rewrite -addn1 leq_add2l.
Qed.

Lemma ac_total_cond_init g c : ac_total c -> ac_total (cond_init g c).
Proof. by move=> h; rewrite /cond_init /sc_guarded /= h. Qed.

Lemma ac_ok_cond_init tin tin' c :
  ac_ok tin c -> ac_ok (tin ++ cbool :: tin') (cond_init (size tin) c).
Proof. by move=> /andP [h1 h2]; rewrite /ac_ok ac_wt_cond_init // ac_total_cond_init. Qed.

Lemma acond_b_cond_init (vs0 vs2 : values) (b : bool) (c : acond) (bb : bool) :
  ac_below (size vs0) c ->
  interp_acond vs0 c = ok (Vbool bb) ->
  acond_b (vs0 ++ Vbool b :: vs2) (cond_init (size vs0) c) = (~~ b) || bb.
Proof. exact: acond_b_guarded. Qed.

Lemma cond_init_val (ts : seq ctype) (vs0 vs2 : values) (b : bool) (c : acond) :
  List.Forall2 (fun t v => exists x : sem_t t, v = to_val x) ts vs0 ->
  ac_total c -> ac_wt ts c ->
  acond_b (vs0 ++ Vbool b :: vs2) (cond_init (size ts) c) = (~~ b) || acond_b vs0 c.
Proof.
move=> hall htot hwt.
have hsz : size ts = size vs0 by apply: Forall2_size hall.
have [x hx] := ac_type_ok hall htot (eqP hwt).
have hbelow : ac_below (size vs0) c.
+ by rewrite -hsz; apply: (ac_type_below (eqP hwt)).
have -> : acond_b vs0 c = x by rewrite /acond_b hx.
by rewrite hsz; apply: (@acond_b_cond_init vs0 vs2 b c x hbelow hx).
Qed.

(* The mask seen by the generic construction under a guard: everything is
   defined when the guard is false, and the original mask otherwise. *)
Lemma cond_init_mask (ts : seq ctype) (vs0 : values) (init : seq acond) (b : bool)
    (vs2 : values) (n : nat) :
  List.Forall2 (fun t v => exists x : sem_t t, v = to_val x) ts vs0 ->
  all ac_total init -> all (ac_wt ts) init ->
  size init = n ->
  map (acond_b (rcons vs0 (Vbool b) ++ vs2)) (map (cond_init (size ts)) init)
  = (if b then map (acond_b vs0) init else nseq n true).
Proof.
move=> hall htot hwt hsz.
rewrite cat_rcons -map_comp.
have hpt : forall c, c \in init ->
    (acond_b (vs0 ++ Vbool b :: vs2) \o cond_init (size ts)) c
    = (~~ b) || acond_b vs0 c.
+ by move=> c hc; apply: (cond_init_val _ _ hall (allP htot _ hc) (allP hwt _ hc)).
case: b hpt => hpt.
+ by apply/eq_in_map => c hc; rewrite hpt.
by rewrite -hsz -map_const_seq; apply/eq_in_map => c hc; rewrite hpt.
Qed.

(* The safety conditions of a conditional instruction are the guarded ones:
   under a false guard they all hold, under a true one they amount to the
   conditions themselves. *)
Lemma acond_b_all_guarded (ts : seq ctype) (vs0 : values) (safe : seq acond)
    (b : bool) (vs2 : values) :
  List.Forall2 (fun t v => exists x : sem_t t, v = to_val x) ts vs0 ->
  all ac_total safe -> all (ac_wt ts) safe ->
  all (acond_b (rcons vs0 (Vbool b) ++ vs2)) (map (sc_guarded (size ts)) safe)
  = (if b then all (acond_b vs0) safe else true).
Proof.
move=> hall htot hwt; rewrite cat_rcons.
elim: safe htot hwt => [ | c safe ih] /=; first by case: b.
move=> /andP [] ht htot /andP [] hw hwt.
have hc := cond_init_val vs2 b hall ht hw; rewrite /cond_init in hc.
by rewrite hc (ih htot hwt); case: b {ih hc}.
Qed.

(* The safety conditions of a conditional instruction are the [Guarded] ones;
   under a false guard they all hold. *)
Lemma check_safe_cond_cat vs1 vs2 sc :
  ssrnat.leq (sc_needed_args sc) (size vs1) ->
  check_safe_cond (vs1 ++ vs2) sc = check_safe_cond vs1 sc.
Proof.
move=> h; apply/idP/idP => /check_safe_condP hc; apply/check_safe_condP.
+ by apply/(@interp_safe_cond_cat vs1 vs2 sc h).
by apply/(@interp_safe_cond_cat vs1 vs2 sc h).
Qed.

Lemma check_safe_cond_all_guarded (n : nat) (vs0 vs2 : values) (safe : seq safe_cond)
    (b : bool) :
  size vs0 = n ->
  all (fun sc => ssrnat.leq (sc_needed_args sc) n) safe ->
  all (check_safe_cond (rcons vs0 (Vbool b) ++ vs2)) (map (Guarded n) safe)
  = (if b then all (check_safe_cond vs0) safe else true).
Proof.
move=> hsz; rewrite cat_rcons -hsz.
elim: safe => [ | sc safe ih] /=.
+ by case: b.
move=> /andP [h1 h2]; rewrite nth_cat ltnn subnn /= (ih h2).
by case: b {ih} => //=; rewrite check_safe_cond_cat.
Qed.

Lemma sc_needed_args_guarded n sc :
  ssrnat.leq (sc_needed_args sc) n ->
  ssrnat.leq (sc_needed_args (Guarded n sc)) (S n).
Proof.
by move=> h; rewrite /= ssrnat.geq_max ssrnat.leqnn /=; apply: (ssrnat.leq_trans h).
Qed.

Lemma all_sc_needed_args_guarded n safe :
  all (fun sc => ssrnat.leq (sc_needed_args sc) n) safe ->
  all (fun sc => ssrnat.leq (sc_needed_args sc) (S n)) (map (Guarded n) safe).
Proof.
by move=> h; rewrite all_map; apply: sub_all h => sc; apply: sc_needed_args_guarded.
Qed.
