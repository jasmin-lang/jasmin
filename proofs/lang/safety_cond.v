(* * The language of the safety conditions.

   A safety condition is a boolean expression on the arguments of an
   operation: [IVar n] denotes its n-th argument and the expression operators
   themselves are used to compute. Conditions are interpreted with the
   *total* semantics of [sem_op_total.v], so that their meaning does not
   depend on the failures they are there to rule out.

   This file holds the language, its typing, the check [check_safe] that an
   operation performs on the values of its arguments, the library of the
   conditions the operators are made of ([sc_toint], [sc_in_range], ...), and
   the conditions of the array and memory accesses ([sc_get], [sc_set], ...).
   What is specific to the expression operators — which conditions each of
   them carries, and how the conditions guard the total semantics — is in
   [op_semi.v]. *)

(* ** Imports and settings *)
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq eqtype ssralg.
From mathcomp Require Import word_ssrZ.
Require Export sem_op_total.
Require Import values.
Import Utf8.

Local Open Scope Z_scope.
Local Open Scope seq_scope.

(* -------------------------------------------------------------------- *)
(* ** Conditions on the arguments of an operation                        *)

(* A boolean expression on the arguments of an operation. [IVar n] refers to
   the n-th argument. *)
Inductive safety_cond :=
  | IBool of bool
  | IConst of Z
  | IVar of nat
  | IOp1 of sop1 & safety_cond
  | IOp2 of sop2 & safety_cond & safety_cond
  (* The predicates of the safety conditions ([opN_safety]) all take three
     arguments, so they need no list and no nested inductive. *)
  | IOpN_safety of opN_safety & safety_cond & safety_cond & safety_cond.

(* The interpretation goes through the *total* semantics of the operators, so
   that it does not depend on [sem_sop1_typed]/[sem_sop2_typed] failing. *)
Fixpoint sem_safety_cond (vs : values) (c : safety_cond) : exec value :=
  match c with
  | IBool b => ok (Vbool b)
  | IConst z => ok (Vint z)
  | IVar n => ok (nth undef_b vs n)
  | IOp1 o c =>
    Let v := sem_safety_cond vs c in
    Let x := of_val _ v in
    ok (to_val (sem_sop1_total o x))
  | IOp2 o c1 c2 =>
    Let v1 := sem_safety_cond vs c1 in
    Let v2 := sem_safety_cond vs c2 in
    Let x1 := of_val _ v1 in
    Let x2 := of_val _ v2 in
    ok (to_val (sem_sop2_total o x1 x2))
  | IOpN_safety o c1 c2 c3 =>
    Let v1 := sem_safety_cond vs c1 in
    Let v2 := sem_safety_cond vs c2 in
    Let v3 := sem_safety_cond vs c3 in
    Let b := app_sopn _ (sem_opN_safety_typed o) [:: v1; v2; v3] in
    ok (Vbool b)
  end.

(* A condition that is not a boolean (in particular an ill-typed one, whose
   interpretation is an error) counts as false. *)
Definition safety_cond_holds (vs : values) (c : safety_cond) : bool :=
  if sem_safety_cond vs c is Ok (Vbool b) then b else false.

(* -------------------------------------------------------------------- *)
(* ** Typing                                                             *)

(* [safety_cond_type tin c] is the type of [c] when the arguments have types
   [tin]. An operator expecting an argument of type [t] accepts a
   sub-condition of type [t'] as soon as [subctype t t'], which is exactly
   what [of_val] accepts (for words: a word of at least that size). *)
Fixpoint safety_cond_type (tin : seq ctype) (c : safety_cond) : option ctype :=
  match c with
  | IBool _ => Some cbool
  | IConst _ => Some cint
  | IVar n => if (n < size tin)%nat then Some (nth cbool tin n) else None
  | IOp1 o c =>
    let t := type_of_op1 o in
    if safety_cond_type tin c is Some t1 then
      if subctype (eval_atype t.1) t1 then Some (eval_atype t.2) else None
    else None
  | IOp2 o c1 c2 =>
    let t := type_of_op2 o in
    if safety_cond_type tin c1 is Some t1 then
      if safety_cond_type tin c2 is Some t2 then
        if subctype (eval_atype t.1.1) t1 && subctype (eval_atype t.1.2) t2
        then Some (eval_atype t.2) else None
      else None
    else None
  | IOpN_safety o c1 c2 c3 =>
    if safety_cond_type tin c1 is Some t1 then
      if safety_cond_type tin c2 is Some t2 then
        if safety_cond_type tin c3 is Some t3 then
          if all2 subctype (map eval_atype (type_of_opN_safety o).1) [:: t1; t2; t3]
          then Some cbool else None
        else None
      else None
    else None
  end.

(* A well-typed condition is one that evaluates to a boolean. *)
Definition safety_cond_wt (tin : seq ctype) (c : safety_cond) : bool :=
  safety_cond_type tin c == Some cbool.

(* The variables of a condition are among the first [n] arguments. *)
Fixpoint safety_cond_below (n : nat) (c : safety_cond) : bool :=
  match c with
  | IBool _ | IConst _ => true
  | IVar k => (k < n)%nat
  | IOp1 _ c => safety_cond_below n c
  | IOp2 _ c1 c2 => safety_cond_below n c1 && safety_cond_below n c2
  | IOpN_safety _ c1 c2 c3 =>
    [&& safety_cond_below n c1, safety_cond_below n c2 & safety_cond_below n c3]
  end.

(* Extra arguments do not change the type of a condition: the descriptors that
   extend the arguments of an instruction ([mk_cond], the shifted variants)
   need this to keep their conditions well typed. *)
Lemma safety_cond_type_cat tin tin' c t :
  safety_cond_type tin c = Some t -> safety_cond_type (tin ++ tin') c = Some t.
Proof.
elim: c t => //=.
+ move=> k t; case: ifP => // hk [<-].
  by rewrite nth_cat hk size_cat (ltn_addr _ hk).
+ move=> o c ih t; case heq: (safety_cond_type tin c) => [t1|] //=; case: ifP => // hsub [<-].
  by rewrite (ih _ heq) /= hsub.
+ move=> o c1 ih1 c2 ih2 t.
  case heq1: (safety_cond_type tin c1) => [t1|] //=; case heq2: (safety_cond_type tin c2) => [t2|] //=.
  case: ifP => // hsub [<-].
  by rewrite (ih1 _ heq1) (ih2 _ heq2) /= hsub.
move=> o c1 ih1 c2 ih2 c3 ih3 t.
case heq1: (safety_cond_type tin c1) => [t1|] //=; case heq2: (safety_cond_type tin c2) => [t2|] //=.
case heq3: (safety_cond_type tin c3) => [t3|] //=.
case: ifP => // hsub [<-].
by rewrite (ih1 _ heq1) (ih2 _ heq2) (ih3 _ heq3) /= hsub.
Qed.

Lemma safety_cond_wt_cat tin tin' c :
  safety_cond_wt tin c -> safety_cond_wt (tin ++ tin') c.
Proof. by rewrite /safety_cond_wt => /eqP /safety_cond_type_cat ->. Qed.

(* -------------------------------------------------------------------- *)
(* ** Checking the conditions                                            *)

(* The safety check: in the [partial] mode, if one of the conditions fails,
   the operation raises the error it declares; in the [total] mode nothing is
   checked. *)
Definition check_safe {sm : SemMode} (vs : values) (safe : seq safety_cond) (err : error) :
    exec unit :=
  if is_total then ok tt
  else if all (safety_cond_holds vs) safe then ok tt else Error err.

(* The arguments are collected, as values, in [vs] along the [sem_prod], and
   [P] is applied to them and to the result. *)
Fixpoint mk_semi_aux {T T'} (P : values -> T -> exec T') (vs : values) (tin : seq ctype) :
  sem_prod tin T -> sem_prod tin (exec T') :=
  match tin return sem_prod tin T -> sem_prod tin (exec T') with
  | [::] => fun t => P vs t
  | t :: tin => fun o v => @mk_semi_aux T T' P (rcons vs (to_val v)) tin (o v)
  end.
Arguments mk_semi_aux {T T'} P vs tin _ : assert.

(* -------------------------------------------------------------------- *)
(* ** The library of conditions                                          *)

Definition sc_toint sg ws k    := IOp1 (Oint_of_word sg ws) (IVar k).
Definition sc_not c            := IOp1 Onot c.
Definition sc_and c1 c2        := IOp2 Oand c1 c2.
Definition sc_or c1 c2         := IOp2 Oor c1 c2.
Definition sc_eqi c1 c2        := IOp2 (Oeq Op_int) c1 c2.
Definition sc_neqi c1 c2       := IOp2 (Oneq Op_int) c1 c2.
Definition sc_lei c1 c2        := IOp2 (Ole Cmp_int) c1 c2.
Definition sc_addi c1 c2       := IOp2 (Oadd Op_int) c1 c2.
Definition sc_muli c1 c2       := IOp2 (Omul Op_int) c1 c2.
Definition sc_lti c1 c2        := IOp2 (Olt Cmp_int) c1 c2.
Definition sc_divi sg c1 c2    := IOp2 (Odiv sg Op_int) c1 c2.
Definition sc_modi sg c1 c2    := IOp2 (Omod sg Op_int) c1 c2.

Definition sc_in_range lo hi c := sc_and (sc_lei (IConst lo) c) (sc_lei c (IConst hi)).

Definition sc_not_zero ws k    := sc_neqi (sc_toint Unsigned ws k) (IConst 0).

(* The condition that never holds. *)
Definition sc_false : safety_cond := IBool false.

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

(* The [size] cells of the [ka]-th argument, an array of [len] bytes, that
   start at [start] are initialised. *)
Definition sc_is_arr_init (len : Z) (ka : nat) (start : safety_cond) (size : Z) : safety_cond :=
  IOpN_safety (Ois_arr_init len) (IVar ka) start (IConst size).

(* Every cell of the [k]-th argument, an array of [len] words of size [ws],
   is initialised. *)
Definition sc_all_init ws len k :=
  sc_is_arr_init (arr_size ws len) k (IConst 0) (arr_size ws len).

(* The condition [c] is required only when the [g]-th argument, a boolean,
   is true. *)
Definition sc_guarded (g : nat) (c : safety_cond) : safety_cond := sc_or (sc_not (IVar g)) c.

(* The result of a [wint] operation fits in its type. *)
Definition sc_wi_range sg sz (c : safety_cond) : safety_cond :=
  signed (sc_in_range 0 (wmax_unsigned sz) c)
         (sc_in_range (wmin_signed sz) (wmax_signed sz) c) sg.

(* The divisor is not zero and, in the signed case, the division does not
   overflow. *)
Definition sc_divmod sg sz (k1 k2 : nat) : seq safety_cond :=
  sc_not_zero sz k2 ::
  signed [::]
    [:: sc_not (sc_and (sc_eqi (sc_toint sg sz k1) (IConst (wmin_signed sz)))
                       (sc_eqi (sc_toint sg sz k2) (IConst (-1)))) ] sg.

(* The x86 division of the double word made of the arguments 0 (high part)
   and 1 (low part) by the argument 2: the divisor is not zero and the
   quotient fits in a word of size [sz]. *)
Definition sc_x86_division (sz : wsize) (sg : signedness) : safety_cond :=
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

(* -------------------------------------------------------------------- *)
(* ** The conditions of the array and memory accesses                    *)

(* The conditions checked in order, each with its own error: an array read
   raises [ErrAddrInvalid], [ErrOob] or [ErrAddrUndef] depending on which guard
   fails, so the single error of [check_safe] does not suffice for the
   accesses. *)
Definition check_safe_seq (vs : values) (scs : seq (safety_cond * error)) : exec unit :=
  foldM (fun ce _ => assert (safety_cond_holds vs ce.1) ce.2) tt scs.

(* The scaled index of an array access: [i * mk_scale aa ws], where [i] is the
   [k]-th argument. *)
Definition sc_arr_scaled (aa : arr_access) ws (k : nat) : safety_cond :=
  sc_muli (IVar k) (IConst (mk_scale aa ws)).

(* [is_aligned_if al (i * mk_scale aa ws) ws]: a scaled access is always
   aligned, and an unaligned access has nothing to check. *)
Definition sc_arr_aligned (al : aligned) (aa : arr_access) ws (k : nat) : safety_cond :=
  if (al == Unaligned) || (aa == AAscale) then IBool true
  else sc_eqi (sc_modi Unsigned (sc_arr_scaled aa ws k) (IConst (wsize_size ws))) (IConst 0).

(* The [size] bytes read or written at [i * mk_scale aa ws] are inside an array
   of length [len]. *)
Definition sc_arr_in_bound (len : Z) (aa : arr_access) ws (k : nat) (size : Z) : safety_cond :=
  sc_and (sc_lei (IConst 0) (sc_arr_scaled aa ws k))
         (sc_lei (sc_addi (sc_arr_scaled aa ws k) (IConst size)) (IConst len)).

(* They are moreover initialised, in the array argument [ka]. *)
Definition sc_arr_init (len : Z) (aa : arr_access) ws (ka k : nat) (size : Z) : safety_cond :=
  sc_is_arr_init len ka (sc_arr_scaled aa ws k) size.

(* The conditions of the four array accesses, on the arguments
   [:: Varr a; Vint i] (plus the written value, which no condition mentions). *)
Definition sc_get (len : Z) al aa ws : seq (safety_cond * error) :=
  [:: (sc_arr_aligned al aa ws 1, ErrAddrInvalid);
      (sc_arr_in_bound len aa ws 1 (wsize_size ws), ErrOob);
      (sc_arr_init len aa ws 0 1 (wsize_size ws), ErrAddrUndef) ].

Definition sc_set (len : Z) al aa ws : seq (safety_cond * error) :=
  [:: (sc_arr_aligned al aa ws 1, ErrAddrInvalid);
      (sc_arr_in_bound len aa ws 1 (wsize_size ws), ErrOob) ].

Definition sc_get_sub (len : Z) aa ws n : seq (safety_cond * error) :=
  [:: (sc_arr_in_bound len aa ws 1 (arr_size ws n), ErrOob) ].

Definition sc_set_sub (len : Z) aa ws n : seq (safety_cond * error) :=
  [:: (sc_arr_in_bound len aa ws 1 (arr_size ws n), ErrOob) ].

Section MEM_COND.

Context {pd : PointerData}.

(* The validity of a memory access depends on the memory, not only on the
   arguments: it is not a condition. Only the alignment of the pointer is a
   condition on the value of an argument. *)
Definition sc_mem_aligned (al : aligned) sz (k : nat) : safety_cond :=
  if al == Unaligned then IBool true
  else sc_eqi (sc_modi Unsigned (sc_toint Unsigned Uptr k) (IConst (wsize_size sz)))
              (IConst 0).

End MEM_COND.

(* -------------------------------------------------------------------- *)
(* ** What the conditions of the library compute                         *)

(* Only the lemmas that the descriptors need are here; the others are in
   [safety_cond_facts.v]. *)

Lemma safety_cond_holds_is_zero ws k (vs : values) (w : word ws) :
  nth undef_b vs k = Vword w -> safety_cond_holds vs (sc_is_zero ws k) = (w == 0%w).
Proof.
by move=> h;
  rewrite /safety_cond_holds /sc_is_zero /sc_eqi /sc_toint /= h /= truncate_word_u /=.
Qed.

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
  get t (add (i * wsize_size ws)%Z k) = WArray.get8 partial t (i * wsize_size ws + k)%Z.
+ by move=> k; rewrite WArray.addE.
have -> :
  all (fun k => WArray.in_bound t (i * wsize_size ws + k)%Z
                && WArray.is_init t (i * wsize_size ws + k)%Z)
      (ziota 0 (wsize_size ws))
  = is_ok (mapM (fun k => get t (add (i * wsize_size ws)%Z k))
                (ziota 0 (wsize_size ws))).
+ by rewrite is_ok_mapM; apply: eq_all => k; rewrite heq WArray.is_ok_get8.
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

Lemma safety_cond_holds_all_init ws len k (vs : values) (t : WArray.array (arr_size ws len)) :
  nth undef_b vs k = Varr t ->
  safety_cond_holds vs (sc_all_init ws len k)
  = all (fun i => is_ok (WArray.get Unaligned AAscale ws t i)) (ziota 0 len).
Proof.
move=> h.
rewrite /safety_cond_holds /sc_all_init /sc_is_arr_init /= h /= arr_sizeE wsize8 Z.mul_1_l
        WArray.castK.
exact: all_init_getE.
Qed.

(* -------------------------------------------------------------------- *)
(* ** The types of the conditions of the library                         *)

Lemma safety_cond_type_op1E tin o c :
  safety_cond_type tin (IOp1 o c) =
  if safety_cond_type tin c is Some t1 then
    if subctype (eval_atype (type_of_op1 o).1) t1 then Some (eval_atype (type_of_op1 o).2)
    else None
  else None.
Proof. by []. Qed.

Lemma safety_cond_type_op2E tin o c1 c2 :
  safety_cond_type tin (IOp2 o c1 c2) =
  if safety_cond_type tin c1 is Some t1 then
    if safety_cond_type tin c2 is Some t2 then
      if subctype (eval_atype (type_of_op2 o).1.1) t1
         && subctype (eval_atype (type_of_op2 o).1.2) t2
      then Some (eval_atype (type_of_op2 o).2) else None
    else None
  else None.
Proof. by []. Qed.

Lemma safety_cond_type_toint tin sg ws k :
  ssrnat.leq (S k) (size tin) -> nth cbool tin k = cword ws ->
  safety_cond_type tin (sc_toint sg ws k) = Some cint.
Proof. by move=> h1 h2; rewrite /sc_toint safety_cond_type_op1E /= h1 h2 /= cmp_le_refl. Qed.
