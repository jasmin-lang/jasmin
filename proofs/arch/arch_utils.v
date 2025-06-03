From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq eqtype.

Require Import
  type
  sem_type
  strings
  utils.
Require Import arch_decl.

(* -------------------------------------------------------------------- *)
(* Empty type for architectures that don't have one of the components of the
   declaration. *)

Variant empty : Set :=.

Definition of_empty (X : Type) (x : empty) : X :=
  match x with end.

#[export]
Instance eqTC_empty : eqTypeC empty :=
  {
    beq := of_empty _;
    ceqP := ltac:(done);
  }.

#[export]
Instance finTC_empty : finTypeC empty :=
  {
    cenum := [::];
    cenumP := ltac:(done);
  }.

#[export]
Instance empty_toS t : ToString t empty :=
  {
    category := "empty";
    to_string := of_empty _;
  }.


(* -------------------------------------------------------------------- *)
(* Instruction argument kinds. *)

Section WITH_ARCH.

Context
  {reg regx xreg rflag cond : Type}
  {ad : arch_decl reg regx xreg rflag cond}.

Definition ak_reg_reg : i_args_kinds :=
    [:: [:: [:: CAreg ]; [:: CAreg ] ] ].

Definition CAimm_sz sz := CAimm CAimmC_none sz.

Definition ak_reg_imm : i_args_kinds :=
    [:: [:: [:: CAreg ]; [:: CAimm_sz reg_size ] ] ].
Definition ak_reg_imm8 : i_args_kinds :=
  [:: [:: [:: CAreg ]; [:: CAimm_sz U8 ] ] ].
Definition ak_reg_imm16 : i_args_kinds :=
  [:: [:: [:: CAreg ]; [:: CAimm_sz U16 ] ] ].

Definition ak_reg_addr : i_args_kinds :=
  [:: [:: [:: CAreg ]; [:: CAmem true ] ] ].

Definition ak_reg_imm8_imm8 : i_args_kinds :=
  [:: [:: [:: CAreg ]; [:: CAimm_sz U8 ]; [:: CAimm_sz U8 ] ] ].

Definition ak_reg_reg_reg : i_args_kinds :=
    [:: [:: [:: CAreg ]; [:: CAreg ]; [:: CAreg ] ] ].
Definition ak_reg_reg_imm : i_args_kinds :=
    [:: [:: [:: CAreg ]; [:: CAreg ]; [:: CAimm_sz reg_size ] ] ].
Definition ak_reg_reg_imm8 : i_args_kinds :=
  [:: [:: [:: CAreg ]; [:: CAreg ]; [:: CAimm_sz U8 ] ] ].
Definition ak_reg_reg_imm16 : i_args_kinds :=
  [:: [:: [:: CAreg ]; [:: CAreg ]; [:: CAimm_sz U16 ] ] ].
Definition ak_reg_reg_imm8_imm8 : i_args_kinds :=
  [:: [:: [:: CAreg ]; [:: CAreg ]; [:: CAimm_sz U8 ]; [:: CAimm_sz U8 ] ] ].

Definition ak_reg_reg_reg_reg : i_args_kinds :=
  [:: [:: [:: CAreg ]; [:: CAreg ]; [:: CAreg ] ; [:: CAreg ] ] ].

End WITH_ARCH.


(* -------------------------------------------------------------------- *)
(* Instruction description transformations. *)

Notation beheadn n xs := (ssrnat.iter n behead xs).
Notation behead1 xs := (beheadn 1 xs). (* Helps inference with [idt_dropn]. *)
Notation behead2 xs := (beheadn 2 xs).
Notation behead3 xs := (beheadn 3 xs).
Notation behead4 xs := (beheadn 4 xs).

#[local]
Lemma size_beheadn {A B} {n : nat} {xs : seq A} {ys : seq B} :
  size xs == size ys ->
  size (beheadn n xs) == size (beheadn n ys).
Proof.
  move=> h.
  elim: n => // n'.
  rewrite !size_behead -!/(beheadn n' _).
  by move=> /eqP <-.
Qed.

#[local]
Lemma all_beheadn {A} {p : A -> bool} {n : nat} {xs : seq A} :
  all p xs ->
  all p (beheadn n xs).
Proof. move=> h. elim: n => // n'. exact: all_behead. Qed.

#[local]
Lemma all2_beheadn
  {A B} {p : A -> B -> bool} {n : nat} {xs : seq A} {ys : seq B} :
  all2 p xs ys ->
  all2 p (beheadn n xs) (beheadn n ys).
Proof. move=> h. elim: n => // n'. exact: all2_behead. Qed.

Definition semi_drop1
  {tin tout} (semi : sem_prod tin (exec (sem_tuple tout))) :
  sem_prod tin (exec (sem_tuple (behead1 tout))) :=
  behead_tuple semi.

Definition semi_drop2
  {tin tout} (semi : sem_prod tin (exec (sem_tuple tout))) :
  sem_prod tin (exec (sem_tuple (behead2 tout))) :=
  behead_tuple (behead_tuple semi).

Definition semi_drop3
  {tin tout} (semi : sem_prod tin (exec (sem_tuple tout))) :
  sem_prod tin (exec (sem_tuple (behead3 tout))) :=
  behead_tuple (behead_tuple (behead_tuple semi)).

Definition semi_drop4
  {tin tout} (semi : sem_prod tin (exec (sem_tuple tout))) :
  sem_prod tin (exec (sem_tuple (behead4 tout))) :=
  behead_tuple (behead_tuple (behead_tuple (behead_tuple semi))).

Lemma behead_tuple_errty tout (semi : sem_prod [::] (exec (sem_tuple tout))) :
  semi <> Error ErrType -> behead_tuple semi <> Error ErrType.
Proof.
  case: semi => [t _ | e h].
  + by rewrite /behead_tuple; case: tout t => //= t1 [ | t2 ts] //= [v1 v2].
  by case: tout h => // t1 [ | t2 ts] //= /[swap] -[->].
Qed.

Lemma behead_tuple_safe tout (semi : sem_prod [::] (exec (sem_tuple tout))) :
  (exists t, semi = ok t) -> exists t, behead_tuple semi = ok t.
Proof.
  move=> [t ->] {semi}; case: tout t => /=; eauto.
  move=> t1 [ | t2 ts] /=; eauto.
  move=> [v1 v2]; eauto.
Qed.

Lemma behead_tuple_app1 t ts tout (semi : sem_prod (t :: ts) (exec (sem_tuple tout))) (v : sem_t t) :
  behead_tuple semi v = behead_tuple (semi v).
Proof. by case: (tout) (semi) => // t1 [ | t2 ts_]. Qed.

Lemma semi_drop1_errty tin tout (semi : sem_prod tin (exec (sem_tuple tout))) :
  sem_forall (fun r => r <> Error ErrType) tin semi ->
  sem_forall (fun r => r <> Error ErrType) tin (semi_drop1 semi).
Proof.
  rewrite /semi_drop1; elim: tin semi => //=.
  + by apply behead_tuple_errty.
  move=> t ts hrec semi h v; rewrite behead_tuple_app1; apply/hrec/h.
Qed.

Lemma semi_drop1_sem_safe tin tout sc (semi : sem_prod tin (exec (sem_tuple tout))) :
  values.interp_safe_cond_ty sc semi ->
  values.interp_safe_cond_ty sc (semi_drop1 semi).
Proof.
  rewrite /values.interp_safe_cond_ty /semi_drop1.
  elim: tin (@nil values.value) semi => /= [ | t ts hrec] vs semi.
  + by move=> h /h; apply behead_tuple_safe.
  move=> h v; rewrite behead_tuple_app1; apply/hrec/h.
Qed.

Lemma semi_drop2_errty tin tout (semi : sem_prod tin (exec (sem_tuple tout))) :
  sem_forall (fun r => r <> Error ErrType) tin semi ->
  sem_forall (fun r => r <> Error ErrType) tin (semi_drop2 semi).
Proof.
  rewrite /semi_drop2; elim: tin semi => //=.
  + by move=> ??; do 2! apply behead_tuple_errty.
  move=> t ts hrec semi h v; rewrite !behead_tuple_app1; apply/hrec/h.
Qed.

Lemma semi_drop2_sem_safe tin tout sc (semi : sem_prod tin (exec (sem_tuple tout))) :
  values.interp_safe_cond_ty sc semi ->
  values.interp_safe_cond_ty sc (semi_drop2 semi).
Proof.
  rewrite /values.interp_safe_cond_ty /semi_drop2.
  elim: tin (@nil values.value) semi => /= [ | t ts hrec] vs semi.
  + by move=> h /h h1; do 2! apply behead_tuple_safe.
  move=> h v; rewrite !behead_tuple_app1; apply/hrec/h.
Qed.

Lemma semi_drop3_errty tin tout (semi : sem_prod tin (exec (sem_tuple tout))) :
  sem_forall (fun r => r <> Error ErrType) tin semi ->
  sem_forall (fun r => r <> Error ErrType) tin (semi_drop3 semi).
Proof.
  rewrite /semi_drop3; elim: tin semi => //=.
  + by move=> ??; do 3! apply behead_tuple_errty.
  move=> t ts hrec semi h v; rewrite !behead_tuple_app1; apply/hrec/h.
Qed.

Lemma semi_drop3_sem_safe tin tout sc (semi : sem_prod tin (exec (sem_tuple tout))) :
  values.interp_safe_cond_ty sc semi ->
  values.interp_safe_cond_ty sc (semi_drop3 semi).
Proof.
  rewrite /values.interp_safe_cond_ty /semi_drop3.
  elim: tin (@nil values.value) semi => /= [ | t ts hrec] vs semi.
  + by move=> h /h h1; do 3! apply behead_tuple_safe.
  move=> h v; rewrite !behead_tuple_app1; apply/hrec/h.
Qed.

Lemma semi_drop4_errty tin tout (semi : sem_prod tin (exec (sem_tuple tout))) :
  sem_forall (fun r => r <> Error ErrType) tin semi ->
  sem_forall (fun r => r <> Error ErrType) tin (semi_drop4 semi).
Proof.
  rewrite /semi_drop4; elim: tin semi => //=.
  + by move=> ??; do 4! apply behead_tuple_errty.
  move=> t ts hrec semi h v; rewrite !behead_tuple_app1; apply/hrec/h.
Qed.

Lemma semi_drop4_sem_safe tin tout sc (semi : sem_prod tin (exec (sem_tuple tout))) :
  values.interp_safe_cond_ty sc semi ->
  values.interp_safe_cond_ty sc (semi_drop4 semi).
Proof.
  rewrite /values.interp_safe_cond_ty /semi_drop4.
  elim: tin (@nil values.value) semi => /= [ | t ts hrec] vs semi.
  + by move=> h /h h1; do 4! apply behead_tuple_safe.
  move=> h v; rewrite !behead_tuple_app1; apply/hrec/h.
Qed.

#[local]
Lemma drop_eq_size {A B} {p} {n : nat} {xs : seq A} {ys : seq B} :
  p && (size xs == size ys) ->
  p && (size (beheadn n xs) == size (beheadn n ys)).
Proof. move=> /andP [-> hsize]. exact: size_beheadn. Qed.

Section WITH_ARCH.

Context
  {reg regx xreg rflag cond : Type}
  {ad : arch_decl reg regx xreg rflag cond}.

Notation idt_dropn semi_dropn semi_errtyp semi_safe :=
  (fun idt =>
     {|
       id_valid := id_valid idt;
       id_msb_flag := id_msb_flag idt;
       id_tin := id_tin idt;
       id_in := id_in idt;
       id_tout := beheadn _ (id_tout idt);
       id_out := beheadn _ (id_out idt);
       id_semi := semi_dropn (id_semi idt);
       id_nargs := id_nargs idt;
       id_args_kinds := id_args_kinds idt;
       id_eq_size := drop_eq_size (id_eq_size idt);
       id_tin_narr := id_tin_narr idt;
       id_tout_narr := all_beheadn (id_tout_narr idt);
       id_check_dest := all2_beheadn (id_check_dest idt);
       id_str_jas := id_str_jas idt;
       id_safe := id_safe idt;
       id_pp_asm := id_pp_asm idt;
       id_safe_wf := id_safe_wf idt;
       id_semi_errty := fun (h : id_valid idt) =>
          semi_errtyp (id_tin idt) (id_tout idt) (id_semi idt) (id_semi_errty (i:=idt) h);
       id_semi_safe  := fun (h : id_valid idt) =>
          semi_safe (id_tin idt) (id_tout idt) (id_safe idt) (id_semi idt) (id_semi_safe (i:=idt) h);
     |}).

Definition idt_drop1 : instr_desc_t -> instr_desc_t := idt_dropn semi_drop1 semi_drop1_errty semi_drop1_sem_safe.
Definition idt_drop2 : instr_desc_t -> instr_desc_t := idt_dropn semi_drop2 semi_drop2_errty semi_drop2_sem_safe.
Definition idt_drop3 : instr_desc_t -> instr_desc_t := idt_dropn semi_drop3 semi_drop3_errty semi_drop3_sem_safe.
Definition idt_drop4 : instr_desc_t -> instr_desc_t := idt_dropn semi_drop4 semi_drop4_errty semi_drop4_sem_safe.

Definition rtuple_drop5th
  {t0 t1 t2 t3 t4 : ctype}
  (xs : sem_tuple [:: t0; t1; t2; t3; t4 ]) :=
  let: (:: x0, x1, x2, x3 & x4 ) := xs in
  (:: x0, x1, x2 & x3 ).

End WITH_ARCH.
