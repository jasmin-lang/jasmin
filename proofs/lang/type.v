(* ** Imports and settings *)
From elpi.apps Require Import derive.std.
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool seq eqtype.
From mathcomp Require Import word_ssrZ.
From Coq Require Import ZArith Lia Wellfounded.
Require Import gen_map utils strings ident.
Require Export wsize.
Import Utf8.

(* ** Syntax
 * -------------------------------------------------------------------- *)

(* Low-level (or linear?) types, i.e. types that exist in architectures. *)
#[only(eqbOK)] derive
Variant ltype : Set :=
| lbool
| lword of wsize.

(* Dummy definitions *)
Definition is_ident (_:Ident.ident) := unit.
Definition is_ident_inhab (_:Ident.ident) := tt.

Definition ident_beq (i1 i2 : Ident.ident) := i1 == i2.
Lemma ident_beq_correct i : eqb_correct_on ident_beq i.
Proof. by move=> i' /eqP. Qed.
Lemma ident_beq_refl i : eqb_refl_on ident_beq i.
Proof. by apply /eqP. Qed.

(* The next line is a hack to circumvent a bug in [register_axiom], fixed in coq-elpi >= 3.3 *)
derive.eqbOK.register_axiom Cident.t is_ident is_ident_inhab ident_beq ident_beq_correct ident_beq_refl.
derive.eqbOK.register_axiom Ident.ident is_ident is_ident_inhab ident_beq ident_beq_correct ident_beq_refl.

(* ALVar case is for bound variables. We represent each bound variable by a pair
   (n, i), where n is a number and i an ident. On the Rocq side, only the number
   has a semantical meaning, the ident is just for printing.
   We use this representation (rather than just a var/Ident.ident), so that when
   we express a concrete signature in Rocq, we can compute with it. *)
#[only(eqbOK)] derive
Inductive array_length :=
| ALConst : Z -> array_length
| ALVar : Uint63.int -> Ident.ident -> array_length
| ALNeg : array_length -> array_length
| ALAdd : array_length -> array_length -> array_length
| ALSub : array_length -> array_length -> array_length
| ALMul : array_length -> array_length -> array_length
| ALDiv : signedness -> array_length -> array_length -> array_length
| ALMod : signedness -> array_length -> array_length -> array_length
| ALShl : array_length -> array_length -> array_length
| ALShr : array_length -> array_length -> array_length.

HB.instance Definition _ := hasDecEq.Build array_length array_length_eqb_OK.

(* Syntax types, i.e. types that appear in programs *)
#[only(eqbOK)] derive
Variant atype :=
| abool
| aint
| aarr of wsize & array_length
| aword of wsize.

(* Value types, i.e. types appearing in the semantics *)
#[only(eqbOK)] derive
Variant ctype : Set :=
| cbool
| cint
| carr  of Z
| cword of wsize.

Definition atype_of_ltype ty :=
  match ty with
  | lbool => abool
  | lword ws => aword ws
  end.

Definition ltype_of_atype ty :=
  match ty with
  | abool => Some lbool
  | aword ws => Some (lword ws)
  | _ => None
  end.

(* -------------------------------------------------------------------- *)
Notation lword8   := (lword U8).
Notation lword16  := (lword U16).
Notation lword32  := (lword U32).
Notation lword64  := (lword U64).
Notation lword128 := (lword U128).
Notation lword256 := (lword U256).

(* -------------------------------------------------------------------- *)
Notation ty_msf := (aword msf_size).
Notation cty_msf := (cword msf_size).

(* -------------------------------------------------------------------- *)
HB.instance Definition _ := hasDecEq.Build ltype ltype_eqb_OK.
HB.instance Definition _ := hasDecEq.Build atype atype_eqb_OK.
HB.instance Definition _ := hasDecEq.Build ctype ctype_eqb_OK.


(* ** Comparison
 * -------------------------------------------------------------------- *)

Definition bvar_cmp x1 x2 :=
  Lex (Uint63.compare x1.1 x2.1) (Ident.Mid.K.cmp x1.2 x2.2).
  (* for some reason, this works while the more natural [Tident.cmp i1 i2]
     produces ill-typed OCaml code *)
  (* I think it's just because this adds Obj.magic at extraction, so this
     works, but not for a good reason *)

Definition signedness_cmp sg1 sg2 :=
  match sg1, sg2 with
  | Signed, Signed => Eq
  | Signed, Unsigned => Lt
  | Unsigned, Unsigned => Eq
  | Unsigned, Signed => Gt
  end.

Fixpoint array_length_cmp al1 al2 :=
  match al1, al2 with
  | ALConst z1, ALConst z2 => Z.compare z1 z2
  | ALConst _, _ => Lt

  | ALVar _ _, ALConst _ => Gt
  | ALVar n1 x1, ALVar n2 x2 => bvar_cmp (n1, x1) (n2, x2)
  | ALVar _ _, _ => Lt

  | ALNeg _, (ALConst _ | ALVar _ _) => Gt
  | ALNeg al1, ALNeg al2 => array_length_cmp al1 al2
  | ALNeg _, _ => Lt

  | ALAdd _ _, (ALConst _ | ALVar _ _ | ALNeg _) => Gt
  | ALAdd al11 al12, ALAdd al21 al22 => Lex (array_length_cmp al11 al21) (array_length_cmp al12 al22)
  | ALAdd _ _, _ => Lt

  | ALSub _ _, (ALConst _ | ALVar _ _ | ALNeg _ | ALAdd _ _) => Gt
  | ALSub al11 al12, ALSub al21 al22 => Lex (array_length_cmp al11 al21) (array_length_cmp al12 al22)
  | ALSub _ _, _ => Lt

  | ALMul _ _, (ALDiv _ _ _ | ALMod _ _ _ | ALShl _ _ | ALShr _ _) => Lt
  | ALMul al11 al12, ALMul al21 al22 => Lex (array_length_cmp al11 al21) (array_length_cmp al12 al22)
  | ALMul _ _, _ => Gt

  | ALDiv _ _ _, (ALMod _ _ _ | ALShl _ _ | ALShr _ _) => Lt
  | ALDiv sg1 al11 al12, ALDiv sg2 al21 al22 => Lex (signedness_cmp sg1 sg2) (Lex (array_length_cmp al11 al21) (array_length_cmp al12 al22))
  | ALDiv _ _ _, _ => Gt

  | ALMod _ _ _, (ALShl _ _ | ALShr _ _) => Lt
  | ALMod sg1 al11 al12, ALMod sg2 al21 al22 => Lex (signedness_cmp sg1 sg2) (Lex (array_length_cmp al11 al21) (array_length_cmp al12 al22))
  | ALMod _ _ _, _ => Gt

  | ALShl _ _, ALShr _ _ => Lt
  | ALShl al11 al12, ALShl al21 al22 => Lex (array_length_cmp al11 al21) (array_length_cmp al12 al22)
  | ALShl _ _, _ => Gt

  | ALShr al11 al12, ALShr al21 al22 => Lex (array_length_cmp al11 al21) (array_length_cmp al12 al22)
  | ALShr _ _, _ => Gt
  end.

Instance intO : Cmp Uint63.compare.
Proof.
  constructor.
  + by move=> n1 n2; rewrite !Uint63.compare_spec; apply cmp_sym.
  + by move=> n1 n2 n3 c; rewrite !Uint63.compare_spec; apply cmp_ctrans.
  by move=> n1 n2; rewrite Uint63.compare_spec => /cmp_eq /Uint63.to_Z_inj.
Qed.

Existing Instance Ident.Mid.K.cmpO.

Instance bvarO : Cmp bvar_cmp.
Proof.
  constructor.
  + move=> [n1 x1] [n2 x2]; rewrite /bvar_cmp /=.
    by rewrite !Lex_lex; apply lex_sym; apply cmp_sym.
  + move=> [n1 x1] [n2 x2] [n3 x3]; rewrite /bvar_cmp /=.
    by rewrite !Lex_lex; apply lex_trans; apply cmp_ctrans.
  move=> [n1 x1] [n2 x2]; rewrite /bvar_cmp /=.
  by rewrite Lex_lex => /lex_eq /= [/cmp_eq <- /cmp_eq <-].
Qed.

Instance signednessO : Cmp signedness_cmp.
Proof.
  constructor.
  + by move=> [|] [|].
  + by move=> [|] [|] [|] //= ? [].
  by move=> [|] [|].
Qed.

Instance array_lengthO : Cmp array_length_cmp.
Proof.
  constructor.
  + elim=>
      [z1|n1 x1|al1 ih1|al11 ih1 al12 ih2|al11 ih1 al12 ih2|al11 ih1 al12 ih2|sg1 al11 ih1 al12 ih2|sg1 al11 ih1 al12 ih2|al11 ih1 al12 ih2|al11 ih1 al12 ih2]
      [z2|n2 x2|al2    |al21     al22    |al21     al22    |al21     al22    |sg2 al21     al22    |sg2 al21     al22    |al21     al22    |al21     al22    ] //=.
    + by apply cmp_sym.
    + by apply cmp_sym.
    + by rewrite !Lex_lex; apply lex_sym.
    + by rewrite !Lex_lex; apply lex_sym.
    + by rewrite !Lex_lex; apply lex_sym.
    + rewrite !Lex_lex; apply lex_sym; first by apply cmp_sym.
      by apply lex_sym.
    + rewrite !Lex_lex; apply lex_sym; first by apply cmp_sym.
      by apply lex_sym.
    + by rewrite !Lex_lex; apply lex_sym.
    by rewrite !Lex_lex; apply lex_sym.
  + elim=>
      [z1|n1 x1|al1 ih1|al11 ih1 al12 ih2|al11 ih1 al12 ih2|al11 ih1 al12 ih2|sg1 al11 ih1 al12 ih2|sg1 al11 ih1 al12 ih2|al11 ih1 al12 ih2|al11 ih1 al12 ih2]
      [z2|n2 x2|al2    |al21     al22    |al21     al22    |al21     al22    |sg2 al21     al22    |sg2 al21     al22    |al21     al22    |al21     al22    ]
      [z3|n3 x3|al3    |al31     al32    |al31     al32    |al31     al32    |sg3 al31     al32    |sg3 al31     al32    |al31     al32    |al31     al32    ] //=;
     try (by apply ctrans_Eq); eauto using ctrans_Lt, ctrans_Gt; try apply cmp_ctrans.
    + by rewrite !Lex_lex; apply lex_trans; eauto.
    + by rewrite !Lex_lex; apply lex_trans; eauto.
    + by rewrite !Lex_lex; apply lex_trans; eauto.
    + rewrite !Lex_lex; apply lex_trans.
      + by apply cmp_ctrans.
      apply lex_trans; eauto.
    + rewrite !Lex_lex; apply lex_trans.
      + by apply cmp_ctrans.
      apply lex_trans; eauto.
    + by rewrite !Lex_lex; apply lex_trans; eauto.
    by rewrite !Lex_lex; apply lex_trans; eauto.
  elim=>
      [z1|n1 x1|al1 ih1|al11 ih1 al12 ih2|al11 ih1 al12 ih2|al11 ih1 al12 ih2|sg1 al11 ih1 al12 ih2|sg1 al11 ih1 al12 ih2|al11 ih1 al12 ih2|al11 ih1 al12 ih2]
      [z2|n2 x2|al2    |al21     al22    |al21     al22    |al21     al22    |sg2 al21     al22    |sg2 al21     al22    |al21     al22    |al21     al22    ] //=.
  + by move=> /cmp_eq ->.
  + by move=> /cmp_eq [<- <-].
  + by move=> /ih1 <-.
  + by rewrite Lex_lex => /lex_eq /= [/ih1 <- /ih2 <-].
  + by rewrite Lex_lex => /lex_eq /= [/ih1 <- /ih2 <-].
  + by rewrite Lex_lex => /lex_eq /= [/ih1 <- /ih2 <-].
  + by rewrite !Lex_lex => /lex_eq /= [/cmp_eq <- /lex_eq /= [/ih1 <- /ih2 <-]].
  + by rewrite !Lex_lex => /lex_eq /= [/cmp_eq <- /lex_eq /= [/ih1 <- /ih2 <-]].
  + by rewrite Lex_lex => /lex_eq /= [/ih1 <- /ih2 <-].
  by rewrite Lex_lex => /lex_eq /= [/ih1 <- /ih2 <-].
Qed.

Definition atype_cmp t t' :=
  match t, t' with
  | abool   , abool         => Eq
  | abool   , _             => Lt

  | aint    , abool         => Gt
  | aint    , aint          => Eq
  | aint    , _             => Lt

  | aword _ , aarr _ _      => Lt
  | aword w , aword w'      => wsize_cmp w w'
  | aword _ , _             => Gt

  | aarr ws al , aarr ws' al' => Lex (wsize_cmp ws ws') (array_length_cmp al al')
  | aarr _ _  , _           => Gt
  end.

#[global]
Instance atypeO : Cmp atype_cmp.
Proof.
  constructor.
  + case => [||ws al|w] [||ws' al'|w'] //=.
    + by rewrite !Lex_lex lex_sym //=; apply cmp_sym.
    by apply cmp_sym.
  + move=> y x; case: x y=> [||ws al|w] [||ws' al'|w'] [||ws'' al''|w''] c //=;
       try (by apply ctrans_Eq);eauto using ctrans_Lt, ctrans_Gt.
    + by rewrite !Lex_lex; apply lex_trans; apply cmp_ctrans.
    by apply cmp_ctrans.
  case=> [||al ws|w] [||al' ws'|w'] //=.
  + by rewrite Lex_lex => /lex_eq /= [/cmp_eq <- /cmp_eq <-].
  by move=> /cmp_eq <-.
Qed.

Module CmpAtype.

  Definition t : eqType := atype.

  Definition cmp : t -> t -> comparison := atype_cmp.

  Definition cmpO : Cmp cmp := atypeO.

End CmpAtype.

Module CEDecAtype.

  Definition t : eqType := atype.

  Definition eq_dec (t1 t2:t) : {t1 = t2} + {True} :=
    match t1 as t return {t = t2} + {True} with
    | abool =>
      match t2 as t0 return {abool = t0} + {True} with
      | abool => left (erefl abool)
      | _     => right I
      end
    | aint =>
      match t2 as t0 return {aint = t0} + {True} with
      | aint => left (erefl aint)
      | _     => right I
      end
    | aarr ws1 al1 =>
      match t2 as t0 return {aarr ws1 al1 = t0} + {True} with
      | aarr ws2 al2 =>
        match wsize_eq_dec ws1 ws2 with
        | left eqw =>
          match array_length_eqb_OK_sumbool al1 al2 with
          | left eqn => left (f_equal2 aarr eqw eqn)
          | right _ => right I
          end
        | _ => right I
        end
      | _          => right I
      end
    | aword w1 =>
      match t2 as t0 return {aword w1 = t0} + {True} with
      | aword w2 =>
        match wsize_eq_dec w1 w2 with
        | left eqw => left (f_equal aword eqw)
        | right _ => right I
        end
      | _     => right I
      end
    end.

  Lemma eq_dec_r t1 t2 tt: eq_dec t1 t2 = right tt -> t1 != t2.
  Proof.
    case: tt;case:t1 t2=> [||ws al|w] [||ws' al'|w'] //=.
    + case: wsize_eq_dec => eqw.
      + case: array_length_eqb_OK_sumbool => // hneq.
        by move=> _; apply /eqP => -[].
      by move=> _; apply/eqP => -[].
    case: wsize_eq_dec => // eqw.
    by move=> _;apply /eqP;congruence.
  Qed.

End CEDecAtype.

Module Mt := DMmake CmpAtype CEDecAtype.

Declare Scope mtype_scope.
Delimit Scope mtype_scope with mt.
Notation "m .[ x ]" := (@Mt.get _ m x) : mtype_scope.
Notation "m .[ x  <- v ]" := (@Mt.set _ m x v) : mtype_scope.
Arguments Mt.get P m%_mtype_scope k.
Arguments Mt.set P m%_mtype_scope k v.

(* A bit hacky: to avoid some nameclashes with the names generated
   by elpi.derive, we put these definitions in a module.
   A better solution would be to change elpi.derive to ensure that all
   names obey the "prefix" parameter. *)
Module Export OtherDefs.

Definition is_abool t := if t is abool then true else false.

Lemma is_aboolP t : reflect (t=abool) (is_abool t).
Proof. by case: t => /=; constructor. Qed.

Definition is_aword t := if t is aword _ then true else false.

Definition is_aarr t := if t is aarr _ _ then true else false.

Definition is_not_aarr t := ~~is_aarr t.

Lemma is_aarrP ty : reflect (exists ws n, ty = aarr ws n) (is_aarr ty).
Proof. by case: ty; constructor; eauto => -[?] [?]. Qed.

Definition is_word_type (t:atype) :=
  if t is aword sz then Some sz else None.

Lemma is_word_typeP ty ws :
  is_word_type ty = Some ws -> ty = aword ws.
Proof. by case: ty => //= w [->]. Qed.

Definition is_cword t := if t is cword _ then true else false.
Definition is_carr t := if t is carr _ then true else false.
Definition is_not_carr t := ~~ is_carr t.

End OtherDefs.

(* -------------------------------------------------------------------- *)
Definition arr_size (ws:wsize) (len:Z)  := 
   (wsize_size ws * len)%Z.

Lemma arr_sizeE ws len : arr_size ws len = (wsize_size ws * len)%Z.
Proof. done. Qed.

Lemma gt0_arr_size ws len : (0 < len)%Z -> (0 < arr_size ws len)%Z.
Proof. by move=> ?; rewrite arr_sizeE; apply Z.mul_pos_pos. Qed.

Opaque arr_size.

Definition env_t := Uint63.int -> Z.
Definition empty_env : env_t := fun _ => 0%Z.

Section EVAL.

Context (env : env_t).

(* FIXME: duplicated from sem_op_typed *)
Definition zlsl (x i : Z) : Z :=
  if (0 <=? i)%Z then (x * 2^i)%Z
  else (x / 2^(-i))%Z.

Definition zasr (x i : Z) : Z :=
  zlsl x (-i).

(* FIXME: duplicated from word *)
Definition signed {A:Type} (fu fs:A) s :=
  match s with
  | Unsigned => fu
  | Signed => fs
  end.

Fixpoint eval_rec (al:array_length) : Z :=
  match al with
  | ALConst z => z
  | ALVar n _ => env n
  | ALNeg al => - eval_rec al
  | ALAdd al1 al2 => eval_rec al1 + eval_rec al2
  | ALSub al1 al2 => eval_rec al1 - eval_rec al2
  | ALMul al1 al2 => eval_rec al1 * eval_rec al2
  | ALDiv sg al1 al2 => signed Z.div Z.quot sg (eval_rec al1) (eval_rec al2)
  | ALMod sg al1 al2 => signed Z.modulo Z.rem sg (eval_rec al1) (eval_rec al2)
  | ALShl al1 al2 => zlsl (eval_rec al1) (eval_rec al2)
  | ALShr al1 al2 => zasr (eval_rec al1) (eval_rec al2)
  end.

(* All negative numbers are mapped to 0%Z, for readability. *)
Definition eval al :=
  let z := eval_rec al in
(*   if (0 <? z)%Z then z else 0%Z. *)
  z.

Definition eval_atype ty :=
  match ty with
  | abool => cbool
  | aint => cint
  | aarr ws len => carr (arr_size ws (eval len))
  | aword ws => cword ws
  end.

Definition eval_ltype ty :=
  match ty with
  | lbool => cbool
  | lword ws => cword ws
  end.

End EVAL.

(* We define a polynomial equality checker. This is what ring or lia know how to do.
   We could probably call functions coming from their implementations instead. *)

Fixpoint size_poly poly : nat :=
  match poly with
  | ALConst _ | ALVar _ _ => 1
  | ALNeg p => S (size_poly p)
  | ALAdd p1 p2 | ALSub p1 p2 | ALMul p1 p2 =>
    size_poly p1 + size_poly p2
  | ALDiv _ _ _ | ALMod _ _ _ | ALShl _ _ | ALShr _ _ => 1
  end.

Lemma lt0_size_poly p : (0 < size_poly p)%nat.
Proof. by elim: p => /=; lia. Qed.

Fixpoint size_Mul poly : nat :=
  match poly with
  | ALConst _ | ALVar _ _ => 0
  | ALNeg p => size_Mul p
  | ALAdd p1 p2 | ALSub p1 p2 => size_Mul p1 + size_Mul p2
  | ALMul p1 p2 => 1 + size_Mul p1 + size_Mul p2
  | ALDiv _ _ _ | ALMod _ _ _ | ALShl _ _ | ALShr _ _ => 0
  end.

Fixpoint left_Mul_under_Mul poly : nat :=
  match poly with
  | ALConst _ | ALVar _ _ => 0
  | ALNeg p => left_Mul_under_Mul p
  | ALAdd p1 p2 | ALSub p1 p2 => left_Mul_under_Mul p1 + left_Mul_under_Mul p2
  | ALMul p1 p2 => size_Mul p1 + left_Mul_under_Mul p2
  | ALDiv _ _ _ | ALMod _ _ _ | ALShl _ _ | ALShr _ _ => 0
  end.

Fixpoint insert_mono x mono :=
  match mono with
  | [::] => [:: x]
  | x2 :: mono =>
    match bvar_cmp x x2 with
    | Lt | Eq => x :: x2 :: mono
    | Gt => x2 :: insert_mono x mono
    end
  end.

Fixpoint insert_term cm terms :=
  match terms with
  | [::] => [:: cm]
  | cm2 :: terms =>
    match List.list_compare bvar_cmp (snd cm) (snd cm2) with
    | Lt => cm :: cm2 :: terms
    | Eq => let new_coeff := fst cm + fst cm2 in if new_coeff =? 0 then terms else (new_coeff, snd cm) :: terms
    | Gt => cm2 :: insert_term cm terms
    end
  end%Z.
Definition insert_term_nice cm terms :=
  if (fst cm =? 0)%Z then terms else insert_term cm terms.

Definition lt_lex :=
  Relation_Operators.slexprod _ _ lt lt.

Definition wf_lt_lex := wf_slexprod _ _ _ _ lt_wf lt_wf.

Program Fixpoint expanded_form_aux terms coeff mono al (ACC: Acc lt_lex (size_poly al, left_Mul_under_Mul al)) {struct ACC} :=
  match al with
  | ALConst z =>
    let coeff := (z * coeff)%Z in
    insert_term_nice (coeff, mono) terms
  | ALVar n i =>
    let mono := insert_mono (n, i) mono in
    insert_term_nice (coeff, mono) terms
  | ALNeg al =>
    @expanded_form_aux terms (-coeff) mono al (Acc_inv ACC _)
  | ALAdd al1 al2 =>
    @expanded_form_aux (@expanded_form_aux terms coeff mono al1 (Acc_inv ACC _)) coeff mono al2 (Acc_inv ACC _)
  | ALSub al1 al2 =>
    @expanded_form_aux (@expanded_form_aux terms coeff mono al1 (Acc_inv ACC _)) (-coeff) mono al2 (Acc_inv ACC _)
  | ALMul al1 al2 =>
    match al1 with
    | ALConst z =>
      let coeff := (z*coeff)%Z in
      @expanded_form_aux terms coeff mono al2 (Acc_inv ACC _)
    | ALVar n i =>
      let mono := insert_mono (n, i) mono in
      @expanded_form_aux terms coeff mono al2 (Acc_inv ACC _)
    | ALNeg al1 =>
      @expanded_form_aux terms (-coeff) mono (ALMul al1 al2) (Acc_inv ACC _)
    | ALAdd al11 al12 =>
      @expanded_form_aux (@expanded_form_aux terms coeff mono (ALMul al11 al2) (Acc_inv ACC _)) coeff mono (ALMul al12 al2) (Acc_inv ACC _)
    | ALSub al11 al12 => 
      @expanded_form_aux (@expanded_form_aux terms coeff mono (ALMul al11 al2) (Acc_inv ACC _)) (-coeff) mono (ALMul al12 al2) (Acc_inv ACC _)
    | ALMul al11 al12 =>
      @expanded_form_aux terms coeff mono (ALMul al11 (ALMul al12 al2)) (Acc_inv ACC _)
    | ALDiv _ _ _ | ALMod _ _ _ | ALShl _ _ | ALShr _ _ => [::] (* dummy case *)
    end
  | ALDiv _ _ _ | ALMod _ _ _ | ALShl _ _ | ALShr _ _ => [::] (* dummy case *)
  end%Z.
Next Obligation. by left => /=; lia. Qed.
Next Obligation. by left => /=; have := lt0_size_poly al2; lia. Qed.
Next Obligation. by left => /=; have := lt0_size_poly al1; lia. Qed.
Next Obligation. by left => /=; have := lt0_size_poly al2; lia. Qed.
Next Obligation. by left => /=; have := lt0_size_poly al1; lia. Qed.
Next Obligation. by left => /=; lia. Qed.
Next Obligation. by left => /=; lia. Qed.
Next Obligation. by left => /=; lia. Qed.
Next Obligation. by left => /=; have := lt0_size_poly al12; lia. Qed.
Next Obligation. by left => /=; have := lt0_size_poly al11; lia. Qed.
Next Obligation. by left => /=; have := lt0_size_poly al12; lia. Qed.
Next Obligation. by left => /=; have := lt0_size_poly al11; lia. Qed.
Final Obligation. by rewrite Nat.add_assoc; right => /=; lia. Qed.

Program Definition expanded_form al :=
  @expanded_form_aux [::] 1 [::] al (wf_lt_lex _).

Fixpoint is_poly al :=
  match al with
  | ALConst _ | ALVar _ _ => true
  | ALNeg al => is_poly al
  | ALAdd al1 al2 | ALSub al1 al2 | ALMul al1 al2 => is_poly al1 && is_poly al2
  | ALDiv _ _ _ | ALMod _ _ _ | ALShl _ _ | ALShr _ _ => false
  end.

Lemma uint_eqb_spec : Equality.axiom Uint63.eqb.
Proof.
  move=> x y; apply (iffP (Uint63.eqbP _ _)); last by move=> ->.
  by move=> /Uint63.to_Z_inj.
Qed.

HB.instance Definition _ := hasDecEq.Build Uint63.int uint_eqb_spec.

(* advanced check when these are polynomials, otherwise just [==] *)
Definition compare_array_length '(ws, al) '(ws', al') :=
  if is_poly al && is_poly al' then
    let ef := expanded_form (ALMul (ALConst (wsize_size ws)) al) in
    let ef' := expanded_form (ALMul (ALConst (wsize_size ws')) al') in
    ef == ef'
  else (ws == ws') && (al == al').

Definition convertible (t t' : atype) :=
  match t with
  | aarr ws al =>
    if t' is aarr ws' al' then compare_array_length (ws, al) (ws', al') else false
  | _ => t == t'
  end.

Lemma convertible_refl t : convertible t t.
Proof.
  case: t => //= ws len.
  by case: ifP => _; rewrite !eq_refl.
Qed.
#[global]
Hint Resolve convertible_refl : core.

Lemma convertible_sym ty1 ty2 : convertible ty1 ty2 -> convertible ty2 ty1.
Proof.
  case: ty1 ty2 => [||ws1 al1|ws1] [||ws2 al2|ws2] //=.
  + by rewrite eq_sym (eq_sym ws1) (eq_sym al1) andbC.
  by rewrite eq_sym.
Qed.

Lemma convertible_trans ty2 ty1 ty3 :
  convertible ty1 ty2 -> convertible ty2 ty3 -> convertible ty1 ty3.
Proof.
  case: ty1 ty2 ty3 => [||ws1 al1|ws1] [||ws2 al2|ws2] [||ws3 al3|ws3] //=.
  + case h1: is_poly => /=.
    + case h2: is_poly => /=.
      + move=> /eqP ->.
        case h3: is_poly => //=.
        by move=> /andP [_ /eqP]; congruence.
      by move=> /andP [_ /eqP]; congruence.
    move=> /andP [/eqP heq1 /eqP heq2].
    by move: h1; rewrite heq1 heq2 => -> /=.
  by move=> /eqP ->.
Qed.

Fixpoint eval_mono (env : env_t) (mono : list (Uint63.int * Ident.ident)) : Z :=
  match mono with
  | [::] => 1
  | x :: mono => env x.1 * eval_mono env mono
  end.

Fixpoint eval_expand (env : env_t) terms : Z :=
  match terms with
  | [::] => 0
  | (count, mono) :: terms =>
    count * eval_mono env mono + eval_expand env terms
  end.

Lemma insert_mono_correct env x mono :
  eval_mono env (insert_mono x mono) = (env x.1 * eval_mono env mono)%Z.
Proof.
  elim: mono => [|x2 mono ih] //=.
  case: bvar_cmp => //=.
  rewrite ih.
  move: (env _) (env _).
  by lia.
Qed.

Lemma insert_term_correct env cm terms :
  eval_expand env (insert_term cm terms) =
    (eval_expand env terms + cm.1 * eval_mono env cm.2)%Z.
Proof.
  elim: terms => [|cm2 terms ih] //=.
  - case: cm => [count mono] /=.
    by lia.
  case: List.list_compareP.
  + move=> x y; split.
    + by apply cmp_eq.
    by move=> <-; apply cmp_refl.
  + case: cm ih => [coeff mono] /= ih.
    case: cm2 => [coeff2 mono2] /=.
    move=> ?; subst mono2.
    case: Z.eqb_spec.
    + by lia.
    move=> _ /=.
    by lia.
  + case: cm ih => [coeff mono] /= ih.
    case: cm2 => [coeff2 mono2] /=.
    by lia.
  + case: cm ih => [coeff mono] /= ih.
    case: cm2 => [coeff2 mono2] /=.
    by lia.
  + case: cm ih => [coeff mono] /= ih.
    case: cm2 => [coeff2 mono2] /=.
    by lia.
  case: cm ih => [coeff mono] /= ih.
  case: cm2 => [coeff2 mono2] /=.
  by lia.
Qed.

Lemma insert_term_nice_correct env cm terms :
  eval_expand env (insert_term_nice cm terms) =
    (eval_expand env terms + cm.1 * eval_mono env cm.2)%Z.
Proof.
  rewrite /insert_term_nice.
  case: Z.eqb_spec.
  + move=> ->.
    by lia.
  move=> _.
  by apply insert_term_correct.
Qed.

Lemma expanded_form_sound_aux terms coeff mono al ACC :
  is_poly al ->
  forall env,
    eval_expand env (@expanded_form_aux terms coeff mono al ACC) =
      (eval_expand env terms + coeff * eval_mono env mono * eval_rec env al)%Z.
Proof.
  move=> hpoly env.
  move E: (size_poly al, left_Mul_under_Mul al) => k; move: al E ACC hpoly terms coeff mono.
  elim/(well_founded_induction wf_lt_lex) : k => -[k1 k2] /(_ _ _ _ erefl) ih al [??] [ACC] hpoly; subst k1 k2.
  case: al ACC ih hpoly => [z|n i|al|al1 al2|al1 al2|al1 al2|sg al1 al2|sg al1 al2|al1 al2|al1 al2] //= ACC ih hpoly terms coeff mono.
  + by rewrite insert_term_nice_correct /=; lia.
  + by rewrite insert_term_nice_correct insert_mono_correct /=; lia.
  + rewrite ih //.
    + by lia.
    by left => /=; lia.
  + move: hpoly => /andP [hpoly1 hpoly2].
    rewrite ih //.
    + rewrite ih //.
      + by lia.
      by left => /=; have := lt0_size_poly al2; lia.
    by left => /=; have := lt0_size_poly al1; lia.
  + move: hpoly => /andP [hpoly1 hpoly2].
    rewrite ih //.
    + rewrite ih //.
      + by lia.
      by left => /=; have := lt0_size_poly al2; lia.
    by left => /=; have := lt0_size_poly al1; lia.
  case: al1 ACC ih hpoly => [z1|n1 i1|al1|al11 al12|al11 al12|al11 al12|sg al11 al12|sg al11 al12|al11 al12|al11 al12] //= ACC ih hpoly.
  + rewrite ih //.
    + by lia.
    by left => /=; lia.
  + rewrite ih //.
    + by rewrite insert_mono_correct /=; lia.
    by left => /=; lia.
  + rewrite ih //=.
    + by lia.
    by left => /=; lia.
  + move: hpoly => /andP[] /andP[] hpoly1 hpoly2 hpoly3.
    rewrite ih /=; last by apply /andP.
    + rewrite ih /=; last by apply /andP.
      + by lia.
      by left => /=; have := lt0_size_poly al12; lia.
    by left => /=; have := lt0_size_poly al11; lia.
  + move: hpoly => /andP[] /andP[] hpoly1 hpoly2 hpoly3.
    rewrite ih //=; last by apply /andP.
    + rewrite ih //=; last by apply /andP.
      + by lia.
      by left => /=; have := lt0_size_poly al12; lia.
    by left => /=; have := lt0_size_poly al11; lia.
  move: hpoly => /andP[] /andP[] hpoly1 hpoly2 hpoly3.
  rewrite ih /=; last by apply /and3P.
  + by lia.
  by rewrite Nat.add_assoc; right; lia.
Qed.

Lemma expanded_form_sound al :
  is_poly al ->
  forall env,
    eval_expand env (expanded_form al) = eval_rec env al.
Proof.
  move=> hpoly env.
  rewrite /expanded_form expanded_form_sound_aux //.
  by rewrite [eval_expand _ _]/= [eval_mono _ _]/= !Z.mul_1_l Z.add_0_l.
Qed.

Lemma compare_array_length_eval ws1 len1 ws2 len2 :
  compare_array_length (ws1, len1) (ws2, len2) ->
  forall env,
  arr_size ws1 (eval env len1) = arr_size ws2 (eval env len2).
Proof.
Local Opaque wsize_size Z.mul.
  rewrite /compare_array_length.
  case: andP.
  + move=> [hpoly1 hpoly2] /eqP heq env.
    have := @expanded_form_sound (ALMul (ALConst (wsize_size ws1)) len1) hpoly1 env.
    have := @expanded_form_sound (ALMul (ALConst (wsize_size ws2)) len2) hpoly2 env.
    rewrite /= heq => ->.
    rewrite /eval !arr_sizeE.
    have ?: (0 < wsize_size ws1)%Z by [].
    have ?: (0 < wsize_size ws2)%Z by [].
    by case: (ZltP 0 (eval_rec env len1)) (ZltP 0 (eval_rec env len2)) => [?|?] [?|?]; lia.
  by move=> _ /andP [/eqP -> /eqP ->].
Local Transparent wsize_size Z.mul.
Qed.

Lemma convertible_eval_atype ty1 ty2 :
  convertible ty1 ty2 ->
  forall env,
    eval_atype env ty1 = eval_atype env ty2.
Proof.
  move=> hc env.
  case: ty1 ty2 hc => [||ws1 len1|ws1] [||ws2 len2|ws2] //=.
  + by move=> /compare_array_length_eval ->.
  by move=> /eqP [<-].
Qed.

Lemma all2_convertible_eval_atype tys1 tys2 :
  all2 convertible tys1 tys2 ->
  forall env,
    map (eval_atype env) tys1 = map (eval_atype env) tys2.
Proof.
  move=> hc env.
  elim: tys1 tys2 hc => [|ty1 tys1 ih1] [|ty2 tys2] //=.
  by move=> /andP [/convertible_eval_atype -> /ih1 ->].
Qed.

Definition subatype (t t': atype) :=
  match t with
  | aword w => if t' is aword w' then (w ≤ w')%CMP else false
  | _ => convertible t t'
  end.

Lemma subatypeE ty ty' :
  subatype ty ty' →
  match ty' return Prop with
  | aword sz' => ∃ sz, ty = aword sz ∧ (sz ≤ sz')%CMP
  | _         => convertible ty ty'
end.
Proof.
  case: ty => [||ws len|ws]; try by move/eqP => <-.
  + by case: ty'.
  by case: ty' => //; eauto.
Qed.

Lemma subatypeEl ty ty' :
  subatype ty ty' →
  match ty return Prop with
  | aword sz => ∃ sz', ty' = aword sz' ∧ (sz ≤ sz')%CMP
  | _        => convertible ty ty'
  end.
Proof.
  case: ty => [||ws len|ws] //=.
  by case: ty' => //; eauto.
Qed.

Lemma subatype_refl ty : subatype ty ty.
Proof.
Local Opaque convertible.
  by case: ty => //=.
Local Transparent convertible.
Qed.
#[global]
Hint Resolve subatype_refl : core.

Lemma subatype_trans ty2 ty1 ty3 :
  subatype ty1 ty2 -> subatype ty2 ty3 -> subatype ty1 ty3.
Proof.
Local Opaque convertible.
  case: ty1 ty2 => [||ws1 len1|ws1] [||ws2 len2|ws2] //=.
  + by apply convertible_trans.
  case: ty3 => // ws3.
  by apply cmp_le_trans.
Local Transparent convertible.
Qed.

Lemma is_aword_subatype t1 t2 : subatype t1 t2 -> is_aword t1 = is_aword t2.
Proof.
  by case: t1 => //= [/eqP <-|/eqP <-|??|?] //; case:t2.
Qed.

Definition subctype (t t': ctype) :=
  match t with
  | cword w => if t' is cword w' then (w ≤ w')%CMP else false
  | _ => t == t'
  end.

Lemma subctypeE ty ty' :
  subctype ty ty' →
  match ty' with
  | cword sz' => ∃ sz, ty = cword sz ∧ (sz ≤ sz')%CMP
  | _         => ty = ty'
end.
Proof.
  case: ty => [||n|ws]; try by move/eqP => <-.
  by case: ty' => //; eauto.
Qed.

Lemma subctypeEl ty ty' :
  subctype ty ty' →
  match ty return Prop with
  | cword sz => ∃ sz', ty' = cword sz' ∧ (sz ≤ sz')%CMP
  | _        => ty = ty'
  end.
Proof.
  case: ty => [||n|ws] //=; try by move/eqP => <-.
  by case: ty' => //; eauto.
Qed.

Lemma subctype_refl ty : subctype ty ty.
Proof. case: ty => //=. Qed.
#[global]
Hint Resolve subctype_refl : core.

Lemma subctype_trans ty2 ty1 ty3 :
  subctype ty1 ty2 -> subctype ty2 ty3 -> subctype ty1 ty3.
Proof.
  case: ty1 => //= [/eqP<-|/eqP<-|n1|ws1] //.
  + by case: ty2 => //= n2 /eqP ->.
  by case: ty2 => //= ws2 hle; case: ty3 => //= ws3; apply: cmp_le_trans hle.
Qed.

Lemma subatype_subctype ty1 ty2 :
  subatype ty1 ty2 ->
  forall env,
    subctype (eval_atype env ty1) (eval_atype env ty2).
Proof.
Local Opaque convertible.
  move=> hsub env.
  have suff hc: convertible ty1 ty2.
  + by move=> /convertible_eval_atype ->.
  case: ty1 ty2 hsub hc => [||ws1 n1|ws1] [||ws2 n2|ws2] // hsub hc; eauto.
Local Transparent convertible.
Qed.

Section SUBST.

(* When [f x] returns [None], we preserve [x]. Is this reasonable?
   Can this situation happen? If not, then this is a reasonable thing to do.
   If yes, does this mean that we ignore an error? Or does this mean that
   [x] is a variable that we do not want to substitute?
*)
Context (f : Uint63.int -> option array_length).

Fixpoint subst_al al :=
  match al with
  | ALConst _ => al
  | ALVar n _ => if f n is Some al' then al' else al
  | ALNeg al => ALNeg (subst_al al)
  | ALAdd al1 al2 =>
    ALAdd (subst_al al1) (subst_al al2)
  | ALSub al1 al2 =>
    ALSub (subst_al al1) (subst_al al2)
  | ALMul al1 al2 =>
    ALMul (subst_al al1) (subst_al al2)
  | ALDiv sg al1 al2 =>
    ALDiv sg (subst_al al1) (subst_al al2)
  | ALMod sg al1 al2 =>
    ALMod sg (subst_al al1) (subst_al al2)
  | ALShl al1 al2 =>
    ALShl (subst_al al1) (subst_al al2)
  | ALShr al1 al2 =>
    ALShr (subst_al al1) (subst_al al2)
  end.

Definition subst_ty ty :=
  match ty with
  | aarr ws al =>
    aarr ws (subst_al al)
  | _ => ty
  end.

End SUBST.

(* -------------------------------------------------------------------- *)
#[only(eqbOK)] derive
Variant extended_type : Type :=
  | ETbool
  | ETint
  | ETarr of wsize & array_length
  | ETword of (option signedness) & wsize.

Definition tbool := ETbool.
Definition tint  := ETint.
Definition tarr  (ws : wsize) (len : array_length) := ETarr ws len.
Definition tword ws : extended_type := ETword None ws.
Definition twint (s : signedness) (ws : wsize) := ETword (Some s) ws.
Definition tuint ws : extended_type := twint Unsigned ws.
Definition tsint ws : extended_type := twint Signed ws.

Definition to_atype (t:extended_type) : atype :=
  match t with
  | ETbool      => abool
  | ETint       => aint
  | ETarr ws l  => aarr ws l
  | ETword _ ws => aword ws
  end.

HB.instance Definition _ := hasDecEq.Build extended_type extended_type_eqb_OK.
