(* ** Imports and settings *)
From elpi.apps Require Import derive.std.
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool seq eqtype.
From mathcomp Require Import word_ssrZ.
From Coq Require Import ZArith.
Require Import gen_map utils strings.
Require Export wsize.
Import Utf8.

(* ** Syntax
 * -------------------------------------------------------------------- *)

(* Low-level (or linear?) types, i.e. types that exist in architectures. *)
#[only(eqbOK)] derive
Variant ltype : Set :=
| lbool
| lword of wsize.

(* Syntax types, i.e. types that appear in programs *)
#[only(eqbOK)] derive
Variant atype : Set :=
| abool
| aint
| aarr of wsize & positive
| aword of wsize.

(* Value types, i.e. types appearing in the semantics *)
#[only(eqbOK)] derive
Variant ctype : Set :=
| cbool
| cint
| carr  of positive
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

  | aarr ws n , aarr ws' n' => Lex (wsize_cmp ws ws') (Pos.compare n n')
  | aarr _ _  , _           => Gt
  end.

#[global]
Instance atypeO : Cmp atype_cmp.
Proof.
  constructor.
  + case => [||ws n|w] [||ws' n'|w'] //=.
    + by rewrite !Lex_lex lex_sym //=; apply cmp_sym.
    by apply cmp_sym.
  + move=> y x; case: x y=> [||ws n|w] [||ws' n'|w'] [||ws'' n''|w''] c //=;
       try (by apply ctrans_Eq);eauto using ctrans_Lt, ctrans_Gt.
    + by rewrite !Lex_lex; apply lex_trans; apply cmp_ctrans.
    by apply cmp_ctrans.
  case=> [||n ws|w] [||n' ws'|w'] //=.
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

  Fixpoint pos_dec (p1 p2:positive) : {p1 = p2} + {True} :=
    match p1 as p1' return {p1' = p2} + {True} with
    | xH =>
      match p2 as p2' return {xH = p2'} + {True} with
      | xH => left (erefl xH)
      | _  => right I
      end
    | xO p1' =>
      match p2 as p2' return {xO p1' = p2'} + {True} with
      | xO p2' =>
        match pos_dec p1' p2' with
        | left eq =>
          left (eq_rect p1' (fun p => xO p1' = xO p) (erefl (xO p1')) p2' eq)
        | _ => right I
        end
      | _ => right I
      end
    | xI p1' =>
      match p2 as p2' return {xI p1' = p2'} + {True} with
      | xI p2' =>
        match pos_dec p1' p2' with
        | left eq =>
          left (eq_rect p1' (fun p => xI p1' = xI p) (erefl (xI p1')) p2' eq)
        | _ => right I
        end
      | _ => right I
      end
    end.

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
    | aarr ws1 n1 =>
      match t2 as t0 return {aarr ws1 n1 = t0} + {True} with
      | aarr ws2 n2 =>
        match wsize_eq_dec ws1 ws2 with
        | left eqw =>
          match pos_dec n1 n2 with
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

  Lemma pos_dec_r n1 n2 tt: pos_dec n1 n2 = right tt -> n1 != n2.
  Proof.
    case: tt.
    elim: n1 n2 => [n1 Hrec|n1 Hrec|] [n2|n2|] //=.
    + case: pos_dec (Hrec n2) => //= -[] /(_ (erefl _)) /eqP ? _.
      by apply /eqP; congruence.
    case: pos_dec (Hrec n2) => //= -[] /(_ (erefl _)) /eqP ? _.
    by apply /eqP; congruence.
  Qed.

  Lemma eq_dec_r t1 t2 tt: eq_dec t1 t2 = right tt -> t1 != t2.
  Proof.
    case: tt;case:t1 t2=> [||ws n|w] [||ws' n'|w'] //=.
    + case: wsize_eq_dec => eqw.
      + case: pos_dec (@pos_dec_r n n' I) => [Heq _ | [] neq ] //=.
        move => _; apply/eqP => -[].
        by move/eqP: (neq erefl).
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
Definition arr_size (ws:wsize) (len:positive)  := 
   (wsize_size ws * len)%Z.

Lemma arr_sizeE ws len : arr_size ws len = (wsize_size ws * len)%Z.
Proof. done. Qed.

Lemma gt0_arr_size ws len : (0 < arr_size ws len)%Z.
Proof. done. Qed.

Opaque arr_size.

Definition eval_atype ty :=
  match ty with
  | abool => cbool
  | aint => cint
  | aarr ws len => carr (Z.to_pos (arr_size ws len))
  | aword ws => cword ws
  end.

Definition eval_ltype ty :=
  match ty with
  | lbool => cbool
  | lword ws => cword ws
  end.

Definition convertible (t t' : atype) :=
  match t with
  | aarr ws n =>
    if t' is aarr ws' n' then arr_size ws n == arr_size ws' n' else false
  | _ => t == t'
  end.

Lemma convertible_refl t : convertible t t.
Proof. by case: t => //=. Qed.
#[global]
Hint Resolve convertible_refl : core.

Lemma convertible_sym ty1 ty2 : convertible ty1 ty2 -> convertible ty2 ty1.
Proof.
  case: ty1 ty2 => [||ws1 n1|ws1] [||ws2 n2|ws2] //=.
  + by rewrite eq_sym.
  by rewrite eq_sym.
Qed.

Lemma convertible_trans ty2 ty1 ty3 :
  convertible ty1 ty2 -> convertible ty2 ty3 -> convertible ty1 ty3.
Proof.
  case: ty1 ty2 => [||ws1 n1|ws1] [||ws2 n2|ws2] //=.
  + by move=> /eqP ->.
  by move=> /eqP ->.
Qed.

Lemma convertible_eval_atype ty1 ty2 :
  convertible ty1 ty2 ->
  eval_atype ty1 = eval_atype ty2.
Proof.
  case: ty1 ty2 => [||ws1 n1|ws1] [||ws2 n2|ws2] //=.
  + by move=> /eqP <-.
  by move=> /eqP [<-].
Qed.

Lemma all2_convertible_eval_atype tys1 tys2 :
  all2 convertible tys1 tys2 ->
  map eval_atype tys1 = map eval_atype tys2.
Proof.
  elim: tys1 tys2 => [|ty1 tys1 ih1] [|ty2 tys2] //=.
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
  case: ty => [||ws n|ws]; try by move/eqP => <-.
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
  case: ty => [||ws n|ws] //=.
  by case: ty' => //; eauto.
Qed.

Lemma subatype_refl ty : subatype ty ty.
Proof. case: ty => //=. Qed.
#[global]
Hint Resolve subatype_refl : core.

Lemma subatype_trans ty2 ty1 ty3 :
  subatype ty1 ty2 -> subatype ty2 ty3 -> subatype ty1 ty3.
Proof.
  case: ty1 => //= [/eqP<-|/eqP<-|ws1 n1|ws1] //.
  + by case: ty2 => //= ws2 n2 /eqP ->.
  by case: ty2 => //= ws2 hle; case: ty3 => //= ws3; apply: cmp_le_trans hle.
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
  subctype (eval_atype ty1) (eval_atype ty2).
Proof.
  case: ty1 ty2 => [||ws1 n1|ws1] [||ws2 n2|ws2] //=.
  by move=> /eqP <-.
Qed.

(* -------------------------------------------------------------------- *)
#[only(eqbOK)] derive
Variant extended_type (len:Type) : Type :=
  | ETbool
  | ETint
  | ETarr of wsize & len
  | ETword of (option signedness) & wsize.

Definition tbool {len} := ETbool len.
Definition tint  {len} := ETint len.
Definition tarr  {len} (ws : wsize) (l : len) := ETarr ws l.
Definition tword {len} ws : extended_type len:= ETword len None ws.
Definition twint {len} (s : signedness) (ws : wsize) := ETword len (Some s) ws.
Definition tuint {len} ws : extended_type len := twint Unsigned ws.
Definition tsint {len} ws : extended_type len := twint Signed ws.

Definition to_atype (t:extended_type positive) : atype :=
  match t with
  | ETbool      => abool
  | ETint       => aint
  | ETarr ws l  => aarr ws l
  | ETword _ ws => aword ws
  end.

Section EQ.
Context {L : eqType}.

HB.instance Definition _ := hasDecEq.Build (extended_type L) (extended_type_eqb_OK (@eqP _)).
End EQ.
