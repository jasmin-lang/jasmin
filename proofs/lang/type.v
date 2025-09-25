(* ** Imports and settings *)
From elpi.apps Require Import derive.std.
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.
From mathcomp.zify Require Import ssrZ.
From Coq Require Import ZArith.
Require Import gen_map utils strings.
Require Export wsize.
Import Utf8.

(* ** Syntax
 * -------------------------------------------------------------------- *)

#[only(eqbOK)] derive
Variant stype (len:Type) :=
| sbool
| sint
| sarr  of len
| sword of wsize.
Arguments sbool {_}.
Arguments sint {_}.
Arguments sarr {_} _.
Arguments sword {_} _.

(* abstract: for variables *)
Definition atype := stype (wsize * positive).
(* concrete: for values *)
Definition ctype := stype positive.

Definition map_stype S T (f : S -> T) (ty : stype S) :=
  match ty with
  | sbool => sbool
  | sint => sint
  | sarr len => sarr (f len)
  | sword ws => sword ws
  end.

(* -------------------------------------------------------------------- *)
(*
Definition string_of_stype (ty: stype) : string :=
  match ty with
  | sbool => "sbool"
  | sint => "sint"
  | sarr n => "(sarr " ++ " ?)"
  | sword sz => "(sword " ++ string_of_wsize sz ++ ")"
  end.
*)

(* -------------------------------------------------------------------- *)
Notation sword8   := (sword U8).
Notation sword16  := (sword U16).
Notation sword32  := (sword U32).
Notation sword64  := (sword U64).
Notation sword128 := (sword U128).
Notation sword256 := (sword U256).

(* -------------------------------------------------------------------- *)
Notation ty_msf := (sword msf_size).

(* -------------------------------------------------------------------- *)
Section EQ.

Context (len:eqType).

HB.instance Definition _ := hasDecEq.Build (stype len) (stype_eqb_OK (@eqP _)).

End EQ.

(* ** Comparison
 * -------------------------------------------------------------------- *)

Section CMP.

Context (len : Type) (len_cmp : len -> len -> comparison) (lenO : Cmp len_cmp).

Definition stype_cmp t t' :=
  match t, t' with
  | sbool   , sbool         => Eq
  | sbool   , _             => Lt

  | sint    , sbool         => Gt
  | sint    , sint          => Eq
  | sint    , _             => Lt

  | sword _ , sarr _        => Lt
  | sword w , sword w'      => wsize_cmp w w'
  | sword _ , _             => Gt

  | sarr n  , sarr n'       => len_cmp n n'
  | sarr _  , _             => Gt
  end.

#[global]
Instance stypeO : Cmp stype_cmp.
Proof.
  constructor.
  + by case => [||n|w] [||n'|w'] //=; apply cmp_sym.
  + by move=> y x; case: x y=> [||n|w] [||n'|w'] [||n''|w''] c//=;
       try (by apply ctrans_Eq);eauto using ctrans_Lt, ctrans_Gt; apply cmp_ctrans.
  case=> [||n|w] [||n'|w'] //= h.
  + by rewrite (@cmp_eq _ _ lenO _ _ h).
  by rewrite (@cmp_eq _ _ wsizeO _ _ h).
Qed.

End CMP.

Module CmpAtype.

  Definition t : eqType := atype.

  Definition cmp : t -> t -> comparison := stype_cmp (lex wsize_cmp Pos.compare).

  Definition cmpO : Cmp cmp := stypeO (LexO wsizeO positiveO).

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
    | sbool =>
      match t2 as t0 return {sbool = t0} + {True} with
      | sbool => left (erefl sbool)
      | _     => right I
      end
    | sint =>
      match t2 as t0 return {sint = t0} + {True} with
      | sint => left (erefl sint)
      | _     => right I
      end
    | sarr (ws1, n1) =>
      match t2 as t0 return {sarr (ws1, n1) = t0} + {True} with
      | sarr (ws2, n2) =>
        match wsize_eq_dec ws1 ws2 with
        | left eqw =>
          match pos_dec n1 n2 with
          | left eqn => left (f_equal2 (fun ws len => sarr (ws, len)) eqw eqn)
          | right _ => right I
          end
        | right _ => right I
        end
      | _          => right I
      end
    | sword w1 =>
      match t2 as t0 return {sword w1 = t0} + {True} with
      | sword w2 =>
        match wsize_eq_dec w1 w2 with
        | left eqw => left (f_equal sword eqw)
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

  (* TODO: define the generic version and just instantiate it with wsize_pos_dec *)
  Lemma eq_dec_r t1 t2 tt: eq_dec t1 t2 = right tt -> t1 != t2.
  Proof.
    case: tt; case:t1 t2=> [||[ws n]|w] [||[ws' n']|w'] //=.
    + case: wsize_eq_dec => ws_eq.
      + case: pos_dec (@pos_dec_r n n' I) => [Heq _ | [] neq ] //=.
        move => _; apply/eqP => -[].
        by move/eqP: (neq erefl).
      by move=> _; apply /eqP; congruence.
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

Definition is_sbool {len:eqType} (t:stype len) := t == sbool.

Lemma is_sboolP {len:eqType} (t:stype len) : reflect (t=sbool) (is_sbool t).
Proof. by rewrite /is_sbool;case:eqP => ?;constructor. Qed.

Definition is_sword {len} (t:stype len) := if t is sword _ then true else false.

Definition is_sarr {len} (t:stype len) := if t is sarr _ then true else false.

Definition is_not_sarr {len} (t:stype len) := ~~is_sarr t.

Lemma is_sarrP {len} (ty:stype len) : reflect (exists n, ty = sarr n) (is_sarr ty).
Proof. by case: ty; constructor; eauto => -[?]. Qed.

Definition is_word_type {len} (t:stype len) :=
  if t is sword sz then Some sz else None.

Lemma is_word_typeP {len} (ty:stype len) ws :
  is_word_type ty = Some ws -> ty = sword ws.
Proof. by case: ty => //= w [->]. Qed.

End OtherDefs.

(* -------------------------------------------------------------------- *)
Definition arr_size (ws:wsize) (len:positive) :=
  (wsize_size ws * len)%Z.

Definition to_ctype (ty : atype) : ctype :=
  map_stype (fun '(ws, len) => Z.to_pos (arr_size ws len)) ty.

Definition to_atype (ty : ctype) : atype :=
  map_stype (fun len => (U8, len)) ty.

Section CONV.

Context {len:eqType} (conv : len -> len -> bool).

Definition convertible_gen (t t': stype len) :=
  match t with
  | sarr n => if t' is sarr n' then conv n n' else false
  | _ => t == t'
  end.

Definition subtype_gen (t t': stype len) :=
  match t with
  | sword w => if t' is sword w' then (w ≤ w')%CMP else false
  | _ => convertible_gen t t'
  end.

Require Import RelationClasses.

Lemma convertible_gen_refl : Reflexive conv -> Reflexive convertible_gen.
Proof. by move=> conv_refl; case=> /=. Qed.

Lemma convertible_gen_sym : Symmetric conv -> Symmetric convertible_gen.
Proof.
  move=> conv_sym.
  move=> [||n1|ws1] [||n2|ws2] //=.
  + exact: conv_sym.
  by rewrite eq_sym.
Qed.

Lemma convertible_gen_trans : Transitive conv -> Transitive convertible_gen.
Proof.
  move=> conv_trans.
  move=> [||n1|ws1] [||n2|ws2] [||n3|ws3] //=.
  + exact: conv_trans.
  by move=> /eqP -> /eqP ->.
Qed.

Lemma subtype_gen_refl : Reflexive conv -> Reflexive subtype_gen.
Proof. by move=> conv_refl; case=> /=. Qed.

Lemma subtype_gen_trans : Transitive conv -> Transitive subtype_gen.
Proof.
  move=> conv_trans.
  move=> [||n1|ws1] [||n2|ws2] [||n3|ws3] //=.
  + exact: conv_trans.
  exact: cmp_le_trans.
Qed.

Lemma subtype_genE ty ty' :
  subtype_gen ty ty' →
  match ty' return Prop with
  | sword sz' => ∃ sz, ty = sword sz ∧ (sz ≤ sz')%CMP
  | _         => convertible_gen ty ty'
end.
Proof.
  case: ty => [||n|ws] /=; try by move/eqP => <-.
  + by case: ty'.
  by case: ty' => //; eauto.
Qed.

Lemma subtype_genEl ty ty' :
  subtype_gen ty ty' →
  match ty return Prop with
  | sword sz => ∃ sz', ty' = sword sz' ∧ (sz ≤ sz')%CMP
  | _        => convertible_gen ty ty'
  end.
Proof.
  case: ty => [||n|ws] //=; try by move/eqP => <-.
  by case: ty' => //; eauto.
Qed.

Lemma is_sword_subtype t1 t2 : subtype_gen t1 t2 -> is_sword t1 = is_sword t2.
Proof.
  by case: t1 => //= [/eqP <-|/eqP <-|?|?] //;case:t2.
Qed.

End CONV.

Definition convertible (ty1 ty2 : atype) :=
  convertible_gen (fun '(ws1, len1) '(ws2, len2) => arr_size ws1 len1 == arr_size ws2 len2) ty1 ty2.

Lemma convertible_refl t : convertible t t.
Proof.
  apply convertible_gen_refl.
  by case.
Qed.
#[global]
Hint Resolve convertible_refl : core.

Lemma convertible_sym t1 t2 : convertible t1 t2 -> convertible t2 t1.
Proof.
  apply convertible_gen_sym.
  move=> [??] [??].
  by rewrite eq_sym.
Qed.

Lemma convertible_trans t1 t2 t3 :
  convertible t1 t2 -> convertible t2 t3 -> convertible t1 t3.
Proof.
  apply convertible_gen_trans.
  move=> [??] [??] [??].
  by move=> /eqP -> /eqP ->.
Qed.

Lemma test ty1 ty2 : convertible ty1 ty2 -> to_ctype ty1 = to_ctype ty2.
Proof.
Local Opaque arr_size.
  case: ty1 ty2 => [||n1|ws1] [||n2|ws2] //=.
  + by case: n1 n2 => [??] [??] /eqP ->.
  by move=> /eqP [->].
Local Transparent arr_size.
Qed.

(* -------------------------------------------------------------------- *)
(* TODO: should it be asubtype? and should there be csubtype? *)
Definition subatype (t t': atype) :=
  subtype_gen (fun '(ws1, len1) '(ws2, len2) => arr_size ws1 len1 == arr_size ws2 len2) t t'.

Definition subctype (t t' : ctype) :=
  subtype_gen eq_op t t'.

Lemma subatype_refl x : subatype x x.
Proof. apply subtype_gen_refl. by case. Qed.
#[global]
Hint Resolve subatype_refl : core.

Lemma subctype_refl x : subctype x x.
Proof. apply subtype_gen_refl. by case. Qed.
#[global]
Hint Resolve subctype_refl : core.

Lemma subatype_trans y x z : subatype x y -> subatype y z -> subatype x z.
Proof.
  apply subtype_gen_trans.
  by move=> [??] [??] [??] /eqP -> /eqP ->.
Qed.

Lemma subctype_trans y x z : subctype x y -> subctype y z -> subctype x z.
Proof.
  apply subtype_gen_trans.
  by move=> ??? /eqP -> /eqP ->.
Qed.

Lemma subatypeE ty ty' :
  subatype ty ty' →
  match ty' return Prop with
  | sword sz' => ∃ sz, ty = sword sz ∧ (sz ≤ sz')%CMP
  | _         => convertible ty ty'
end.
Proof. exact: subtype_genE. Qed.

Lemma subtypeaEl ty ty' :
  subatype ty ty' →
  match ty return Prop with
  | sword sz => ∃ sz', ty' = sword sz' ∧ (sz ≤ sz')%CMP
  | _        => convertible ty ty'
  end.
Proof. exact: subtype_genEl. Qed.

Lemma toto (ty1 ty2:ctype) : convertible_gen eq_op ty1 ty2 -> ty1 = ty2.
Proof. case: ty1 ty2 => [||n|ws] [||n'|ws'] //=.
  + by move=> /eqP <-.
  by move=> /eqP [<-].
Qed.

Lemma subctypeE ty ty' :
  subctype ty ty' →
  match ty' return Prop with
  | sword sz' => ∃ sz, ty = sword sz ∧ (sz ≤ sz')%CMP
  | _         => ty = ty'
end.
Proof.
  move=> /subtype_genE.
  by case: ty' => [||len|ws] // /toto.
Qed.

Lemma subctypeEl ty ty' :
  subctype ty ty' →
  match ty return Prop with
  | sword sz => ∃ sz', ty' = sword sz' ∧ (sz ≤ sz')%CMP
  | _        => ty = ty'
  end.
Proof.
  move=> /subtype_genEl.
  by case: ty => [||len|ws] // /toto.
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

Definition to_stype {len} (t:extended_type len) : stype (wsize * len) :=
  match t with
  | ETbool      => sbool
  | ETint       => sint
  | ETarr ws l  => sarr (ws, l)
  | ETword _ ws => sword ws
  end.

Section EQ.
Context {L : eqType}.

HB.instance Definition _ := hasDecEq.Build (extended_type L) (extended_type_eqb_OK (@eqP _)).
End EQ.
