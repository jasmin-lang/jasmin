(* * Syntax and semantics of the dmasm source language *)
(* ** License
 * -----------------------------------------------------------------------
 * Copyright 2016--2017 IMDEA Software Institute
 * Copyright 2016--2017 Inria
 *
 * Permission is hereby granted, free of charge, to any person obtaining
 * a copy of this software and associated documentation files (the
 * "Software"), to deal in the Software without restriction, including
 * without limitation the rights to use, copy, modify, merge, publish,
 * distribute, sublicense, and/or sell copies of the Software, and to
 * permit persons to whom the Software is furnished to do so, subject to
 * the following conditions:
 *
 * The above copyright notice and this permission notice shall be
 * included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
 * EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.
 * IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY
 * CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT,
 * TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE
 * SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 * ----------------------------------------------------------------------- *)


(* ** Imports and settings *)
From mathcomp Require Import all_ssreflect all_algebra.
Require Import ZArith gen_map utils strings.
Import Utf8.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* ** Syntax
 * -------------------------------------------------------------------- *)

Variant wsize :=
  | U8 
  | U16
  | U32 
  | U64
  | U128
  | U256.

Variant stype : Set :=
| sbool
| sint
| sarr of wsize & positive
| sword of wsize.

Variant signedness := 
  | Signed
  | Unsigned.

(* Size in bits of the elements of a vector. *)
Variant velem := VE16 | VE32 | VE64.

Coercion wsize_of_velem (ve: velem) : wsize :=
  match ve with
  | VE16 => U16
  | VE32 => U32
  | VE64 => U64
  end.

(* -------------------------------------------------------------------- *)
Definition string_of_wsize (sz: wsize) : string :=
  match sz with
  | U8 => "U8"
  | U16 => "U16"
  | U32 => "U32"
  | U64 => "U64"
  | U128 => "U128"
  | U256 => "U256"
  end.

Definition string_of_stype (ty: stype) : string :=
  match ty with
  | sbool => "sbool"
  | sint => "sint"
  | sarr sz n => "(sarr " ++ string_of_wsize sz ++ " ?)"
  | sword sz => "(sword " ++ string_of_wsize sz ++ ")"
  end.

Definition string_of_velem (ve: velem) : string :=
  match ve with
  | VE16 => "VE16"
  | VE32 => "VE32"
  | VE64 => "VE64"
  end.

(* -------------------------------------------------------------------- *)
Notation sword8   := (sword U8).
Notation sword16  := (sword U16).
Notation sword32  := (sword U32).
Notation sword64  := (sword U64).
Notation sword128 := (sword U128).
Notation sword256 := (sword U256).

(* -------------------------------------------------------------------- *)
Scheme Equality for wsize. 

Lemma wsize_axiom : Equality.axiom wsize_beq. 
Proof. 
  move=> x y;apply:(iffP idP).
  + by apply: internal_wsize_dec_bl.
  by apply: internal_wsize_dec_lb.
Qed.

Definition wsize_eqMixin     := Equality.Mixin wsize_axiom.
Canonical  wsize_eqType      := Eval hnf in EqType wsize wsize_eqMixin.

Definition wsizes :=
  [:: U8 ; U16 ; U32 ; U64 ; U128 ; U256 ].

Lemma wsize_fin_axiom : Finite.axiom wsizes.
Proof. by case. Qed.

Definition wsize_choiceMixin :=
  PcanChoiceMixin (FinIsCount.pickleK wsize_fin_axiom).
Canonical wsize_choiceType :=
  Eval hnf in ChoiceType wsize wsize_choiceMixin.

Definition wsize_countMixin :=
  PcanCountMixin (FinIsCount.pickleK wsize_fin_axiom).
Canonical wsize_countType :=
  Eval hnf in CountType wsize wsize_countMixin.

Definition wsize_finMixin :=
  FinMixin wsize_fin_axiom.
Canonical wsize_finType :=
  Eval hnf in FinType wsize wsize_finMixin.

(* -------------------------------------------------------------------- *)
Scheme Equality for stype. 

Lemma stype_axiom : Equality.axiom stype_beq. 
Proof. 
  move=> x y;apply:(iffP idP).
  + by apply: internal_stype_dec_bl.
  by apply: internal_stype_dec_lb.
Qed.

Definition stype_eqMixin     := Equality.Mixin stype_axiom.
Canonical  stype_eqType      := Eval hnf in EqType stype stype_eqMixin.

(* -------------------------------------------------------------------- *)
Scheme Equality for velem.

Lemma velem_axiom : Equality.axiom velem_beq.
Proof.
  move=> x y;apply:(iffP idP).
  + by apply: internal_velem_dec_bl.
  by apply: internal_velem_dec_lb.
Qed.

Definition velem_eqMixin     := Equality.Mixin velem_axiom.
Canonical  velem_eqType      := Eval hnf in EqType velem velem_eqMixin.

(* ** Comparison 
 * -------------------------------------------------------------------- *)
Definition wsize_cmp s s' := 
  match s, s' with
  | U8, U8 => Eq
  | U8, (U16 | U32 | U64 | U128 | U256)  => Lt
  | U16, U8 => Gt
  | U16, U16 => Eq
  | U16, (U32 | U64 | U128 | U256) => Lt
  | U32, (U8 | U16) => Gt
  | U32, U32 => Eq
  | U32, (U64 | U128 | U256) => Lt
  | U64, (U8 | U16 | U32) => Gt
  | U64, U64 => Eq
  | U64, ( U128 | U256) => Lt
  | U128, (U8 | U16 | U32 | U64) => Gt
  | U128, U128 => Eq
  | U128, U256 => Lt
  | U256, (U8 | U16 | U32 | U64 | U128) => Gt
  | U256, U256 => Eq
  end.

Instance wsizeO : Cmp wsize_cmp.
Proof.
  constructor.
  + by move=> [] [].
  + by move=> [] [] [] //= ? [].
  by move=> [] [].
Qed.

Definition stype_cmp t t' :=
  match t, t' with
  | sbool   , sbool         => Eq 
  | sbool   , _             => Lt

  | sint    , sbool         => Gt
  | sint    , sint          => Eq
  | sint    , _             => Lt

  | sword _ , sarr _ _      => Lt
  | sword w , sword w'      => wsize_cmp w w'
  | sword _ , _             => Gt

  | sarr w n , sarr w' n'   => lex wsize_cmp Pos.compare (w,n) (w',n')
  | sarr _ _ , _             => Gt
  end.

Instance stypeO : Cmp stype_cmp. 
Proof.
  constructor.
  + case => [||w n|w] [||w' n'|w'] //=.
    + by apply lex_sym => /=;apply cmp_sym.
    by apply cmp_sym.
  + move=> y x; case: x y=> [||w n|w] [||w' n'|w'] [||w'' n''|w''] c//=;
    try (by apply ctrans_Eq);eauto using ctrans_Lt, ctrans_Gt.
    + by apply lex_trans;apply cmp_ctrans.
    by apply cmp_ctrans.
  case=> [||w n|w] [||w' n'|w'] //=.
  + by move=> /lex_eq /= [H H'];rewrite (@cmp_eq _ _ wsizeO _ _ H) (@cmp_eq _ _ positiveO _ _ H'). 
  by move=> H; rewrite (@cmp_eq _ _ wsizeO _ _ H). 
Qed.

Module CmpStype.

  Definition t : eqType := [eqType of stype].

  Definition cmp : t -> t -> comparison := stype_cmp.

  Definition cmpO : Cmp cmp := stypeO.
  
End CmpStype.

Lemma wsize_le_U8 s: (U8 <= s)%CMP.
Proof. by case: s. Qed.

Lemma wsize_le_U8_inv s: (s <= U8)%CMP -> s = U8.
Proof. by case: s. Qed.

Module CEDecStype.

  Definition t := [eqType of stype].
  
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
    | sarr w1 n1 =>
      match t2 as t0 return {sarr w1 n1 = t0} + {True} with
      | sarr w2 n2 =>
        match wsize_eq_dec w1 w2 with
        | left eqw => 
          match pos_dec n1 n2 with
          | left eqn => left (f_equal2 sarr eqw eqn)
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
    + by case: pos_dec (Hrec n2) => //= -[] /(_ (erefl _)).
    by case: pos_dec (Hrec n2) => //= -[] /(_ (erefl _)).
  Qed.
 
  Lemma eq_dec_r t1 t2 tt: eq_dec t1 t2 = right tt -> t1 != t2.
  Proof.
    case: tt;case:t1 t2=> [||w n|w] [||w' n'|w'] //=.
    + case: wsize_eq_dec => // eqw.
      + case: pos_dec (@pos_dec_r n n' I) => [Heq _ | [] neq ] //=.
        move: (neq (erefl _))=> /eqP H _;rewrite !eqE /= (internal_wsize_dec_lb eqw) /=.
        by case H':positive_beq=> //;move:H'=> /internal_positive_dec_bl.
      by move=> _;apply /eqP;congruence.
    case: wsize_eq_dec => // eqw.
    by move=> _;apply /eqP;congruence.
  Qed.

End CEDecStype.

Lemma pos_dec_n_n n: CEDecStype.pos_dec n n = left (erefl n).
Proof. by elim: n=> // p0 /= ->. Qed.

Module Mt := DMmake CmpStype CEDecStype.

Delimit Scope mtype_scope with mt.
Notation "m .[ x ]" := (@Mt.get _ m x) : mtype_scope.
Notation "m .[ x  <- v ]" := (@Mt.set _ m x v) : mtype_scope.
Arguments Mt.get P m%mtype_scope k.
Arguments Mt.set P m%mtype_scope k v.


Definition is_sword t := 
  match t with
  | sword _ => true
  | _       => false
  end.

(* -------------------------------------------------------------------- *)
Definition subtype (t t': stype) :=
  match t with
  | sword w => if t' is sword w' then (w ≤ w')%CMP else false
  | _ => t == t'
  end.

Lemma subtypeE ty ty' :
  subtype ty ty' →
  match ty' with
  | sword sz => ∃ sz', ty = sword sz' ∧ (sz' ≤ sz)%CMP
  | _ => ty = ty'
end.
Proof.
  destruct ty; try by move/eqP => <-.
  case: ty' => //; eauto.
Qed.

Lemma subtype_refl x : subtype x x.
Proof. by case: x => /=. Qed.

Lemma subtype_trans y x z : subtype x y -> subtype y z -> subtype x z.
Proof.
  case: x => //= [/eqP<-|/eqP<-|??/eqP<-|sx] //.
  case: y => //= sy hle;case: z => //= sz;apply: cmp_le_trans hle.
Qed.

(* -------------------------------------------------------------------- *)
Definition check_size_8_64 sz := assert (sz ≤ U64)%CMP ErrType.
Definition check_size_16_64 sz := assert ((U16 ≤ sz) && (sz ≤ U64))%CMP ErrType.
Definition check_size_32_64 sz := assert ((U32 ≤ sz) && (sz ≤ U64))%CMP ErrType.
Definition check_size_128_256 sz := assert ((U128 ≤ sz) && (sz ≤ U256))%CMP ErrType.

Lemma wsize_nle_u64_check_128_256 sz :
  (sz ≤ U64)%CMP = false →
  check_size_128_256 sz = ok tt.
Proof. by case: sz. Qed.
