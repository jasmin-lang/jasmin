Require Import utils wsize word type.
From elpi.apps Require Import derive.std.
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq eqtype div.
From Coq Require Import ZArith.


(* ** Operators
 * -------------------------------------------------------------------- *)
(* *** Summary
   Operators represent several constructs in the Ocaml compiler:
   - const-op: compile-time expressions (constexpr in C++)
   - list-op: argument and result lists
   - arr-op: reading and writing arrays
   - cpu-op: CPU instructions such as addition with carry
*)

#[only(eqbOK)] derive
Variant cmp_kind :=
  | Cmp_int
  | Cmp_w of signedness & wsize.

#[only(eqbOK)] derive
Variant op_kind :=
  | Op_int
  | Op_w of wsize.

#[only(eqbOK)] derive
Variant wiop1 :=
| WIwint_of_int  of wsize (* int → word *)
| WIint_of_wint  of wsize (* word/uint/sint → int, signed or unsigned interpretation *)
| WIword_of_wint of wsize (* uint/sint -> word *)
| WIwint_of_word of wsize (* word -> uint/sint *)
| WIwint_ext     of wsize & wsize (* Size-extension: output-size, input-size *)
| WIneg          of wsize (* negation *)
.

#[only(eqbOK)] derive
Variant sop1 :=
| Oword_of_int of wsize     (* int → word *)
| Oint_of_word of signedness & wsize (* word → signed/unsigned int *)
| Osignext of wsize & wsize (* Sign-extension: output-size, input-size *)
| Ozeroext of wsize & wsize (* Zero-extension: output-size, input-size *)
| Onot                      (* Boolean negation *)
| Olnot of wsize            (* Bitwize not: 1s’ complement *)
| Oneg  of op_kind          (* Arithmetic negation *)
(* wint operations *)
| Owi1 of signedness & wiop1
.

#[only(eqbOK)] derive
Variant wiop2 :=
| WIadd
| WImul
| WIsub
| WIdiv
| WImod
| WIshl
| WIshr
| WIeq
| WIneq
| WIlt
| WIle
| WIgt
| WIge
.

#[only(eqbOK)] derive
Variant sop2 :=
| Obeq                        (* const : abool -> abool -> abool *)
| Oand                        (* const : abool -> abool -> abool *)
| Oor                         (* const : abool -> abool -> abool *)

| Oadd  of op_kind
| Omul  of op_kind
| Osub  of op_kind
| Odiv  of signedness & op_kind
| Omod  of signedness & op_kind

| Oland of wsize
| Olor  of wsize
| Olxor of wsize
| Olsr  of wsize
| Olsl  of op_kind
| Oasr  of op_kind
| Oror  of wsize
| Orol  of wsize

| Oeq   of op_kind
| Oneq  of op_kind
| Olt   of cmp_kind
| Ole   of cmp_kind
| Ogt   of cmp_kind
| Oge   of cmp_kind

(* vector operation *)
| Ovadd of velem & wsize (* VPADD   *)
| Ovsub of velem & wsize (* VPSUB   *)
| Ovmul of velem & wsize (* VPMULLW *)
| Ovlsr of velem & wsize
| Ovlsl of velem & wsize
| Ovasr of velem & wsize

(* wint operations *)
| Owi2 of signedness & wsize & wiop2
.

(* N-ary operators *)
#[only(eqbOK)] derive
Variant combine_flags :=
| CF_LT    of signedness   (* Alias : signed => L  ; unsigned => B   *)
| CF_LE    of signedness   (* Alias : signed => LE ; unsigned => BE  *)
| CF_EQ                    (* Alias : E                              *)
| CF_NEQ                   (* Alias : !E                             *)
| CF_GE    of signedness   (* Alias : signed => !L ; unsigned => !B  *)
| CF_GT    of signedness   (* Alias : signed => !LE; unsigned => !BE *)
.

#[only(eqbOK)] derive
Variant opN :=
| Opack of wsize & pelem (* Pack words of size pelem into one word of wsize *)
| Oarray of Z (* Literal array of bytes *)
| Ocombine_flags of combine_flags
.

#[only(eqbOK)] derive
Variant opN_safety :=
| Ois_arr_init of Z
| Ois_barr_init of Z
.

HB.instance Definition _ := hasDecEq.Build op_kind op_kind_eqb_OK.

HB.instance Definition _ := hasDecEq.Build sop1 sop1_eqb_OK.

HB.instance Definition _ := hasDecEq.Build sop2 sop2_eqb_OK.

HB.instance Definition _ := hasDecEq.Build opN opN_eqb_OK.

HB.instance Definition _ := hasDecEq.Build opN_safety opN_safety_eqb_OK.

(* ----------------------------------------------------------------------------- *)

(* ** Types of operators
 * -------------------------------------------------------------------- *)

(* Type of unany operators: input, output *)
Definition etype_of_wiop1 {len:Type} (s: signedness) (o:wiop1) : extended_type len * extended_type len :=
  match o with
  | WIwint_of_int  sz => (tint, twint s sz)
  | WIint_of_wint  sz => (twint s sz, tint)
  | WIword_of_wint sz => (twint s sz, tword sz)
  | WIwint_of_word sz => (tword sz, twint s sz)
  | WIwint_ext szo szi => (twint s szi, twint s szo)
  | WIneg          sz => (twint s sz, twint s sz)
  end.

Definition type_of_wiop1 (o:wiop1) : atype * atype :=
  match o with
  | WIwint_of_int  sz => (aint, aword sz)
  | WIint_of_wint  sz => (aword sz, aint)
  | WIword_of_wint sz => (aword sz, aword sz)
  | WIwint_of_word sz => (aword sz, aword sz)
  | WIwint_ext szo szi => (aword szi, aword szo)
  | WIneg          sz => (aword sz, aword sz)
  end.

Lemma e_type_of_wiop1 s o :
  let t := etype_of_wiop1 s o in
  type_of_wiop1 o = (to_atype t.1, to_atype t.2).
Proof. by case: o. Qed.

Definition type_of_opk (k:op_kind) :=
  match k with
  | Op_int => aint
  | Op_w sz => aword sz
  end.

Definition etype_of_opk {len} (k:op_kind) : extended_type len :=
  match k with
  | Op_int => tint
  | Op_w sz => tword sz
  end.

Lemma e_type_of_opk k : type_of_opk k = to_atype (etype_of_opk k).
Proof. by case: k. Qed.

(* Type of unany operators: input, output *)
Definition etype_of_op1 {len} (o: sop1) : extended_type len * extended_type len :=
  match o with
  | Oword_of_int sz => (tint, tword sz)
  | Oint_of_word _ sz => (tword sz, tint)
  | Osignext szo szi
  | Ozeroext szo szi
    => (tword szi, tword szo)
  | Onot => (tbool, tbool)
  | Olnot sz => (tword sz, tword sz)
  | Oneg k => let t := etype_of_opk k in (t, t)
  | Owi1 s o => etype_of_wiop1 s o
  end.

Definition type_of_op1 (o: sop1) : atype * atype :=
  match o with
  | Oword_of_int sz => (aint, aword sz)
  | Oint_of_word _ sz => (aword sz, aint)
  | Osignext szo szi
  | Ozeroext szo szi
    => (aword szi, aword szo)
  | Onot => (abool, abool)
  | Olnot sz => (aword sz, aword sz)
  | Oneg k => let t := type_of_opk k in (t, t)
  | Owi1 s o => type_of_wiop1 o
  end.

Lemma e_type_of_op1 o :
  let t := etype_of_op1 o in
  type_of_op1 o = (to_atype t.1, to_atype t.2).
Proof.
  case: o => //= >.
  + by rewrite !e_type_of_opk.
  apply e_type_of_wiop1.
Qed.

(* Type of binany operators: inputs, output *)
Definition etype_of_wiop2 {len} s sz (o : wiop2) :
  extended_type len * extended_type len * extended_type len :=
  match o with
  | WIadd | WImul | WIsub | WIdiv | WImod =>
    let t := twint s sz in (t, t, t)

  | WIshl | WIshr =>
    let t := twint s sz in
    let tu8 := tuint U8 in
    (t, tu8, t)

  | WIeq | WIneq | WIlt | WIle | WIgt | WIge =>
    let t := twint s sz in (t, t, tbool)
  end.

Definition type_of_wiop2 sz (o : wiop2) :
  atype * atype * atype :=
  match o with
  | WIadd | WImul | WIsub | WIdiv | WImod =>
    let t := aword sz in (t, t, t)

  | WIshl | WIshr =>
    let t := aword sz in
    let tu8 := aword U8 in
    (t, tu8, t)

  | WIeq | WIneq | WIlt | WIle | WIgt | WIge =>
    let t := aword sz in (t, t, abool)
  end.

Lemma e_type_of_wiop2 s sz o :
  let t := etype_of_wiop2 s sz o in
  type_of_wiop2 sz o = (to_atype t.1.1, to_atype t.1.2, to_atype t.2).
Proof. by case: o. Qed.

Definition opk8 k :=
  match k with
  | Op_int => Op_int
  | Op_w _ => Op_w U8
  end.

Definition opk_of_cmpk k :=
  match k with
  | Cmp_int => Op_int
  | Cmp_w _ sz => Op_w sz
  end.

(* Type of binany operators: inputs, output *)
Definition etype_of_op2 {len} (o : sop2) : extended_type len * extended_type len * extended_type len :=
 match o with
  | Obeq | Oand | Oor => (tbool, tbool, tbool)
  | Oadd k | Omul k | Osub k | Odiv _ k | Omod _ k =>
    let t := etype_of_opk k in (t, t, t)
  | Olsl k | Oasr k =>
    let t1 := etype_of_opk k in
    let t2 := etype_of_opk (opk8 k) in
    (t1, t2, t1)
  | Oland s | Olor s | Olxor s | Ovadd _ s | Ovsub _ s | Ovmul _ s
    => let t := tword s in (t, t, t)
  | Olsr s | Oror s | Orol s
    => let t := tword s in (t, tword U8, t)
  | Ovlsr _ s | Ovlsl _ s | Ovasr _ s
    => let t := tword s in (t, tword U128, t)
  | Oeq k | Oneq k =>
    let t := etype_of_opk k in
    (t, t, tbool)
  | Olt k | Ole k | Ogt k | Oge k =>
    let t := etype_of_opk (opk_of_cmpk k) in
    (t, t, tbool)
  | Owi2 s sz o => etype_of_wiop2 s sz o
  end.

Definition type_of_op2 (o : sop2) : atype * atype * atype :=
 match o with
  | Obeq | Oand | Oor => (abool, abool, abool)
  | Oadd k | Omul k | Osub k | Odiv _ k | Omod _ k =>
    let t := type_of_opk k in (t, t, t)
  | Olsl k | Oasr k =>
    let t1 := type_of_opk k in
    let t2 := type_of_opk (opk8 k) in
    (t1, t2, t1)
  | Oland s | Olor s | Olxor s | Ovadd _ s | Ovsub _ s | Ovmul _ s
    => let t := aword s in (t, t, t)
  | Olsr s | Oror s | Orol s
    => let t := aword s in (t, aword U8, t)
  | Ovlsr _ s | Ovlsl _ s | Ovasr _ s
    => let t := aword s in (t, aword U128, t)
  | Oeq k | Oneq k =>
    let t := type_of_opk k in
    (t, t, abool)
  | Olt k | Ole k | Ogt k | Oge k =>
    let t := type_of_opk (opk_of_cmpk k) in
    (t, t, abool)
  | Owi2 s sz o => type_of_wiop2 sz o
  end.

Lemma e_type_of_op2 o :
  let t := etype_of_op2 o in
  type_of_op2 o = (to_atype t.1.1, to_atype t.1.2, to_atype t.2).
Proof.
  case: o => //= *; try rewrite !(e_type_of_opk) //.
  by apply e_type_of_wiop2.
Qed.

(* Type of n-ary operators: inputs, output *)

Definition tin_combine_flags := [:: abool; abool; abool; abool].

Definition type_of_opN (op: opN) : seq atype * atype :=
  match op with
  | Opack ws p =>
    let n := nat_of_wsize ws %/ nat_of_pelem p in
    (nseq n aint, aword ws)
  | Oarray len => (nseq (Z.to_nat len) (aword U8), aarr U8 len)
  | Ocombine_flags c => (tin_combine_flags, abool)
  end.

Definition type_of_opN_safety (op: opN_safety) : seq atype * atype :=
  (match op with
   | Ois_arr_init len | Ois_barr_init len => [:: aarr U8 len; aint; aint]
   end, abool).
