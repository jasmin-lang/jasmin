Require Import utils wsize.
From elpi.apps Require Import derive.std.
From HB Require Import structures.
From mathcomp Require Import eqtype .
From Coq Require Export ZArith.



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
(* [ (Omake_arr len) e ] returns a fresh array of length [len], initialized with [e] *)
| Oarr_make of positive
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
| Ocombine_flags of combine_flags
| Ois_arr_init of positive
| Ois_barr_init of positive
.

HB.instance Definition _ := hasDecEq.Build op_kind op_kind_eqb_OK.

HB.instance Definition _ := hasDecEq.Build sop1 sop1_eqb_OK.

HB.instance Definition _ := hasDecEq.Build sop2 sop2_eqb_OK.

HB.instance Definition _ := hasDecEq.Build opN opN_eqb_OK.

(* -------------------------------------------------------------------- *)


Inductive init_cond :=
  | IBool of bool
  | IConst of Z
  | IVar of nat
  | IOp1 of sop1 & init_cond
  | IOp2 of sop2 & init_cond & init_cond
.
