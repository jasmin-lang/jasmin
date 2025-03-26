Require Import wsize.
From HB Require Import structures.
Require Import  ZArith.

(* -------------------------------------------------------------------- *)
(* ** Operators
 * -------------------------------------------------------------------- *)
(* *** Summary
   Operators represent several constructs in the Ocaml compiler:
   - const-op: compile-time expressions (constexpr in C++)
   - list-op: argument and result lists
   - arr-op: reading and writing arrays
   - cpu-op: CPU instructions such as addition with carry
*)
Variant cmp_kind :=
  | Cmp_int
  | Cmp_w of signedness & wsize.

Variant op_kind :=
  | Op_int
  | Op_w of wsize.

Variant sop1 :=
| Oword_of_int of wsize     (* int → word *)
| Oint_of_word of wsize     (* word → unsigned int *)
| Osignext of wsize & wsize (* Sign-extension: output-size, input-size *)
| Ozeroext of wsize & wsize (* Zero-extension: output-size, input-size *)
| Onot                      (* Boolean negation *)
| Olnot of wsize            (* Bitwize not: 1s’ complement *)
| Oneg  of op_kind          (* Arithmetic negation *)
.

Variant sop2 :=
| Obeq                        (* const : sbool -> sbool -> sbool *)
| Oand                        (* const : sbool -> sbool -> sbool *)
| Oor                         (* const : sbool -> sbool -> sbool *)

| Oadd  of op_kind
| Omul  of op_kind
| Osub  of op_kind
| Odiv  of cmp_kind
| Omod  of cmp_kind

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
.
(* -------------------------------------------------------------------- *)


Inductive init_cond :=
  | IBool of bool
  | IConst of Z
  | IVar of nat
  | IOp1 of sop1 & init_cond
  | IOp2 of sop2 & init_cond & init_cond
.