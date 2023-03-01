(* ** Imports and settings *)
From mathcomp Require Import all_ssreflect all_algebra.
Require Import oseq.
Require Export ZArith Setoid Morphisms.
From mathcomp Require Import word_ssrZ.
Require Export strings word utils type ident var global sem_type sopn.
Require Import xseq.
Import Utf8 ZArith.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Unset Elimination Schemes.

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

(* N-ary operators *)
Variant combine_flags_core := 
| CFC_O       (* overflow:                                OF = 1 *)
| CFC_B       (* below, not above or equal:               CF = 1 *)
| CFC_E       (* equal, zero:                             ZF = 1 *)
| CFC_S       (* sign:                                    SF = 1 *)
| CFC_L       (* less than, not greater than or equal to: !(OF = SF) *)
| CFC_BE      (* below or equal, not above:               CF = 1 \/ ZF = 1 *)
| CFC_LE      (* less than or equal to, not greater than: (!(SF = OF) \/ ZF = 1 *)
.

Variant combine_flags :=
| CF_LT    of signedness   (* Alias : signed => L  ; unsigned => B   *) 
| CF_LE    of signedness   (* Alias : signed => LE ; unsigned => BE  *)
| CF_EQ                    (* Alias : E                              *)
| CF_NEQ                   (* Alias : !E                             *)
| CF_GE    of signedness   (* Alias : signed => !L ; unsigned => !B  *)
| CF_GT    of signedness   (* Alias : signed => !LE; unsigned => !BE *)
.

Variant opN :=
| Opack of wsize & pelem (* Pack words of size pelem into one word of wsize *)
| Ocombine_flags of combine_flags
.

Scheme Equality for sop1.
(* Definition sop1_beq : sop1 -> sop1 -> bool *)

Lemma sop1_eq_axiom : Equality.axiom sop1_beq.
Proof.
  move=> x y;apply:(iffP idP).
  + by apply: internal_sop1_dec_bl.
  by apply: internal_sop1_dec_lb.
Qed.

Definition sop1_eqMixin     := Equality.Mixin sop1_eq_axiom.
Canonical  sop1_eqType      := Eval hnf in EqType sop1 sop1_eqMixin.

Scheme Equality for sop2.
(* Definition sop2_beq : sop2 -> sop2 -> bool *)

Lemma sop2_eq_axiom : Equality.axiom sop2_beq.
Proof.
  move=> x y;apply:(iffP idP).
  + by apply: internal_sop2_dec_bl.
  by apply: internal_sop2_dec_lb.
Qed.

Definition sop2_eqMixin     := Equality.Mixin sop2_eq_axiom.
Canonical  sop2_eqType      := Eval hnf in EqType sop2 sop2_eqMixin.

Scheme Equality for combine_flags_core.

Lemma combine_flags_core_eq_axiom : Equality.axiom combine_flags_core_beq.
Proof.
  move=> x y;apply:(iffP idP).
  + by apply: internal_combine_flags_core_dec_bl.
  by apply: internal_combine_flags_core_dec_lb.
Qed.

Definition combine_flags_core_eqMixin     := Equality.Mixin combine_flags_core_eq_axiom.
Canonical  combine_flags_core_eqType      := Eval hnf in EqType combine_flags_core combine_flags_core_eqMixin.

Scheme Equality for combine_flags.

Lemma combine_flags_eq_axiom : Equality.axiom combine_flags_beq.
Proof.
  move=> x y;apply:(iffP idP).
  + by apply: internal_combine_flags_dec_bl.
  by apply: internal_combine_flags_dec_lb.
Qed.

Definition combine_flags_eqMixin     := Equality.Mixin combine_flags_eq_axiom.
Canonical  combine_flags_eqType      := Eval hnf in EqType combine_flags combine_flags_eqMixin.

Scheme Equality for opN.

Lemma opN_eq_axiom : Equality.axiom opN_beq.
Proof.
  move=> x y;apply:(iffP idP).
  + by apply: internal_opN_dec_bl.
  by apply: internal_opN_dec_lb.
Qed.

Definition opN_eqMixin     := Equality.Mixin opN_eq_axiom.
Canonical  opN_eqType      := Eval hnf in EqType opN opN_eqMixin.

(* ----------------------------------------------------------------------------- *)

(* Type of unany operators: input, output *)
Definition type_of_op1 (o: sop1) : stype * stype :=
  match o with
  | Oword_of_int sz => (sint, sword sz)
  | Oint_of_word sz => (sword sz, sint)
  | Osignext szo szi
  | Ozeroext szo szi
    => (sword szi, sword szo)
  | Onot => (sbool, sbool)
  | Olnot sz
  | Oneg (Op_w sz)
    => let t := sword sz in (t, t)
  | Oneg Op_int => (sint, sint)
  end.

(* Type of binany operators: inputs, output *)
Definition type_of_op2 (o: sop2) : stype * stype * stype :=
  match o with
  | Obeq | Oand | Oor => (sbool, sbool, sbool)
  | Oadd Op_int
  | Omul Op_int
  | Osub Op_int
  | Odiv Cmp_int | Omod Cmp_int
  | Olsl Op_int | Oasr Op_int
    => (sint, sint, sint)
  | Oadd (Op_w s)
  | Omul (Op_w s)
  | Osub (Op_w s)
  | Odiv (Cmp_w _ s) | Omod (Cmp_w _ s)
  | Oland s | Olor s | Olxor s | Ovadd _ s | Ovsub _ s | Ovmul _ s
    => let t := sword s in (t, t, t)
  | Olsr s | Olsl (Op_w s) | Oasr (Op_w s)
  | Ovlsr _ s | Ovlsl _ s | Ovasr _ s
    => let t := sword s in (t, sword8, t)
  | Oeq Op_int | Oneq Op_int
  | Olt Cmp_int | Ole Cmp_int
  | Ogt Cmp_int | Oge Cmp_int
    => (sint, sint, sbool)
  | Oeq (Op_w s) | Oneq (Op_w s)
  | Olt (Cmp_w _ s) | Ole (Cmp_w _ s)
  | Ogt (Cmp_w _ s) | Oge (Cmp_w _ s)
    => let t := sword s in (t, t, sbool)
  end.

(* Type of n-ary operators: inputs, output *)

Definition cf_tbl (c:combine_flags) := 
  match c with
  | CF_LT Signed   => (false, CFC_L)
  | CF_LT Unsigned => (false, CFC_B)
  | CF_LE Signed   => (false, CFC_LE)
  | CF_LE Unsigned => (false, CFC_BE)
  | CF_EQ          => (false, CFC_E)
  | CF_NEQ         => (true , CFC_E)
  | CF_GE Signed   => (true , CFC_L)
  | CF_GE Unsigned => (true , CFC_B)
  | CF_GT Signed   => (true , CFC_LE)
  | CF_GT Unsigned => (true , CFC_BE)
  end.
  
Definition tin_combine_flags := [:: sbool; sbool; sbool; sbool].

Definition type_of_opN (op: opN) : seq stype * stype :=
  match op with
  | Opack ws p =>
    let n := nat_of_wsize ws %/ nat_of_pelem p in
    (nseq n sint, sword ws)
  | Ocombine_flags c => (tin_combine_flags, sbool) 
  end.

(* ** Expressions
 * -------------------------------------------------------------------- *)
(* Used only by the ocaml compiler *)
Definition var_info := positive.

Record var_i := VarI {
  v_var :> var;
  v_info : var_info
}.

Notation vid ident :=
  {|
    v_var :=
      {|
        vtype := sword Uptr;
        vname := ident%string;
      |};
    v_info := xH;
  |}.

Definition var_i_beq x1 x2 :=
  match x1, x2 with
  | VarI x1 i1, VarI x2 i2 => (x1 == x2) && (i1 == i2)
  end.

Lemma var_i_eq_axiom : Equality.axiom var_i_beq.
Proof.
  move=> [x xi] [y yi] /=.
  by apply (iffP andP) => -[] /eqP-> /eqP->.
Qed.

Definition var_i_eqMixin     := Equality.Mixin var_i_eq_axiom.
Canonical  var_i_eqType      := Eval hnf in EqType var_i var_i_eqMixin.

Record var_attr := VarA {
  va_pub : bool
}.

Variant v_scope := 
  | Slocal 
  | Sglob.

Scheme Equality for v_scope.

Lemma v_scope_eq_axiom : Equality.axiom v_scope_beq.
Proof.
  move=> x y;apply:(iffP idP).
  + by apply: internal_v_scope_dec_bl.
  by apply: internal_v_scope_dec_lb.
Qed.

Definition v_scope_eqMixin     := Equality.Mixin v_scope_eq_axiom.
Canonical  v_scope_eqType      := Eval hnf in EqType v_scope v_scope_eqMixin.

Record gvar := Gvar { gv : var_i; gs : v_scope }.

Definition mk_gvar x := {| gv := x; gs := Sglob  |}.
Definition mk_lvar x := {| gv := x; gs := Slocal |}.

Definition is_lvar (x:gvar) := x.(gs) == Slocal.
Definition is_glob (x:gvar) := x.(gs) == Sglob.

Definition gvar_beq (x1 x2:gvar) := 
  (x1.(gs) == x2.(gs)) && (x1.(gv) == x2.(gv)).

Lemma gvar_eq_axiom : Equality.axiom gvar_beq.
Proof.
  move=> [x1 k1] [x2 k2] /=; apply (equivP andP) => /=.
  by split => [[]/eqP -> /eqP -> |[] -> ->].
Qed.

Definition gvar_eqMixin := Equality.Mixin gvar_eq_axiom.
Canonical gvar_eqType := Eval hnf in EqType gvar gvar_eqMixin.

Inductive pexpr : Type :=
| Pconst :> Z -> pexpr
| Pbool  :> bool -> pexpr
| Parr_init : positive → pexpr
| Pvar   :> gvar -> pexpr
| Pget   : arr_access -> wsize -> gvar -> pexpr -> pexpr
| Psub   : arr_access -> wsize -> positive -> gvar -> pexpr -> pexpr 
| Pload  : wsize -> var_i -> pexpr -> pexpr
| Papp1  : sop1 -> pexpr -> pexpr
| Papp2  : sop2 -> pexpr -> pexpr -> pexpr
| PappN of opN & seq pexpr
| Pif    : stype -> pexpr -> pexpr -> pexpr -> pexpr.

Notation pexprs := (seq pexpr).

Definition Plvar x := Pvar (mk_lvar x).

Fixpoint pexpr_beq (e1 e2:pexpr) : bool :=
  match e1, e2 with
  | Pconst n1   , Pconst n2    => n1 == n2
  | Pbool  b1   , Pbool  b2    => b1 == b2
  | Parr_init n1, Parr_init n2 => n1 == n2
  | Pvar   x1   , Pvar   x2    => (x1 == x2)
  | Pget aa1 sz1 x1 e1, Pget aa2 sz2 x2 e2 => (aa1 == aa2) && (sz1 == sz2) && (x1 == x2) && pexpr_beq e1 e2
  | Psub aa1 sz1 len1 x1 e1, Psub aa2 sz2 len2 x2 e2 => (aa1 == aa2) && (sz1 == sz2) && (len1 == len2) && (x1 == x2) && pexpr_beq e1 e2
  | Pload sz1 x1 e1, Pload sz2 x2 e2 => (sz1 == sz2) && (x1 == x2) && pexpr_beq e1 e2
  | Papp1 o1 e1 , Papp1  o2 e2 => (o1 == o2) && pexpr_beq e1 e2
  | Papp2 o1 e11 e12, Papp2 o2 e21 e22  =>
     (o1 == o2) && pexpr_beq e11 e21 && pexpr_beq e12 e22
  | PappN o1 es1, PappN o2 es2 =>
    (o1 == o2) && all2 pexpr_beq es1 es2
  | Pif t1 b1 e11 e12, Pif t2 b2 e21 e22  =>
     (t1 == t2) && pexpr_beq b1 b2 && pexpr_beq e11 e21 && pexpr_beq e12 e22
  | _, _ => false
  end.

Lemma pexpr_eq_axiom : Equality.axiom pexpr_beq.
Proof.
  rewrite /Equality.axiom.
  fix Hrec 1; move =>
    [n1|b1|n1|x1|aa1 w1 x1 e1|aa1 w1 x1 e1 len1|w1 x1 e1|o1 e1|o1 e11 e12|o1 es1|st1 t1 e11 e12]
    [n2|b2|n2|x2|aa2 w2 x2 e2|aa2 w2 x2 e2 len2|w2 x2 e2|o2 e2|o2 e21 e22|o2 es2|st2 t2 e21 e22] /=;
  try by constructor.
  + by apply (iffP idP) => [|[]] /eqP ->.
  + by apply (iffP idP) => [|[]] /eqP ->.
  + by apply (iffP idP) => [|[]] /eqP ->.
  + by apply (iffP idP) => [|[]] /eqP ->.
  + by apply (iffP idP) => [/andP[]/andP[]/andP[] | []] /eqP -> /eqP -> /eqP -> /Hrec ->.
  + by apply (iffP idP) => [/andP[]/andP[]/andP[]/andP[] | []] /eqP -> /eqP -> /eqP -> /eqP -> /Hrec ->.
  + by apply (iffP idP) => [/andP[]/andP[] | []] /eqP -> /eqP -> /Hrec ->.
  + by apply (iffP idP) => [/andP[] | []] /eqP -> /Hrec ->.
  + by apply (iffP idP) => [/andP[]/andP[] | []] /eqP -> /Hrec -> /Hrec ->.
  + by apply (iffP idP) => [/andP[] | []] /eqP -> /(reflect_all2_eqb Hrec) ->.
  by apply (iffP idP) => [/andP[]/andP[]/andP[] | []] /eqP -> /Hrec -> /Hrec -> /Hrec ->.
Qed.

Definition pexpr_eqMixin := Equality.Mixin pexpr_eq_axiom.
Canonical  pexpr_eqType  := Eval hnf in EqType pexpr pexpr_eqMixin.

(* ** Left values
 * -------------------------------------------------------------------- *)

Variant lval : Type :=
| Lnone `(var_info) `(stype)
| Lvar  `(var_i)
| Lmem  `(wsize) `(var_i) `(pexpr)
| Laset `(arr_access) `(wsize) `(var_i) `(pexpr)
| Lasub `(arr_access) `(wsize) `(positive) `(var_i) `(pexpr).

Coercion Lvar : var_i >-> lval.

Notation lvals := (seq lval).

Definition lval_beq (x1:lval) (x2:lval) :=
  match x1, x2 with
  | Lnone i1 t1, Lnone i2 t2 => (i1 == i2) && (t1 == t2)
  | Lvar  x1   , Lvar  x2    => x1 == x2
  | Lmem w1 x1 e1, Lmem w2 x2 e2 => (w1 == w2) && (x1 == x2) && (e1 == e2)
  | Laset aa1 w1 x1 e1, Laset aa2 w2 x2 e2 => (aa1 == aa2) && (w1 == w2) && (x1 == x2) && (e1 == e2)
  | Lasub aa1 w1 len1 x1 e1, Lasub aa2 w2 len2 x2 e2 => (aa1 == aa2) && (w1 == w2) && (len1 == len2) && (x1 == x2) && (e1 == e2)
  | _          , _           => false
  end.

Lemma lval_eq_axiom : Equality.axiom lval_beq.
Proof.
  case=>
    [i1 t1|x1|w1 x1 e1|aa1 w1 x1 e1|aa1 w1 len1 x1 e1]
    [i2 t2|x2|w2 x2 e2|aa2 w2 x2 e2|aa2 w2 len2 x2 e2] /=;
  try by constructor.
  + by apply (iffP idP) => [/andP[] | []] /eqP -> /eqP ->.
  + by apply (iffP idP) => [| []] /eqP ->.
  + by apply (iffP idP) => [/andP[]/andP[] | []] /eqP -> /eqP -> /eqP ->.
  + by apply (iffP idP) => [/andP[]/andP[]/andP[] | []] /eqP -> /eqP -> /eqP -> /eqP ->.
  by apply (iffP idP) => [/andP[]/andP[]/andP[]/andP[] | []] /eqP -> /eqP -> /eqP -> /eqP -> /eqP ->.
Qed.

Definition lval_eqMixin     := Equality.Mixin lval_eq_axiom.
Canonical  lval_eqType      := Eval hnf in EqType lval lval_eqMixin.

(* ** Instructions
 * -------------------------------------------------------------------- *)

Variant dir := UpTo | DownTo.

Scheme Equality for dir.

Lemma dir_eq_axiom : Equality.axiom dir_beq.
Proof.
  move=> x y;apply:(iffP idP).
  + by apply: internal_dir_dec_bl.
  by apply: internal_dir_dec_lb.
Qed.

Definition dir_eqMixin     := Equality.Mixin dir_eq_axiom.
Canonical  dir_eqType      := Eval hnf in EqType dir dir_eqMixin.

Definition range := (dir * pexpr * pexpr)%type.

Definition wrange d (n1 n2 : Z) :=
  let n := Z.to_nat (n2 - n1) in
  match d with
  | UpTo   => [seq (Z.add n1 (Z.of_nat i)) | i <- iota 0 n]
  | DownTo => [seq (Z.sub n2 (Z.of_nat i)) | i <- iota 0 n]
  end.

Definition instr_info := positive.

Variant assgn_tag :=
  | AT_none       (* assignment introduced by the developer that can be removed *)
  | AT_keep       (* assignment that should be kept by the compiler *)
  | AT_rename     (* equality constraint introduced by inline, used in reg-alloc
                     and compiled to no-op *)
  | AT_inline     (* assignment to be propagated and removed later : introduced
                     by unrolling, inlining or lowering *)
  | AT_phinode    (* renaming during SSA transformation *)
  .

Scheme Equality for assgn_tag.

Lemma assgn_tag_eq_axiom : Equality.axiom assgn_tag_beq.
Proof.
  move=> x y;apply:(iffP idP).
  + by apply: internal_assgn_tag_dec_bl.
  by apply: internal_assgn_tag_dec_lb.
Qed.

Definition assgn_tag_eqMixin     := Equality.Mixin assgn_tag_eq_axiom.
Canonical  assgn_tag_eqType      := Eval hnf in EqType assgn_tag assgn_tag_eqMixin.

(* -------------------------------------------------------------------- *)

Variant inline_info :=
  | InlineFun
  | DoNotInline.

Scheme Equality for inline_info.

Lemma inline_info_eq_axiom : Equality.axiom inline_info_beq.
Proof.
  move=> x y;apply:(iffP idP).
  + by apply: internal_inline_info_dec_bl.
  by apply: internal_inline_info_dec_lb.
Qed.

Definition inline_info_eqMixin     := Equality.Mixin inline_info_eq_axiom.
Canonical  inline_info_eqType      := Eval hnf in EqType inline_info inline_info_eqMixin.

(* -------------------------------------------------------------------- *)

Variant align :=
  | Align
  | NoAlign.

Scheme Equality for align.

Lemma align_eq_axiom : Equality.axiom align_beq.
Proof.
  move=> x y;apply:(iffP idP).
  + by apply: internal_align_dec_bl.
  by apply: internal_align_dec_lb.
Qed.

Definition align_eqMixin     := Equality.Mixin align_eq_axiom.
Canonical  align_eqType      := Eval hnf in EqType align align_eqMixin.

(* -------------------------------------------------------------------- *)

(* ----------------------------------------------------------------------------- *)

Section ASM_OP.

Context `{asmop:asmOp}.

Inductive instr_r :=
| Cassgn : lval -> assgn_tag -> stype -> pexpr -> instr_r
| Copn   : lvals -> assgn_tag -> sopn -> pexprs -> instr_r

| Cif    : pexpr -> seq instr -> seq instr  -> instr_r
| Cfor   : var_i -> range -> seq instr -> instr_r
| Cwhile : align -> seq instr -> pexpr -> seq instr -> instr_r
| Ccall  : inline_info -> lvals -> funname -> pexprs -> instr_r

with instr := MkI : instr_info -> instr_r ->  instr.

End ASM_OP.

Notation cmd := (seq instr).

Section ASM_OP.

Context `{asmop:asmOp}.

Fixpoint instr_r_beq (i1 i2:instr_r) :=
  match i1, i2 with
  | Cassgn x1 tag1 ty1 e1, Cassgn x2 tag2 ty2 e2 =>
     (tag1 == tag2) && (ty1 == ty2) && (x1 == x2) && (e1 == e2)
  | Copn x1 tag1 o1 e1, Copn x2 tag2 o2 e2 =>
     (x1 == x2) && (tag1 == tag2) && (o1 == o2) && (e1 == e2)
  | Cif e1 c11 c12, Cif e2 c21 c22 =>
    (e1 == e2) && all2 instr_beq c11 c21 && all2 instr_beq c12 c22
  | Cfor i1 (dir1,lo1,hi1) c1, Cfor i2 (dir2,lo2,hi2) c2 =>
    (i1 == i2) && (dir1 == dir2) && (lo1 == lo2) && (hi1 == hi2) && all2 instr_beq c1 c2
  | Cwhile a1 c1 e1 c1' , Cwhile a2 c2 e2 c2' =>
    (a1 == a2) && all2 instr_beq c1 c2 && (e1 == e2) && all2 instr_beq c1' c2'
  | Ccall ii1 x1 f1 arg1, Ccall ii2 x2 f2 arg2 =>
    (ii1 == ii2) && (x1==x2) && (f1 == f2) && (arg1 == arg2)
  | _, _ => false
  end
with instr_beq i1 i2 :=
  match i1, i2 with
  | MkI if1 i1, MkI if2 i2 => (if1 == if2) && (instr_r_beq i1 i2)
  end.

Section EQI.
  Variable Heq : forall (x y:instr_r), reflect (x=y) (instr_r_beq x y).

  Lemma instr_eq_axiom_ : Equality.axiom instr_beq.
  Proof.
    move=> [ii1 ir1] [ii2 ir2] /=.
    by apply (iffP andP) => -[] /eqP -> /Heq ->.
  Defined.
End EQI.

Lemma instr_r_eq_axiom : Equality.axiom instr_r_beq.
Proof.
  rewrite /Equality.axiom.
  fix Hrec 1; move =>
    [x1 t1 ty1 e1|x1 t1 o1 e1|e1 c11 c12|x1 [[dir1 lo1] hi1] c1|a1 c1 e1 c1'|ii1 x1 f1 arg1 ]
    [x2 t2 ty2 e2|x2 t2 o2 e2|e2 c21 c22|x2 [[dir2 lo2] hi2] c2|a2 c2 e2 c2'|ii2 x2 f2 arg2 ] /=;
  try by constructor.
  + by apply (iffP idP) => [/andP[]/andP[]/andP[] | []] /eqP -> /eqP -> /eqP -> /eqP ->.
  + by apply (iffP idP) => [/andP[]/andP[]/andP[] | []] /eqP -> /eqP -> /eqP -> /eqP ->.
  + have Hrec2 := reflect_all2_eqb (instr_eq_axiom_ Hrec).
    by apply (iffP idP) => [/andP[]/andP[] | []] /eqP -> /Hrec2 -> /Hrec2 ->.
  + have Hrec2 := reflect_all2_eqb (instr_eq_axiom_ Hrec).
    by apply (iffP idP) => [/andP[]/andP[]/andP[]/andP[] | []] /eqP -> /eqP -> /eqP -> /eqP -> /Hrec2 ->.
  + have Hrec2 := reflect_all2_eqb (instr_eq_axiom_ Hrec).
    by apply (iffP idP) => [/andP[]/andP[]/andP[] | []] /eqP -> /Hrec2 -> /eqP -> /Hrec2 ->.
  by apply (iffP idP) => [/andP[]/andP[]/andP[] | []] /eqP -> /eqP -> /eqP -> /eqP ->.
Qed.

Definition instr_r_eqMixin     := Equality.Mixin instr_r_eq_axiom.
Canonical  instr_r_eqType      := Eval hnf in EqType instr_r instr_r_eqMixin.

Lemma instr_eq_axiom : Equality.axiom instr_beq.
Proof.
  apply: instr_eq_axiom_ instr_r_eq_axiom .
Qed.

Definition instr_eqMixin     := Equality.Mixin instr_eq_axiom.
Canonical  instr_eqType      := Eval hnf in EqType instr instr_eqMixin.

(* ** Functions
 * -------------------------------------------------------------------- *)

Definition fun_info := positive.

Class progT (eft:eqType) := {
  extra_prog_t : Type;
  extra_val_t  : Type;
}.

Definition extra_fun_t {eft} {pT: progT eft} := eft.

Record _fundef (extra_fun_t: Type) := MkFun {
  f_info   : fun_info;
  f_tyin   : seq stype;
  f_params : seq var_i;
  f_body   : cmd;
  f_tyout  : seq stype;
  f_res    : seq var_i;
  f_extra  : extra_fun_t;
}.

Definition _fun_decl (extra_fun_t: Type) := (funname * _fundef extra_fun_t)%type.

Record _prog (extra_fun_t: Type) (extra_prog_t: Type):= {
  p_funcs : seq (_fun_decl extra_fun_t);
  p_globs : glob_decls;
  p_extra : extra_prog_t;
}.

Section PROG.

Context {eft} {pT:progT eft}.

Definition fundef := _fundef extra_fun_t.

Definition function_signature : Type :=
  (seq stype * seq stype).

Definition signature_of_fundef (fd: fundef) : function_signature :=
  (f_tyin fd, f_tyout fd).

Definition fun_decl := (funname * fundef)%type.

Definition prog := _prog extra_fun_t extra_prog_t.

Definition fundef_beq (fd1 fd2:fundef) :=
  match fd1, fd2 with
  | MkFun ii1 tin1 x1 c1 tout1 r1 e1, MkFun ii2 tin2 x2 c2 tout2 r2 e2 =>
    (ii1 == ii2) && (tin1 == tin2) && (x1 == x2) && (c1 == c2) && (tout1 == tout2) && (r1 == r2) && (e1 == e2)
  end.

Lemma fundef_eq_axiom : Equality.axiom fundef_beq.
Proof.
  move=> [i1 tin1 p1 c1 tout1 r1 e1] [i2 tin2 p2 c2 tout2 r2 e2] /=.
  by apply (iffP idP) => [/andP[]/andP[]/andP[]/andP[]/andP[]/andP[] | []]
    /eqP->/eqP->/eqP->/eqP->/eqP->/eqP->/eqP->.
Qed.

Definition fundef_eqMixin     := Equality.Mixin fundef_eq_axiom.
Canonical  fundef_eqType      := Eval hnf in EqType fundef fundef_eqMixin.

Definition Build_prog p_funcs p_globs p_extra : prog := Build__prog p_funcs p_globs p_extra.

End PROG.

End ASM_OP.

Notation fun_decls  := (seq fun_decl).

Section ASM_OP.

Context {pd: PointerData}.
Context `{asmop:asmOp}.

(* ** Programs before stack/memory allocation 
 * -------------------------------------------------------------------- *)

Definition progUnit : progT [eqType of unit] :=
  {| extra_val_t := unit;
     extra_prog_t := unit;
  |}.

Definition ufundef     := @fundef _ _ _ progUnit.
Definition ufun_decl   := @fun_decl _ _ _ progUnit.
Definition ufun_decls  := seq (@fun_decl _ _ _ progUnit).
Definition uprog       := @prog _ _ _ progUnit.

(* For extraction *)
Definition _ufundef    := _fundef unit. 
Definition _ufun_decl  := _fun_decl unit.
Definition _ufun_decls :=  seq (_fun_decl unit).
Definition _uprog      := _prog unit unit. 
Definition to_uprog (p:_uprog) : uprog := p.

(* ** Programs after stack/memory allocation 
 * -------------------------------------------------------------------- *)

Variant saved_stack :=
| SavedStackNone
| SavedStackReg of var
| SavedStackStk of Z.

Definition saved_stack_beq (x y : saved_stack) :=
  match x, y with
  | SavedStackNone, SavedStackNone => true
  | SavedStackReg v1, SavedStackReg v2 => v1 == v2
  | SavedStackStk z1, SavedStackStk z2 => z1 == z2
  | _, _ => false
  end.

Lemma saved_stack_eq_axiom : Equality.axiom saved_stack_beq.
Proof.
  move=> [ | v1 | z1] [ | v2 | z2] /=; try by constructor.
  + by apply (iffP eqP); congruence.
  by apply (iffP eqP); congruence.
Qed.

Definition saved_stack_eqMixin   := Equality.Mixin saved_stack_eq_axiom.
Canonical  saved_stack_eqType    := Eval hnf in EqType saved_stack saved_stack_eqMixin.

Variant return_address_location :=
| RAnone
| RAreg of var
| RAstack of Z.

Definition return_address_location_beq (r1 r2: return_address_location) : bool :=
  match r1 with
  | RAnone => if r2 is RAnone then true else false
  | RAreg x1 => if r2 is RAreg x2 then x1 == x2 else false
  | RAstack z1 => if r2 is RAstack z2 then z1 == z2 else false
  end.

Lemma return_address_location_eq_axiom : Equality.axiom return_address_location_beq.
Proof.
  case => [ | x1 | z1 ] [ | x2 | z2 ] /=; try by constructor.
  + by apply (iffP eqP); congruence.
  by apply (iffP eqP); congruence.
Qed.

Definition return_address_location_eqMixin := Equality.Mixin return_address_location_eq_axiom.
Canonical  return_address_location_eqType  := Eval hnf in EqType return_address_location return_address_location_eqMixin.

Record stk_fun_extra := MkSFun { 
  sf_align          : wsize;
  sf_stk_sz         : Z;
  sf_stk_extra_sz   : Z;
  sf_stk_max        : Z; 
  sf_to_save        : seq (var * Z);
  sf_save_stack     : saved_stack;
  sf_return_address : return_address_location;
}.

Definition sfe_beq (e1 e2: stk_fun_extra) : bool :=
  (e1.(sf_align) == e2.(sf_align)) &&
  (e1.(sf_stk_sz) == e2.(sf_stk_sz)) &&
  (e1.(sf_stk_max) == e2.(sf_stk_max)) && 
  (e1.(sf_stk_extra_sz) == e2.(sf_stk_extra_sz)) &&
  (e1.(sf_to_save) == e2.(sf_to_save)) &&
  (e1.(sf_save_stack) == e2.(sf_save_stack)) &&
  (e1.(sf_return_address) == e2.(sf_return_address)).

Lemma sfe_eq_axiom : Equality.axiom sfe_beq.
Proof.
  case => a b c d e f g [] a' b' c' d' e' f' g'; apply: (equivP andP) => /=; split.
  + by case => /andP[] /andP[] /andP[] /andP[] /andP [] /eqP <- /eqP <- /eqP <- /eqP <- /eqP <- /eqP <- /eqP <-.
  by case => <- <- <- <- <- <- <-; rewrite !eqxx.
Qed.

Definition sfe_eqMixin   := Equality.Mixin sfe_eq_axiom.
Canonical  sfe_eqType    := Eval hnf in EqType stk_fun_extra sfe_eqMixin.

Record sprog_extra := {
  sp_rsp   : Ident.ident;
  sp_rip   : Ident.ident;
  sp_globs : seq u8;
}.

Definition progStack : progT [eqType of stk_fun_extra] := 
  {| extra_val_t := pointer;
     extra_prog_t := sprog_extra  |}.

Definition sfundef     := @fundef _ _ _ progStack.
Definition sfun_decl   := @fun_decl _ _ _ progStack.
Definition sfun_decls  := seq (@fun_decl _ _ _ progStack).
Definition sprog       := @prog _ _ _ progStack.

(* For extraction *)

Definition _sfundef    := _fundef stk_fun_extra.
Definition _sfun_decl  := _fun_decl stk_fun_extra. 
Definition _sfun_decls := seq (_fun_decl stk_fun_extra).
Definition _sprog      := _prog stk_fun_extra sprog_extra.
Definition to_sprog (p:_sprog) : sprog := p.

(* Update functions *)
Definition with_body eft (fd:_fundef eft) body := {|
  f_info   := fd.(f_info);
  f_tyin   := fd.(f_tyin);
  f_params := fd.(f_params);
  f_body   := body;
  f_tyout  := fd.(f_tyout);
  f_res    := fd.(f_res);
  f_extra  := fd.(f_extra);
|}.

Definition swith_extra {_: PointerData} (fd:ufundef) f_extra : sfundef := {|
  f_info   := fd.(f_info);
  f_tyin   := fd.(f_tyin);
  f_params := fd.(f_params);
  f_body   := fd.(f_body);
  f_tyout  := fd.(f_tyout);
  f_res    := fd.(f_res);
  f_extra  := f_extra;
|}.

End ASM_OP.

Section ASM_OP.

Context `{asmop:asmOp}.
Context {eft} {pT : progT eft}.

(* ** Some smart constructors
 * -------------------------------------------------------------------------- *)

Definition is_const (e:pexpr) :=
  match e with
  | Pconst n => Some n
  | _        => None
  end.

Definition is_bool (e:pexpr) :=
  match e with
  | Pbool b => Some b
  | _ => None
  end.

Definition cast_w ws := Papp1 (Oword_of_int ws).

Section WITH_POINTER_DATA.
Context {pd: PointerData}.

Definition cast_ptr := cast_w Uptr.

Definition cast_const z := cast_ptr (Pconst z).

End WITH_POINTER_DATA.

Definition wconst (sz: wsize) (n: word sz) : pexpr :=
  Papp1 (Oword_of_int sz) (Pconst (wunsigned n)).

Definition is_wconst (sz: wsize) (e: pexpr) : option (word sz) :=
  match e with
  | Papp1 (Oword_of_int sz') e =>
    if (sz <= sz')%CMP then
      is_const e >>= λ n, Some (zero_extend sz (wrepr sz' n))
    else None
  | _       => None
  end%O.

Definition is_wconst_of_size sz (e: pexpr) : option Z :=
  match e with
  | Papp1 (Oword_of_int sz') (Pconst z) =>
    if sz' == sz then Some z else None
  | _ => None end.

(* ** Compute written variables
 * -------------------------------------------------------------------- *)

Definition vrv_rec (s:Sv.t) (rv:lval) :=
  match rv with
  | Lnone _ _  => s
  | Lvar  x    => Sv.add x s
  | Lmem _ _ _  => s
  | Laset _ _ x _  => Sv.add x s
  | Lasub _ _ _ x _ => Sv.add x s
  end.

Definition vrvs_rec s (rv:lvals) := foldl vrv_rec s rv.

Definition vrv := (vrv_rec Sv.empty).
Definition vrvs := (vrvs_rec Sv.empty).

Definition lv_write_mem (r:lval) : bool :=
  if r is Lmem _ _ _ then true else false.

Fixpoint write_i_rec s (i:instr_r) :=
  match i with
  | Cassgn x _ _ _    => vrv_rec s x
  | Copn xs _ _ _   => vrvs_rec s xs
  | Cif   _ c1 c2   => foldl write_I_rec (foldl write_I_rec s c2) c1
  | Cfor  x _ c     => foldl write_I_rec (Sv.add x s) c
  | Cwhile _ c _ c'   => foldl write_I_rec (foldl write_I_rec s c') c
  | Ccall _ x _ _   => vrvs_rec s x
  end
with write_I_rec s i :=
  match i with
  | MkI _ i => write_i_rec s i
  end.

Definition write_i i := write_i_rec Sv.empty i.

Definition write_I i := write_I_rec Sv.empty i.

Definition write_c_rec s c := foldl write_I_rec s c.

Definition write_c c := write_c_rec Sv.empty c.

(* ** Compute read variables
 * -------------------------------------------------------------------- *)

Definition read_gvar (x:gvar) := 
  if is_lvar x then Sv.singleton x.(gv)
  else Sv.empty.

Fixpoint read_e_rec (s:Sv.t) (e:pexpr) : Sv.t :=
  match e with
  | Pconst _
  | Pbool  _
  | Parr_init _    => s
  | Pvar   x       => Sv.union (read_gvar x) s
  | Pget _ _ x e   => read_e_rec (Sv.union (read_gvar x) s) e
  | Psub _ _ _ x e => read_e_rec (Sv.union (read_gvar x) s) e
  | Pload _ x e    => read_e_rec (Sv.add x s) e
  | Papp1  _ e     => read_e_rec s e
  | Papp2  _ e1 e2 => read_e_rec (read_e_rec s e2) e1
  | PappN _ es     => foldl read_e_rec s es
  | Pif  _ t e1 e2 => read_e_rec (read_e_rec (read_e_rec s e2) e1) t
  end.

Definition read_e := read_e_rec Sv.empty.
Definition read_es_rec := foldl read_e_rec.
Definition read_es := read_es_rec Sv.empty.

Definition read_rv_rec  (s:Sv.t) (r:lval) :=
  match r with
  | Lnone _ _     => s
  | Lvar  _       => s
  | Lmem _ x e    => read_e_rec (Sv.add x s) e
  | Laset _ _ x e => read_e_rec (Sv.add x s) e
  | Lasub _ _ _ x e => read_e_rec (Sv.add x s) e
  end.

Definition read_rv := read_rv_rec Sv.empty.
Definition read_rvs_rec := foldl read_rv_rec.
Definition read_rvs := read_rvs_rec Sv.empty.

Fixpoint read_i_rec (s:Sv.t) (i:instr_r) : Sv.t :=
  match i with
  | Cassgn x _ _ e => read_rv_rec (read_e_rec s e) x
  | Copn xs _ _ es => read_es_rec (read_rvs_rec s xs) es
  | Cif b c1 c2 =>
    let s := foldl read_I_rec s c1 in
    let s := foldl read_I_rec s c2 in
    read_e_rec s b
  | Cfor x (dir, e1, e2) c =>
    let s := foldl read_I_rec s c in
    read_e_rec (read_e_rec s e2) e1
  | Cwhile a c e c' =>
    let s := foldl read_I_rec s c in
    let s := foldl read_I_rec s c' in
    read_e_rec s e
  | Ccall _ xs _ es => read_es_rec (read_rvs_rec s xs) es
  end
with read_I_rec (s:Sv.t) (i:instr) : Sv.t :=
  match i with
  | MkI _ i => read_i_rec s i
  end.

Definition read_c_rec := foldl read_I_rec.

Definition read_i := read_i_rec Sv.empty.

Definition read_I := read_I_rec Sv.empty.

Definition read_c := read_c_rec Sv.empty.

(* ** Compute occurring variables (= read + write)
 * -------------------------------------------------------------------------- *)

Definition vars_I (i: instr) := Sv.union (read_I i) (write_I i).

Definition vars_c c := Sv.union (read_c c) (write_c c).

Definition vars_lval l := Sv.union (read_rv l) (vrv l).

Definition vars_lvals ls := Sv.union (read_rvs ls) (vrvs ls).

Fixpoint vars_l (l: seq var_i) :=
  match l with
  | [::] => Sv.empty
  | h :: q => Sv.add h (vars_l q)
  end.

Definition vars_fd (fd:fundef) :=
  Sv.union (vars_l fd.(f_params)) (Sv.union (vars_l fd.(f_res)) (vars_c fd.(f_body))).

Definition vars_p (p: fun_decls) :=
  foldr (fun f x => let '(fn, fd) := f in Sv.union x (vars_fd fd)) Sv.empty p.

End ASM_OP.

(* --------------------------------------------------------------------- *)
(* Test the equality of two expressions modulo variable info             *)

Definition eq_gvar x x' := 
  (x.(gs) == x'.(gs)) && (v_var x.(gv) == v_var x'.(gv)).

Fixpoint eq_expr e e' :=
  match e, e' with
  | Pconst z      , Pconst z'         => z == z'
  | Pbool  b      , Pbool  b'         => b == b'
  | Parr_init n   , Parr_init n'      => n == n'
  | Pvar   x      , Pvar   x'         => eq_gvar x x'
  | Pget aa w x e , Pget aa' w' x' e' => (aa==aa') && (w == w') && (eq_gvar x x') && eq_expr e e'
  | Psub aa w len x e , Psub aa' w' len' x' e' => (aa==aa') && (w == w') && (len == len') && (eq_gvar x x') && eq_expr e e'
  | Pload w x e, Pload w' x' e' => (w == w') && (v_var x == v_var x') && eq_expr e e'
  | Papp1  o e    , Papp1  o' e'      => (o == o') && eq_expr e e'
  | Papp2  o e1 e2, Papp2  o' e1' e2' => (o == o') && eq_expr e1 e1' && eq_expr e2 e2'
  | PappN o es, PappN o' es' => (o == o') && (all2 eq_expr es es')
  | Pif t e e1 e2, Pif t' e' e1' e2' =>
    (t == t') && eq_expr e e' && eq_expr e1 e1' && eq_expr e2 e2'
  | _             , _                 => false
  end.

Definition eq_lval (x x': lval) : bool :=
  match x, x' with
  | Lnone _ ty,  Lnone _ ty' => ty == ty'
  | Lvar v, Lvar v' => v_var v == v_var v'
  | Lmem w v e, Lmem w' v' e' => (w == w') && (v_var v == v_var v') && (eq_expr e e')
  | Laset aa w v e, Laset aa' w' v' e'
    => (aa == aa') && (w == w') && (v_var v == v_var v') && (eq_expr e e')
  | Lasub aa w len v e, Lasub aa' w' len' v' e'
    => (aa == aa') && (w == w') && (len == len') && (v_var v == v_var v') && (eq_expr e e')

  | _, _ => false
  end.
