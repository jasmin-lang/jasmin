(* ** Imports and settings *)
From mathcomp Require Import all_ssreflect all_algebra.
Require Import oseq.
Require Export ZArith Setoid Morphisms.
From CoqWord Require Import ssrZ.
Require Export strings word utils type var global sem_type x86_decl x86_instr_decl.
Require Export leakage.
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
| Oword_of_int of wsize (* int → word *)
| Oint_of_word of wsize (* word → unsigned int *)
| Osignext of wsize & wsize (* Sign-extension: output-size, input-size *)
| Ozeroext of wsize & wsize (* Zero-extension: output-size, input-size *)
| Onot (* Boolean negation *)
| Olnot of wsize (* Bitwize not: 1s’ complement *)
| Oneg  of op_kind (* Arithmetic negation *)
.

Variant sop2 :=
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
| Olsl  of wsize
| Oasr  of wsize

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
Variant opN :=
| Opack of wsize & pelem (* Pack words of size pelem into one word of wsize *)
.

Variant sopn : Set :=
(* Generic operation *)
| Omulu     of wsize   (* cpu   : [sword; sword]        -> [sword;sword] *)
| Oaddcarry of wsize   (* cpu   : [sword; sword; sbool] -> [sbool;sword] *)
| Osubcarry of wsize   (* cpu   : [sword; sword; sbool] -> [sbool;sword] *)

(* Low level x86 operations *)
| Oset0     of wsize  (* set register + flags to 0 (implemented using XOR x x or VPXOR x x) *)
| Oconcat128          (* concatenate 2 128 bits word into 1 256 word register *)   
| Ox86MOVZX32
| Ox86      of asm_op  (* x86 instruction *)
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

Scheme Equality for opN.

Lemma opN_eq_axiom : Equality.axiom opN_beq.
Proof.
  move=> x y;apply:(iffP idP).
  + by apply: internal_opN_dec_bl.
  by apply: internal_opN_dec_lb.
Qed.

Definition opN_eqMixin     := Equality.Mixin opN_eq_axiom.
Canonical  opN_eqType      := Eval hnf in EqType opN opN_eqMixin.

Scheme Equality for sopn.
(* Definition sopn_beq : sopn -> sopn -> bool *)
Lemma sopn_eq_axiom : Equality.axiom sopn_beq.
Proof.
  move=> x y;apply:(iffP idP).
  + by apply: internal_sopn_dec_bl.
  by apply: internal_sopn_dec_lb.
Qed.

Definition sopn_eqMixin     := Equality.Mixin sopn_eq_axiom.
Canonical  sopn_eqType      := Eval hnf in EqType sopn sopn_eqMixin.

(* ----------------------------------------------------------------------------- *)

Record instruction := mkInstruction {
  str      : unit -> string;
  tin      : list stype;
  i_in     : seq arg_desc; 
  tout     : list stype;
  i_out    : seq arg_desc;
  semi     : sem_prod tin (exec (sem_tuple tout));
  seml     : LeakOp → sem_prod tin (exec leak_e);
  tin_narr : all is_not_sarr tin;
  wsizei   : wsize;
  i_safe   : seq safe_cond;
}.

Notation mk_instr str tin i_in tout i_out semi seml wsizei safe:=
  {| str      := str;
     tin      := tin;
     i_in     := i_in;
     tout     := tout;
     i_out    := i_out;
     semi     := semi;
     seml     := seml;
     tin_narr := refl_equal;
     wsizei   := wsizei;
     i_safe   := safe;
  |}.

(* ----------------------------------------------------------------------------- *)

Definition Omulu_instr sz := 
  mk_instr (pp_sz "mulu" sz) 
           (w2_ty sz sz) [:: R RAX; E 0]
           (w2_ty sz sz) [:: R RDX; R RAX] (fun x y => ok (@wumul sz x y)) 
           (op_leak_ty (w2_ty sz sz)) sz [::].
 
Definition Oaddcarry_instr sz := 
  mk_instr (pp_sz "adc" sz)
           [::sword sz; sword sz; sbool] 
           [::E 0; E 1; F CF]
           (sbool :: (w_ty sz))  
           [:: F CF; E 0]
           (fun x y c => let p := @waddcarry sz x y c in ok (Some p.1, p.2))
           (op_leak_ty [::sword sz; sword sz; sbool]) sz [::].

Definition Osubcarry_instr sz:= 
  mk_instr (pp_sz "sbb" sz)
           [::sword sz; sword sz; sbool] [::E 0; E 1; F CF]
           (sbool :: (w_ty sz)) [:: F CF; E 0] 
           (fun x y c => let p := @wsubcarry sz x y c in ok (Some p.1, p.2))
           (op_leak_ty [::sword sz; sword sz; sbool]) sz [::].

Definition Oset0_instr sz  :=
  if (sz <= U64)%CMP then 
    mk_instr (pp_sz "set0" sz)
             [::] [::]
             (b5w_ty sz) (implicit_flags ++ [::E 0])
             (let vf := Some false in
              let vt := Some true in
              ok (::vf, vf, vf, vt, vt & (0%R: word sz)))
             (op_leak_ty [::]) sz [::]
  else 
    mk_instr (pp_sz "set0" sz)
             [::] [::]  
             (w_ty sz) [::E 0] 
             (ok (0%R: word sz)) (op_leak_ty [::]) sz [::].

Definition Ox86MOVZX32_instr := 
  mk_instr (pp_s "MOVZX32") 
           [:: sword32] [:: E 1] 
           [:: sword64] [:: E 0] 
           (λ x : u32, ok (zero_extend U64 x)) 
           (op_leak_ty [:: sword32]) U32 [::].

Definition Oconcat128_instr := 
  mk_instr (pp_s "concat_2u128") 
           [:: sword128; sword128 ] [:: E 1; E 2] 
           [:: sword256] [:: E 0] 
           (λ h l : u128, ok (make_vec U256 [::l;h]))
           (op_leak_ty [:: sword128; sword128]) U128 [::].

Definition get_instr o :=
  match o with
  | Omulu     sz => Omulu_instr sz
  | Oaddcarry sz => Oaddcarry_instr sz
  | Osubcarry sz => Osubcarry_instr sz
  | Oset0     sz => Oset0_instr sz
  | Oconcat128   => Oconcat128_instr 
  | Ox86MOVZX32  => Ox86MOVZX32_instr
  | Ox86   instr =>
      let id := instr_desc instr in
      {|
        str      := id.(id_str_jas);
        tin      := id.(id_tin);
        i_in     := id.(id_in);
        i_out    := id.(id_out);
        tout     := id.(id_tout);
        semi     := id.(id_semi);
        seml     := id.(id_seml);
        tin_narr := id.(id_tin_narr);
        wsizei   := id.(id_wsize);
        i_safe   := id.(id_safe)
      |}
  end.

Definition string_of_sopn o : string := str (get_instr o) tt.

Definition sopn_tin o : list stype := tin (get_instr o).
Definition sopn_tout o : list stype := tout (get_instr o).
Definition sopn_sem  o := semi (get_instr o).
Definition wsize_of_sopn o : wsize := wsizei (get_instr o).

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
  | Oand | Oor => (sbool, sbool, sbool)
  | Oadd Op_int
  | Omul Op_int
  | Osub Op_int
  | Odiv Cmp_int | Omod Cmp_int
    => (sint, sint, sint)
  | Oadd (Op_w s)
  | Omul (Op_w s)
  | Osub (Op_w s)
  | Odiv (Cmp_w _ s) | Omod (Cmp_w _ s)
  | Oland s | Olor s | Olxor s | Ovadd _ s | Ovsub _ s | Ovmul _ s
    => let t := sword s in (t, t, t)
  | Olsr s | Olsl s | Oasr s
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
Definition type_of_opN (op: opN) : seq stype * stype :=
  match op with
  | Opack ws p =>
    let n := nat_of_wsize ws %/ nat_of_pelem p in
    (nseq n sint, sword ws)
  end.

(* ** Expressions
 * -------------------------------------------------------------------- *)
(* Used only by the ocaml compiler *)

Inductive pexpr : Type :=
| Pconst :> Z -> pexpr
| Pbool  :> bool -> pexpr
| Parr_init : positive → pexpr
| Pvar   :> var_i -> pexpr
| Pglobal :> global -> pexpr
| Pget   : wsize -> var_i -> pexpr -> pexpr
| Pload  : wsize -> var_i -> pexpr -> pexpr
| Papp1  : sop1 -> pexpr -> pexpr
| Papp2  : sop2 -> pexpr -> pexpr -> pexpr
| PappN of opN & seq pexpr
| Pif    : stype -> pexpr -> pexpr -> pexpr -> pexpr.

Notation pexprs := (seq pexpr).

Section ALL2.
   Variable T:Type.
   Variable eqb: T -> T -> bool.
   Variable Heq : forall (x y:T), reflect (x = y) (eqb x y).

   Lemma reflect_all2 l1 l2 : reflect (l1 = l2) (all2 eqb l1 l2).
   Proof.
     elim: l1 l2 => [|e1 l1 Hrec1] [|e2 l2] /=;try by constructor.
     apply (@equivP (eqb e1 e2 /\ all2 eqb l1 l2));first by apply andP.
     split=> [ [] /Heq -> /Hrec1 ->|[] ??] //.
     split. by apply /Heq. by apply /Hrec1.
   Defined.
End ALL2.

Section ALLT.
  Context (A: Type) (P: A → Type).
  Fixpoint allT (m: seq A) : Type :=
    if m is a :: m' then P a * allT m' else unit.
End ALLT.

Lemma allT_refl A (P: A → A → Prop) m :
  allT (λ a, P a a) m → List.Forall2 P m m.
Proof. by elim: m => // a m ih [h] /ih{ih}ih; constructor. Qed.

Section PEXPR_RECT.

  Context
    (P: pexpr → Type)
    (Hconst: ∀ z, P (Pconst z))
    (Hbool: ∀ b, P (Pbool b))
    (Harr_init: ∀ n, P (Parr_init n))
    (Hvar: ∀ x, P (Pvar x))
    (Hglobal: ∀ g, P (Pglobal g))
    (Hget: ∀ sz x e, P e → P (Pget sz x e))
    (Hload: ∀ sz x e, P e → P (Pload sz x e))
    (Happ1: ∀ op e, P e → P (Papp1 op e))
    (Happ2: ∀ op e1 e2, P e1 → P e2 → P (Papp2 op e1 e2))
    (HappN: ∀ op es, allT P es → P (PappN op es))
    (Hif: ∀ t e e1 e2, P e → P e1 → P e2 → P (Pif t e e1 e2))
  .

  Definition pexpr_rect_rec (f: ∀ e, P e) : ∀ es, allT P es :=
    fix loop es :=
      if es is e :: es
      then (f e, loop es)
      else tt.

  Fixpoint pexpr_rect (e: pexpr) : P e :=
    match e with
    | Pconst z => Hconst z
    | Pbool b => Hbool b
    | Parr_init n => Harr_init n
    | Pvar x => Hvar x
    | Pglobal g => Hglobal g
    | Pget sz x e => Hget sz x (pexpr_rect e)
    | Pload sz x e => Hload sz x (pexpr_rect e)
    | Papp1 op e => Happ1 op (pexpr_rect e)
    | Papp2 op e1 e2 => Happ2 op (pexpr_rect e1) (pexpr_rect e2)
    | PappN op es => HappN op (pexpr_rect_rec pexpr_rect es)
    | Pif t e e1 e2 => Hif t (pexpr_rect e) (pexpr_rect e1) (pexpr_rect e2)
    end.

End PEXPR_RECT.

Arguments pexpr_rect: clear implicits.

Definition var_i_beq x1 x2 :=
  match x1, x2 with
  | VarI x1 i1, VarI x2 i2 => (x1 == x2) && (i1 == i2)
  end.

Lemma var_i_eq_axiom : Equality.axiom var_i_beq.
Proof.
  move=> [x xi] [y yi] /=.
  apply (@equivP ((x == y) /\ (xi == yi)));first by apply: andP.
  by split => -[] => [/eqP -> /eqP| -> ] ->.
Qed.

Definition var_i_eqMixin     := Equality.Mixin var_i_eq_axiom.
Canonical  var_i_eqType      := Eval hnf in EqType var_i var_i_eqMixin.

Module Eq_pexpr.

Fixpoint eqb (e1 e2:pexpr) : bool :=
  match e1, e2 with
  | Pconst n1   , Pconst n2    => n1 == n2
  | Pbool  b1   , Pbool  b2    => b1 == b2
  | Parr_init n1, Parr_init n2 => n1 == n2
  | Pvar   x1   , Pvar   x2    => (x1 == x2)
  | Pglobal g1, Pglobal g2 => g1 == g2
  | Pget sz1 x1 e1, Pget sz2 x2 e2 => (sz1 == sz2) && (x1 == x2) && eqb e1 e2
  | Pload sz1 x1 e1, Pload sz2 x2 e2 => (sz1 == sz2) && (x1 == x2) && eqb e1 e2
  | Papp1 o1 e1 , Papp1  o2 e2 => (o1 == o2) && eqb e1 e2
  | Papp2 o1 e11 e12, Papp2 o2 e21 e22  =>
     (o1 == o2) && eqb e11 e21 && eqb e12 e22
  | PappN o1 es1, PappN o2 es2 =>
    (o1 == o2) && all2 eqb es1 es2
  | Pif t1 b1 e11 e12, Pif t2 b2 e21 e22  =>
     (t1 == t2) && eqb b1 b2 && eqb e11 e21 && eqb e12 e22
  | _, _ => false
  end.

  Lemma eqb_refl e : eqb e e.
  Proof.
    elim/pexpr_rect: e => //= *;
    repeat match goal with
    | H : _ |- _ => rewrite H //=
    | |- context[ (?a == ?a) ] => rewrite eqxx //=
    end.
    apply/all2P; exact: allT_refl.
  Qed.

  Lemma eq_axiom : Equality.axiom eqb.
  Proof.
    elim => [n1|b1| n1 |x1|g1|w1 x1 e1 He1|w1 x1 e1 He1
            |o1 e1 He1|o1 e11 e12 He11 He12 | o1 es1 Hes1 | st1 t1 e11 e12 Ht1 He11 He12]
            [n2|b2| n2 |x2|g2|w2 x2 e2|w2 x2 e2|o2 e2|o2 e21 e22 | o2 es2 |st2 t2 e21 e22] /=;
        try by constructor.
    + apply (@equivP (n1 = n2));first by apply: eqP.
      by split => [->|[]->].
    + apply (@equivP (b1 = b2));first by apply: eqP.
      by split => [->|[]->].
    + apply (@equivP (n1 = n2));first by apply eqP.
      by split => [->|[]->].
    + apply (@equivP (x1 = x2));first by apply: eqP.
      by split => [->|[]->].
    + apply (@equivP (g1 = g2));first by apply: eqP.
      by split => [->|[]->].
    + apply (@equivP (((w1 == w2) && (x1 == x2)) /\ eqb e1 e2));first by apply andP.
      split => [ [] /andP [] /eqP -> /eqP -> /He1 -> | [] -> -> <-] //.
      by rewrite ! eq_refl; split => //; apply/ He1.
    + apply (@equivP (((w1 == w2) && (x1 == x2)) /\ eqb e1 e2)); first by apply andP.
      split => [ [] /andP [] /eqP -> /eqP -> /He1 -> | [] -> -> <-] //.
      by rewrite ! eq_refl; split => //; apply/ He1.
    + apply (@equivP ((o1 == o2) /\ eqb e1 e2));first by apply andP.
      by split=> [ [] /eqP -> /He1 -> | [] -> <- ] //;split => //;apply /He1.
    + apply (@equivP (((o1 == o2) && eqb e11 e21) /\ eqb e12 e22));first by apply andP.
      split=> [ []/andP[]/eqP-> /He11 -> /He12->| [] <- <- <- ] //.
      by rewrite eq_refl /=;split;[apply /He11|apply /He12].
    + apply (@equivP ((o1 == o2) ∧ all2 eqb es1 es2)); first by apply: andP.
      split.
      - case => /eqP <-{o2} h; f_equal.
        elim: es1 es2 Hes1 h; first by case.
        by move => e1 es1 ih [] // e2 es2 [h1] /ih{ih}ih/=/andP[]/(rwP (h1 _)) <- /ih <-.
      move => h.
      have : o1 = o2 ∧ es1 = es2 by refine (let: erefl := h in conj erefl erefl).
      move => {h} [??]; subst es2 o2; split; first exact: eqxx.
      elim: es1 Hes1 => // e es ih [h] /ih{ih}ih /=.
      by case: (h e).
    apply (@equivP (((st1 == st2) && eqb t1 t2 && eqb e11 e21) /\ eqb e12 e22));first by apply andP.
    split => [ [] /andP[]/andP[] /eqP -> /Ht1 -> /He11 -> /He12 ->| [<- <- <- <-]] //.
    by split;[apply /andP;split;[apply /andP;split|]|]; [apply /eqP | apply /Ht1 | apply /He11 | apply /He12].
  Qed.

  Definition pexpr_eqMixin := Equality.Mixin eq_axiom.
  Module Exports.
  Canonical pexpr_eqType  := Eval hnf in EqType pexpr pexpr_eqMixin.
  End Exports.
End Eq_pexpr.
Export Eq_pexpr.Exports.

Section PEXPR_IND.
  Context
    (P: pexpr → Prop)
    (Hconst: ∀ z, P (Pconst z))
    (Hbool: ∀ b, P (Pbool b))
    (Harr_init: ∀ n, P (Parr_init n))
    (Hvar: ∀ x, P (Pvar x))
    (Hglobal: ∀ g, P (Pglobal g))
    (Hget: ∀ sz x e, P e → P (Pget sz x e))
    (Hload: ∀ sz x e, P e → P (Pload sz x e))
    (Happ1: ∀ op e, P e → P (Papp1 op e))
    (Happ2: ∀ op e1, P e1 → ∀ e2, P e2 → P (Papp2 op e1 e2))
    (HappN: ∀ op es, (∀ e, e \in es → P e) → P (PappN op es))
    (Hif: ∀ t e, P e → ∀ e1, P e1 → ∀ e2, P e2 → P (Pif t e e1 e2))
  .

  Definition pexpr_ind_rec (f: ∀ e, P e) : ∀ es : pexprs, ∀ e, e \in es → P e.
  refine
    (fix loop es :=
       if es is e :: es'
       then λ (e: pexpr), _
       else λ e (k: e \in [::]), False_ind _ (Bool.diff_false_true k)
    ).
  rewrite in_cons; case/orP.
  + move => /eqP -> ; exact: f.
  apply: loop.
  Defined.

  Fixpoint pexpr_ind (e: pexpr) : P e :=
    match e with
    | Pconst z => Hconst z
    | Pbool b => Hbool b
    | Parr_init n => Harr_init n
    | Pvar x => Hvar x
    | Pglobal g => Hglobal g
    | Pget sz x e => Hget sz x (pexpr_ind e)
    | Pload sz x e => Hload sz x (pexpr_ind e)
    | Papp1 op e => Happ1 op (pexpr_ind e)
    | Papp2 op e1 e2 => Happ2 op (pexpr_ind e1) (pexpr_ind e2)
    | PappN op es => HappN op (@pexpr_ind_rec pexpr_ind es)
    | Pif t e e1 e2 => Hif t (pexpr_ind e) (pexpr_ind e1) (pexpr_ind e2)
    end.

End PEXPR_IND.

(* Mutual induction scheme for pexpr and pexprs *)
Section PEXPRS_IND.
  Context
    (P: pexpr → Prop)
    (Q: pexprs → Prop)
  .

  Record pexpr_ind_hypotheses : Prop := {
    pexprs_nil: Q [::];
    pexprs_cons: ∀ pe, P pe → ∀ pes, Q pes → Q (pe :: pes);
    pexprs_const: ∀ z, P (Pconst z);
    pexprs_bool: ∀ b, P (Pbool b);
    pexprs_arr_init: ∀ n, P (Parr_init n);
    pexprs_var: ∀ x, P (Pvar x);
    pexprs_global: ∀ g, P (Pglobal g);
    pexprs_get: ∀ sz x e, P e → P (Pget sz x e);
    pexprs_load: ∀ sz x e, P e → P (Pload sz x e);
    pexprs_app1: ∀ op e, P e → P (Papp1 op e);
    pexprs_app2: ∀ op e1, P e1 → ∀ e2, P e2 → P (Papp2 op e1 e2);
    pexprs_appN: ∀ op es, Q es → P (PappN op es);
    pexprs_if: ∀ t e, P e → ∀ e1, P e1 → ∀ e2, P e2 → P (Pif t e e1 e2);
  }.

  Context (h: pexpr_ind_hypotheses).

  Definition pexprs_ind pexpr_mut_ind : ∀ pes, Q pes :=
    fix pexprs_ind pes :=
      if pes is pe :: pes'
      then pexprs_cons h (pexpr_mut_ind pe) (pexprs_ind pes')
      else pexprs_nil h.

  Fixpoint pexpr_mut_ind pe : P pe :=
    match pe with
    | Pconst z => pexprs_const h z
    | Pbool b => pexprs_bool h b
    | Parr_init n => pexprs_arr_init h n
    | Pvar x => pexprs_var h x
    | Pglobal g => pexprs_global h g
    | Pget sz x e => pexprs_get h sz x (pexpr_mut_ind e)
    | Pload sz x e => pexprs_load h sz x (pexpr_mut_ind e)
    | Papp1 op e => pexprs_app1 h op (pexpr_mut_ind e)
    | Papp2 op e1 e2 => pexprs_app2 h op (pexpr_mut_ind e1) (pexpr_mut_ind e2)
    | PappN op es => pexprs_appN h op (pexprs_ind pexpr_mut_ind es)
    | Pif t e e1 e2 => pexprs_if h t (pexpr_mut_ind e) (pexpr_mut_ind e1) (pexpr_mut_ind e2)
    end.

  Definition pexprs_ind_pair :=
    conj pexpr_mut_ind (pexprs_ind pexpr_mut_ind).

End PEXPRS_IND.

(* ** Left values
 * -------------------------------------------------------------------- *)

Variant lval : Type :=
| Lnone `(var_info) `(stype)
| Lvar `(var_i)
| Lmem `(wsize) `(var_i) `(pexpr)
| Laset `(wsize) `(var_i) `(pexpr).

Coercion Lvar : var_i >-> lval.

Notation lvals := (seq lval).

Definition lval_beq (x1:lval) (x2:lval) :=
  match x1, x2 with
  | Lnone i1 t1, Lnone i2 t2 => (i1 == i2) && (t1 == t2)
  | Lvar  x1   , Lvar  x2    => x1 == x2
  | Lmem w1 x1 e1, Lmem w2 x2 e2 => (w1 == w2) && (x1 == x2) && (e1 == e2)
  | Laset w1 x1 e1, Laset w2 x2 e2 => (w1 == w2) && (x1 == x2) && (e1 == e2)
  | _          , _           => false
  end.

Lemma lval_eq_axiom : Equality.axiom lval_beq.
Proof.
  case=> [i1 t1|x1|w1 x1 e1|w1 x1 e1] [i2 t2|x2|w2 x2 e2|w2 x2 e2] /=;try by constructor.
  + apply (@equivP ((i1 == i2) /\ t1 == t2));first by apply andP.
    by split=> [ [] /eqP -> /eqP -> | [] -> <- ] //.
  + apply (@equivP (x1 = x2));first by apply: eqP.
    by split => [->|[]->].
  + apply (@equivP (((w1 == w2) && (x1 == x2)) /\ e1 == e2));first by apply andP.
    split => [ [] /andP [] /eqP -> /eqP -> /eqP -> // | [] -> -> <- ].
    by rewrite !eq_refl.
  apply (@equivP (((w1 == w2) && (x1 == x2)) /\ e1 == e2));first by apply andP.
  split => [ [] /andP [] /eqP -> /eqP -> /eqP -> // | [] -> -> <- ].
  by rewrite !eq_refl.
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
  | AT_none       (* assignment introduced by the develloper that can be removed *)
  | AT_keep       (* assignment that should be keep *)
  | AT_rename     (* equality constraint introduced by inline *)
  | AT_inline.    (* assignment to be removed later : introduce by unrolling or inlining *)

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

Inductive instr_r :=
| Cassgn : lval -> assgn_tag -> stype -> pexpr -> instr_r
| Copn   : lvals -> assgn_tag -> sopn -> pexprs -> instr_r

| Cif    : pexpr -> seq instr -> seq instr  -> instr_r
| Cfor   : var_i -> range -> seq instr -> instr_r
| Cwhile : align -> seq instr -> pexpr -> seq instr -> instr_r
| Ccall  : inline_info -> lvals -> funname -> pexprs -> instr_r

with instr := MkI : instr_info -> instr_r ->  instr.

Notation cmd := (seq instr).

Record fundef := MkFun {
  f_iinfo  : instr_info;
  f_tyin  : seq stype;
  f_params : seq var_i;
  f_body   : cmd;
  f_tyout : seq stype;
  f_res    : seq var_i;
}.

Definition function_signature : Type :=
  (seq stype * seq stype).

Definition signature_of_fundef (fd: fundef) : function_signature :=
  (f_tyin fd, f_tyout fd).

Definition fun_decl := (funname * fundef)%type.
Notation fun_decls  := (seq fun_decl).

Record prog := {
  p_globs : glob_decls;
  p_funcs : fun_decls;
}.

Definition instr_d (i:instr) :=
  match i with
  | MkI i _ => i
  end.

Fixpoint instr_r_beq i1 i2 :=
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
    move=> [ii1 ir1] [ii2 ir2].
    apply (@equivP (ii1 == ii2 /\ instr_r_beq ir1 ir2));first by apply andP.
    by split=> [[] /eqP -> /Heq -> |[]/eqP ?/Heq ]//; split.
  Defined.
End EQI.

Lemma instr_r_eq_axiom : Equality.axiom instr_r_beq.
Proof.
  rewrite /Equality.axiom.
  fix Hrec 1;case =>
    [x1 t1 ty1 e1|x1 t1 o1 e1|e1 c11 c12|x1 [[dir1 lo1] hi1] c1|a1 c1 e1 c1'|ii1 x1 f1 arg1]
    [x2 t2 ty2 e2|x2 t2 o2 e2|e2 c21 c22|x2 [[dir2 lo2] hi2] c2|a2 c2 e2 c2'|ii2 x2 f2 arg2] /=;
  try by constructor.
  + apply (@equivP ((t1 == t2) && (ty1 == ty2) && (x1 == x2) && (e1 == e2)));first by apply idP.
    split=> [/andP [] /andP [] /andP [] /eqP -> /eqP-> /eqP-> /eqP-> | [] <- <- <- <- ] //.
    by rewrite !eq_refl.
  + apply (@equivP ((x1 == x2) && (t1 == t2)&& (o1 == o2) && (e1 == e2)));first by apply idP.
    split=> [/andP [] /andP [] /andP [] /eqP-> /eqP-> /eqP-> /eqP-> | [] <- <- <- <-] //.
    by rewrite !eq_refl.
  + apply (@equivP ((e1 == e2) && (all2 instr_beq c11 c21) && (all2 instr_beq c12 c22)));
      first by apply idP.
    have H := reflect_all2 (instr_eq_axiom_ Hrec).
    split=> [/andP[]/andP[]| []] /eqP -> /H -> /H -> //.
  + apply (@equivP  ((x1 == x2) && (dir1 == dir2) && (lo1 == lo2) && (hi1 == hi2) &&
      all2 instr_beq c1 c2)); first by apply idP.
    have H := reflect_all2 (instr_eq_axiom_ Hrec).
    split=> [/andP[]/andP[]/andP[]/andP[]| []] /eqP->/eqP->/eqP->/eqP->/H-> //.
  + apply (@equivP  ((a1 == a2) && all2 instr_beq c1 c2 && (e1 == e2) && all2 instr_beq c1' c2')); first by apply idP.
    have H := reflect_all2 (instr_eq_axiom_ Hrec).
    split=> [/andP[]/andP[]/andP[]/eqP->/H->/eqP->/H-> | []/eqP->/H->/eqP->/H->] //.
  apply (@equivP ((ii1 == ii2) && (x1 == x2) && (f1 == f2) && (arg1 == arg2)));first by apply idP.
  by split=> [/andP[]/andP[]/andP[]| []]/eqP->/eqP->/eqP->/eqP->.
Qed.

Definition instr_r_eqMixin     := Equality.Mixin instr_r_eq_axiom.
Canonical  instr_r_eqType      := Eval hnf in EqType instr_r instr_r_eqMixin.

Lemma instr_eq_axiom : Equality.axiom instr_beq.
Proof.
  apply: instr_eq_axiom_ instr_r_eq_axiom .
Qed.

Definition instr_eqMixin     := Equality.Mixin instr_eq_axiom.
Canonical  instr_eqType      := Eval hnf in EqType instr instr_eqMixin.

Definition fundef_beq fd1 fd2 :=
  match fd1, fd2 with
  | MkFun ii1 tin1 x1 c1 tout1 r1, MkFun ii2 tin2 x2 c2 tout2 r2 =>
    (ii1 == ii2) && (tin1 == tin2) && (x1 == x2) && (c1 == c2) && (tout1 == tout2) && (r1 == r2)
  end.

Lemma fundef_eq_axiom : Equality.axiom fundef_beq.
Proof.
  move=> [i1 tin1 p1 c1 tout1 r1] [i2 tin2 p2 c2 tout2 r2] /=.
  apply (@equivP ((i1 == i2) && (tin1 == tin2) && (p1 == p2) &&
           (c1 == c2) && (tout1 == tout2) &&(r1 == r2)));first by apply idP.
  by split=> [/andP[]/andP[]/andP[]/andP[]/andP[] | []] /eqP->/eqP->/eqP->/eqP->/eqP->/eqP->.
Qed.

Definition fundef_eqMixin     := Equality.Mixin fundef_eq_axiom.
Canonical  fundef_eqType      := Eval hnf in EqType fundef fundef_eqMixin.

Definition prog_beq p1 p2 := (p_globs p1 == p_globs p2) && (p_funcs p1 == p_funcs p2).

Lemma prog_eq_axiom : Equality.axiom prog_beq.
Proof.
  move=> [gd1 fs1] [gd2 fs2] /=.
  apply (@equivP ((gd1 == gd2) && (fs1 == fs2)));first by apply idP.
  by split => [/andP [] | []] /eqP -> /eqP ->.
Qed.

Definition prog_eqMixin     := Equality.Mixin prog_eq_axiom.
Canonical  prog_eqType      := Eval hnf in EqType prog prog_eqMixin.

Definition map_prog (F: fundef -> fundef) (p:prog) :=
  {| p_globs := p_globs p;
     p_funcs := map (fun f => (f.1, F f.2)) (p_funcs p) |}.

Lemma map_prog_globs F p : p_globs (map_prog F p) = p_globs p.
Proof. done. Qed.

Lemma get_map_prog F p fn :
  get_fundef (p_funcs (map_prog F p)) fn = ssrfun.omap F (get_fundef (p_funcs p) fn).
Proof. exact: assoc_map. Qed.

Lemma get_fundef_cons {T} (fnd: funname * T) p fn:
  get_fundef (fnd :: p) fn = if fn == fnd.1 then Some fnd.2 else get_fundef p fn.
Proof. by case: fnd. Qed.

Lemma get_fundef_in {T} p f (fd: T) : get_fundef p f = Some fd -> f \in [seq x.1 | x <- p].
Proof. by rewrite/get_fundef; apply: assoc_mem_dom'. Qed.

Lemma get_fundef_in' {T} p fn (fd: T):
  get_fundef p fn = Some fd -> List.In (fn, fd) p.
Proof. exact: assoc_mem'. Qed.

Definition all_prog {aT bT cT} (s1: seq (funname * aT)) (s2: seq (funname * bT)) (ll: seq cT) f :=
  (size s1 == size s2) && all2 (fun fs a => let '(fd1, fd2) := fs in (fd1.1 == fd2.1) && f a fd1.2 fd2.2) (zip s1 s2) ll.

Lemma all_progP {aT bT cT} (s1: seq (funname * aT)) (s2: seq (funname * bT)) (l: seq cT) f:
  all_prog s1 s2 l f ->
  forall fn fd, get_fundef s1 fn = Some fd ->
  exists fd' l', get_fundef s2 fn = Some fd' /\ f l' fd fd'.
Proof.
elim: s1 s2 l=> // [[fn fd] p IH] [|[fn' fd'] p'] // [|lh la] //.
+ by rewrite /all_prog /= andbF.
+ move=> /andP [/= Hs /andP [/andP [/eqP Hfn Hfd] Hall]].
  move=> fn0 fd0.
  case: ifP=> /eqP Hfn0.
  + move=> [] <-.
    exists fd', lh.
    rewrite -Hfn Hfn0 /= eq_refl; split=> //.
  + move=> H.
    have [|fd'' [l' [IH1 IH2]]] := (IH p' la _ _ _ H).
    apply/andP; split.
    by rewrite -eqSS.
    exact: Hall.
    exists fd'', l'; split=> //.
    rewrite /= -Hfn.
    by case: ifP=> // /eqP.
Qed.

Section RECT.
  Variables (Pr:instr_r -> Type) (Pi:instr -> Type) (Pc : cmd -> Type).
  Hypothesis Hmk  : forall i ii, Pr i -> Pi (MkI ii i).
  Hypothesis Hnil : Pc [::].
  Hypothesis Hcons: forall i c, Pi i -> Pc c -> Pc (i::c).
  Hypothesis Hasgn: forall x tg ty e, Pr (Cassgn x tg ty e).
  Hypothesis Hopn : forall xs t o es, Pr (Copn xs t o es).
  Hypothesis Hif  : forall e c1 c2, Pc c1 -> Pc c2 -> Pr (Cif e c1 c2).
  Hypothesis Hfor : forall v dir lo hi c, Pc c -> Pr (Cfor v (dir,lo,hi) c).
  Hypothesis Hwhile : forall a c e c', Pc c -> Pc c' -> Pr (Cwhile a c e c').
  Hypothesis Hcall: forall i xs f es, Pr (Ccall i xs f es).

  Section C.
  Variable instr_rect : forall i, Pi i.

  Fixpoint cmd_rect_aux (c:cmd) : Pc c :=
    match c return Pc c with
    | [::] => Hnil
    | i::c => @Hcons i c (instr_rect i) (cmd_rect_aux c)
    end.
  End C.

  Fixpoint instr_Rect (i:instr) : Pi i :=
    match i return Pi i with
    | MkI ii i => @Hmk i ii (instr_r_Rect i)
    end
  with instr_r_Rect (i:instr_r) : Pr i :=
    match i return Pr i with
    | Cassgn x tg ty e => Hasgn x tg ty e
    | Copn xs t o es => Hopn xs t o es
    | Cif e c1 c2  => @Hif e c1 c2 (cmd_rect_aux instr_Rect c1) (cmd_rect_aux instr_Rect c2)
    | Cfor i (dir,lo,hi) c => @Hfor i dir lo hi c (cmd_rect_aux instr_Rect c)
    | Cwhile a c e c'   => @Hwhile a c e c' (cmd_rect_aux instr_Rect c) (cmd_rect_aux instr_Rect c')
    | Ccall ii xs f es => @Hcall ii xs f es
    end.

  Definition cmd_rect := cmd_rect_aux instr_Rect.

End RECT.

(* ** Compute written variables
 * -------------------------------------------------------------------- *)

Definition vrv_rec (s:Sv.t) (rv:lval) :=
  match rv with
  | Lnone _ _  => s
  | Lvar  x    => Sv.add x s
  | Lmem _ _ _  => s
  | Laset _ x _  => Sv.add x s
  end.

Definition vrvs_rec s (rv:lvals) := foldl vrv_rec s rv.

Definition vrv := (vrv_rec Sv.empty).
Definition vrvs := (vrvs_rec Sv.empty).

Fixpoint write_i_rec s i :=
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

Instance vrv_rec_m : Proper (Sv.Equal ==> eq ==> Sv.Equal) vrv_rec.
Proof.
  move=> s1 s2 Hs x r ->;case:r => //= [v | _ v _];SvD.fsetdec.
Qed.

Lemma vrv_none i t: vrv (Lnone i t) = Sv.empty.
Proof. by []. Qed.

Lemma vrv_var x: Sv.Equal (vrv (Lvar x)) (Sv.singleton x).
Proof. rewrite /vrv /=;SvD.fsetdec. Qed.

Lemma vrv_mem w x e : vrv (Lmem w x e) = Sv.empty.
Proof. by []. Qed.

Lemma vrv_aset w x e : Sv.Equal (vrv (Laset w x e)) (Sv.singleton x).
Proof. rewrite /vrv /=;SvD.fsetdec. Qed.

Lemma vrv_recE s (r:lval) : Sv.Equal (vrv_rec s r) (Sv.union s (vrv r)).
Proof.
  case: r => [i| x| x e| x e];
    rewrite ?vrv_none ?vrv_var ?vrv_mem ?vrv_aset /=;
    SvD.fsetdec.
Qed.

Lemma vrvs_recE s rs : Sv.Equal (vrvs_rec s rs) (Sv.union s (vrvs rs)).
Proof.
  rewrite /vrvs;elim: rs s => [|r rs Hrec] s /=;first by SvD.fsetdec.
  rewrite Hrec (Hrec (vrv_rec _ _)) (vrv_recE s);SvD.fsetdec.
Qed.

Lemma vrvs_cons r rs : Sv.Equal (vrvs (r::rs)) (Sv.union (vrv r) (vrvs rs)).
Proof. by rewrite /vrvs /= vrvs_recE. Qed.

Lemma write_c_recE s c : Sv.Equal (write_c_rec s c) (Sv.union s (write_c c)).
Proof.
  apply (@cmd_rect
           (fun i => forall s, Sv.Equal (write_i_rec s i) (Sv.union s (write_i i)))
           (fun i => forall s, Sv.Equal (write_I_rec s i) (Sv.union s (write_I i)))
           (fun c => forall s, Sv.Equal (foldl write_I_rec s c) (Sv.union s (write_c c)))) =>
     /= {c s}
    [ i ii Hi | | i c Hi Hc | x tg ty e | xs t o es | e c1 c2 Hc1 Hc2
    | v dir lo hi c Hc | a c e c' Hc Hc' | ii xs f es] s;
    rewrite /write_I /write_i /write_c /=
    ?Hc1 ?Hc2 /write_c_rec ?Hc ?Hc' ?Hi -?vrv_recE -?vrvs_recE //;
    by SvD.fsetdec.
Qed.

Lemma write_I_recE s i : Sv.Equal (write_I_rec s i) (Sv.union s (write_I i)).
Proof. by apply (write_c_recE s [:: i]). Qed.

Lemma write_i_recE s i : Sv.Equal (write_i_rec s i) (Sv.union s (write_i i)).
Proof. by apply (write_I_recE s (MkI 1%positive i)). Qed.

Lemma write_c_nil : write_c [::] = Sv.empty.
Proof. done. Qed.

Lemma write_c_cons i c: Sv.Equal (write_c (i::c)) (Sv.union (write_I i) (write_c c)).
Proof. rewrite {1}/write_c /= write_c_recE write_I_recE;SvD.fsetdec. Qed.

Lemma write_c_app c1 c2 :
  Sv.Equal (write_c (c1 ++ c2)) (Sv.union (write_c c1) (write_c c2)).
Proof. by elim: c1 => //= i c1 Hrec;rewrite !write_c_cons;SvD.fsetdec. Qed.

Lemma write_i_assgn x tag ty e : write_i (Cassgn x tag ty e) = vrv x.
Proof. done. Qed.

Lemma write_i_opn xs t o es : write_i (Copn xs t o es) = vrvs xs.
Proof. done. Qed.

Lemma write_i_if e c1 c2 :
   Sv.Equal (write_i (Cif e c1 c2)) (Sv.union (write_c c1) (write_c c2)).
Proof.
  rewrite /write_i /= -/(write_c_rec _ c1) -/(write_c_rec _ c2) !write_c_recE;SvD.fsetdec.
Qed.

Lemma write_i_for x rn c :
   Sv.Equal (write_i (Cfor x rn c)) (Sv.union (Sv.singleton x) (write_c c)).
Proof.
  rewrite /write_i /= -/(write_c_rec _ c) write_c_recE ;SvD.fsetdec.
Qed.

Lemma write_i_while a c e c' :
   Sv.Equal (write_i (Cwhile a c e c')) (Sv.union (write_c c) (write_c c')).
Proof.
  rewrite /write_i /= -/(write_c_rec _ c) write_c_recE;SvD.fsetdec.
Qed.

Lemma write_i_call ii xs f es :
  write_i (Ccall ii xs f es) = vrvs xs.
Proof. done. Qed.

(* -------------------------------------------------------------------- *)
Hint Rewrite write_c_nil write_c_cons : write_c.
Hint Rewrite write_i_assgn write_i_opn write_i_if : write_i.
Hint Rewrite write_i_while write_i_for write_i_call : write_i.
Hint Rewrite vrv_none vrv_var : vrv.

Ltac writeN := autorewrite with write_c write_i vrv.

(* ** Compute read variables
 * -------------------------------------------------------------------- *)

Fixpoint read_e_rec (s:Sv.t) (e:pexpr) : Sv.t :=
  match e with
  | Pconst _
  | Pbool  _
  | Parr_init _    => s
  | Pvar   x       => Sv.add x s
  | Pglobal _      => s
  | Pget _ x e     => read_e_rec (Sv.add x s) e
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
  | Lnone _ _   => s
  | Lvar  _     => s
  | Lmem _ x e  => read_e_rec (Sv.add x s) e
  | Laset _ x e => read_e_rec (Sv.add x s) e
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

Lemma read_eE e s : Sv.Equal (read_e_rec s e) (Sv.union (read_e e) s).
Proof.
  elim: e s => //= [v | w v e He | w v e He | o e1 He1 e2 He2 | o es Hes | t e He e1 He1 e2 He2] s;
   rewrite /read_e /= ?He ?He1 ?He2; try SvD.fsetdec.
  rewrite -/read_es_rec -/read_es.
  elim: es Hes s.
  + by move => _ /= s; SvD.fsetdec.
  move => e es ih Hes s /=.
  rewrite /read_es /= -/read_e ih.
  + rewrite Hes.
    + rewrite ih.
      + by SvD.fsetdec.
      move => e' he' s'; apply: Hes.
      by rewrite in_cons he' orbT.
    by rewrite in_cons eqxx.
  move => e' he' s'; apply: Hes.
  by rewrite in_cons he' orbT.
Qed.

Lemma read_e_var (x:var_i) : Sv.Equal (read_e (Pvar x)) (Sv.singleton x).
Proof. rewrite /read_e /=;SvD.fsetdec. Qed.

Lemma read_esE es s : Sv.Equal (read_es_rec s es) (Sv.union (read_es es) s).
Proof.
  elim: es s => [ | e es Hes] s;rewrite /read_es /= ?Hes ?read_eE;SvD.fsetdec.
Qed.

Lemma read_es_cons e es :
  Sv.Equal (read_es (e :: es)) (Sv.union (read_e e) (read_es es)).
Proof. by rewrite /read_es /= !read_esE read_eE;SvD.fsetdec. Qed.

Lemma read_rvE s x: Sv.Equal (read_rv_rec s x) (Sv.union s (read_rv x)).
Proof.
  case: x => //= [_|_|w x e|w x e]; rewrite /read_rv /= ?read_eE; SvD.fsetdec.
Qed.

Lemma read_rvsE s xs:  Sv.Equal (read_rvs_rec s xs) (Sv.union s (read_rvs xs)).
Proof.
  elim: xs s => [ |x xs Hxs] s;rewrite /read_rvs /= ?Hxs ?read_rvE;SvD.fsetdec.
Qed.

Lemma read_rvs_nil : read_rvs [::] = Sv.empty.
Proof. done. Qed.

Lemma read_rvs_cons x xs : Sv.Equal (read_rvs (x::xs)) (Sv.union (read_rv x) (read_rvs xs)).
Proof.
  rewrite {1}/read_rvs /= read_rvsE read_rvE;SvD.fsetdec.
Qed.

Lemma read_cE s c : Sv.Equal (read_c_rec s c) (Sv.union s (read_c c)).
Proof.
  apply (@cmd_rect
           (fun i => forall s, Sv.Equal (read_i_rec s i) (Sv.union s (read_i i)))
           (fun i => forall s, Sv.Equal (read_I_rec s i) (Sv.union s (read_I i)))
           (fun c => forall s, Sv.Equal (foldl read_I_rec s c) (Sv.union s (read_c c))))
           => /= {c s}
   [ i ii Hi | | i c Hi Hc | x tg ty e | xs t o es | e c1 c2 Hc1 Hc2
    | v dir lo hi c Hc | a c e c' Hc Hc' | ii xs f es] s;
    rewrite /read_I /read_i /read_c /=
     ?read_rvE ?read_eE ?read_esE ?read_rvsE ?Hc2 ?Hc1 /read_c_rec ?Hc' ?Hc ?Hi //;
    by SvD.fsetdec.
Qed.

Lemma read_IE s i : Sv.Equal (read_I_rec s i) (Sv.union s (read_I i)).
Proof. by apply (read_cE s [:: i]). Qed.

Lemma read_iE s i : Sv.Equal (read_i_rec s i) (Sv.union s (read_i i)).
Proof. by apply (read_IE s (MkI 1%positive i)). Qed.

Lemma read_c_nil : read_c [::] = Sv.empty.
Proof. done. Qed.

Lemma read_c_cons i c: Sv.Equal (read_c (i::c)) (Sv.union (read_I i) (read_c c)).
Proof. by rewrite {1}/read_c /= read_cE //. Qed.

Lemma read_i_assgn x tag ty e :
  Sv.Equal (read_i (Cassgn x tag ty e)) (Sv.union (read_rv x) (read_e e)).
Proof. rewrite /read_i /= read_rvE read_eE;SvD.fsetdec. Qed.

Lemma read_i_opn xs t o es:
  Sv.Equal (read_i (Copn xs t o es)) (Sv.union (read_rvs xs) (read_es es)).
Proof. by rewrite /read_i /= read_esE read_rvsE;SvD.fsetdec. Qed.

Lemma read_i_if e c1 c2 :
   Sv.Equal (read_i (Cif e c1 c2)) (Sv.union (read_e e) (Sv.union (read_c c1) (read_c c2))).
Proof.
  rewrite /read_i /= -/read_c_rec read_eE !read_cE;SvD.fsetdec.
Qed.

Lemma read_i_for x dir lo hi c :
   Sv.Equal (read_i (Cfor x (dir, lo, hi) c))
            (Sv.union (read_e lo) (Sv.union (read_e hi) (read_c c))).
Proof.
  rewrite /read_i /= -/read_c_rec !read_eE read_cE;SvD.fsetdec.
Qed.

Lemma read_i_while a c e c' :
   Sv.Equal (read_i (Cwhile a c e c'))
            (Sv.union (read_c c) (Sv.union (read_e e) (read_c c'))).
Proof.
  rewrite /read_i /= -/read_c_rec !read_eE read_cE;SvD.fsetdec.
Qed.

Lemma read_i_call ii xs f es :
  Sv.Equal (read_i (Ccall ii xs f es)) (Sv.union (read_rvs xs) (read_es es)).
Proof. rewrite /read_i /= read_esE read_rvsE;SvD.fsetdec. Qed.

Lemma read_Ii ii i: read_I (MkI ii i) = read_i i.
Proof. by done. Qed.

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

Variant is_reflect (A:Type) (P:A -> pexpr) : pexpr -> option A -> Prop :=
 | Is_reflect_some : forall a, is_reflect P (P a) (Some a)
 | Is_reflect_none : forall e, is_reflect P e None.

Lemma is_boolP e : is_reflect Pbool e (is_bool e).
Proof. by case e=> *;constructor. Qed.

Lemma is_constP e : is_reflect Pconst e (is_const e).
Proof. by case: e=>*;constructor. Qed.

Lemma is_reflect_some_inv {A P e a} (H: @is_reflect A P e (Some a)) : e = P a.
Proof.
  set (d e m := match m with None => True | Some a => e = P a end).
  change (d e (Some a)).
  case H; simpl; auto.
Qed.

Lemma is_wconst_of_sizeP sz e :
  is_reflect (fun z => Papp1 (Oword_of_int sz) (Pconst z)) e (is_wconst_of_size sz e).
Proof.
case: e; try constructor.
case; try constructor.
move => sz' []; try constructor.
move => z /=; case: eqP; try constructor.
move => ->; exact: Is_reflect_some.
Qed.

(* --------------------------------------------------------------------- *)
(* Test the equality of two expressions modulo variable info              *)
Fixpoint eq_expr e e' :=
  match e, e' with
  | Pconst z      , Pconst z'         => z == z'
  | Pbool  b      , Pbool  b'         => b == b'
  | Parr_init n   , Parr_init n'      => n == n'
  | Pvar   x      , Pvar   x'         => v_var x == v_var x'
  | Pglobal g, Pglobal g' => g == g'
  | Pget w x e    , Pget w' x' e'      => (w == w') && (v_var x == v_var x') && eq_expr e e'
  | Pload w x e, Pload w' x' e' => (w == w') && (v_var x == v_var x') && eq_expr e e'
  | Papp1  o e    , Papp1  o' e'      => (o == o') && eq_expr e e'
  | Papp2  o e1 e2, Papp2  o' e1' e2' => (o == o') && eq_expr e1 e1' && eq_expr e2 e2'
  | PappN o es, PappN o' es' => (o == o') && (all2 eq_expr es es')
  | Pif t e e1 e2, Pif t' e' e1' e2' =>
    (t == t') && eq_expr e e' && eq_expr e1 e1' && eq_expr e2 e2'
  | _             , _                 => false
  end.

Lemma eq_expr_refl e : eq_expr e e.
Proof.
elim: e => //= [ ??? -> | ??? -> | ?? -> | ?? -> ? -> | ? es ih | ??-> ? -> ? -> ] //=;
  rewrite ?eqxx //=.
elim: es ih => // e es ih h /=; rewrite h.
+ by apply: ih => e' he'; apply: h; rewrite in_cons he' orbT.
by rewrite in_cons eqxx.
Qed.

Definition eq_lval (x x': lval) : bool :=
  match x, x' with
  | Lnone _ ty,  Lnone _ ty' => ty == ty'
  | Lvar v, Lvar v' => v_var v == v_var v'
  | Lmem w v e, Lmem w' v' e' => (w == w') && (v_var v == v_var v') && (eq_expr e e')
  | Laset w v e, Laset w' v' e'
    => (w == w') && (v_var v == v_var v') && (eq_expr e e')
  | _, _ => false
  end.

Lemma eq_lval_refl x : eq_lval x x.
Proof.
  by case: x => // [ i ty | x | w x e | w x e] /=; rewrite !eqxx // eq_expr_refl.
Qed.

Lemma eq_expr_constL z e :
  eq_expr (Pconst z) e -> e = z :> pexpr.
Proof. by case: e => // z' /eqP ->. Qed.

Lemma eq_expr_const z1 z2 :
  eq_expr (Pconst z1) (Pconst z2) -> z1 = z2.
Proof. by move/eqP. Qed.

Lemma eq_expr_var x1 x2 :
  eq_expr (Pvar x1) (Pvar x2) -> x1 = x2 :> var.
Proof. by move/eqP. Qed.

Lemma eq_expr_global g1 g2 :
  eq_expr (Pglobal g1) (Pglobal g2) -> g1 = g2.
Proof. by move/eqP. Qed.

Lemma eq_expr_load w1 w2 v1 v2 e1 e2 :
     eq_expr (Pload w1 v1 e1) (Pload w2 v2 e2)
  -> [/\ w1 = w2, v1 = v2 :> var & eq_expr e1 e2].
Proof. by move=> /= /andP [/andP[]] /eqP-> /eqP-> ->. Qed.

Lemma eq_expr_app1 o1 o2 e1 e2 :
     eq_expr (Papp1 o1 e1) (Papp1 o2 e2)
  -> [/\ o1 = o2 & eq_expr e1 e2].
Proof. by move=> /= /andP[/eqP-> ->]. Qed.
