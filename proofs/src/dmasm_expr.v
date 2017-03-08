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

(* * Syntax and semantics of the dmasm source language *)

(* ** Imports and settings *)
Require Import ZArith Setoid Morphisms.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat ssrint ssralg tuple.
From mathcomp Require Import choice fintype eqtype div seq zmodp.
Require Import strings word dmasm_utils dmasm_type dmasm_var.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* ** Operators
 * -------------------------------------------------------------------- *)
(* *** Summary
   Operators represent several constructs in the Ocaml compiler:
   - const-op: compile-time expressions (constexpr in C++)
   - list-op: argument and result lists
   - arr-op: reading and writing arrays
   - cpu-op: CPU instructions such as addition with carry
*)

Inductive sop2 : Set :=
| Oand  : sop2                      (* const : sbool -> sbool -> sbool *)
| Oor   : sop2                      (* const : sbool -> sbool -> sbool *)

| Oadd  : sop2                      (* const : sint -> sint -> sint *)
| Omul  : sop2                      (* const : sint -> sint -> sint *)
| Osub  : sop2                      (* const : sint -> sint -> sint *)

| Oeq   : sop2                      (* const : sint -> sint -> sbool *)
| Oneq  : sop2                      (* const : sint -> sint -> sbool *)
| Olt   : sop2                      (* const : sint -> sint -> sbool *)
| Ole   : sop2                      (* const : sint -> sint -> sbool *)
| Ogt   : sop2                      (* const : sint -> sint -> sbool *)
| Oge   : sop2.                     (* const : sint -> sint -> sbool *)

Inductive sopn : Set :=
| Olnot : sopn                      (* cpu : sword -> sword *) 

| Oxor  : sopn                      (* cpu   : sword -> sword -> sword *)
| Oland : sopn                      (* cpu   : sword -> sword -> sword *)
| Olor  : sopn                      (* cpu   : sword -> sword -> sword *)
| Olsr  : sopn                      (* cpu   : sword -> sword -> sword *)
| Olsl  : sopn                      (* cpu   : sword -> sword -> sword *)

| Oif   : sopn                      (* cpu  : sbool -> sword -> sword -> sword *)

| Omulu     : sopn                  (* cpu   : [sword; sword]        -> [sword;sword] *)
| Omuli     : sopn                  (* cpu   : [sword; sword]        -> [sword]       *)
| Oaddcarry : sopn                  (* cpu   : [sword; sword; sbool] -> [sbool;sword] *)
| Osubcarry : sopn.                 (* cpu   : [sword; sword; sbool] -> [sbool;sword] *) 

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

(* ** Expressions
 * -------------------------------------------------------------------- *)
(* Used only by the ocaml compiler *)
Definition var_info := positive.

Record var_i := VarI {
  v_var :> var;
  v_info : var_info 
}.

Inductive pexpr : Type :=
| Pconst :> Z -> pexpr
| Pbool  :> bool -> pexpr
| Pcast  : pexpr -> pexpr              (* int -> word *)
| Pvar   : var_i -> pexpr
| Pget   : var_i -> pexpr -> pexpr 
| Pload  : var_i -> pexpr -> pexpr 
| Pnot   : pexpr -> pexpr 
| Papp2  : sop2 -> pexpr -> pexpr -> pexpr.

Notation pexprs := (seq pexpr).

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
  | Pcast  e1   , Pcast  e2    => eqb e1 e2
  | Pvar   x1   , Pvar   x2    => (x1 == x2)
  | Pget   x1 e1, Pget   x2 e2 => (x1 == x2) && eqb e1 e2
  | Pload  x1 e1, Pload  x2 e2 => (x1 == x2) && eqb e1 e2 
  | Pnot   e1   , Pnot   e2    => eqb e1 e2 
  | Papp2 o1 e11 e12, Papp2 o2 e21 e22  =>  
     (o1 == o2) && eqb e11 e21 && eqb e12 e22
  | _, _ => false
  end.

  Lemma eq_axiom : Equality.axiom eqb. 
  Proof. 
    elim => [n1|b1|e1 He1|x1|x1 e1 He1|x1 e1 He1|e1 He1|o1 e11 He11 e12 He12] 
            [n2|b2|e2|x2|x2 e2|x2 e2|e2|o2 e21 e22] /=;try by constructor.
    + apply (@equivP (n1 = n2));first by apply: eqP.
      by split => [->|[]->].
    + apply (@equivP (b1 = b2));first by apply: eqP.
      by split => [->|[]->].
    + by apply: (equivP (He1 e2)); split => [->|[]->].
    + apply (@equivP (x1 = x2));first by apply: eqP.
      by split => [->|[]->].
    + apply (@equivP ((x1 == x2) /\ eqb e1 e2));first by apply andP.
      by split=> [ [] /eqP -> /He1 -> | [] -> <- ] //;split => //;apply /He1.
    + apply (@equivP ((x1 == x2) /\ eqb e1 e2));first by apply andP.
      by split=> [ [] /eqP -> /He1 -> | [] -> <- ] //;split => //;apply /He1.
    + by apply: (equivP (He1 e2)); split => [->|[]->].
    apply (@equivP (((o1 == o2) && eqb e11 e21) /\ eqb e12 e22));first by apply andP.
    split=> [ []/andP[]/eqP-> /He11 -> /He12->| [] <- <- <- ] //.
    by rewrite eq_refl /=;split;[apply /He11|apply /He12].
  Qed.

  Definition eqMixin := Equality.Mixin eq_axiom.
  Module Exports.
  Canonical eqType  := Eval hnf in EqType pexpr eqMixin.
  End Exports.
End Eq_pexpr.
Export Eq_pexpr.Exports.

(* ** Right values
 * -------------------------------------------------------------------- *)

Inductive rval : Type :=
| Rnone : var_info -> rval
| Rvar  : var_i -> rval
| Rmem  : var_i -> pexpr -> rval
| Raset : var_i -> pexpr -> rval.

Notation rvals := (seq rval).

Definition rval_beq (x1:rval) (x2:rval) :=
  match x1, x2 with
  | Rnone i1   , Rnone i2    => i1 == i2
  | Rvar  x1   , Rvar  x2    => x1 == x2
  | Rmem  x1 e1, Rmem  x2 e2 => (x1 == x2) && (e1 == e2)
  | Raset x1 e1, Raset x2 e2 => (x1 == x2) && (e1 == e2)
  | _          , _           => false   
  end.

Lemma rval_eq_axiom : Equality.axiom rval_beq. 
Proof. 
  case=> [i1|x1|x1 e1|x1 e1] [i2|x2|x2 e2|x2 e2] /=;try by constructor. 
  + apply (@equivP (i1 = i2));first by apply: eqP.
    by split => [->|[]->].
  + apply (@equivP (x1 = x2));first by apply: eqP.
    by split => [->|[]->].
  + apply (@equivP ((x1 == x2) /\ e1 == e2));first by apply andP.
    by split=> [ [] /eqP -> /eqP -> | [] -> <- ] //.
  apply (@equivP ((x1 == x2) /\ e1 == e2));first by apply andP.
  by split=> [ [] /eqP -> /eqP -> | [] -> <- ] //.
Qed.

Definition rval_eqMixin     := Equality.Mixin rval_eq_axiom.
Canonical  rval_eqType      := Eval hnf in EqType rval rval_eqMixin.

(* ** Instructions 
 * -------------------------------------------------------------------- *)

Inductive dir := UpTo | DownTo.

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

Definition instr_info := positive.
Definition dummy_iinfo := xH.

Inductive assgn_tag := 
  | AT_keep    (* normal assignment *)
  | AT_rename  (* equality constraint introduced by inline ... *)
  | AT_inline. (* assignment to be removed later : introduce by unrolling ... *) 

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

Definition funname := positive.

Inductive inline_info := 
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


Inductive instr_r := 
| Cassgn : rval -> assgn_tag -> pexpr -> instr_r
| Copn   : rvals -> sopn -> pexprs -> instr_r 
 
| Cif    : pexpr -> seq instr -> seq instr  -> instr_r
| Cfor   : var_i -> range -> seq instr -> instr_r
| Cwhile : pexpr -> seq instr -> instr_r
| Ccall  : inline_info -> rvals -> funname -> pexprs -> instr_r 

with instr := MkI : instr_info -> instr_r ->  instr.

Notation cmd := (seq instr).

Record fundef := MkFun {
  f_iinfo  : instr_info;
  f_params : seq var_i;
  f_body   : cmd;
  f_res    : seq var_i;
}.

Definition prog := seq (funname * fundef).

Definition dummy_fundef := 
 {|f_iinfo := dummy_iinfo; f_params := [::]; f_body := [::]; f_res := [::] |}. 

Definition instr_d (i:instr) := 
  match i with
  | MkI i _ => i
  end.

Fixpoint instr_r_beq i1 i2 := 
  match i1, i2 with
  | Cassgn x1 tag1 e1, Cassgn x2 tag2 e2 => 
     (tag1 == tag2) && (x1 == x2) && (e1 == e2)
  | Copn x1 o1 e1, Copn x2 o2 e2 =>
     (x1 == x2) && (o1 == o2) && (e1 == e2)
  | Cif e1 c11 c12, Cif e2 c21 c22 =>
    (e1 == e2) && all2 instr_beq c11 c21 && all2 instr_beq c12 c22
  | Cfor i1 (dir1,lo1,hi1) c1, Cfor i2 (dir2,lo2,hi2) c2 =>
    (i1 == i2) && (dir1 == dir2) && (lo1 == lo2) && (hi1 == hi2) && all2 instr_beq c1 c2
  | Cwhile e1 c1 , Cwhile e2 c2 =>
    (e1 == e2) && all2 instr_beq c1 c2
  | Ccall ii1 x1 f1 arg1, Ccall ii2 x2 f2 arg2 => 
    (ii1 == ii2) && (x1==x2) && (f1 == f2) && (arg1 == arg2)
  | _, _ => false 
  end
with instr_beq i1 i2 := 
  match i1, i2 with
  | MkI if1 i1, MkI if2 i2 => (if1 == if2) && (instr_r_beq i1 i2) 
  end.

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
    [x1 t1 e1|x1 o1 e1|e1 c11 c12|x1 [[dir1 lo1] hi1] c1|e1 c1|ii1 x1 f1 arg1]
    [x2 t2 e2|x2 o2 e2|e2 c21 c22|x2 [[dir2 lo2] hi2] c2|e2 c2|ii2 x2 f2 arg2] /=;
  try by constructor.
  + apply (@equivP ((t1 == t2) && (x1 == x2) && (e1 == e2)));first by apply idP.
    split=> [/andP [] /andP [] /eqP-> /eqP-> /eqP-> | [] <- <- <- ] //.
    by rewrite !eq_refl.
  + apply (@equivP ((x1 == x2) && (o1 == o2) && (e1 == e2)));first by apply idP.
    split=> [/andP [] /andP [] /eqP-> /eqP-> /eqP-> | [] <- <- <- ] //.
    by rewrite !eq_refl.
  + apply (@equivP ((e1 == e2) && (all2 instr_beq c11 c21) && (all2 instr_beq c12 c22)));
      first by apply idP. 
    have H := reflect_all2 (instr_eq_axiom_ Hrec).    
    split=> [/andP[]/andP[]| []] /eqP -> /H -> /H -> //.
  + apply (@equivP  ((x1 == x2) && (dir1 == dir2) && (lo1 == lo2) && (hi1 == hi2) &&
      all2 instr_beq c1 c2)); first by apply idP. 
    have H := reflect_all2 (instr_eq_axiom_ Hrec).    
    split=> [/andP[]/andP[]/andP[]/andP[]| []] /eqP->/eqP->/eqP->/eqP->/H-> //.
  + apply (@equivP  ((e1 == e2) && all2 instr_beq c1 c2)); first by apply idP. 
    have H := reflect_all2 (instr_eq_axiom_ Hrec).    
    split=> [/andP[]/eqP->/H-> | []/eqP->/H->] //.
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
  | MkFun ii1 x1 c1 r1, MkFun ii2 x2 c2 r2 =>
    (ii1 == ii2) && (x1 == x2) && (c1 == c2) && (r1 == r2)
  end.

Lemma fundef_eq_axiom : Equality.axiom fundef_beq. 
Proof. 
  move=> [i1 p1 c1 r1] [i2 p2 c2 r2] /=.
  apply (@equivP ((i1 == i2) && (p1 == p2) && (c1 == c2) && (r1 == r2)));first by apply idP.
  by split=> [/andP[]/andP[]/andP[] | []] /eqP->/eqP->/eqP->/eqP->.
Qed.

Definition fundef_eqMixin     := Equality.Mixin fundef_eq_axiom.
Canonical  fundef_eqType      := Eval hnf in EqType fundef fundef_eqMixin.

Definition get_fundef p f := 
  let pos := find (fun ffd => f == fst ffd) p in
  if pos < size p then
    Some (snd (nth (xH,dummy_fundef) p pos))
  else None.

Definition map_prog (F:fundef -> fundef) := map (fun (f:funname * fundef) => (f.1, F f.2)).

Lemma get_map_prog F p fn : 
  get_fundef (map_prog F p) fn = omap F (get_fundef p fn).
Proof.
  rewrite /get_fundef /map_prog size_map find_map. 
  set F1 := (F1 in find F1 _);case: ifPn => // Hlt.
  rewrite (nth_map (1%positive, dummy_fundef)) //.
Qed.

Section RECT.
  Variables (Pr:instr_r -> Type) (Pi:instr -> Type) (Pc : cmd -> Type).
  Hypothesis Hmk  : forall i ii, Pr i -> Pi (MkI ii i).
  Hypothesis Hnil : Pc [::].
  Hypothesis Hcons: forall i c, Pi i -> Pc c -> Pc (i::c).
  Hypothesis Hasgn: forall x t e, Pr (Cassgn x t e).
  Hypothesis Hopn : forall xs o es, Pr (Copn xs o es).
  Hypothesis Hif  : forall e c1 c2, Pc c1 -> Pc c2 -> Pr (Cif e c1 c2).
  Hypothesis Hfor : forall v dir lo hi c, Pc c -> Pr (Cfor v (dir,lo,hi) c).
  Hypothesis Hwhile : forall e c, Pc c -> Pr (Cwhile e c).
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
    | Cassgn x t e => Hasgn x t e
    | Copn xs o es => Hopn xs o es
    | Cif e c1 c2  => @Hif e c1 c2 (cmd_rect_aux instr_Rect c1) (cmd_rect_aux instr_Rect c2)
    | Cfor i (dir,lo,hi) c => @Hfor i dir lo hi c (cmd_rect_aux instr_Rect c)
    | Cwhile e c   => @Hwhile e c (cmd_rect_aux instr_Rect c)
    | Ccall ii xs f es => @Hcall ii xs f es 
    end.

  Definition cmd_rect := cmd_rect_aux instr_Rect.

End RECT.
 
(* ** Compute written variables
 * -------------------------------------------------------------------- *)

Definition vrv_rec (s:Sv.t) (rv:rval) :=
  match rv with
  | Rnone _    => s
  | Rvar  x    => Sv.add x s
  | Rmem  _ _  => s
  | Raset x _  => Sv.add x s
  end.

Definition vrvs_rec s (rv:rvals) := foldl vrv_rec s rv.

Definition vrv := (vrv_rec Sv.empty).
Definition vrvs := (vrvs_rec Sv.empty).

Fixpoint write_i_rec s i := 
  match i with
  | Cassgn x _ _    => vrv_rec s x
  | Copn xs _ _     => vrvs_rec s xs
  | Cif   _ c1 c2   => foldl write_I_rec (foldl write_I_rec s c2) c1
  | Cfor  x _ c     => foldl write_I_rec (Sv.add x s) c
  | Cwhile  _ c     => foldl write_I_rec s c
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
  move=> s1 s2 Hs x r ->;case:r => //= [v | v _];SvD.fsetdec. 
Qed.

Lemma vrv_none i : vrv (Rnone i) = Sv.empty.
Proof. by []. Qed.

Lemma vrv_var x: Sv.Equal (vrv (Rvar x)) (Sv.singleton x). 
Proof. rewrite /vrv /=;SvD.fsetdec. Qed.

Lemma vrv_mem x e : vrv (Rmem x e) = Sv.empty. 
Proof. by []. Qed.

Lemma vrv_aset x e : Sv.Equal (vrv (Raset x e)) (Sv.singleton x). 
Proof. rewrite /vrv /=;SvD.fsetdec. Qed.

Lemma vrv_recE s (r:rval) : Sv.Equal (vrv_rec s r) (Sv.union s (vrv r)).
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
    [ i ii Hi | | i c Hi Hc | x t e | xs o es | e c1 c2 Hc1 Hc2
    | v dir lo hi c Hc | e c Hc | ii xs f es] s;
    rewrite /write_I /write_i /write_c /=
    ?Hc1 ?Hc2 /write_c_rec ?Hc ?Hi -?vrv_recE -?vrvs_recE //;
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

Lemma write_i_assgn x tag e : write_i (Cassgn x tag e) = vrv x. 
Proof. done. Qed.

Lemma write_i_opn xs o es : write_i (Copn xs o es) = vrvs xs. 
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

Lemma write_i_while e c :
   Sv.Equal (write_i (Cwhile e c)) (write_c c).
Proof.
  rewrite /write_i /= -/(write_c_rec _ c) write_c_recE;SvD.fsetdec.
Qed.

Lemma write_i_call ii xs f es :
  write_i (Ccall ii xs f es) = vrvs xs.
Proof. done. Qed.

(* ** Compute read variables
 * -------------------------------------------------------------------- *)

Fixpoint read_e_rec (s:Sv.t) (e:pexpr) : Sv.t := 
  match e with
  | Pconst _        => s
  | Pbool  _        => s
  | Pcast  e        => read_e_rec s e 
  | Pvar   x        => Sv.add x s 
  | Pget   x e      => read_e_rec (Sv.add x s) e
  | Pload  x e      => read_e_rec (Sv.add x s) e
  | Pnot   e        => read_e_rec s e 
  | Papp2  op e1 e2 => read_e_rec (read_e_rec s e2) e1
  end.

Definition read_e := read_e_rec Sv.empty.
Definition read_es_rec := foldl read_e_rec.
Definition read_es := read_es_rec Sv.empty.
         
Definition read_rv_rec  (s:Sv.t) (r:rval) := 
  match r with
  | Rnone _   => s 
  | Rvar  _   => s
  | Rmem  x e => read_e_rec (Sv.add x s) e
  | Raset x e => read_e_rec (Sv.add x s) e 
  end.

Definition read_rv := read_rv_rec Sv.empty.
Definition read_rvs_rec := foldl read_rv_rec.
Definition read_rvs := read_rvs_rec Sv.empty.

Fixpoint read_i_rec (s:Sv.t) (i:instr_r) : Sv.t :=
  match i with
  | Cassgn x _ e => read_rv_rec (read_e_rec s e) x
  | Copn xs _ es => read_es_rec (read_rvs_rec s xs) es
  | Cif b c1 c2 => 
    let s := foldl read_I_rec s c1 in
    let s := foldl read_I_rec s c2 in
    read_e_rec s b 
  | Cfor x (dir, e1, e2) c =>
    let s := foldl read_I_rec s c in
    read_e_rec (read_e_rec s e2) e1
  | Cwhile e c =>
    let s := foldl read_I_rec s c in
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
  elim: e s => //= [v | v e He | v e He | o e1 He1 e2 He2] s;
   rewrite /read_e /= ?He ?He1 ?He2; by SvD.fsetdec.
Qed.

Lemma read_esE es s : Sv.Equal (read_es_rec s es) (Sv.union (read_es es) s).
Proof.
  elim: es s => [ | e es Hes] s;rewrite /read_es /= ?Hes ?read_eE;SvD.fsetdec.
Qed.

Lemma read_es_cons e es : 
  Sv.Equal (read_es (e :: es)) (Sv.union (read_e e) (read_es es)).
Proof. by rewrite /read_es /= !read_esE read_eE;SvD.fsetdec. Qed.

Lemma read_rvE s x: Sv.Equal (read_rv_rec s x) (Sv.union s (read_rv x)).
Proof.
  case: x => //= [_|_|x e|x e]; rewrite /read_rv /= ?read_eE;SvD.fsetdec.
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
   [ i ii Hi | | i c Hi Hc | x t e | xs o es | e c1 c2 Hc1 Hc2
    | v dir lo hi c Hc | e c Hc | ii xs f es] s;
    rewrite /read_I /read_i /read_c /=
     ?read_rvE ?read_eE ?read_esE ?read_rvsE ?Hc2 ?Hc1 /read_c_rec ?Hc ?Hi //;
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

Lemma read_i_assgn x tag e :
  Sv.Equal (read_i (Cassgn x tag e)) (Sv.union (read_rv x) (read_e e)).
Proof. rewrite /read_i /= read_rvE read_eE;SvD.fsetdec. Qed.

Lemma read_i_opn xs o es: 
  Sv.Equal (read_i (Copn xs o es)) (Sv.union (read_rvs xs) (read_es es)).
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

Lemma read_i_while e c :
   Sv.Equal (read_i (Cwhile e c)) 
            (Sv.union (read_e e) (read_c c)).
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

Fixpoint is_const (e:pexpr) := 
  match e with
  | Pconst n => Some n
  | _        => None
  end.

Definition is_bool (e:pexpr) :=
  match e with 
  | Pbool b => Some b 
  | _ => None 
  end.

Inductive is_reflect (A:Type) (P:A -> pexpr) : pexpr -> option A -> Prop := 
 | Is_reflect_some : forall a, is_reflect P (P a) (Some a)
 | Is_reflect_none : forall e, is_reflect P e None.


Lemma is_boolP e : is_reflect Pbool e (is_bool e).
Proof. by case e=> *;constructor. Qed.

Lemma is_constP e : is_reflect Pconst e (is_const e).
Proof. by case: e=>*;constructor. Qed.

