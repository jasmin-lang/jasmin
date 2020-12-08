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

(* * Syntax and semantics of the linear language *)

(* ** Imports and settings *)

From mathcomp Require Import all_ssreflect.
Require Import ZArith.
Require Import Utf8.
Import Relations.

Require Import expr compiler_util stack_alloc leakage.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope seq_scope.
(* --------------------------------------------------------------------------- *)
(* Syntax                                                                      *)

Definition label := positive.

(* low level instructions *)
(* Lilabel l --> Creats a label names l *)
(* Ligoto l --> Jumps to the location which is labelled as l.
   Once execution of goto is finished, the control jumps to the next instruction after l *)
(* Licond e l --> Conditional expression as e and takes a label l *)
Variant linstr_r :=
  | Liopn   : lvals -> sopn -> pexprs -> linstr_r
  | Lialign : linstr_r
  | Lilabel : label -> linstr_r
  | Ligoto  : label -> linstr_r
  | Licond  : pexpr -> label -> linstr_r
.

Record linstr : Type := MkLI { li_ii : instr_info; li_i : linstr_r }.

Definition lcmd := seq linstr.


Definition is_label (lbl: label) (i:linstr) : bool :=
  match i.(li_i) with
  | Lilabel lbl' => lbl == lbl'
  | _ => false
  end.

(* -------------------------------------------------------------------- *)
Definition find_label (lbl : label) (c : seq linstr) :=
  let idx := seq.find (is_label lbl) c in
  if idx < size c then ok idx else type_error.

Record lfundef := LFundef {
 lfd_stk_size : Z;
 lfd_nstk : Ident.ident;
 lfd_tyin : seq stype;
 lfd_arg  : seq var_i;
 lfd_body : lcmd;
 lfd_tyout : seq stype;
 lfd_res  : seq var_i;  (* /!\ did we really want to have "seq var_i" here *)
 lfd_extra : list var * saved_stack;
}.

Definition signature_of_lfundef (lfd: lfundef) : function_signature :=
  (lfd_tyin lfd, lfd_tyout lfd).

Definition lprog := seq (funname * lfundef).

(* --------------------------------------------------------------------------- *)
(* Translation                                                                 *)

(*c1(c2)*)
Notation "c1 ';;' c2" :=  (c2 >>= (fun p => c1 p.1.1 p.1.2 p.2))
   (at level 26, right associativity).

Notation "c1 '>;' c2" :=  (c2 >>= (fun p => ok (p.1.1, c1 :: p.1.2, p.2)))
   (at level 26, right associativity).

Section LINEAR_C.

  Variable linear_i : instr -> label -> lcmd -> ciexec (label * lcmd * leak_i_il_tr).
  
  (* FIX NEEDED *)
  Fixpoint linear_c (c:cmd) (lbl:label) (lc:lcmd) : 
  ciexec (label * lcmd * seq leak_i_il_tr) :=
    match c with
    | [::] => ciok (lbl, lc, [::])
    | i::c => Let rc := linear_c c lbl lc in 
              Let ri := linear_i i rc.1.1 rc.1.2 in 
              ciok (ri.1.1, ri.1.2, (ri.2 :: rc.2))
     (*linear_i i ;; linear_c c lbl lc*)
    end.

End LINEAR_C.

(* increment the label by 1 which helps to go to the next instruction*)
Definition next_lbl lbl := (lbl + 1)%positive.

Fixpoint snot e : (pexpr * leak_e_tr) :=
  match e with
  | Papp1 Onot e => (e, LT_id)
  | Papp2 Oand e1 e2 => let re1 := (snot e1) in 
                        let re2 := (snot e2) in 
                        (Papp2 Oor re1.1 re2.1,
                         LT_map [:: re1.2; re2.2])
  | Papp2 Oor e1 e2 => let re1 := (snot e1) in
                       let re2 := (snot e2) in 
                       (Papp2 Oand re1.1 re2.1,
                        LT_map [:: re1.2; re2.2])
  | Pif t e e1 e2 => let re1 := (snot e1) in 
                     let re2 := (snot e2) in 
                     (Pif t e re1.1 re2.1,
                      LT_map [:: LT_id; re1.2; re2.2])
  | Pbool b => (Pbool (~~ b), LT_id)
  | _ => (Papp1 Onot e, LT_id)
  end.

(* Adds an alignment instruction in front of the seqence of instructions *)
Definition add_align ii a (lc:lcmd) : (lcmd) :=
  match a with
  | NoAlign => lc
  | Align   =>  MkLI ii Lialign :: lc
  end.

(* Computes the leakage depending on alignment *) 
Definition get_align_leak_il a : seq leak_il :=
  match a with 
  | NoAlign => [::]
  | Align => [:: Lempty]
  end.

Definition align ii a (lc:ciexec (label * lcmd * seq leak_i_il_tr)) : 
  ciexec (label * lcmd * seq leak_i_il_tr) :=
  Let p := lc in
  ok (p.1.1, add_align ii a p.1.2, p.2).

Fixpoint linear_i (i:instr) (lbl:label) (lc:lcmd) : ciexec (label * lcmd * leak_i_il_tr) :=
  let (ii, ir) := i in
  match ir with
  | Cassgn x _ ty e =>
    if ty is sword sz
    then
      let op := if (sz ≤ U64)%CMP then (MOV sz) else (VMOVDQU sz) in
      ok (lbl, MkLI ii (Liopn [:: x ] (Ox86 op) [:: e]) :: lc, LT_ilkeepa)
    else cierror ii (Cerr_linear "assign not a word")
  | Copn xs _ o es => ok (lbl, MkLI ii (Liopn xs o es) :: lc, LT_ilkeep)

    (* Licond e L1; c2; Lilabel L1 *)
    (* Lcondl le b :: lc2 :: Lempty *)
    (* Cif e [::] c2; L1 (label for next instruction) *)
  | Cif e [::] c2 =>
    let L1 := lbl in
    let lbl := next_lbl L1 in
    Let rs := MkLI ii (Licond e L1) >; linear_c linear_i c2 lbl (MkLI ii (Lilabel L1) :: lc) in 
    ciok (rs.1.1, rs.1.2, LT_ilcond_0 rs.2)
  
    (* Licond e L1; c1; Lilabel L1 *)
    (* Lcondl le b :: lc1 :: Lempty *)
  | Cif e c1 [::] =>
    let L1 := lbl in
    let lbl := next_lbl L1 in
    let rse := snot e in 
    Let rs := MkLI ii (Licond rse.1 L1) >; linear_c linear_i c1 lbl (MkLI ii (Lilabel L1) :: lc) in 
    ciok (rs.1.1, rs.1.2, LT_ilcond_0 rs.2)

    (* Licond e L1; c2; Ligoto L2; Lilabel L1; c1; Lilabel L2 *)
    (* L1 is then and L2 is end *)
    (* Lcondl le b :: Lc2 :: Lempty :: Lc1 :: Lempty *)
  | Cif e c1 c2 =>
    let L1 := lbl in
    let L2 := next_lbl L1 in
    let lbl := next_lbl L2 in
    Let rs1 := MkLI ii (Ligoto L2) >; MkLI ii (Lilabel L1) >; linear_c linear_i c1 lbl (MkLI ii (Lilabel L2) :: lc) in
    Let rs2 :=  MkLI ii (Licond e L1) >; linear_c linear_i c2 rs1.1.1 rs1.1.2 in 
    ok (rs2.1.1, rs2.1.2, LT_ilcond rs1.2 rs2.2)
                           (*MkLI ii (Lcond e L1) >;
                           linear_c linear_i c2 ;;
                           MkLI ii (Lgoto L2) >;
    MkLI ii (Llabel L1) >; linear_c linear_i c1 lbl
   (MkLI ii (Llabel L2) :: lc)*)

  | Cwhile a c e c' =>
    (* We never reach a state where e evaluates to true as instruction won't terminate *)
    match is_bool e with
    | Some false =>
      Let rs := linear_c linear_i c lbl lc in 
      ciok (rs.1.1, rs.1.2, LT_ilwhile_f rs.2)

    | _ =>
      match c' with
      (* align; Lilabel L1; c ; Licond e L1 *)
      (* Lempty :: Lempty :: Lc :: Lcondl e b :: Lc :: Lcondl e b ..... *)
      (* L1 is loop head label *)
      | [::] =>
      let L1 := lbl in
      let lbl := next_lbl L1 in
      Let rs := align ii a (MkLI ii (Lilabel L1) >; linear_c linear_i c lbl
                             (MkLI ii (Licond e L1) :: lc)) in 
      ciok (rs.1.1, rs.1.2, LT_ilkeep)
      (* Ligoto L1; align; Lilabel L2; c'; Lilabel L1; c; Lcond e L2; 
         c'; Lilabel L1; c; Lcond e L2; .....*)
      (* Lempty :: Lempty :: Lempty :: Lc' :: Lempty :: Lcondl e b :: 
         Lc' :: Lempty :: Lc :: Lcondl e b :: .......*)
      | _ =>
      let L1 := lbl in
      let L2 := next_lbl L1 in
      let lbl := next_lbl L2 in
      Let rs1 :=  MkLI ii (Lilabel L1) >; linear_c linear_i c lbl
                             (MkLI ii (Licond e L2) :: lc) in 
      let rs3 := align ii a (MkLI ii (Lilabel L2) >; linear_c linear_i c' rs1.1.1 rs1.1.2) in 
      Let rs := MkLI ii (Ligoto L1) >; rs3 in 
      ciok (rs.1.1, rs.1.2, LT_ilkeep)

      end
    end

  | Cfor _ _ _ => cierror ii (Cerr_linear "for found in linear")

  | Ccall _ _ _ _ => cierror ii (Cerr_linear "call found in linear")
  end.

Definition linear_fd (fd: sfundef) : ciexec (lfundef * seq leak_i_il_tr) :=
  Let fd' := linear_c linear_i (sf_body fd) 1%positive [::] in
  ok (LFundef (sf_stk_sz fd) (sf_stk_id fd) (sf_tyin fd) (sf_params fd) fd'.1.2 (sf_tyout fd) (sf_res fd) (sf_extra fd),
      fd'.2).

Definition linear_prog (p: sprog) : cfexec (lprog * leak_f_lf_tr) :=
  map_cfprog_leak linear_fd p.

Module Eq_linstr.
  Definition eqb_r i1 i2 :=
    match i1, i2 with
    | Liopn lv1 o1 e1, Liopn lv2 o2 e2 => (lv1 == lv2) && (o1 == o2) && (e1 == e2)
    | Lialign, Lialign => true
    | Lilabel l1, Lilabel l2 => l1 == l2
    | Ligoto l1, Ligoto l2 => l1 == l2
    | Licond e1 l1, Licond e2 l2 => (e1 == e2) && (l1 == l2)
    | _, _ => false
    end.

  Lemma eqb_r_axiom : Equality.axiom eqb_r.
  Proof.
    case => [lv1 o1 e1||l1|l1|e1 l1] [lv2 o2 e2||l2|l2|e2 l2] //=;try by constructor.
    + apply (@equivP (((lv1 == lv2) && (o1 == o2)) /\ e1 == e2 ));first by apply andP.
      by split => [ [] /andP [] /eqP -> /eqP -> /eqP -> //| [] -> -> ->];rewrite !eqxx.
    + apply (@equivP (l1 = l2));first by apply eqP.
      by split => [->|[]->].
    + apply (@equivP (l1 = l2));first by apply eqP.
      by split => [->|[]->].
    apply (@equivP ((e1 == e2) /\ (l1 == l2)));first by apply andP.
    by split => [ [] /eqP -> /eqP -> //| [] -> ->];rewrite !eqxx.
  Qed.

  Definition linstr_r_eqMixin := Equality.Mixin eqb_r_axiom.

  Definition eqb i1 i2 :=
    (li_ii i1 == li_ii i2) && (eqb_r (li_i i1) (li_i i2)).

  Lemma eqb_axiom : Equality.axiom eqb.
  Proof.
    case=> [ii1 i1] [ii2 i2];rewrite /eqb /=.
    apply (@equivP ((ii1 == ii2) /\ eqb_r i1 i2));first by apply andP.
    split => [[]/eqP -> /eqb_r_axiom -> // | [] -> ->];rewrite eqxx;split => //.
    by apply /eqb_r_axiom.
  Qed.

  Definition linstr_eqMixin := Equality.Mixin eqb_axiom.

  Module Exports.
  Canonical linstr_r_eqType  := Eval hnf in EqType linstr_r linstr_r_eqMixin.
  Canonical linstr_eqType  := Eval hnf in EqType linstr linstr_eqMixin.
  End Exports.
End Eq_linstr.
Export Eq_linstr.Exports.
