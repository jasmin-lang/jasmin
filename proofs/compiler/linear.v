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

From mathcomp Require Import all_ssreflect all_algebra.
Require Import ZArith.
Require Import Utf8.
Import Relations.

Require Import expr compiler_util.
Import ssrZ.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope seq_scope.
(* --------------------------------------------------------------------------- *)
(* Syntax                                                                      *)

Variant linstr_r :=
  | Lopn   : lvals -> sopn -> pexprs -> linstr_r
  | Lalign : linstr_r
  | Llabel : label -> linstr_r
  | Lgoto  : remote_label -> linstr_r
  | Ligoto : pexpr -> linstr_r (* Absolute indirect jump *)
  | LstoreLabel : lval -> label -> linstr_r
  | Lcond  : pexpr -> label -> linstr_r
.

Arguments Llabel _%positive_scope.

Record linstr : Type := MkLI { li_ii : instr_info; li_i : linstr_r }.

Definition lcmd := seq linstr.

Definition is_label (lbl: label) (i:linstr) : bool :=
  match i.(li_i) with
  | Llabel lbl' => lbl == lbl'
  | _ => false
  end.

(* -------------------------------------------------------------------- *)
Definition find_label (lbl : label) (c : seq linstr) :=
  let idx := seq.find (is_label lbl) c in
  if idx < size c then ok idx else type_error.

Record lfundef := LFundef {
 lfd_stk_size : Z;
 lfd_tyin : seq stype;
 lfd_arg  : seq var_i;
 lfd_body : lcmd;
 lfd_tyout : seq stype;
 lfd_res  : seq var_i;  (* /!\ did we really want to have "seq var_i" here *)
 lfd_to_save: seq var;
 lfd_save_stack: saved_stack;
 lfd_export: bool;
}.

Definition signature_of_lfundef (lfd: lfundef) : function_signature :=
  (lfd_tyin lfd, lfd_tyout lfd).

Record lprog :=
 {  lp_rip   : Ident.ident;
    lp_globs : seq u8;
    lp_stk_id: Ident.ident;
    lp_funcs : seq (funname * lfundef) }.

(* --------------------------------------------------------------------------- *)
(* Translation                                                                 *)

Notation "c1 ';;' c2" :=  (c2 >>= (fun p => c1 p.1 p.2))
   (at level 26, right associativity).

Notation "c1 '>;' c2" :=  (c2 >>= (fun p => ok (p.1, c1 :: p.2)))
   (at level 26, right associativity).

Section LINEAR_C.

  Variable linear_i : instr -> label -> lcmd -> ciexec (label * lcmd).

  Fixpoint linear_c (c:cmd) (lbl:label) (lc:lcmd) :=
    match c with
    | [::] => ciok (lbl, lc)
    | i::c =>
      linear_i i ;; linear_c c lbl lc
    end.

End LINEAR_C.

Definition next_lbl lbl := (lbl + 1)%positive.

Fixpoint snot e :=
  match e with
  | Papp1 Onot e => e
  | Papp2 Oand e1 e2 => Papp2 Oor (snot e1) (snot e2)
  | Papp2 Oor e1 e2 => Papp2 Oand (snot e1) (snot e2)
  | Pif t e e1 e2 => Pif t e (snot e1) (snot e2)
  | Pbool b => Pbool (~~ b)
  | _ => Papp1 Onot e
  end.

Definition add_align ii a (lc:lcmd) :=
  match a with
  | NoAlign => lc
  | Align   =>  MkLI ii Lalign :: lc
  end.

Definition align ii a (lc:ciexec (label * lcmd)) : ciexec (label * lcmd) :=
  Let p := lc in
  ok (p.1, add_align ii a p.2).

Section PROG.

Context (p: sprog) (fn: funname).

Let rsp : var := Var (sword Uptr) p.(p_extra).(sp_stk_id).
Let rspi : var_i := VarI rsp xH.
Let rspg : gvar := Gvar rspi Slocal.

Definition round32 (sz: Z) : Z :=
  (let _32 := 32 in if sz mod _32 == 0 then sz else ((sz + 1) / _32) * _32)%Z.

(*TODO: use cast_const *)
Definition allocate_stack_frame (free: bool) (ii: instr_info) (sz: Z) : linstr :=
  let m i := {| li_ii := ii ; li_i := i |} in
  m (Lopn [:: Lvar rspi] (Ox86 ((if free then ADD else SUB) Uptr)) [:: Pvar rspg; Papp1 (Oword_of_int Uptr) (Pconst sz) ]).

Fixpoint linear_i (i:instr) (lbl:label) (lc:lcmd) :=
  let (ii, ir) := i in
  match ir with
  | Cassgn x _ ty e =>
    if ty is sword sz
    then
      let op := if (sz ≤ U64)%CMP then (MOV sz) else (VMOVDQU sz) in
      ok (lbl, MkLI ii (Lopn [:: x ] (Ox86 op) [:: e]) :: lc)
    else cierror ii (Cerr_linear "assign not a word")
  | Copn xs _ o es => ok (lbl, MkLI ii (Lopn xs o es) :: lc)

  | Cif e [::] c2 =>
    let L1 := lbl in
    let lbl := next_lbl L1 in
    MkLI ii (Lcond e L1) >; linear_c linear_i c2 lbl (MkLI ii (Llabel L1) :: lc)

  | Cif e c1 [::] =>
    let L1 := lbl in
    let lbl := next_lbl L1 in
    MkLI ii (Lcond (snot e) L1) >; linear_c linear_i c1 lbl (MkLI ii (Llabel L1) :: lc)

  | Cif e c1 c2 =>
    let L1 := lbl in
    let L2 := next_lbl L1 in
    let lbl := next_lbl L2 in
                           MkLI ii (Lcond e L1) >;
                           linear_c linear_i c2 ;;
                           MkLI ii (Lgoto (fn, L2)) >;
    MkLI ii (Llabel L1) >; linear_c linear_i c1 lbl
   (MkLI ii (Llabel L2) :: lc)

  | Cwhile a c e c' =>
    match is_bool e with
    | Some true =>
      let L1 := lbl in
      let lbl := next_lbl L1 in
      align ii a (
      MkLI ii (Llabel L1) >; linear_c linear_i c ;;
                             linear_c linear_i c' lbl
                             (MkLI ii (Lgoto (fn, L1)) :: lc))

    | Some false =>
      linear_c linear_i c lbl lc

    | None =>
      match c' with
      | [::] =>
      let L1 := lbl in
      let lbl := next_lbl L1 in
      align ii a (MkLI ii (Llabel L1) >; linear_c linear_i c lbl
                             (MkLI ii (Lcond e L1) :: lc))
      | _ =>
      let L1 := lbl in
      let L2 := next_lbl L1 in
      let lbl := next_lbl L2 in
                             MkLI ii (Lgoto (fn, L1)) >;
      align ii a (MkLI ii (Llabel L2) >; linear_c linear_i c' ;;
      MkLI ii (Llabel L1) >; linear_c linear_i c lbl
                             (MkLI ii (Lcond e L2) :: lc))
      end
    end

  | Ccall _ xs fn es =>
    if get_fundef (p_funcs p) fn is Some fd then
    if all2 (λ e a, if e is Pvar (Gvar v _) then v_var v == v_var a else false) es (f_params fd)
    then if all2 (λ x r, if x is Lvar v then v_var v == v_var r else false) xs (f_res fd)
    then
      let e := f_extra fd in
      if sf_return_address e is Some ra then
      if sf_to_save e is [::] then
        let sz := round32 (sf_stk_sz e) in
        let: (before, after) :=
           if sz == 0 then ([::], [::]) else ([:: allocate_stack_frame false ii sz ], [:: allocate_stack_frame true ii sz ])
        in
        let lret := next_lbl lbl in
        ok (lret, MkLI ii (LstoreLabel (Lvar (VarI ra xH)) lret) :: before ++ MkLI ii (Lgoto (fn, xH)) :: MkLI ii (Llabel lret) :: after ++ lc)
      else cierror ii (Cerr_linear "called function will destroy local variables")
      else cierror ii (Cerr_linear "nowhere to store the return address")
    else cierror ii (Cerr_linear "bad call dests")
    else cierror ii (Cerr_linear "bad call args")
    else cierror ii (Cerr_linear "call to unknown function")

  | Cfor _ _ _ => cierror ii (Cerr_linear "for found in linear")
  end.

Definition linear_fd (fd: sfundef) :=
  let: (tail, head, lbl) :=
     if sf_return_address (f_extra fd) is Some r
     then ([:: MkLI xH (Ligoto (Pvar {| gv := VarI r xH ; gs := Slocal |})) ], [:: MkLI xH (Llabel 1) ], 2%positive)
     else ([::], [::], 1%positive)
  in
  Let fd' := linear_c linear_i (f_body fd) lbl tail in
  let e := fd.(f_extra) in
  let is_export := sf_return_address e == None in
  let res := if is_export then f_res fd else [::] in
  ok (LFundef (sf_stk_sz e) (f_tyin fd) (f_params fd) (head ++ fd'.2) (f_tyout fd) res (sf_to_save e) (sf_save_stack e)
              is_export).

End PROG.

Definition linear_prog (p: sprog) : cfexec lprog :=
  Let _ := assert (size p.(p_globs) == 0) 
             (Ferr_msg (Cerr_linear "invalid p_globs, please report")) in
  Let funcs := map_cfprog_name (linear_fd p) p.(p_funcs) in
  ok {| lp_rip   := p.(p_extra).(sp_rip);
        lp_globs := p.(p_extra).(sp_globs);
        lp_stk_id := p.(p_extra).(sp_stk_id);
        lp_funcs := funcs |}.

Module Eq_linstr.
  Definition eqb_r i1 i2 :=
    match i1, i2 with
    | Lopn lv1 o1 e1, Lopn lv2 o2 e2 => (lv1 == lv2) && (o1 == o2) && (e1 == e2)
    | Lalign, Lalign => true
    | Llabel l1, Llabel l2 => l1 == l2
    | Lgoto l1, Lgoto l2 => l1 == l2
    | Ligoto e1, Ligoto e2 => e1 == e2
    | LstoreLabel lv1 lbl1, LstoreLabel lv2 lbl2 => (lv1 == lv2) && (lbl1 == lbl2)
    | Lcond e1 l1, Lcond e2 l2 => (e1 == e2) && (l1 == l2)
    | _, _ => false
    end.

  Lemma eqb_r_axiom : Equality.axiom eqb_r.
  Proof.
    case => [lv1 o1 e1||l1|l1|e1|lv1 l1|e1 l1] [lv2 o2 e2||l2|l2|e2|lv2 l2|e2 l2] //=;try by constructor.
    + apply (@equivP (((lv1 == lv2) && (o1 == o2)) /\ e1 == e2 ));first by apply andP.
      by split => [ [] /andP [] /eqP -> /eqP -> /eqP -> //| [] -> -> ->];rewrite !eqxx.
    + by apply: (equivP eqP); split; congruence.
    + by apply: (equivP eqP); split; congruence.
    + by apply: (equivP eqP); split; congruence.
    + apply: (equivP andP); split.
      * by case=> /eqP <- /eqP <-.
      by case => <- <-; rewrite !eqxx.
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
