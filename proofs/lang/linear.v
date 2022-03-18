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

(* * Syntax of the linear language *)

From mathcomp Require Import all_ssreflect all_algebra.
Require Import expr label sopn.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section ASM_OP.

Context `{asmop:asmOp}.

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
 lfd_info : fun_info;
 lfd_align : wsize;
 lfd_tyin : seq stype;
 lfd_arg  : seq var_i;
 lfd_body : lcmd;
 lfd_tyout : seq stype;
 lfd_res  : seq var_i;  (* /!\ did we really want to have "seq var_i" here *)
 lfd_export: bool;
 lfd_callee_saved: seq var; (* A list of variables that must be initialized before calling this function *)
 lfd_total_stack: Z; (* total amount of stack memory needed by this function (and all functions called by this one *)
 (* This is [lfd_total_stack] without padding, rounded to the next alignment
    multiple if the function is export and we need to clean the stack. *)
  lfd_used_stack : Z;
}.

Definition signature_of_lfundef (lfd: lfundef) : function_signature :=
  (lfd_tyin lfd, lfd_tyout lfd).

Definition map_lfundef (f : lcmd -> lcmd) (lfd : lfundef) : lfundef :=
  {|
    lfd_info := lfd_info lfd;
    lfd_align := lfd_align lfd;
    lfd_tyin := lfd_tyin lfd;
    lfd_arg := lfd_arg lfd;
    lfd_body := f (lfd_body lfd);
    lfd_tyout := lfd_tyout lfd;
    lfd_res := lfd_res lfd;
    lfd_export := lfd_export lfd;
    lfd_callee_saved := lfd_callee_saved lfd;
    lfd_total_stack := lfd_total_stack lfd;
    lfd_used_stack := lfd_used_stack lfd;
  |}.


(* -------------------------------------------------------------------- *)

Record lprog :=
  {
    lp_rip : Ident.ident;
    lp_rsp : Ident.ident;
    lp_globs : seq u8;
    lp_funcs : seq (funname * lfundef);
  }.

Definition map_lprog_name
  (f : funname -> lfundef -> lfundef) (lp : lprog) : lprog :=
  {|
    lp_rip := lp_rip lp;
    lp_rsp := lp_rsp lp;
    lp_globs := lp_globs lp;
    lp_funcs := map (fun '(fn, fd) => (fn, f fn fd)) (lp_funcs lp);
  |}.

Definition map_lprog (f : lfundef -> lfundef) (lp : lprog) : lprog :=
  map_lprog_name (fun _ => f) lp.

Lemma get_map_lprog_name f lp fn :
  get_fundef (lp_funcs (map_lprog_name f lp)) fn
  = ssrfun.omap (f fn) (get_fundef (lp_funcs lp) fn).
Proof.
  rewrite /get_fundef /map_lprog_name /=.
  elim: lp_funcs => // -[fn' fd] pfuns /= ->;
    by case: eqP => [-> |].
Qed.

Lemma get_map_lprog f lp fn :
  get_fundef (lp_funcs (map_lprog f lp)) fn
  = ssrfun.omap f (get_fundef (lp_funcs lp) fn).
Proof. by apply: get_map_lprog_name. Qed.


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
Canonical  linstr_r_eqType  := Eval hnf in EqType linstr_r linstr_r_eqMixin.

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
Canonical  linstr_eqType  := Eval hnf in EqType linstr linstr_eqMixin.


(* -------------------------------------------------------------------- *)

Fixpoint max_map
  {A B : Type} `{Cmp B} (f : A -> option B) xs acc : option B :=
  match xs with
  | [::] => acc
  | x :: xs' =>
      let acc' :=
        if f x is Some y
        then Some (if acc is Some z then max y z else y)
        else acc
      in
      max_map f xs' acc'
  end.

Definition max_lcmd_lbl (c : lcmd) : option label :=
  let f '(MkLI _ i) :=
    if i is Llabel lbl
    then Some lbl
    else None
  in
  max_map f c None.

Definition max_lfd_lbl (lfd : lfundef) : option label :=
  max_lcmd_lbl (lfd_body lfd).

Definition max_lprog_lbl (p : lprog) : option label :=
  max_map (fun '(_, fd) => max_lfd_lbl fd) (lp_funcs p) None.

Definition next_lbl lbl := (lbl + 1)%positive.

Definition next_lprog_lbl (p : lprog) : label :=
  if max_lprog_lbl p is Some lbl
  then next_lbl lbl
  else xH.

End ASM_OP.

