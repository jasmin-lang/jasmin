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

From mathcomp Require Import all_ssreflect.
Require Import Utf8.
Require Import expr.

Section LOWERING.

Record fresh_vars : Type :=
  {
    fresh_OF : var;
    fresh_CF : var;
    fresh_SF : var;
    fresh_PF : var;
    fresh_ZF : var;
  }.

Context (fv: fresh_vars).

Definition var_info_of_lval (x: lval) : var_info :=
  match x with 
  | Lnone i t => i
  | Lvar x | Lmem x _ | Laset x _ => v_info x
  end.

Definition lower_condition vi (pe: pexpr) : seq instr_r * pexpr :=
  let f := Lnone vi sbool in
  let fr n := {| v_var := n fv ; v_info := vi |} in
  match pe with
  | Papp2 op x y =>
    match op with
    | Oeq (Cmp_sw | Cmp_uw) =>
      ([:: Copn [:: f ; f ; f ; f ; Lvar (fr fresh_ZF) ] Ox86_CMP [:: x ; y ] ], Pvar (fr fresh_ZF))
    | Oneq (Cmp_sw | Cmp_uw) =>
      ([:: Copn [:: f ; f ; f ; f ; Lvar (fr fresh_ZF) ] Ox86_CMP [:: x ; y ] ], Papp1 Onot (Pvar (fr fresh_ZF)))
    | Olt Cmp_sw =>
      ([:: Copn [:: Lvar (fr fresh_OF) ; f ; Lvar (fr fresh_SF) ; f ; f ] Ox86_CMP [:: x ; y ] ],
       Pif (Pvar (fr fresh_SF)) (Papp1 Onot (Pvar (fr fresh_OF))) (Pvar (fr fresh_OF)))
    | Olt Cmp_uw =>
      ([:: Copn [:: f ; Lvar (fr fresh_CF) ; f ; f ; f ] Ox86_CMP [:: x ; y ] ], Pvar (fr fresh_CF))
    | Ole Cmp_sw =>
      ([:: Copn [:: Lvar (fr fresh_OF) ; f ; Lvar (fr fresh_SF) ; f ; Lvar (fr fresh_ZF) ] Ox86_CMP [:: x ; y ] ],
       Papp2 Oor (Pvar (fr fresh_ZF))
             (Pif (Pvar (fr fresh_SF)) (Papp1 Onot (Pvar (fr fresh_OF))) (Pvar (fr fresh_OF))))
    | Ole Cmp_uw =>
      ([:: Copn [:: f ; Lvar (fr fresh_CF) ; f ; f ; Lvar (fr fresh_ZF) ] Ox86_CMP [:: x ; y ] ],
       Papp2 Oor (Pvar (fr fresh_CF)) (Pvar (fr fresh_ZF)))
    | Ogt Cmp_sw =>
      ([:: Copn [:: Lvar (fr fresh_OF) ; f ; Lvar (fr fresh_SF) ; f ; Lvar (fr fresh_ZF) ] Ox86_CMP [:: x ; y ] ],
       Papp2 Oand
             (Papp1 Onot (Pvar (fr fresh_ZF)))
             (Pif (Pvar (fr fresh_SF)) (Pvar (fr fresh_OF)) (Papp1 Onot (Pvar (fr fresh_OF)))))
    | Ogt Cmp_uw =>
      ([:: Copn [:: f ; Lvar (fr fresh_CF) ; f ; f ; Lvar (fr fresh_ZF) ] Ox86_CMP [:: x ; y ] ],
       Papp2 Oand
             (Papp1 Onot (Pvar (fr fresh_CF)))
             (Papp1 Onot (Pvar (fr fresh_ZF))))
    | Oge Cmp_sw =>
      ([:: Copn [:: Lvar (fr fresh_OF) ; f ; Lvar (fr fresh_SF) ; f ; f ] Ox86_CMP [:: x ; y ] ],
             (Pif (Pvar (fr fresh_SF)) (Pvar (fr fresh_OF)) (Papp1 Onot (Pvar (fr fresh_OF)))))
    | Oge Cmp_uw =>
      ([:: Copn [:: f ; Lvar (fr fresh_CF) ; f ; f ; f ] Ox86_CMP [:: x ; y ] ],
       Papp1 Onot (Pvar (fr fresh_CF)))
    | _ => ([::], pe)
    end
  | _ => ([::], pe)
  end.

(* Lowering of Cassgn
*)

Variant add_inc_dec : Type :=
  | AddInc of pexpr
  | AddDec of pexpr
  | AddNone.

Definition add_inc_dec_classify (a: pexpr) (b: pexpr) :=
  match a, b with
  | Pcast (Pconst 1), y | y, Pcast (Pconst 1) => AddInc y
  | Pcast (Pconst (-1)), y | y, Pcast (Pconst (-1)) => AddDec y
  | _, _ => AddNone
  end.

Variant sub_inc_dec : Type :=
  | SubInc
  | SubDec
  | SubNone.

Definition sub_inc_dec_classify (e: pexpr) :=
  match e with
  | Pcast (Pconst (-1)) => SubInc
  | Pcast (Pconst 1) => SubDec
  | _ => SubNone
  end.

Definition lower_cassgn  (x: lval) (tg: assgn_tag) (e: pexpr) : seq instr_r :=
  let vi := var_info_of_lval x in
  let f := Lnone vi sbool in
  let copn o a := [:: Copn [:: x ] o [:: a] ] in
  let fopn o a b := [:: Copn [:: f ; f ; f ; f ; f ; x ] o [:: a ; b ] ] in
  let mul o a b := [:: Copn [:: f ; f ; f ; f ; f ; Lnone vi sword (* hi *) ; x ] o [:: a ; b ] ] in
  let inc o a := [:: Copn [:: f ; f ; f ; f ; x ] o [:: a ] ] in
  match e with
  | Pcast (Pconst _)
  | Pvar {| v_var := {| vtype := sword |} |}
  | Pget _ _
  | Pload _ _
    => copn Ox86_MOV e

  | Papp1 Olnot a => copn Ox86_NOT a

  | Papp2 op a b =>
    match op with
    | Oadd Op_w =>
      match add_inc_dec_classify a b with
      | AddInc y => inc Ox86_INC y
      | AddDec y => inc Ox86_DEC y
      | AddNone => fopn Ox86_ADD a b (* TODO: lea *)
      end
    | Osub Op_w =>
      match sub_inc_dec_classify b with
      | SubInc => inc Ox86_INC a
      | SubDec => inc Ox86_DEC a
      | SubNone => fopn Ox86_SUB a b
      end
    | Omul Op_w => mul Ox86_MUL a b
    | Oland => fopn Ox86_AND a b
    | Olor => fopn Ox86_OR a b
    | Olxor => fopn Ox86_XOR a b
    | Olsr => fopn Ox86_SHR a b
    | Olsl => fopn Ox86_SHL a b
    | Oasr => fopn Ox86_SAR a b
    | Oeq (Cmp_sw | Cmp_uw) => [:: Copn [:: f ; f ; f ; f ; x ] Ox86_CMP [:: a ; b ] ]
    | Olt Cmp_uw => [:: Copn [:: f ; x ; f ; f ; f ] Ox86_CMP [:: a ; b ] ]
    | _ => [:: Cassgn x tg e ]
    end

  | Pif e e1 e2 => 
    let (l, e) := lower_condition vi e in
    l ++ [:: Copn [:: x] Ox86_CMOVcc [:: e; e1; e2]]
    
  | _ => [:: Cassgn x tg e ]
  end.

(* Lowering of Oaddcarry
… = #addc(x, y, false) → ADD(x, y)
… = #addc(?, ?, true) → #error
… = #addc(?, ?, c) → ADC
*)

Definition Lnone_b vi := Lnone vi sbool.

Definition lower_addcarry (sub: bool) (xs: lvals) (es: pexprs) : seq instr_r :=
  match xs, es with
  | [:: cf ; r ], [:: x ; y ; Pbool false ] =>
    let vi := var_info_of_lval r in
    [:: Copn [:: Lnone_b vi; cf ; Lnone_b vi ; Lnone_b vi ; Lnone_b vi ; r ]
        (if sub then Ox86_SUB else Ox86_ADD) [:: x ; y ] ]
  | [:: cf ; r ], [:: _ ; _ ; Pvar cfi ] =>
    let vi := v_info cfi in
    [:: Copn [:: Lnone_b vi ; cf ; Lnone_b vi ; Lnone_b vi ; Lnone_b vi ; r ]
        (if sub then Ox86_SBB else Ox86_ADC) es ]
  | _, _ => [:: Copn xs (if sub then Osubcarry else Oaddcarry) es ]
  end.

Definition lower_mulu (xs: lvals) (es: pexprs) : seq instr_r :=
  match xs, es with
  | [:: r1; r2 ], [:: x ; y ] =>
    let vi := var_info_of_lval r2 in
    let f := Lnone_b vi in
    [:: Copn [:: f ; f ; f ; f ; f ; r1 ; r2 ] Ox86_MUL es ]
  | _, _ => [:: Copn xs Omulu es ]
  end.

Definition lower_copn (xs: lvals) (op: sopn) (es: pexprs) : seq instr_r :=
  match op with
  | Oaddcarry => lower_addcarry false xs es
  | Osubcarry => lower_addcarry true xs es
  | Omulu => lower_mulu xs es
  | _ => [:: Copn xs op es]
  end.

Definition lower_cmd (lower_i: instr -> cmd) (c:cmd) : cmd :=
  List.fold_right (fun i c' => lower_i i ++ c') [::] c.

Fixpoint lower_i (i:instr) : cmd :=
  let (ii, ir) := i in
  map (MkI ii)
  match ir with
  | Cassgn l t e => lower_cassgn l t e
  | Copn   l o e => lower_copn l o e
  | Cif e c1 c2  =>
     let '(pre, e) := lower_condition xH e in
     rcons pre (Cif e (lower_cmd lower_i c1) (lower_cmd lower_i c2))
  | Cfor v (d, lo, hi) c =>
     [:: Cfor v (d, lo, hi) (lower_cmd lower_i c)]
  | Cwhile c e c' =>
     let '(pre, e) := lower_condition xH e in
     [:: Cwhile ((lower_cmd lower_i c) ++ map (MkI xH) pre) e (lower_cmd lower_i c')]
  | _ => [:: ir]
  end.

Definition lower_fd (fd: fundef) : fundef :=
  {| f_iinfo := f_iinfo fd;
     f_params := f_params fd;
     f_body := lower_cmd lower_i (f_body fd);
     f_res := f_res fd
  |}.

Definition lower_prog (p: prog) := map_prog lower_fd p.

End LOWERING.
