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

Require Import Utf8.
Require Import expr.
Import seq.

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
  match x with Lnone i => i | Lvar x | Lmem x _ | Laset x _ => v_info x end.

Definition lower_condition vi (pe: pexpr) : seq instr_r * pexpr :=
  let f := Lnone vi in
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
TODO: Pif → CMOVcc
*)

Definition lower_cassgn  (x: lval) (tg: assgn_tag) (e: pexpr) : seq instr_r :=
  let vi := var_info_of_lval x in
  let f := Lnone vi in
  let copn o a := [:: Copn [:: x ] o [:: a] ] in
  let fopn o a b := [:: Copn [:: f ; f ; f ; f ; f ; x ] o [:: a ; b ] ] in
  let mul o a b := [:: Copn [:: f ; f ; f ; f ; f ; f ; x ] o [:: a ; b ] ] in
  let inc o a := [:: Copn [:: f ; f ; f ; f ; x ] o [:: a ] ] in
  let shift o a b :=
      let fr n := Pvar {| v_var := n fv ; v_info := vi |} in
      [:: Copn [:: f ; f ; f ; f ; f ; x ] o [:: fr fresh_OF ; fr fresh_CF ; fr fresh_SF ; fr fresh_PF ; fr fresh_ZF ; a ; b ] ] in
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
      match a, b with
      | Pcast (Pconst 1), y | y, Pcast (Pconst 1) => inc Ox86_INC y
      | Pcast (Pconst (-1)), y | y, Pcast (Pconst (-1)) => inc Ox86_DEC y
      | _, _ => fopn Ox86_ADD a b (* TODO: lea *)
      end
    | Osub Op_w =>
      match a, b with
      | Pcast (Pconst 1), y | y, Pcast (Pconst 1) => inc Ox86_DEC y
      | Pcast (Pconst (-1)), y | y, Pcast (Pconst (-1)) => inc Ox86_INC y
      | _, _ => fopn Ox86_SUB a b
      end
    | Omul Op_w => mul Ox86_MUL a b
    | Oland => fopn Ox86_AND a b
    | Olor => fopn Ox86_OR a b
    | Olxor => fopn Ox86_XOR a b
    | Olsr => shift Ox86_SHR a b
    | Olsl => shift Ox86_SHL a b
    | Oasr => shift Ox86_SAR a b
    | Oeq (Cmp_sw | Cmp_uw) => [:: Copn [:: f ; f ; f ; f ; x ] Ox86_CMP [:: a ; b ] ]
    | Olt Cmp_uw => [:: Copn [:: f ; x ; f ; f ; f ] Ox86_CMP [:: a ; b ] ]
    | _ => [:: Cassgn x tg e ]
    end

  | _ => [:: Cassgn x tg e ]
  end.

(* Lowering of Oaddcarry
… = #addc(x, y, false) → ADD(x, y)
… = #addc(?, ?, true) → #error
… = #addc(?, ?, c) → ADC
*)

Definition lower_addcarry (sub: bool) (xs: lvals) (es: pexprs) : seq instr_r :=
  match xs, es with
  | [:: cf ; r ], [:: x ; y ; Pbool false ] =>
    let vi := var_info_of_lval r in
    [:: Copn [:: Lnone vi ; cf ; Lnone vi ; Lnone vi ; Lnone vi ; r ]
        (if sub then Ox86_SUB else Ox86_ADD) [:: x ; y ] ]
  | [:: cf ; r ], [:: _ ; _ ; Pvar cfi ] =>
    let vi := v_info cfi in
    [:: Copn [:: Lnone vi ; cf ; Lnone vi ; Lnone vi ; Lnone vi ; r ]
        (if sub then Ox86_SBB else Ox86_ADC) es ]
  | _, _ => [:: Copn xs (if sub then Osubcarry else Oaddcarry) es ]
  end.

Definition lower_copn (xs: lvals) (op: sopn) (es: pexprs) : seq instr_r :=
  match op with
  | Oaddcarry => lower_addcarry false xs es
  | Osubcarry => lower_addcarry true xs es
  | Omulu (* TODO *)
  | _ => [:: Copn xs op es]
  end.

Definition lower_instruction_set_cmd (c: cmd) : cmd :=
  @cmd_rect (λ _, seq instr_r) (λ _, cmd) (λ _, cmd)
    (λ _ ii, map (MkI ii))
    [::]
    (λ _ _, cat)
    lower_cassgn
    lower_copn
    (λ e _ _ c1 c2,
     let '(pre, e) := lower_condition xH e in
     rcons pre (Cif e c1 c2))
    (λ v d lo hi _ c, [:: Cfor v (d, lo, hi) c ])
    (λ _ e _ c c',
     let '(pre, e) := lower_condition xH e in
     [:: Cwhile (c ++ map (MkI xH) pre) e c' ])
    (λ ii xs f es, [:: Ccall ii xs f es])
    c
.

Definition lower_instruction_set_fd (fd: fundef) : fundef :=
  {| f_iinfo := f_iinfo fd;
     f_params := f_params fd;
     f_body := lower_instruction_set_cmd (f_body fd);
     f_res := f_res fd
  |}.

Definition lower_instruction_set_prog (p: prog) : prog :=
  map
    (λ x, let '(n, d) := x in (n, lower_instruction_set_fd d))
    p.

End LOWERING.
