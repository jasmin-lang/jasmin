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

Definition lower_pexpr (pe: pexpr) : seq instr_r * pexpr :=
  ([::], pe).

(* Lowering of Oaddcarry
… = #addc(x, y, false) → ADD(x, y)
… = #addc(?, ?, true) → #error
… = #addc(?, ?, c) → ADC
*)

Definition lower_addcarry (sub: bool) (xs: lvals) (es: pexprs) : seq instr_r :=
  match xs, es with
  | [:: cf ; r ], [:: x ; y ; Pbool false ] =>
    let vi := match r with Lnone i => i | Lvar x | Lmem x _ | Laset x _ => v_info x end in
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
    (λ x tg e, [:: Cassgn x tg e])
    lower_copn
    (λ e _ _ c1 c2,
     let '(pre, e) := lower_pexpr e in
     rcons pre (Cif e c1 c2))
    (λ v d lo hi _ c, [:: Cfor v (d, lo, hi) c ])
    (λ _ e _ c c',
     let '(pre, e) := lower_pexpr e in
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
