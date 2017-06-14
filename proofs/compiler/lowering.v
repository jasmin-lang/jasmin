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
Require Import compiler_util expr.

Section LOWERING.

Record fresh_vars : Type :=
  {
    fresh_OF : Equality.sort Ident.ident;
    fresh_CF : Equality.sort Ident.ident;
    fresh_SF : Equality.sort Ident.ident;
    fresh_PF : Equality.sort Ident.ident;
    fresh_ZF : Equality.sort Ident.ident;

    fresh_multiplicand : Equality.sort Ident.ident;
  }.

Context (use_lea : bool).

Context (warning: instr_info -> warning_msg -> instr_info).

Definition vars_I (i: instr) := Sv.union (read_I i) (write_I i).

Definition vars_c c := Sv.union (read_c c) (write_c c).

Definition vars_lval l := Sv.union (read_rv l) (vrv l).

Definition vars_lvals ls := Sv.union (read_rvs ls) (vrvs ls).

Fixpoint vars_l (l: seq var_i) :=
  match l with
  | [::] => Sv.empty
  | h :: q => Sv.add h (vars_l q)
  end.

Definition vars_fd fd :=
  Sv.union (vars_l fd.(f_params)) (Sv.union (vars_l fd.(f_res)) (vars_c fd.(f_body))).

Definition vars_p (p: prog) :=
  foldr (fun f x => let '(fn, fd) := f in Sv.union x (vars_fd fd)) Sv.empty p.

Definition vbool vn := {| vtype := sbool ; vname := vn |}.
Definition vword vn := {| vtype := sword ; vname := vn |}.

Context (fv: fresh_vars).

Definition fv_of := vbool fv.(fresh_OF).
Definition fv_cf := vbool fv.(fresh_CF).
Definition fv_sf := vbool fv.(fresh_SF).
Definition fv_pf := vbool fv.(fresh_PF).
Definition fv_zf := vbool fv.(fresh_ZF).

Definition fvars := Sv.add (vword fv.(fresh_multiplicand)) (Sv.add fv_of (Sv.add fv_cf (Sv.add fv_sf (Sv.add fv_pf (Sv.singleton fv_zf))))).

Definition disj_fvars v := disjoint v fvars.

Definition fvars_correct p :=
  disj_fvars (vars_p p) &&
  (fv.(fresh_SF) != fv.(fresh_OF)) &&
  (fv.(fresh_CF) != fv.(fresh_ZF)) &&
  (fv.(fresh_SF) != fv.(fresh_ZF)) &&
  (fv.(fresh_OF) != fv.(fresh_ZF)) &&
  (fv.(fresh_OF) != fv.(fresh_SF)).

Definition var_info_of_lval (x: lval) : var_info :=
  match x with 
  | Lnone i t => i
  | Lvar x | Lmem x _ | Laset x _ => v_info x
  end.

Definition stype_of_lval (x: lval) : stype :=
  match x with
  | Lnone _ t => t
  | Lvar v | Lmem v _ | Laset v _ => v.(vtype)
  end.

Variant lower_cond1 :=
  | CondVar
  | CondNotVar.

Variant lower_cond2 :=
  | CondEq
  | CondNeq
  | CondOr
  | CondAndNot.

Variant lower_cond3 :=
  | CondOrNeq
  | CondAndNotEq.

Variant lower_cond_t : Type :=
  | Cond1 of lower_cond1 & var_i
  | Cond2 of lower_cond2 & var_i & var_i
  | Cond3 of lower_cond3 & var_i & var_i & var_i.

Definition lower_cond_classify vi (e: pexpr) :=
  let nil := Lnone vi sbool in
  let fr n := {| v_var := {| vtype := sbool; vname := n fv |} ; v_info := vi |} in
  let vof := fr fresh_OF in
  let vcf := fr fresh_CF in
  let vsf := fr fresh_SF in
  let vpf := fr fresh_PF in
  let vzf := fr fresh_ZF in
  let lof := Lvar vof in
  let lcf := Lvar vcf in
  let lsf := Lvar vsf in
  let lpf := Lvar vpf in
  let lzf := Lvar vzf in
  match e with
  | Papp2 op x y =>
    match op with
    | Oeq (Cmp_sw | Cmp_uw) =>
      Some ([:: nil ; nil ; nil ; nil ; lzf ], Cond1 CondVar vzf, x, y)
    | Oneq (Cmp_sw | Cmp_uw) =>
      Some ([:: nil ; nil ; nil ; nil ; lzf ], Cond1 CondNotVar vzf, x, y)
    | Olt Cmp_sw =>
      Some ([:: lof ; nil ; lsf ; nil ; nil ], Cond2 CondNeq vsf vof, x, y)
    | Olt Cmp_uw =>
      Some ([:: nil ; lcf ; nil ; nil ; nil ], Cond1 CondVar vcf, x, y)
    | Ole Cmp_sw =>
      Some ([:: lof ; nil ; lsf ; nil ; lzf ], Cond3 CondOrNeq vzf vsf vof, x, y)
    | Ole Cmp_uw =>
      Some ([:: nil ; lcf ; nil ; nil ; lzf ], Cond2 CondOr vcf vzf, x, y)
    | Ogt Cmp_sw =>
      Some ([:: lof ; nil ; lsf ; nil ; lzf ], Cond3 CondAndNotEq vzf vsf vof, x, y)
    | Ogt Cmp_uw =>
      Some ([:: nil ; lcf ; nil ; nil ; lzf ], Cond2 CondAndNot vcf vzf, x, y)
    | Oge Cmp_sw =>
      Some ([:: lof ; nil ; lsf ; nil ; nil ], Cond2 CondEq vsf vof, x, y)
    | Oge Cmp_uw =>
      Some ([:: nil ; lcf ; nil ; nil ; nil ], Cond1 CondNotVar vcf, x, y)
    | _ => None
    end
  | _ => None
  end.

Definition eq_f  v1 v2 := Pif (Pvar v1) (Pvar v2) (Papp1 Onot (Pvar v2)).
Definition neq_f v1 v2 := Pif (Pvar v1) (Papp1 Onot (Pvar v2)) (Pvar v2).

Definition lower_condition vi (pe: pexpr) : seq instr_r * pexpr :=
  match lower_cond_classify vi pe with
  | Some (l, r, x, y) =>
    ([:: Copn l Ox86_CMP [:: x; y] ],
    match r with
    | Cond1 CondVar v => Pvar v
    | Cond1 CondNotVar v => Papp1 Onot (Pvar v)
    | Cond2 CondEq v1 v2 => eq_f v1 v2
    | Cond2 CondNeq v1 v2 => neq_f v1 v2
    | Cond2 CondOr v1 v2 => Papp2 Oor v1 v2
    | Cond2 CondAndNot v1 v2 => Papp2 Oand (Papp1 Onot (Pvar v1)) (Papp1 Onot (Pvar v2))
    | Cond3 CondOrNeq v1 v2 v3 => Papp2 Oor v1 (neq_f v2 v3)
    | Cond3 CondAndNotEq v1 v2 v3 => Papp2 Oand (Papp1 Onot v1) (eq_f v2 v3)
    end)
  | None => ([::], pe)
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

(* -------------------------------------------------------------------- *)

(* disp + base + scale * offset *)
Record lea := MkLea { 
  lea_disp   : word;               
  lea_base   : option var_i;
  lea_scale  : word;
  lea_offset : option var_i;
}.

(* -------------------------------------------------------------------- *)

Variant lower_cassgn_t : Type :=
  | LowerMov  of bool (* whether it needs a intermediate register *)
  | LowerCopn of sopn & pexpr
  | LowerInc  of sopn & pexpr
  | LowerLea  of lea
  | LowerFopn of sopn & list pexpr & Z
  | LowerEq   of pexpr & pexpr
  | LowerLt   of pexpr & pexpr
  | LowerIf   of pexpr & pexpr & pexpr
  | LowerAssgn.

Context (is_var_in_memory : var_i → bool).

Definition is_lval_in_memory (x: lval) : bool :=
  match x with
  | Lnone _ _ => false
  | Lvar v
  | Laset v _
    => is_var_in_memory v
  | Lmem _ _ => true
  end.

(* -------------------------------------------------------------------- *)

Definition lea_const z := MkLea z   None     I64.one None.

Definition lea_var   x := MkLea I64.zero (Some x) I64.one None.

Definition mkLea d b sc o := 
  if sc == I64.zero then MkLea d b I64.one None
  else MkLea d b sc o.
  
Definition lea_mul l1 l2 := 
  match l1, l2 with 
  | MkLea d1 b1 sc1 o1, MkLea d2 b2 sc2 o2 =>
    let d := I64.mul d1 d2 in
    match b1, o1, b2, o2 with
    | None  , None  , None  , None   => Some (lea_const d)
    | Some _, None  , None  , None   => Some (mkLea d None d2 b1)
    | None  , None  , Some _, None   => Some (mkLea d None d1 b2)
    | None  , Some _, None  , None   => Some (mkLea d None (I64.mul d2 sc1) o1)
    | None  , None  , None  , Some _ => Some (mkLea d None (I64.mul d1 sc2) o2)
    | _     , _     , _     , _      => None
    end
  end.
 
Definition lea_add l1 l2 := 
  match l1, l2 with 
  | MkLea d1 b1 sc1 o1, MkLea d2 b2 sc2 o2 =>
    let disp := I64.add d1 d2 in
    match b1, o1    , b2    , o2    with
    | None  , None  , _     , _      => Some (mkLea disp b2 sc2 o2)
    | _     , _     , None  , None   => Some (mkLea disp b1 sc1 o1)
    | Some _, None  , _     , None   => Some (mkLea disp b1 I64.one b2) 
    | Some _, None  , None  , Some _ => Some (mkLea disp b1 sc2 o2)
    | None  , Some _, Some _, None   => Some (mkLea disp b2 sc1 o1)
    | None  , Some _, None  , Some _ =>
      if sc1 == I64.one then Some (mkLea disp o1 sc2 o2)
      else if sc2 == I64.one then Some (mkLea disp o2 sc1 o1)
      else None
    | _     , _     , _     , _      => None
    end
  end.

Fixpoint mk_lea e := 
  match e with
  | Pcast (Pconst z) => Some (lea_const (I64.repr z))
  | Pvar  x          => Some (lea_var x)
  | Papp2 (Omul Op_w) e1 e2 =>
    match mk_lea e1, mk_lea e2 with
    | Some l1, Some l2 => lea_mul l1 l2
    | _      , _       => None
    end
  | Papp2 (Oadd Op_w) e1 e2 =>
    match mk_lea e1, mk_lea e2 with
    | Some l1, Some l2 => lea_add l1 l2
    | _      , _       => None
    end
  | _ => None
  end.

Definition is_lea x e := 
  if ~~ is_lval_in_memory x then
    match mk_lea e with 
    | Some (MkLea d b sc o) => 
      let check o := match o with Some x => ~~(is_var_in_memory x) | None => true end in
      (* FIXME: check that d is not to big *)
      if check_scale sc && check b && check o then  Some (MkLea d b sc o)
      else None
    | None => None
    end
  else None.

(* -------------------------------------------------------------------- *)

Definition lower_cassgn_classify e x : lower_cassgn_t :=
  match e with
  | Pcast (Pconst _) => LowerMov false
  | Pget v _
  | Pvar ({| v_var := {| vtype := sword |} |} as v) => LowerMov (if is_var_in_memory v then is_lval_in_memory x else false)
  | Pload _ _ => LowerMov (is_lval_in_memory x)

  | Papp1 Olnot a => LowerCopn Ox86_NOT a
  | Papp1 Oneg a => LowerFopn Ox86_NEG [:: a] 0

  | Papp2 op a b =>
    match op with
    | Oadd Op_w =>
      match is_lea x e with
      | Some l => LowerLea l
      | None   => 
        match add_inc_dec_classify a b with
        | AddInc y => LowerInc Ox86_INC y
        | AddDec y => LowerInc Ox86_DEC y
        | AddNone  => LowerFopn Ox86_ADD [:: a ; b ] I32.modulus 
        end
      end
    | Osub Op_w =>
      match sub_inc_dec_classify b with
      | SubInc => LowerInc Ox86_INC a
      | SubDec => LowerInc Ox86_DEC a
      | SubNone => LowerFopn Ox86_SUB [:: a ; b ] I32.modulus
      end
    | Omul Op_w => 
      match is_lea x e with 
      | Some l => LowerLea l
      | _      => 
        match is_wconst a with
        | Some _ => LowerFopn Ox86_IMUL64 [:: b ; a ] I32.modulus
        | _      => LowerFopn Ox86_IMUL64 [:: a ; b ] I32.modulus 
        end 
      end
    | Oland => LowerFopn Ox86_AND [:: a ; b ] I32.modulus
    | Olor => LowerFopn Ox86_OR [:: a ; b ] I32.modulus
    | Olxor => LowerFopn Ox86_XOR [:: a ; b ] I32.modulus
    | Olsr => LowerFopn Ox86_SHR [:: a ; b ] I8.modulus
    | Olsl => LowerFopn Ox86_SHL [:: a ; b ] I8.modulus
    | Oasr => LowerFopn Ox86_SAR [:: a ; b ] I8.modulus
    | Oeq (Cmp_sw | Cmp_uw) => LowerEq a b
    | Olt Cmp_uw => LowerLt a b
    | _ => LowerAssgn
    end

  | Pif e e1 e2 => 
    if (stype_of_lval x == sword) then
      LowerIf e e1 e2
    else
      LowerAssgn
  | _ => LowerAssgn
  end.

Definition Lnone_b vi := Lnone vi sbool.

Variant opn_5flags_cases_t (a: pexprs) (m: Z) : Type :=
| Opn5f_large_immed x y n z `(a = x :: y :: z) `(y = wconst n)
| Opn5f_other.

Arguments Opn5f_large_immed [a m] {x y n z} _ _.
Arguments Opn5f_other [a m].

Lemma is_reflect_some {A P e a} (H: @is_reflect A P e (Some a)) : e = P a.
Proof.
  set (d e m := match m with None => True | Some a => e = P a end).
  change (d e (Some a)).
  case H; simpl; auto.
Qed.

Definition opn_5flags_cases (a: pexprs) (m: Z) : opn_5flags_cases_t a m :=
  match a with
  | x :: y :: z =>
    match is_wconst y as u return is_reflect wconst y u → _ with
    | None => λ _, Opn5f_other
    | Some n =>
      λ W,
      if let h := m / 2 in if -h <=? n then n <? h else false
      then Opn5f_other
      else Opn5f_large_immed erefl (is_reflect_some W)
    end%Z (is_wconstP y)
  | _ => Opn5f_other end.

Definition opn_5flags (immed_bound: Z) (vi: var_info)
           (cf: lval) (x: lval) (o: sopn) (a: pexprs) : seq instr_r :=
  let f := Lnone_b vi in
  let fopn o a := [:: Copn [:: f ; cf ; f ; f ; f ; x ] o a ] in
  match opn_5flags_cases a immed_bound with
  | Opn5f_large_immed x y n z _ _ =>
    let c := {| v_var := {| vtype := sword; vname := fresh_multiplicand fv |} ; v_info := vi |} in
    Copn [:: Lvar c ] Ox86_MOV [:: y] :: fopn o (x :: Pvar c :: z)
  | Opn5f_other => fopn o a
  end.

Definition lower_cassgn (ii:instr_info) (x: lval) (tg: assgn_tag) (e: pexpr) : cmd :=
  let vi := var_info_of_lval x in
  let f := Lnone_b vi in
  let copn o a := [:: MkI ii (Copn [:: x ] o [:: a]) ] in
  let inc o a := [:: MkI ii (Copn [:: f ; f ; f ; f ; x ] o [:: a ]) ] in
  match lower_cassgn_classify e x with
  | LowerMov b =>
    if b
    then
      let c := {| v_var := {| vtype := sword; vname := fresh_multiplicand fv |} ; v_info := vi |} in
      [:: MkI ii (Copn [:: Lvar c] Ox86_MOV [:: e ]) ; MkI ii (Copn [:: x ] Ox86_MOV [:: Pvar c ]) ]
    else 
      (* IF e is 0 then use Oset0 instruction *)
      if (e == Pcast (Pconst 0)) && ~~ is_lval_in_memory x then
        [:: MkI ii (Copn [:: f ; f ; f ; f ; f ; x] Oset0 [::]) ]
      else copn Ox86_MOV e
  | LowerCopn o e => copn o e
  | LowerInc o e => inc o e
  | LowerFopn o es m => map (MkI ii) (opn_5flags m vi f x o es)
  | LowerLea (MkLea d b sc o) => 
    let de := wconst (I64.unsigned d) in
    let sce := wconst (I64.unsigned sc) in
    let b := oapp Pvar (wconst 0) b in
    let o := oapp Pvar (wconst 0) o in
    let lea tt := 
      let ii := warning ii Use_lea in
      [:: MkI ii (Copn [::x] Ox86_LEA [:: de; b; sce; o]) ] in
    if use_lea then lea tt
    (* d + b + sc * o *)
    else 
      if d == I64.zero then 
        (* b + sc * o *)
        if sc == I64.one then
          (* b + o *)
          [::MkI ii (Copn [:: f ; f ; f ; f ; f; x ] Ox86_ADD [:: b ; o])]
        else if b == wconst 0 then
          (* sc * o *)
          [::MkI ii (Copn [:: f ; f ; f ; f ; f; x ] Ox86_IMUL64 [:: o; sce])]
        else lea tt
      else if o == wconst 0 then
          (* d + b *)
          if d == I64.one then inc Ox86_INC b
          else [::MkI ii (Copn [:: f ; f ; f ; f ; f; x ] Ox86_ADD [:: b ; de])]
      else lea tt
      
  | LowerEq a b => [:: MkI ii (Copn [:: f ; f ; f ; f ; x ] Ox86_CMP [:: a ; b ]) ]
  | LowerLt a b => [:: MkI ii (Copn [:: f ; x ; f ; f ; f ] Ox86_CMP [:: a ; b ]) ]
  | LowerIf e e1 e2 =>
     let (l, e) := lower_condition vi e in
     map (MkI ii) (l ++ [:: Copn [:: x] Ox86_CMOVcc [:: e; e1; e2]])
  | LowerAssgn => [::  MkI ii (Cassgn x tg e)]    
  end.

(* Lowering of Oaddcarry
… = #addc(x, y, false) → ADD(x, y)
… = #addc(?, ?, true) → #error
… = #addc(?, ?, c) → ADC
*)

Definition lower_addcarry_classify (sub: bool) (xs: lvals) (es: pexprs) :=
  match xs, es with
  | [:: cf ; r ], [:: x ; y ; Pbool false ] =>
    let vi := var_info_of_lval r in
    Some (vi, if sub then Ox86_SUB else Ox86_ADD, [:: x ; y ], cf, r)
  | [:: cf ; r ], [:: _ ; _ ; Pvar cfi ] =>
    let vi := v_info cfi in
    Some (vi, (if sub then Ox86_SBB else Ox86_ADC), es, cf, r)
  | _, _ => None
  end.

Definition lower_addcarry (sub: bool) (xs: lvals) (es: pexprs) : seq instr_r :=
  match lower_addcarry_classify sub xs es with
  | Some (vi, o, es, cf, r) => opn_5flags I32.modulus vi cf r o es
  | None => [:: Copn xs (if sub then Osubcarry else Oaddcarry) es ]
  end.

Definition lower_mulu (xs: lvals) (es: pexprs) : seq instr_r :=
  match xs, es with
  | [:: r1; r2 ], [:: x ; y ] =>
    let vi := var_info_of_lval r2 in
    let f := Lnone_b vi in
    match is_wconst x with
    | Some _ =>
      let c := {| v_var := {| vtype := sword; vname := fresh_multiplicand fv |} ; v_info := vi |} in
      [:: Copn [:: Lvar c ] Ox86_MOV [:: x ] ; Copn [:: f ; f ; f ; f ; f ; r1 ; r2 ] Ox86_MUL [:: y ; Pvar c ] ]
    | None =>
    match is_wconst y with
    | Some _ =>
      let c := {| v_var := {| vtype := sword; vname := fresh_multiplicand fv |} ; v_info := vi |} in
      [:: Copn [:: Lvar c ] Ox86_MOV [:: y ] ; Copn [:: f ; f ; f ; f ; f ; r1 ; r2 ] Ox86_MUL [:: x ; Pvar c ] ]
    | None => [:: Copn [:: f ; f ; f ; f ; f ; r1 ; r2 ] Ox86_MUL es ]
    end end
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
  match ir with
  | Cassgn l t e => lower_cassgn ii l t e
  | Copn   l o e =>   map (MkI ii) (lower_copn l o e)
  | Cif e c1 c2  =>
     let '(pre, e) := lower_condition xH e in
       map (MkI ii) (rcons pre (Cif e (lower_cmd lower_i c1) (lower_cmd lower_i c2)))
  | Cfor v (d, lo, hi) c =>
     [:: MkI ii (Cfor v (d, lo, hi) (lower_cmd lower_i c))]
  | Cwhile c e c' =>
     let '(pre, e) := lower_condition xH e in
       map (MkI ii) [:: Cwhile ((lower_cmd lower_i c) ++ map (MkI xH) pre) e (lower_cmd lower_i c')]
  | _ =>   map (MkI ii) [:: ir]
  end.

Definition lower_fd (fd: fundef) : fundef :=
  {| f_iinfo := f_iinfo fd;
     f_params := f_params fd;
     f_body := lower_cmd lower_i (f_body fd);
     f_res := f_res fd
  |}.

Definition lower_prog (p: prog) := map_prog lower_fd p.

End LOWERING.
