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

(* * New semantic which is "unsafe" (may not fail on invalid code) but simplifies the Hoare logic *)

(* ** Imports and settings *)
Require Import strings word utils type var expr sem.
Require Import low_memory psem.
Import all_ssreflect all_algebra zmodp.
Import ZArith.

Require Import Utf8.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope string_scope.

(* ** Type interpretation
 * -------------------------------------------------------------------- *)

Variant sstype : Type := ssbool | ssint | ssarr of wsize | ssword of wsize.

Coercion sstype_of_stype (ty: stype) : sstype :=
  match ty with
  | sbool    => ssbool
  | sint     => ssint
  | sarr s _ => ssarr s
  | sword s  => ssword s
  end.

Definition ssem_t (t : sstype) : Type :=
  match t with
  | ssbool   => bool
  | ssint    => Z
  | ssarr s  => FArray.array (word s)
  | ssword s => word s
  end.

Definition sdflt_val st : ssem_t st :=
  match st with
  | ssbool   => false
  | ssint    => Z0
  | ssarr s  => FArray.cnst 0%R
  | ssword s => 0%R
  end.

(* ** Values
  * -------------------------------------------------------------------- *)

Variant svalue : Type :=
  | SVbool   :> bool                   -> svalue
  | SVint    :> Z                      -> svalue
  | SVarr  s : FArray.array (word s)   -> svalue
  | SVword s : (word s)                -> svalue.

Definition svalues := seq svalue.

Definition sto_bool v :=
  match v with
  | SVbool b => ok b
  | _        => type_error
  end.

Definition sto_int v :=
  match v with
  | SVint z => ok z
  | _       => type_error
  end.

Definition sto_arr sz (v: svalue) : exec (FArray.array (word sz)) :=
  if v is SVarr s t then
    if wsize_eq_dec s sz is left eqsz then ok (eq_rect s (λ s, FArray.array (word s)) t sz eqsz)
    else type_error
  else type_error.

Definition sto_word sz v :=
  match v with
  | SVword sz' w => truncate_word sz w
  | _            => type_error
  end.

Definition sto_pointer : svalue → exec pointer :=
  sto_word _.

Definition sval_sstype (v: svalue) : sstype :=
  match v with
  | SVbool _    => ssbool
  | SVint  _    => ssint
  | SVarr sz  _ => ssarr sz
  | SVword sz _ => ssword sz
  end.

Definition of_sval t : svalue -> exec (ssem_t t) :=
  match t return svalue -> exec (ssem_t t) with
  | ssbool      => sto_bool
  | ssint       => sto_int
  | ssarr sz    => sto_arr sz
  | ssword sz   => sto_word sz
  end.

Definition to_sval t : ssem_t t -> svalue :=
  match t return ssem_t t -> svalue with
  | ssbool      => SVbool
  | ssint       => SVint
  | ssarr sz    => @SVarr sz
  | ssword sz   => @SVword sz
  end.

Lemma of_sval_ex ty (s: svalue) :
  ty = sval_sstype s →
  ∃ v,
  of_sval ty s = ok v ∧ to_sval v = s.
Proof.
move=>->; case: s => /=; eauto.
- by move => sz t; exists t; rewrite eq_dec_refl.
by move => sz w; exists w; split; [rewrite truncate_word_u |].
Qed.

(* ** Traduction of Arrays into Farrays & Truncation of Farrays
 * -------------------------------------------------------------------- *)

Definition word_array_to_farray {n} {s} (a : Array.array n (word s)) : FArray.array (word s):=
  fun i => match Array.get a i with
           |Ok z => z
           |_    => sdflt_val (ssword s)
           end.


Definition truncate_farray {s} s' (a : FArray.array (word s)) : FArray.array (word s'):=
  fun i => match truncate_word s' (a i) with
           |Ok z => z
           |_    => sdflt_val (ssword s')
           end.


(* ** Variable map
 * -------------------------------------------------------------------- *)
Delimit Scope svmap_scope with svmap.

Notation svmap    := (Fv.t ssem_t).
Notation svmap0   := (@Fv.empty ssem_t (fun x => sdflt_val x.(vtype))).

Definition sget_var (m:svmap) x :=
  @to_sval (vtype x) (m.[x]%vmap).

Definition sset_var (m: svmap) x v :=
  on_vu (λ v, m.[x <- v]%vmap)
        (if x.(vtype) is sword _ then type_error
         else ok m)
        (of_sval (vtype x) v).

(* ** Parameter expressions
 * -------------------------------------------------------------------- *)

Definition ssem_prod ts tr := lprod (map ssem_t ts) tr.

Definition mk_ssem_sop1 t1 tr (o:ssem_t t1 -> ssem_t tr) v1 :=
  Let v1 := of_sval t1 v1 in
  ok (@to_sval tr (o v1)).

Definition mk_ssem_sop2 t1 t2 tr (o:ssem_t t1 -> ssem_t t2 -> ssem_t tr) v1 v2 :=
  Let v1 := of_sval t1 v1 in
  Let v2 := of_sval t2 v2 in
  ok (@to_sval tr (o v1 v2)).

Definition ssem_op1_b    := @mk_ssem_sop1 sbool sbool.
Definition ssem_op1_i    := @mk_ssem_sop1 sint sint.
Definition ssem_op1_w sz := @mk_ssem_sop1 (sword sz) (sword sz).

Definition ssem_zeroext (sz: wsize) (v: svalue) : exec svalue :=
  match v with
  | SVword sz' w' => ok (SVword (@zero_extend sz sz' w'))
  | _             => type_error
  end.

Definition ssem_arr_init sz (v:svalue) :=
  Let n := sto_int v in 
  ok (@SVarr sz (FArray.cnst 0%R)).

Definition ssem_sop1 (o:sop1) := 
  match o with
  | Osignext sz sz' => @mk_ssem_sop1 (ssword sz') (ssword sz) (@sign_extend sz sz')
  | Ozeroext sz sz' => @mk_ssem_sop1 (ssword sz') (ssword sz) (@zero_extend sz sz')
  | Onot           => ssem_op1_b negb
  | Olnot sz       => @ssem_op1_w sz wnot
  | Oneg Op_int    => ssem_op1_i Z.opp
  | Oneg (Op_w sz) => @ssem_op1_w sz -%R
  | Oarr_init sz   => ssem_arr_init sz
  end%R.

Definition ssem_op2_b     := @mk_ssem_sop2 sbool sbool sbool.
Definition ssem_op2_i     := @mk_ssem_sop2 sint  sint  sint.
Definition ssem_op2_w sz  := @mk_ssem_sop2 (sword sz) (sword sz) (sword sz).
Definition ssem_op2_w8 sz := @mk_ssem_sop2 (sword sz) sword8 (sword sz).
Definition ssem_op2_ib    := @mk_ssem_sop2 sint  sint  sbool.
Definition ssem_op2_wb sz := @mk_ssem_sop2 (sword sz) (sword sz) sbool.

Definition ssem_sop2 (o:sop2) :=
  match o with
  | Oand           => ssem_op2_b andb     
  | Oor            => ssem_op2_b orb

  | Oadd Op_int    => ssem_op2_i Z.add
  | Oadd (Op_w sz) => @ssem_op2_w sz +%R
  | Osub Op_int    => ssem_op2_i Z.sub
  | Osub (Op_w sz) => ssem_op2_w (λ x y : word sz, x - y)%R
  | Omul Op_int    => ssem_op2_i Z.mul
  | Omul (Op_w sz) => @ssem_op2_w sz *%R

  | Oland sz       => @ssem_op2_w sz wand
  | Olor sz        => @ssem_op2_w sz wor
  | Olxor sz       => @ssem_op2_w sz wxor
  | Olsr sz        => @ssem_op2_w8 sz sem_shr
  | Olsl sz        => @ssem_op2_w8 sz sem_shl
  | Oasr sz        => @ssem_op2_w8 sz sem_sar

  | Oeq Op_int     => ssem_op2_ib Z.eqb
  | Oeq (Op_w sz)  => @ssem_op2_wb sz eq_op
  | Oneq Op_int    => ssem_op2_ib (fun x y => negb (Z.eqb x y))
  | Oneq (Op_w sz) => ssem_op2_wb (λ x y : word sz, x != y)
  | Olt Cmp_int    => ssem_op2_ib Z.ltb
  | Ole Cmp_int    => ssem_op2_ib Z.leb
  | Ogt Cmp_int    => ssem_op2_ib Z.gtb
  | Oge Cmp_int    => ssem_op2_ib Z.geb
  | Olt (Cmp_w sg sz)   => @ssem_op2_wb sz (wlt sg)
  | Ole (Cmp_w sg sz)   => @ssem_op2_wb sz (wle sg)
  | Ogt (Cmp_w sg sz)   => ssem_op2_wb (λ x y : word sz, wlt sg y x)
  | Oge (Cmp_w sg sz)   => ssem_op2_wb (λ x y : word sz, wle sg y x)
  end.

Import UnsafeMemory.

Record sestate := SEstate {
  semem : mem;
  sevm  : svmap
}.

Definition son_arr_var A (s: sestate) (x: var) (f: forall sz n, FArray.array (word sz) → exec A) :=
  match vtype x as t return ssem_t t → exec A with
  | sarr sz n => f sz n
  | _ => λ _, type_error
  end  (s.(sevm).[ x ]%vmap).

Notation "'SLet' ( sz , n , t ) ':=' s '.[' x ']' 'in' body" :=
  (@son_arr_var _ s x (fun sz n (t:FArray.array (word sz)) => body)) (at level 25, s at level 0).

Definition sget_global gd g : svalue :=
  if get_global_value gd g is Some (Vword sz w)
  then SVword w
  else SVword (sdflt_val (sword (size_of_global g))).

Section SSEM_PEXPR.

Context (gd: glob_defs).

Fixpoint ssem_pexpr (s:sestate) (e : pexpr) : exec svalue :=
  match e with
  | Pconst z    => ok (SVint z)
  | Pbool b     => ok (SVbool b)
  | Pcast sz e  =>
    Let z := ssem_pexpr s e >>= sto_int in
    ok (SVword (wrepr sz z))
  | Pvar v    => ok (sget_var s.(sevm) v)
  | Pglobal g => ok (sget_global gd g)
  | Pget x e  =>
    SLet (sz, n, t) := s.[x] in
    Let i := ssem_pexpr s e >>= sto_int in
    let w := FArray.get t i in
    ok (SVword w)
  | Pload sz x e => 
    Let w1 := ok (sget_var s.(sevm) x) >>= sto_pointer in
    Let w2 := ssem_pexpr s e >>= sto_pointer in
    let w := read_mem s.(semem) (w1 + w2) sz in
    ok (@to_sval (sword sz) w)
  | Papp1 o e =>
    Let v := ssem_pexpr s e in
    ssem_sop1 o v
  | Papp2 o e1 e2 =>
    Let v1 := ssem_pexpr s e1 in
    Let v2 := ssem_pexpr s e2 in
    ssem_sop2 o v1 v2
  | Pif e e1 e2 =>
    Let b  := ssem_pexpr s e >>= sto_bool in
    Let v1 := ssem_pexpr s e1 in
    Let v2 := ssem_pexpr s e2 in
    Let _ := of_sval (sval_sstype v1) v1 in
    Let _ := of_sval (sval_sstype v1) v2 in
    ok (if b then v1 else v2)
  end.

Definition ssem_pexprs s := mapM (ssem_pexpr s).

Definition swrite_var (x:var_i) (v:svalue) (s:sestate) : exec sestate :=
  Let vm := sset_var s.(sevm) x v in
  ok {| semem := s.(semem); sevm := vm |}.

Definition swrite_vars xs vs s :=
  fold2 ErrType swrite_var xs vs s.

Definition swrite_lval (l:lval) (v:svalue) (s:sestate) : exec sestate :=
  match l with
  | Lnone _ _   => ok s
  | Lvar x      => swrite_var x v s
  | Lmem sz x e =>
    Let vx := sto_pointer (sget_var (sevm s) x) in
    Let ve := ssem_pexpr s e >>= sto_pointer in
    let p := (vx + ve)%R in  (* should we add the size of value, i.e vx + sz * se *)
    Let w := sto_word sz v in
    let m := write_mem s.(semem) p w in
    ok {|semem := m;  sevm := s.(sevm) |}
  | Laset x i   =>
    SLet (sz, n,t) := s.[x] in
    Let i := ssem_pexpr s i >>= sto_int in
    Let v := sto_word sz v in
    let t := FArray.set t i v in
    Let vm := sset_var s.(sevm) x (@to_sval (sarr sz n) t) in
    ok {| semem := s.(semem); sevm := vm |}
  end.

Definition swrite_lvals (s:sestate) xs vs :=
   fold2 ErrType swrite_lval xs vs s.

End SSEM_PEXPR.

Fixpoint sapp_sopn ts : ssem_prod ts (exec svalues) -> svalues -> exec svalues :=
  match ts return ssem_prod ts (exec svalues) -> svalues -> exec svalues with
  | [::]    => fun (o:exec svalues) (vs:svalues) =>
    match vs with
    | [::]  => o
    | _     => type_error
    end
  | t::ts   => fun (o:ssem_t t -> ssem_prod ts (exec svalues)) (vs:svalues) =>
    match vs with
    | [::]  => type_error
    | v::vs =>
      Let v := of_sval t v in
      sapp_sopn (o v) vs
    end
  end.
Arguments sapp_sopn ts o l:clear implicits.

Notation sapp_b      o := (sapp_sopn [:: ssbool] o).
Notation sapp_w   sz o := (sapp_sopn [:: ssword sz] o).
Notation sapp_w8  sz o := (sapp_sopn [:: ssword sz; ssword U8] o).
Notation sapp_ww  sz o := (sapp_sopn [:: ssword sz; ssword sz] o).
Notation sapp_wwb sz o := (sapp_sopn [:: ssword sz; ssword sz; ssbool] o).
Notation sapp_bww sz o := (sapp_sopn [:: ssbool; ssword sz; ssword sz] o).
Notation sapp_www sz o := (sapp_sopn [:: ssword sz; ssword sz; ssword sz ] o).
Notation sapp_ww8 sz o := (sapp_sopn [:: ssword sz; ssword sz; ssword U8] o).
Notation sapp_w4  sz o := (sapp_sopn [:: ssword sz; ssword sz; ssword sz ; ssword sz] o).

Definition svalue_of_value (v: value) : svalue :=
  match v with
  | Vbool b => SVbool b
  | Vint z => SVint z
  | Varr sz n t => SVarr (λ x, match Array.get t x with Error _ => 0%R | Ok e => e end)
  | Vword sz w => SVword w
  | Vundef ty =>
    match ty with
    | sbool => SVbool (sdflt_val sbool)
    | sint => SVint (sdflt_val sint)
    | sarr sz _ => SVarr (λ _, sdflt_val (sword sz))
    | sword sz => SVword (sdflt_val (sword sz))
    end
  end.

Definition svalues_of_values (vs: values) : svalues := map svalue_of_value vs.

Notation w1 o := (λ x, Result.map svalues_of_values (o x)).
Notation w2 o := (λ x y, Result.map svalues_of_values (o x y)).
Notation w3 o := (λ x y z, Result.map svalues_of_values (o x y z)).
Notation w4 o := (λ x y z w, Result.map svalues_of_values (o x y z w)).

Definition spval t1 t2 (p: ssem_t t1 * ssem_t t2) :=
  [::to_sval p.1; to_sval p.2].

Definition ssem_sopn (o:sopn) :  svalues -> exec svalues :=
  match o with
  | Omulu sz       => sapp_ww  sz (fun x y   => ok (@spval (ssword sz)  (ssword sz) (wumul x y)))
  | Oaddcarry sz   => sapp_wwb sz (fun x y c => ok (@spval ssbool (ssword sz) (waddcarry x y c)))
  | Osubcarry sz   => sapp_wwb sz (fun x y c => ok (@spval ssbool (ssword sz) (wsubcarry x y c)))
  | Oset0 sz       =>
    λ _,
    (let vf := SVbool false in
     ok [:: vf; vf; vf; vf; SVbool true; @SVword sz 0%R])

  (* Low level x86 operations *)
  | Ox86_MOV sz    => sapp_w sz (w1 (@x86_MOV sz)) (*sapp_w sz (w1 x86_MOV)*)
  | Ox86_MOVSX sz sz' => sapp_w sz' (w1 (@x86_MOVSX sz sz'))
  | Ox86_MOVZX sz sz' => sapp_w sz' (w1 (@x86_MOVZX sz sz'))
  | Ox86_CMOVcc sz => (fun v => match v with
    | [:: v1; v2; v3] =>
      Let b := sto_bool v1 in
      if b then
        Let w2 := sto_word sz v2 in ok [:: SVword w2]
      else
        Let w3 := sto_word sz v3 in ok [:: SVword w3]
    | _ => type_error end)
  | Ox86_ADD sz      => sapp_ww sz  (w2 x86_add)
  | Ox86_SUB sz      => sapp_ww sz  (w2 x86_sub)
  | Ox86_MUL sz      => sapp_ww sz  (w2 x86_mul)
  | Ox86_IMUL sz     => sapp_ww sz  (w2 x86_imul)
  | Ox86_IMULt sz    => sapp_ww sz  (w2 x86_imult)
  | Ox86_IMULtimm sz => sapp_ww sz  (w2 x86_imult)
  | Ox86_DIV sz      => sapp_www sz (w3 x86_div)
  | Ox86_IDIV sz     => sapp_www sz (w3 x86_idiv)
  | Ox86_ADC sz      => sapp_wwb sz (w3 x86_adc)
  | Ox86_SBB sz      => sapp_wwb sz (w3 x86_sbb)
  | Ox86_NEG sz      => sapp_w sz   (w1 x86_neg)
  | Ox86_INC sz      => sapp_w sz   (w1 x86_inc)
  | Ox86_DEC sz      => sapp_w sz   (w1 x86_dec)
  | Ox86_SETcc       => sapp_b      (w1 x86_setcc)
  | Ox86_BT sz       => sapp_ww sz  (w2 x86_bt)
  | Ox86_LEA sz      => sapp_w4 sz  (w4 x86_lea)
  | Ox86_TEST sz     => sapp_ww sz  (w2 x86_test)
  | Ox86_CMP sz      => sapp_ww sz  (w2 x86_cmp)
  | Ox86_AND sz      => sapp_ww sz  (w2 x86_and)
  | Ox86_OR  sz      => sapp_ww sz  (w2 x86_or)
  | Ox86_XOR sz      => sapp_ww sz  (w2 x86_xor)
  | Ox86_NOT sz      => sapp_w sz   (w1 x86_not)
  | Ox86_ROL sz      => sapp_w8 sz  (w2 x86_rol)
  | Ox86_ROR sz      => sapp_w8 sz  (w2 x86_ror)
  | Ox86_SHL sz      => sapp_w8 sz  (w2 x86_shl)
  | Ox86_SHR sz      => sapp_w8 sz  (w2 x86_shr)
  | Ox86_SAR sz      => sapp_w8 sz  (w2 x86_sar)
  | Ox86_SHLD sz     => sapp_ww8 sz (w3 x86_shld)
  | Ox86_BSWAP sz => sapp_w sz (w1 x86_bswap)
  | Ox86_MOVD sz => sapp_w sz (w1 x86_movd)
  | Ox86_VMOVDQU sz => sapp_sopn [:: ssword sz ] (λ x, ok [:: SVword x])
  | Ox86_VPAND sz => sapp_ww sz (w2 x86_vpand)
  | Ox86_VPOR sz => sapp_ww sz (w2 x86_vpor)
  | Ox86_VPXOR sz => sapp_ww sz (w2 x86_vpxor)
  | Ox86_VPADD ve sz => sapp_ww sz (w2 (x86_vpadd ve))
  | Ox86_VPSLL ve sz => sapp_w8 sz (w2 (x86_vpsll ve))
  | Ox86_VPSRL ve sz => sapp_w8 sz (w2 (x86_vpsrl ve))
  | Ox86_VPSHUFB sz => sapp_ww sz (w2 x86_vpshufb)
  | Ox86_VPSHUFD sz => sapp_w8 sz (w2 x86_vpshufd)
  | Ox86_VPBLENDD sz => sapp_ww8 sz (w3 x86_vpblendd)
  end.

(* ** Instructions
 * -------------------------------------------------------------------- *)

Section SEM.

Variable P:prog.
Context (gd: glob_defs).

Inductive ssem : sestate -> cmd -> sestate -> Prop :=
| SEskip s :
    ssem s [::] s

| SEseq s1 s2 s3 i c :
    ssem_I s1 i s2 -> ssem s2 c s3 -> ssem s1 (i::c) s3

with ssem_I : sestate -> instr -> sestate -> Prop :=
| SEmkI ii i s1 s2:
    ssem_i s1 i s2 ->
    ssem_I s1 (MkI ii i) s2

with ssem_i : sestate -> instr_r -> sestate -> Prop :=
| SEassgn s1 s2 (x:lval) tag ty e:
    (Let v := ssem_pexpr gd s1 e in swrite_lval gd x v s1) = ok s2 ->
    ssem_i s1 (Cassgn x tag ty e) s2

| SEopn s1 s2 t o xs es:
    ssem_pexprs gd s1 es >>= ssem_sopn o >>= (swrite_lvals gd s1 xs) = ok s2 ->
    ssem_i s1 (Copn xs t o es) s2

| SEif_true s1 s2 e c1 c2 :
    ssem_pexpr gd s1 e >>= sto_bool = ok true ->
    ssem s1 c1 s2 ->
    ssem_i s1 (Cif e c1 c2) s2

| SEif_false s1 s2 e c1 c2 :
    ssem_pexpr gd s1 e >>= sto_bool = ok false ->
    ssem s1 c2 s2 ->
    ssem_i s1 (Cif e c1 c2) s2

| SEwhile_true s1 s2 s3 s4 c e c' :
    ssem s1 c s2 ->
    ssem_pexpr gd s2 e >>= sto_bool = ok true ->
    ssem s2 c' s3 ->
    ssem_i s3 (Cwhile c e c') s4 ->
    ssem_i s1 (Cwhile c e c') s4

| SEwhile_false s1 s2 c e c' :
    ssem s1 c s2 ->
    ssem_pexpr gd s2 e >>= sto_bool = ok false ->
    ssem_i s1 (Cwhile c e c') s2

| SEfor s1 s2 (i:var_i) d lo hi c vlo vhi :
    ssem_pexpr gd s1 lo >>= sto_int = ok vlo ->
    ssem_pexpr gd s1 hi >>= sto_int = ok vhi ->
    ssem_for i (wrange d vlo vhi) s1 c s2 ->
    ssem_i s1 (Cfor i (d, lo, hi) c) s2

| SEcall s1 m2 s2 ii xs f args vargs vs :
    ssem_pexprs gd s1 args = ok vargs ->
    ssem_call s1.(semem) f vargs m2 vs ->
    swrite_lvals gd {|semem:= m2; sevm := s1.(sevm) |} xs vs = ok s2 ->
    ssem_i s1 (Ccall ii xs f args) s2

with ssem_for : var -> seq Z -> sestate -> cmd -> sestate -> Prop :=
| SEForDone s i c :
    ssem_for i [::] s c s

| SEForOne s1 s1' s2 s3 i w ws c :
    swrite_var i (SVint w) s1 = ok s1' ->
    ssem s1' c s2 ->
    ssem_for i ws s2 c s3 ->
    ssem_for i (w :: ws) s1 c s3

with ssem_call : mem -> funname -> seq svalue -> mem -> seq svalue -> Prop := 
| SEcallRun m1 m2 fn f vargs s1 vm2 vres:
    get_fundef P fn = Some f ->
    swrite_vars f.(f_params) vargs (SEstate m1 svmap0) = ok s1 ->
    ssem s1 f.(f_body) (SEstate m2 vm2) ->
    map (fun (x:var_i) => sget_var vm2 x) f.(f_res) = vres ->
    ssem_call m1 fn vargs m2 vres.

End SEM.

Definition MkI_inj {ii i ii' i'} (H: MkI ii i = MkI ii' i') :
  ii = ii' ∧ i = i' :=
  let 'Logic.eq_refl := H in conj Logic.eq_refl Logic.eq_refl.

Definition Some_inj {A} (a a': A) (H: Some a = Some a') : a = a' :=
  let 'Logic.eq_refl := H in Logic.eq_refl.

Lemma sval_sstype_to_sval sst (z : ssem_t sst) :
  sval_sstype (to_sval z) = sst.
Proof. by case: sst z. Qed.

(*Lemma sval_sstype_of_sval sst (z : svalue) y :
  of_sval sst z = ok y -> sval_sstype z = sst.
Proof.
  case: sst y z;[by move => y []| by move => y [] | |] => s; [by destruct s => y [] [] |]; (try by move => y [] ).
  simpl => w. move => []; (try by move).
  move => s' w'. simpl. rewrite /truncate_word. case (s<=s')%CMP. 
  move => H. apply ok_inj in H.
  simpl. move => H. 
Qed.

Lemma of_sval_inj sst z1 z2 :
     sval_sstype z1 = sst
  -> sval_sstype z2 = sst
  -> of_sval sst z1 = of_sval sst z2
  -> z1 = z2.
Proof. by case: sst; case: z2; case: z1 => //= x1 x2 _ _ [->]. Qed.

Lemma of_sval_to_sval ty x :
  of_sval ty (to_sval x) = ok x.
Proof. by move: x; case ty. Qed.
*)
Lemma sto_word_inv sz'(x : word sz') sz (i: word sz) :
  sto_word sz (SVword x) = ok i →
  (sz <= sz')%CMP ->
  truncate_word sz x = ok i.
Proof.
case: x => //i';simpl.
(*rewrite /truncate_word.
case:cmp_le => //= H; apply ok_inj in H.
rewrite -H. congr. congruence.
apply ok_inj in H. congruence.*) Qed.

Lemma sto_int_inv x i :
  sto_int x = ok i →
  x = i.
Proof. case: x => // i' H; apply ok_inj in H. congruence. Qed.

Lemma sto_bool_inv x b :
  sto_bool x = ok b →
  x = b.
Proof. case: x => // i' H; apply ok_inj in H. congruence. Qed.
(*
Lemma sto_arr_inv x a :
  sto_arr x = ok a →
  x = SVarr s a.
Proof. case: x => // a' H;apply ok_inj in H. congruence. Qed.

Lemma slet_inv {A s x} {f: _ → _ → exec A} {y} :
  SLet (n, t) := s.[x] in f n t = ok y →
  ∃ n (Tx: vtype x = sarr n), f n (eq_rect _ _ (sevm s).[x]%vmap _ Tx) = ok y.
Proof.
  unfold son_arr_var.
  generalize ((sevm s).[x])%vmap.
  case: (vtype x) => // n t E.
  exists n, Logic.eq_refl. exact E.
Qed.

Lemma ssem_inv { prg gd s c s' } :
  ssem prg gd s c s' →
  match c with
  | [::]    => s' = s
  | i :: c' => ∃ si, ssem_I prg gd s i si ∧ ssem prg gd si c' s'
end.
Proof. case; eauto. Qed.

Lemma ssem_I_inv { prg gd s i s' } :
  ssem_I prg gd s i s' →
  ∃ i' ii, i = MkI ii i' ∧ ssem_i prg gd s i' s'.
Proof. case; eauto. Qed.

Lemma ssem_i_inv { prg gd s i s' } :
  ssem_i prg gd s i s' →
  match i with
  | Cassgn x tg e   => ∃ v, ssem_pexpr gd s e = ok v ∧ swrite_lval gd x v s = ok s'
  | Copn xs t op es => ∃ args vs, ssem_pexprs gd s es = ok args ∧ ssem_sopn op args = ok vs ∧ swrite_lvals gd s xs vs = ok s'
  | Cif e c1 c2     => ∃ b : bool, ssem_pexpr gd s e = ok (SVbool b) ∧ ssem prg gd s (if b then c1 else c2) s'
  | _ => True
  end.
Proof.
  case; eauto; clear.
  - (* Cassgn *)
  move=> s s' x _ e; apply: rbindP; eauto.
  - (* Copn *)
  move=> s s' xs t op es; apply: rbindP => vs; apply: rbindP; eauto.
  - (* Cif true *)
  move=> s s' e c1 c2; apply: rbindP => v Hv /sto_bool_inv ?; subst v; eauto.
  - (* Cif false *)
  move=> s s' e c1 c2; apply: rbindP => v Hv /sto_bool_inv ?; subst v; eauto.
Qed.

Lemma of_val_addr_undef ty v :
  of_val ty v = Error ErrAddrUndef →
  v = Vundef ty.
Proof.
  case: ty => //; case: v => //=; try by case => //.
  + move=> n a p. case: CEDecStype.pos_dec => //.
  case => //. move=> p p'; case: eqP => // -> //.
Qed.

Lemma swrite_lval_inv {gd x v s s'} :
  swrite_lval gd x v s = ok s' →
  match x with
  | Lnone _ _ => s' = s
  | Lvar x => (∃ v', of_sval (vtype x) v = ok v' ∧
                    s' = {| semem := semem s ; sevm := (sevm s).[ x <- v' ] |})
                ∨ of_sval (vtype x) v = Error ErrAddrUndef ∧ s' = s
  | Lmem x e =>
    ∃ (Tx: vtype x = sword),
    ∃ vx ve w: word, eq_rect _ _ ((sevm s).[ x ]) _ Tx = vx ∧ ssem_pexpr gd s e = ok (SVword ve) ∧ v = w ∧
               s' = {| semem := write_mem (semem s) (I64.add vx ve) w ; sevm := sevm s |}
  | Laset x i =>
    ∃ n (Tx: vtype x = sarr n) (vi : Z) (w: word),
  ssem_pexpr gd s i = ok (SVint vi) ∧
  v = w ∧
  let q := FArray.set (eq_rect (vtype x) ssem_t ((sevm s).[x]) (sarr n) Tx) vi w in
  s' = {| semem := semem s ; sevm := (sevm s).[x <- eq_rect _ _ q _ (Logic.eq_sym Tx)] |}
end%vmap.
Proof.
  destruct x as [ vi | x | x e | x i ].
  - move=> H; apply ok_inj in H; auto.
  - apply: rbindP => vm H K; apply ok_inj in K; subst s'.
    revert H; apply: on_vuP.
    + move=> w -> <-; eauto.
    + move=> ->; case: eqP => // ht k; apply ok_inj in k; subst; right; constructor; auto.
      by case: s.
  - apply: rbindP => vx /sto_word_inv H.
    apply: rbindP => ve.
    apply: rbindP => ve' He /sto_word_inv ?; subst ve'.
    apply: rbindP => w /sto_word_inv -> X; apply ok_inj in X; subst s'.
    unfold sget_var in H.
    case: x H=> [[[] x] xi] //.
    exists Logic.eq_refl, vx, ve, w.
    split. simpl in *. congruence. auto.
  - move=> /slet_inv [n [Tx H]].
    exists n, Tx.
    apply: rbindP H=> vi;apply: rbindP => vj Hi /sto_int_inv H;subst vj.
    apply: rbindP => w /sto_word_inv ->;apply: rbindP => vm' L [<-].
    exists vi, w;split=> //;split=>//=;f_equal;f_equal.
    by case: x Tx L=>  -[ty x] xi /= ?;subst ty => /= -[] <-.
Qed.
*)
