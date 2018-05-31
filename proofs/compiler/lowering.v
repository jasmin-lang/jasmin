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

From mathcomp Require Import all_ssreflect all_algebra.
From CoqWord Require Import ssrZ.
Require Import Utf8.
Require Import compiler_util expr low_memory.

Section LOWERING.

Record fresh_vars : Type :=
  {
    fresh_OF : Equality.sort Ident.ident;
    fresh_CF : Equality.sort Ident.ident;
    fresh_SF : Equality.sort Ident.ident;
    fresh_PF : Equality.sort Ident.ident;
    fresh_ZF : Equality.sort Ident.ident;

    fresh_multiplicand : wsize → Equality.sort Ident.ident;
  }.

Record lowering_options : Type := 
  { 
    use_lea  : bool;
    use_set0 : bool;
  }.

Context (options : lowering_options).

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
Definition vword vt vn := {| vtype := sword vt ; vname := vn |}.

Context (fv: fresh_vars).

Definition fv_of := vbool fv.(fresh_OF).
Definition fv_cf := vbool fv.(fresh_CF).
Definition fv_sf := vbool fv.(fresh_SF).
Definition fv_pf := vbool fv.(fresh_PF).
Definition fv_zf := vbool fv.(fresh_ZF).

Definition fvars :=
  foldl (λ s sz, Sv.add (vword sz (fv.(fresh_multiplicand) sz)) s)
    (Sv.add fv_of (Sv.add fv_cf (Sv.add fv_sf (Sv.add fv_pf (Sv.singleton fv_zf)))))
    wsizes.

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
  | Lvar x | Lmem _ x _ | Laset x _ => v_info x
  end.

Definition stype_of_lval (x: lval) : stype :=
  match x with
  | Lnone _ t => t
  | Lvar v | Lmem _ v _ | Laset v _ => v.(vtype)
  end.

Definition wsize_of_stype (ty: stype) : wsize :=
  match ty with
  | sarr sz _
  | sword sz => sz
  | sbool | sint => U64
  end.

Definition wsize_of_lval (lv: lval) : wsize :=
  match lv with
  | Lnone _ ty
  | Lvar {| v_var := {| vtype := ty |} |}
  | Laset {| v_var := {| vtype := ty |} |} _
    => wsize_of_stype ty
  | Lmem sz _ _ => sz
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
    | Oeq (Op_w sz) =>
      Some ([:: nil ; nil ; nil ; nil ; lzf ], sz, Cond1 CondVar vzf, x, y)
    | Oneq (Op_w sz) =>
      Some ([:: nil ; nil ; nil ; nil ; lzf ], sz, Cond1 CondNotVar vzf, x, y)
    | Olt (Cmp_w Signed sz) =>
      Some ([:: lof ; nil ; lsf ; nil ; nil ], sz, Cond2 CondNeq vof vsf, x, y)
    | Olt (Cmp_w Unsigned sz) =>
      Some ([:: nil ; lcf ; nil ; nil ; nil ], sz, Cond1 CondVar vcf, x, y)
    | Ole (Cmp_w Signed sz) =>
      Some ([:: lof ; nil ; lsf ; nil ; lzf ], sz, Cond3 CondOrNeq vof vsf vzf, x, y)
    | Ole (Cmp_w Unsigned sz) =>
      Some ([:: nil ; lcf ; nil ; nil ; lzf ], sz, Cond2 CondOr vcf vzf, x, y)
    | Ogt (Cmp_w Signed sz) =>
      Some ([:: lof ; nil ; lsf ; nil ; lzf ], sz, Cond3 CondAndNotEq vof vsf vzf, x, y)
    | Ogt (Cmp_w Unsigned sz) =>
      Some ([:: nil ; lcf ; nil ; nil ; lzf ], sz, Cond2 CondAndNot vcf vzf, x, y)
    | Oge (Cmp_w Signed sz) =>
      Some ([:: lof ; nil ; lsf ; nil ; nil ], sz, Cond2 CondEq vof vsf, x, y)
    | Oge (Cmp_w Unsigned sz) =>
      Some ([:: nil ; lcf ; nil ; nil ; nil ], sz, Cond1 CondNotVar vcf, x, y)
    | _ => None
    end
  | _ => None
  end.

Definition eq_f  v1 v2 := Pif (Pvar v1) (Pvar v2) (Papp1 Onot (Pvar v2)).
Definition neq_f v1 v2 := Pif (Pvar v1) (Papp1 Onot (Pvar v2)) (Pvar v2).

Definition lower_condition vi (pe: pexpr) : seq instr_r * pexpr :=
  match lower_cond_classify vi pe with
  | Some (l, sz, r, x, y) =>
    if (sz ≤ U64)%CMP then
    ([:: Copn l AT_none (Ox86_CMP sz) [:: x; y] ],
    match r with
    | Cond1 CondVar v => Pvar v
    | Cond1 CondNotVar v => Papp1 Onot (Pvar v)
    | Cond2 CondEq v1 v2 => eq_f v2 v1
    | Cond2 CondNeq v1 v2 => neq_f v2 v1
    | Cond2 CondOr v1 v2 => Papp2 Oor v1 v2
    | Cond2 CondAndNot v1 v2 => Papp2 Oand (Papp1 Onot (Pvar v1)) (Papp1 Onot (Pvar v2))
    | Cond3 CondOrNeq v1 v2 v3 => Papp2 Oor v3 (neq_f v2 v1)
    | Cond3 CondAndNotEq v1 v2 v3 => Papp2 Oand (Papp1 Onot v3) (eq_f v2 v1)
    end)
    else ([::], pe)
  | None => ([::], pe)
  end.

(* Lowering of Cassgn
*)

Variant add_inc_dec : Type :=
  | AddInc of pexpr
  | AddDec of pexpr
  | AddNone.

Definition add_inc_dec_classify (sz: wsize) (a: pexpr) (b: pexpr) :=
  match a, b with
  | Pcast w (Pconst 1), y | y, Pcast w (Pconst 1) =>
    if w == sz then AddInc y else AddNone
  | Pcast w (Pconst (-1)), y | y, Pcast w (Pconst (-1)) =>
    if w == sz then AddDec y else AddNone
  | _, _ => AddNone
  end.

Variant sub_inc_dec : Type :=
  | SubInc
  | SubDec
  | SubNone.

Definition sub_inc_dec_classify sz (e: pexpr) :=
  match e with
  | Pcast w (Pconst (-1)) => if w == sz then SubInc else SubNone
  | Pcast w (Pconst 1) => if w == sz then SubDec else SubNone
  | _ => SubNone
  end.

(* -------------------------------------------------------------------- *)

(* disp + base + scale * offset *)
Record lea := MkLea {
  lea_disp   : pointer;
  lea_base   : option var_i;
  lea_scale  : pointer;
  lea_offset : option var_i;
}.

(* -------------------------------------------------------------------- *)

Variant lower_cassgn_t : Type :=
  | LowerMov of bool (* whether it needs a intermediate register *)
  | LowerCopn of sopn & list pexpr
  | LowerInc  of sopn & pexpr
  | LowerLea of wsize & lea
  | LowerFopn of sopn & list pexpr & option wsize
  | LowerEq   of wsize & pexpr & pexpr
  | LowerLt   of wsize & pexpr & pexpr
  | LowerIf   of pexpr & pexpr & pexpr
  | LowerAssgn.

Context (is_var_in_memory : var_i → bool).

Definition is_lval_in_memory (x: lval) : bool :=
  match x with
  | Lnone _ _ => false
  | Lvar v
  | Laset v _
    => is_var_in_memory v
  | Lmem _ _ _ => true
  end.

(* -------------------------------------------------------------------- *)

Definition lea_const z := MkLea z   None     1%R None.

Definition lea_var x := MkLea 0%R (Some x) 1%R None.

Definition mkLea d b sc o :=
  if sc == 0%R then MkLea d b 1%R None
  else MkLea d b sc o.
  
Definition lea_mul l1 l2 :=
  let 'MkLea d1 b1 sc1 o1 := l1 in
  let 'MkLea d2 b2 sc2 o2 := l2 in
  let d := (d1 * d2)%R in
  match b1, o1, b2, o2 with
  | None  , None  , None  , None   => Some (lea_const d)
  | Some _, None  , None  , None   => Some (mkLea d None d2 b1)
  | None  , None  , Some _, None   => Some (mkLea d None d1 b2)
  | None  , Some _, None  , None   => Some (mkLea d None (d2 * sc1) o1)
  | None  , None  , None  , Some _ => Some (mkLea d None (d1 * sc2) o2)
  | _     , _     , _     , _      => None
  end%R.

Definition lea_add l1 l2 :=
  let 'MkLea d1 b1 sc1 o1 := l1 in
  let 'MkLea d2 b2 sc2 o2 := l2 in
  let disp := (d1 + d2)%R in
  match b1, o1    , b2    , o2    with
  | None  , None  , _     , _      => Some (mkLea disp b2 sc2 o2)
  | _     , _     , None  , None   => Some (mkLea disp b1 sc1 o1)
  | Some _, None  , _     , None   => Some (mkLea disp b1 1 b2)
  | Some _, None  , None  , Some _ => Some (mkLea disp b1 sc2 o2)
  | None  , Some _, Some _, None   => Some (mkLea disp b2 sc1 o1)
  | None  , Some _, None  , Some _ =>
    if sc1 == 1 then Some (mkLea disp o1 sc2 o2)
    else if sc2 == 1 then Some (mkLea disp o2 sc1 o1)
    else None
  | _     , _     , _     , _      => None
  end%R.

Definition lea_sub l1 l2 :=
  let 'MkLea d1 b1 sc1 o1 := l1 in
  let 'MkLea d2 b2 sc2 o2 := l2 in
  let disp := (d1 - d2)%R in
  match b2, o2 with
  | None, None => Some (mkLea disp b1 sc1 o1)
  | _   , _    => None
  end.

Fixpoint mk_lea e :=
  match e with
  | Pcast sz' (Pconst z) => Some (lea_const (zero_extend Uptr (wrepr sz' z)))
  | Pvar  x          => Some (lea_var x)
  | Papp2 (Omul (Op_w Uptr)) e1 e2 =>
    match mk_lea e1, mk_lea e2 with
    | Some l1, Some l2 => lea_mul l1 l2
    | _      , _       => None
    end
  | Papp2 (Oadd (Op_w Uptr)) e1 e2 =>
    match mk_lea e1, mk_lea e2 with
    | Some l1, Some l2 => lea_add l1 l2
    | _      , _       => None
    end
  | Papp2 (Osub (Op_w Uptr)) e1 e2 =>
    match mk_lea e1, mk_lea e2 with
    | Some l1, Some l2 => lea_sub l1 l2
    | _      , _       => None
    end
  | _ => None
  end.

Definition is_lea sz x e :=
  if (sz == Uptr) && ~~ is_lval_in_memory x then
    match mk_lea e with 
    | Some (MkLea d b sc o) => 
      let check o := match o with Some x => ~~(is_var_in_memory x) | None => true end in
      (* FIXME: check that d is not to big *)
      if check_scale (wunsigned sc) && check b && check o then  Some (MkLea d b sc o)
      else None
    | None => None
    end
  else None.

(* -------------------------------------------------------------------- *)

Definition lower_cassgn_classify sz' e x : lower_cassgn_t :=
  let chk (b: bool) r := if b then r else LowerAssgn in
  let kb b sz := chk (b && (sz == sz')) in
  let k8 sz := kb (sz ≤ U64)%CMP sz in
  let k16 sz := kb ((U16 ≤ sz) && (sz ≤ U64))%CMP sz in
  let k32 sz := kb ((U32 ≤ sz) && (sz ≤ U64))%CMP sz in
  match e with
  | Pcast sz (Pconst _) => chk (sz' ≤ U64)%CMP (LowerMov false)
  | Pget ({| v_var := {| vtype := sword sz |} |} as v) _
  | Pvar ({| v_var := {| vtype := sword sz |} |} as v) =>
    chk (sz ≤ U64)%CMP (LowerMov (if is_var_in_memory v then is_lval_in_memory x else false))
  | Pload sz _ _ => chk (sz ≤ U64)%CMP (LowerMov (is_lval_in_memory x))

  | Papp1 (Olnot sz) a => k8 sz (LowerCopn (Ox86_NOT sz) [:: a ])
  | Papp1 (Oneg (Op_w sz)) a => k8 sz (LowerFopn (Ox86_NEG sz) [:: a] None)
  | Papp1 (Osignext szo szi) a =>
    match szi with
    | U8 => k16 szo
    | U16 => k32 szo
    | U32 => kb (szo == U64) szo
    | _ => chk false
    end (LowerCopn (Ox86_MOVSX szo szi) [:: a])
  | Papp1 (Ozeroext szo szi) a =>
    match szi with
    | U8 => k16 szo
    | U16 => k32 szo
    | _ => chk false
    end (LowerCopn (Ox86_MOVZX szo szi) [:: a])

  | Papp2 op a b =>
    match op with
    | Oadd (Op_w sz) =>
      k8 sz
      match is_lea sz x e with
      | Some l => LowerLea sz l
      | None   => 
        match add_inc_dec_classify sz a b with
        | AddInc y => LowerInc (Ox86_INC sz) y
        | AddDec y => LowerInc (Ox86_DEC sz) y
        | AddNone  => LowerFopn (Ox86_ADD sz) [:: a ; b ] (Some U32)
        end
      end
    | Osub (Op_w sz) =>
      k8 sz
      match is_lea sz x e with
      | Some l => LowerLea sz l
      | None   => 
        match sub_inc_dec_classify sz b with
        | SubInc => LowerInc (Ox86_INC sz) a
        | SubDec => LowerInc (Ox86_DEC sz) a
        | SubNone => LowerFopn (Ox86_SUB sz) [:: a ; b ] (Some U32)
        end
      end
    | Omul (Op_w sz) =>
      k16 sz
      match is_lea sz x e with
      | Some l => LowerLea sz l
      | _      => 
        match is_wconst sz a with
        | Some _ => LowerFopn (Ox86_IMULtimm sz) [:: b ; a ] (Some U32)
        | _      =>
        match is_wconst sz b with
        | Some _ => LowerFopn (Ox86_IMULtimm sz) [:: a ; b ] (Some U32)
        | _ => LowerFopn (Ox86_IMULt sz) [:: a ; b ] (Some U32)
        end
        end
      end
    | Oland sz =>
      if (sz ≤ U64)%CMP
      then k8 sz (LowerFopn (Ox86_AND sz) [:: a ; b ] (Some U32))
      else kb true sz (LowerCopn (Ox86_VPAND sz) [:: a ; b ])
    | Olor sz =>
      if (sz ≤ U64)%CMP
      then k8 sz (LowerFopn (Ox86_OR sz) [:: a ; b ] (Some U32))
      else kb true sz (LowerCopn (Ox86_VPOR sz) [:: a ; b ])
    | Olxor sz =>
      if (sz ≤ U64)%CMP
      then k8 sz (LowerFopn (Ox86_XOR sz) [:: a ; b ] (Some U32))
      else kb true sz (LowerCopn (Ox86_VPXOR sz) [:: a ; b ])
    | Olsr sz => k8 sz (LowerFopn (Ox86_SHR sz) [:: a ; b ] (Some U8))
    | Olsl sz => k8 sz (LowerFopn (Ox86_SHL sz) [:: a ; b ] (Some U8))
    | Oasr sz => k8 sz (LowerFopn (Ox86_SAR sz) [:: a ; b ] (Some U8))
    | Oeq (Op_w sz) => k8 sz (LowerEq sz a b)
    | Olt (Cmp_w Unsigned sz) => k8 sz (LowerLt sz a b)
    | _ => LowerAssgn
    end

  | Pif e e1 e2 =>
    if stype_of_lval x is sword _ then
      k16 (wsize_of_lval x) (LowerIf e e1 e2)
    else
      LowerAssgn
  | _ => LowerAssgn
  end.

Definition Lnone_b vi := Lnone vi sbool.

(* TODO: other sizes than U64 *)
(* TODO: remove dependent types *)
Variant opn_5flags_cases_t (a: pexprs) : Type :=
| Opn5f_large_immed x y (n: Z) z `(a = x :: y :: z) `(y = Pcast U64 n)
| Opn5f_other.

Arguments Opn5f_large_immed [a] {x y n z} _ _.
Arguments Opn5f_other [a].

Definition check_signed_range (m: option wsize) sz' (n: Z) : bool :=
  if m is Some ws then (
      let z := wsigned (wrepr sz' n) in
      let h := (wbase ws) / 2 in
      if -h <=? z then z <? h else false)%Z
  else false.

Definition opn_5flags_cases (a: pexprs) (m: option wsize) (sz: wsize) : opn_5flags_cases_t a :=
  match a with
  | x :: y :: _ =>
    match is_wconst_of_size U64 y as u return is_reflect (λ z : Z, Pcast U64 z) y u → _ with
    | None => λ _, Opn5f_other
    | Some n =>
      λ W,
      if check_signed_range m sz n
      then Opn5f_other
      else Opn5f_large_immed erefl (is_reflect_some_inv W)
    end%Z (is_wconst_of_sizeP U64 y)
  | _ => Opn5f_other end.

Definition opn_no_imm (op: sopn) : sopn :=
  match op with
  | Ox86_IMULtimm sz => Ox86_IMULt sz
  | _ => op end.

(* TODO: move *)
Definition wsize_of_sopn (op: sopn) : wsize :=
  match op with
  | Ox86_SETcc => U8
  | Omulu x
  | Oaddcarry x
  | Osubcarry x
  | Oset0 x
  | Ox86_MOV x
  | Ox86_MOVSX _ x
  | Ox86_MOVZX _ x
  | Ox86_CMOVcc x
  | Ox86_ADD x
  | Ox86_SUB x
  | Ox86_MUL x
  | Ox86_IMUL x
  | Ox86_IMULt x
  | Ox86_IMULtimm x
  | Ox86_DIV x
  | Ox86_IDIV x
  | Ox86_ADC x
  | Ox86_SBB x
  | Ox86_NEG x
  | Ox86_INC x
  | Ox86_DEC x
  | Ox86_BT x
  | Ox86_LEA x
  | Ox86_TEST x
  | Ox86_CMP x
  | Ox86_AND x
  | Ox86_OR x
  | Ox86_XOR x
  | Ox86_NOT x
  | Ox86_ROR x
  | Ox86_ROL x
  | Ox86_SHL x
  | Ox86_SHR x
  | Ox86_SAR x
  | Ox86_SHLD x
  | Ox86_BSWAP x
  | Ox86_VMOVDQU x
  | Ox86_VPAND x | Ox86_VPANDN x | Ox86_VPOR x | Ox86_VPXOR x
  | Ox86_VPADD _ x | Ox86_VPMULU x
  | Ox86_VPSLL _ x | Ox86_VPSRL _ x
  | Ox86_VPSHUFB x | Ox86_VPSHUFHW x | Ox86_VPSHUFLW x | Ox86_VPSHUFD x
  | Ox86_VPUNPCKH _ x | Ox86_VPUNPCKL _ x
  | Ox86_VPBLENDD x
    => x
  | Ox86_MOVD _
    => U128
  | Ox86_VPERM2I128
  | Ox86_VPERMQ
    => U256
  end.

Definition opn_5flags (immed_bound: option wsize) (vi: var_info)
           (cf: lval) (x: lval) tg (o: sopn) (a: pexprs) : seq instr_r :=
  let f := Lnone_b vi in
  let fopn o a := [:: Copn [:: f ; cf ; f ; f ; f ; x ] tg o a ] in
  match opn_5flags_cases a immed_bound (wsize_of_sopn o) with
  | Opn5f_large_immed x y n z _ _ =>
    let c := {| v_var := {| vtype := sword U64; vname := fresh_multiplicand fv U64 |} ; v_info := vi |} in
    Copn [:: Lvar c ] tg (Ox86_MOV U64) [:: y] :: fopn (opn_no_imm o) (x :: Pvar c :: z)
  | Opn5f_other => fopn o a
  end.

Definition reduce_wconst sz (e: pexpr) : pexpr :=
  if e is Pcast sz' (Pconst z)
  then Pcast (cmp_min sz sz') (Pconst z)
  else e.

Definition lower_cassgn (ii:instr_info) (x: lval) (tg: assgn_tag) (ty: stype) (e: pexpr) : cmd :=
  let vi := var_info_of_lval x in
  let f := Lnone_b vi in
  let copn o a := [:: MkI ii (Copn [:: x ] tg o a) ] in
  let inc o a := [:: MkI ii (Copn [:: f ; f ; f ; f ; x ] tg o [:: a ]) ] in
  let szty := wsize_of_stype ty in
  match lower_cassgn_classify szty e x with
  | LowerMov b =>
    let e := reduce_wconst szty e in
    if b
    then
      let c := {| v_var := {| vtype := sword szty; vname := fresh_multiplicand fv szty |} ; v_info := vi |} in
      [:: MkI ii (Copn [:: Lvar c] tg (Ox86_MOV szty) [:: e ])
       ; MkI ii (Copn [:: x ] tg (Ox86_MOV szty) [:: Pvar c ]) ]
    else 
      (* IF e is 0 then use Oset0 instruction *)
      if (e == @wconst szty 0) && ~~ is_lval_in_memory x && options.(use_set0) then
        [:: MkI ii (Copn [:: f ; f ; f ; f ; f ; x] tg (Oset0 szty) [::]) ]
      else copn (Ox86_MOV szty) [:: e ]
  | LowerCopn o e => copn o e
  | LowerInc o e => inc o e
  | LowerFopn o es m => map (MkI ii) (opn_5flags m vi f x tg o es)
  | LowerLea sz (MkLea d b sc o) =>
    let de := wconst d in
    let sce := wconst sc in
    let b := oapp Pvar (@wconst sz 0) b in
    let o := oapp Pvar (@wconst sz 0) o in
    let lea tt := 
      let ii := warning ii Use_lea in
      [:: MkI ii (Copn [::x] tg (Ox86_LEA sz) [:: de; b; sce; o]) ] in
    if options.(use_lea) then lea tt
    (* d + b + sc * o *)
    else 
      if d == 0%R then
        (* b + sc * o *)
        if sc == 1%R then
          (* b + o *)
          [::MkI ii (Copn [:: f ; f ; f ; f ; f; x ] tg (Ox86_ADD sz) [:: b ; o])]
        else if b == @wconst sz 0 then
          (* sc * o *)
          [::MkI ii (Copn [:: f ; f ; f ; f ; f; x ] tg (Ox86_IMULt sz) [:: o; sce])]
        else lea tt
      else if o == @wconst sz 0 then
          (* d + b *)
          if d == 1%R then inc (Ox86_INC sz) b
          else
            let w := wunsigned d in
            if check_signed_range (Some U32) sz w
            then [::MkI ii (Copn [:: f ; f ; f ; f ; f; x ] tg (Ox86_ADD sz) [:: b ; de ])]
            else if w == (wbase U32 / 2)%Z
            then [::MkI ii (Copn [:: f ; f ; f ; f ; f; x ] tg (Ox86_SUB sz) [:: b ; wconst (wrepr sz (-w)) ])]
            else
              let c := {| v_var := {| vtype := sword U64; vname := fresh_multiplicand fv U64 |} ; v_info := vi |} in
              [:: MkI ii (Copn [:: Lvar c ] tg (Ox86_MOV U64) [:: de]);
                 MkI ii (Copn [:: f ; f ; f ; f ; f; x ] tg (Ox86_ADD sz) [:: b ; Pvar c ])]
      else lea tt
      
  | LowerEq sz a b => [:: MkI ii (Copn [:: f ; f ; f ; f ; x ] tg (Ox86_CMP sz) [:: a ; b ]) ]
  | LowerLt sz a b => [:: MkI ii (Copn [:: f ; x ; f ; f ; f ] tg (Ox86_CMP sz) [:: a ; b ]) ]
  | LowerIf e e1 e2 =>
     let (l, e) := lower_condition vi e in
     let sz := wsize_of_lval x in
     map (MkI ii) (l ++ [:: Copn [:: x] tg (Ox86_CMOVcc sz) [:: e; e1; e2]])
  | LowerAssgn => [::  MkI ii (Cassgn x tg ty e)]
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

Definition lower_addcarry sz (sub: bool) (xs: lvals) tg (es: pexprs) : seq instr_r :=
  if (sz ≤ U64)%CMP then
  match lower_addcarry_classify sub xs es with
  | Some (vi, o, es, cf, r) => opn_5flags (Some U32) vi cf r tg (o sz) es
  | None => [:: Copn xs tg ((if sub then Osubcarry else Oaddcarry) sz) es ]
  end
  else [:: Copn xs tg ((if sub then Osubcarry else Oaddcarry) sz) es ].

Definition lower_mulu sz (xs: lvals) tg (es: pexprs) : seq instr_r :=
  if check_size_16_64 sz is Ok _ then
  match xs, es with
  | [:: r1; r2 ], [:: x ; y ] =>
    let vi := var_info_of_lval r2 in
    let f := Lnone_b vi in
    match is_wconst sz x with
    | Some _ =>
      let c := {| v_var := {| vtype := sword sz; vname := fresh_multiplicand fv sz |} ; v_info := vi |} in
      [:: Copn [:: Lvar c ] tg (Ox86_MOV sz) [:: x ] ;
          Copn [:: f ; f ; f ; f ; f ; r1 ; r2 ] tg (Ox86_MUL sz) [:: y ; Pvar c ] ]
    | None =>
    match is_wconst sz y with
    | Some _ =>
      let c := {| v_var := {| vtype := sword sz; vname := fresh_multiplicand fv sz |} ; v_info := vi |} in
      [:: Copn [:: Lvar c ] tg (Ox86_MOV sz) [:: y ] ;
          Copn [:: f ; f ; f ; f ; f ; r1 ; r2 ] tg (Ox86_MUL sz) [:: x ; Pvar c ] ]
    | None => [:: Copn [:: f ; f ; f ; f ; f ; r1 ; r2 ] tg (Ox86_MUL sz) es ]
    end end
  | _, _ => [:: Copn xs tg (Omulu sz) es ]
  end
  else [:: Copn xs tg (Omulu sz) es ].

Definition lower_copn (xs: lvals) tg (op: sopn) (es: pexprs) : seq instr_r :=
  match op with
  | Oaddcarry sz => lower_addcarry sz false xs tg es
  | Osubcarry sz => lower_addcarry sz true xs tg es
  | Omulu sz => lower_mulu sz xs tg es
  | _ => [:: Copn xs tg op es]
  end.

Definition lower_cmd (lower_i: instr -> cmd) (c:cmd) : cmd :=
  List.fold_right (fun i c' => lower_i i ++ c') [::] c.

Fixpoint lower_i (i:instr) : cmd :=
  let (ii, ir) := i in
  match ir with
  | Cassgn l tg ty e => lower_cassgn ii l tg ty e
  | Copn l t o e =>   map (MkI ii) (lower_copn l t o e)
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
     f_tyin := f_tyin fd;
     f_params := f_params fd;
     f_body := lower_cmd lower_i (f_body fd);
     f_tyout := f_tyout fd;
     f_res := f_res fd
  |}.

Definition lower_prog (p: prog) := map_prog lower_fd p.

End LOWERING.
