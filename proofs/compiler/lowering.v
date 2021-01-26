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
Require Import compiler_util expr low_memory leakage.

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

Definition vars_p (p: fun_decls) :=
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
  | Lvar x | Lmem _ x _ | Laset _ x _ => v_info x
  end.

Definition stype_of_lval (x: lval) : stype :=
  match x with
  | Lnone _ t => t
  | Lvar v | Lmem _ v _ | Laset _ v _ => v.(vtype)
  end.

Definition wsize_of_stype (ty: stype) : wsize :=
  match ty with
  | sword sz => sz
  | sbool | sint | sarr _ => U64
  end.

Definition wsize_of_lval (lv: lval) : wsize :=
  match lv with
  | Lnone _ ty
  | Lvar {| v_var := {| vtype := ty |} |} => wsize_of_stype ty
  | Laset sz _  _
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

Definition eq_f  v1 v2 := Pif sbool (Pvar v1) (Pvar v2) (Papp1 Onot (Pvar v2)).
Definition neq_f v1 v2 := Pif sbool (Pvar v1) (Papp1 Onot (Pvar v2)) (Pvar v2). 

Definition lower_condition vi (pe: pexpr) : (seq instr_r * leak_e_i_tr) * (pexpr * leak_e_tr) :=
  match lower_cond_classify vi pe with
  | Some (l, sz, r, x, y) =>
    if (sz ≤ U64)%CMP then
    (([:: Copn l AT_none (Ox86 (CMP sz)) [:: x; y] ], LT_iconditionl (LT_id)), 
    match r with
    | Cond1 CondVar v => (Pvar v, LT_remove)
    | Cond1 CondNotVar v => (Papp1 Onot (Pvar v), LT_remove)
    | Cond2 CondEq v1 v2 => (eq_f v2 v1, LT_seq [:: LT_remove; LT_remove; LT_remove])
    | Cond2 CondNeq v1 v2 => (neq_f v2 v1, LT_seq [:: LT_remove; LT_remove; LT_remove])
    | Cond2 CondOr v1 v2 => (Papp2 Oor v1 v2, LT_seq [:: LT_remove; LT_remove])
    | Cond2 CondAndNot v1 v2 => 
       (Papp2 Oand (Papp1 Onot (Pvar v1)) (Papp1 Onot (Pvar v2)), LT_seq [:: LT_remove; LT_remove])
    | Cond3 CondOrNeq v1 v2 v3 => (Papp2 Oor v3 (neq_f v2 v1), LT_seq [:: LT_remove; LT_seq [:: LT_remove; LT_remove; LT_remove]])
    | Cond3 CondAndNotEq v1 v2 v3 => (Papp2 Oand (Papp1 Onot v3) (eq_f v2 v1), 
      LT_seq[:: LT_remove; LT_seq [:: LT_remove; LT_remove; LT_remove]])
    end)
    else (([::], LT_iemptyl), (pe, LT_id))
  | None => (([::], LT_iemptyl), (pe, LT_id))
  end.

(* Lowering of Cassgn
*)

Variant add_inc_dec : Type :=
  | AddInc of pexpr
  | AddDec of pexpr
  | AddNone.

Definition add_inc_dec_classify (sz: wsize) (a: pexpr) (b: pexpr) :=
  match a, b with
  | Papp1 (Oword_of_int w) (Pconst 1), y => if w == sz then (AddInc y, LT_subi 1) else (AddNone, LT_id)
  | y, Papp1 (Oword_of_int w) (Pconst 1) => if w == sz then (AddInc y, LT_subi 0) else (AddNone, LT_id)
  | Papp1 (Oword_of_int w) (Pconst (-1)), y => if w == sz then (AddDec y, LT_subi 1) else (AddNone, LT_id)
  | y, Papp1 (Oword_of_int w) (Pconst (-1)) => if w == sz then (AddDec y, LT_subi 0) else (AddNone, LT_id)
  | _, _ => (AddNone, LT_id)
  end.

Variant sub_inc_dec : Type :=
  | SubInc
  | SubDec
  | SubNone.

Definition sub_inc_dec_classify sz (e: pexpr) :=
  match e with
  | Papp1 (Oword_of_int w) (Pconst (-1)) => if w == sz then SubInc else SubNone
  | Papp1 (Oword_of_int w) (Pconst 1) => if w == sz then SubDec else SubNone
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
Variant divmod_pos :=
  | DM_Fst
  | DM_Snd.

Variant lower_cassgn_t : Type :=
  | LowerMov of bool (* whether it needs a intermediate register *)
  | LowerCopn of sopn & list pexpr
  | LowerInc  of sopn & pexpr
  | LowerLea of wsize & lea
  | LowerFopn of sopn & list pexpr & option wsize
  | LowerEq   of wsize & pexpr & pexpr
  | LowerLt   of wsize & pexpr & pexpr
  | LowerIf   of stype & pexpr & pexpr & pexpr
  | LowerDivMod of divmod_pos & signedness & wsize & sopn & pexpr & pexpr
  | LowerAssgn.

Context (is_var_in_memory : var_i → bool).

Definition is_lval_in_memory (x: lval) : bool :=
  match x with
  | Lnone _ _ => false
  | Lvar v
  | Laset _ v _
    => is_var_in_memory v
  | Lmem _ _ _ => true
  end.

(* -------------------------------------------------------------------- *)

Definition lea_const z := MkLea z None 1%R None.

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

Fixpoint mk_lea_rec (sz:wsize) e : option lea :=
  match e with
  | Papp1 (Oword_of_int sz') (Pconst z) => 
      Some (lea_const (sign_extend Uptr (wrepr sz' z)))
  | Pvar  x          => Some (lea_var x)
  | Papp2 (Omul (Op_w sz')) e1 e2 =>
    match mk_lea_rec sz e1, mk_lea_rec sz e2 with
    | Some l1, Some l2 => lea_mul l1 l2
    | _      , _       => None
    end
  | Papp2 (Oadd (Op_w sz')) e1 e2 =>
    match mk_lea_rec sz e1, mk_lea_rec sz e2 with
    | Some l1, Some l2 => lea_add l1 l2
    | _      , _       => None
    end
  | Papp2 (Osub (Op_w sz')) e1 e2 =>
    match mk_lea_rec sz e1, mk_lea_rec sz e2 with
    | Some l1, Some l2 => lea_sub l1 l2
    | _      , _       => None
    end
  | _ => None
  end.

Fixpoint push_cast_sz sz e := 
  match e with
  | Papp2 (Oadd Op_int) e1 e2 => 
    Papp2 (Oadd (Op_w sz)) (push_cast_sz sz e1) (push_cast_sz sz e2)

  | Papp2 (Omul Op_int) e1 e2 => 
    Papp2 (Omul (Op_w sz)) (push_cast_sz sz e1) (push_cast_sz sz e2)

  | Papp2 (Osub Op_int) e1 e2 => 
    Papp2 (Osub (Op_w sz)) (push_cast_sz sz e1) (push_cast_sz sz e2)

(*  | Papp1 (Oneg Op_int) e1 =>
    Papp1 (Oneg (Op_w sz)) (push_cast_sz sz e1) *)
  
  | Papp1 (Oint_of_word sz') e1 => 
    if (sz <= sz')%CMP then e1
    else Papp1 (Oword_of_int sz) e 
  | _ => Papp1 (Oword_of_int sz) e
  end.

Fixpoint push_cast e :=
  match e with
  | Papp1 (Oword_of_int sz) e1 => push_cast_sz sz (push_cast e1)
  | Papp1 o e1                 => Papp1 o (push_cast e1)
  | Papp2 o e1 e2              => Papp2 o (push_cast e1) (push_cast e2)
  | _                          => e
  end.

Definition mk_lea sz e := mk_lea_rec sz (push_cast e).

Definition is_lea sz x e :=
  if ((U16 ≤ sz)%CMP && (sz ≤ U64)%CMP) && ~~ is_lval_in_memory x then
    match mk_lea sz e with
    | Some (MkLea d b sc o) =>
      let check o := match o with Some x => ~~(is_var_in_memory x) | None => true end in
      (* FIXME: check that d is not to big *)
      if check_scale (wunsigned sc) && check b && check o then  Some (MkLea d b sc o)
      else None
    | None => None
    end
  else None.

(* -------------------------------------------------------------------- *)

Definition is_lnot a :=
  match a with
  | Papp1 (Olnot _) a => Some a
  | _                 => None
  end.

Definition is_andn  a b :=
  match is_lnot a, is_lnot b with
  | Some a, _      => Some (a, b)
  | None  , Some b => Some (b, a)
  | None  , None   => None
  end.

Definition mulr sz a b :=
  match is_wconst sz a with
  | Some _ => ((IMULri sz, [:: b ; a ]), LT_rev)
  | _      =>
    match is_wconst sz b with
    | Some _ => ((IMULri sz, [:: a ; b ]), LT_id)
    | _      => ((IMULr sz,  [:: a ; b ]), LT_id)
    end
 end.

Definition lower_cassgn_classify sz' e x : lower_cassgn_t * leak_e_es_tr :=
  let chk (b: bool) r := if b then r else LowerAssgn in
  let kb b sz := chk (b && (sz == sz')) in
  let k8 sz := kb (sz ≤ U64)%CMP sz in
  let k16 sz := kb ((U16 ≤ sz) && (sz ≤ U64))%CMP sz in
  let k32 sz := kb ((U32 ≤ sz) && (sz ≤ U64))%CMP sz in
  match e with
  | Pvar ({| v_var := {| vtype := sword sz |} |} as v) =>
    (chk (sz ≤ U64)%CMP (LowerMov (if is_var_in_memory v then is_lval_in_memory x else false)), LT_idseq LT_id)
  | Pload sz _ _ => (chk (sz ≤ U64)%CMP (LowerMov (is_lval_in_memory x)), LT_idseq LT_id)

  | Papp1 (Oword_of_int sz) (Pconst _) => (chk (sz' ≤ U64)%CMP (LowerMov false), LT_idseq LT_id)
  | Papp1 (Olnot sz) a => (k8 sz (LowerCopn (Ox86 (NOT sz)) [:: a ]),  LT_leseq)
  | Papp1 (Oneg (Op_w sz)) a => (k8 sz (LowerFopn (Ox86 (NEG sz)) [:: a] None),  LT_leseq)
  | Papp1 (Osignext szo szi) a =>
    match szi with
    | U8 => (k16 szo (LowerCopn (Ox86 (MOVSX szo szi)) [:: a]), LT_leseq)
    | U16 => (k32 szo (LowerCopn (Ox86 (MOVSX szo szi)) [:: a]), LT_leseq)
    | U32 => (kb (szo == U64) szo (LowerCopn (Ox86 (MOVSX szo szi)) [:: a]), LT_leseq)
    | _ => (chk false (LowerCopn (Ox86 (MOVSX szo szi)) [:: a]), LT_idseq LT_id)
    end
  | Papp1 (Ozeroext szo szi) a =>
    match szi with
    | U8 => (k16 szo (LowerCopn (Ox86 (MOVZX szo szi)) [:: a]),  LT_leseq)
    | U16 => (k32 szo (LowerCopn (Ox86 (MOVZX szo szi)) [:: a]),  LT_leseq)
    | U32 => (kb (szo == U64) szo (LowerCopn Ox86MOVZX32 [:: a]),  LT_leseq)
    | _ => (LowerAssgn, LT_emseq)
    end

  | Papp2 op a b =>
    match op with
    | Oadd (Op_w sz) =>
      match is_lea sz x e with
      | Some l => (LowerLea sz l, LT_emseq)
      | None   =>
        match add_inc_dec_classify sz a b with
        | (AddInc y, lte) => (k8 sz (LowerInc (Ox86 (INC sz)) y), LT_subseq lte)
        | (AddDec y, lte) => (k8 sz (LowerInc (Ox86 (DEC sz)) y), LT_subseq lte)
        | (AddNone, lte)  => (k8 sz (LowerFopn (Ox86 (ADD sz)) [:: a ; b ] (Some U32)), LT_idseq lte)
        end
      end
    | Osub (Op_w sz) =>
      match is_lea sz x e with
      | Some l => (k8 sz (LowerLea sz l), LT_emseq)
      | None   =>
        match sub_inc_dec_classify sz b with
        | SubInc => (k8 sz (LowerInc (Ox86 (INC sz)) a), LT_subseq (LT_subi 0))
        | SubDec => (k8 sz (LowerInc (Ox86 (DEC sz)) a), LT_subseq (LT_subi 0))
        | SubNone => (k8 sz (LowerFopn (Ox86 (SUB sz)) [:: a ; b ] (Some U32)), LT_idseq LT_id)
        end
      end
    | Omul (Op_w sz) =>
      match is_lea sz x e with
      | Some l => (k16 sz (LowerLea sz l), LT_emseq)
      | _      =>
        let (op, args) := mulr sz a b in
        (k16 sz (LowerFopn (Ox86 op.1) op.2 (Some U32)), LT_idseq args)
      end
    | Odiv (Cmp_w u sz) =>
      let opn :=
        match u with
        | Unsigned => Ox86 (DIV sz)
        | Signed   => Ox86 (IDIV sz)
        end in
      (k16 sz (LowerDivMod DM_Fst u sz opn a b), LT_idseq LT_id)

    | Omod (Cmp_w u sz) =>
       let opn :=
        match u with
        | Unsigned => Ox86 (DIV sz)
        | Signed   => Ox86 (IDIV sz)
        end in
      (k16 sz (LowerDivMod DM_Snd u sz opn a b),  LT_idseq LT_id)

    | Oland sz =>
      match is_andn a b with
      | Some (a,b) =>
        if (sz ≤ U64)%CMP
        then (k32 sz (LowerFopn (Ox86 (ANDN sz)) [:: a ; b ] None),  LT_idseq LT_id)
        else (kb true sz (LowerCopn (Ox86 (VPANDN sz)) [:: a ; b ]), LT_emseq)
      | None =>
        if (sz ≤ U64)%CMP
        then (k8 sz (LowerFopn (Ox86 (AND sz)) [:: a ; b ] (Some U32)), LT_emseq)
        else (kb true sz (LowerCopn (Ox86 (VPAND sz)) [:: a ; b ]), LT_emseq)
      end


    | Olor sz =>
      if (sz ≤ U64)%CMP
      then (k8 sz (LowerFopn (Ox86 (OR sz)) [:: a ; b ] (Some U32)), LT_idseq LT_id)
      else (kb true sz (LowerCopn (Ox86 (VPOR sz)) [:: a ; b ]), LT_idseq LT_id)
    | Olxor sz =>
      if (sz ≤ U64)%CMP
      then (k8 sz (LowerFopn (Ox86 (XOR sz)) [:: a ; b ] (Some U32)), LT_idseq LT_id)
      else (kb true sz (LowerCopn (Ox86 (VPXOR sz)) [:: a ; b ]), LT_idseq LT_id)
    | Olsr sz => (k8 sz (LowerFopn (Ox86 (SHR sz)) [:: a ; b ] (Some U8)), LT_idseq LT_id)
    | Olsl sz => (k8 sz (LowerFopn (Ox86 (SHL sz)) [:: a ; b ] (Some U8)), LT_idseq LT_id)
    | Oasr sz => (k8 sz (LowerFopn (Ox86 (SAR sz)) [:: a ; b ] (Some U8)), LT_idseq LT_id)
    | Oeq (Op_w sz) => (k8 sz (LowerEq sz a b), LT_idseq LT_id)
    | Olt (Cmp_w Unsigned sz) => (k8 sz (LowerLt sz a b), LT_idseq LT_id)

    | Ovadd ve sz =>
      (kb (U128 <= sz)%CMP sz (LowerCopn (Ox86 (VPADD ve sz)) [::a; b]), LT_idseq LT_id)
    | Ovsub ve sz =>
      (kb (U128 <= sz)%CMP sz (LowerCopn (Ox86 (VPSUB ve sz)) [::a; b]), LT_idseq LT_id)
    | Ovmul ve sz =>
      (kb ((U32 <= ve) && (U128 <= sz))%CMP sz (LowerCopn (Ox86 (VPMULL ve sz)) [::a; b]), LT_idseq LT_id)
    | Ovlsl ve sz =>
      (kb ((U16 <= ve) && (U128 <= sz))%CMP sz (LowerCopn (Ox86 (VPSLL ve sz)) [::a; b]), LT_idseq LT_id)
    | Ovlsr ve sz =>
      (kb ((U16 <= ve) && (U128 <= sz))%CMP sz (LowerCopn (Ox86 (VPSRL ve sz)) [::a; b]), LT_idseq LT_id)
    | Ovasr ve sz =>
      (kb ((U16 <= ve) && (U128 <= sz))%CMP sz (LowerCopn (Ox86 (VPSRA ve sz)) [::a; b]), LT_idseq LT_id)

    | _ => (LowerAssgn, LT_idseq LT_id)
    end

  | Pif t e e1 e2 =>
    if stype_of_lval x is sword _ then
      (k16 (wsize_of_lval x) (LowerIf t e e1 e2), LT_idseq LT_id)
    else
      (LowerAssgn, LT_idseq LT_id)
  | _ => (LowerAssgn, LT_idseq LT_id)
  end.

Definition Lnone_b vi := Lnone vi sbool.

(* TODO: other sizes than U64 *)
(* TODO: remove dependent types *)
Variant opn_5flags_cases_t (a: pexprs) : Type :=
| Opn5f_large_immed x y (n: Z) z `(a = x :: y :: z) `(y = Papp1 (Oword_of_int U64) n)
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
    match is_wconst_of_size U64 y as u return is_reflect (λ z : Z, Papp1 (Oword_of_int U64) z) y u → _ with
    | None => λ _, Opn5f_other
    | Some n =>
      λ W,
      if check_signed_range m sz n
      then Opn5f_other
      else Opn5f_large_immed erefl (is_reflect_some_inv W)
    end%Z (is_wconst_of_sizeP U64 y)
  | _ => Opn5f_other end.

Definition opn_no_imm op :=
  match op with
  | Ox86 (IMULri sz) => Ox86 (IMULr sz)
  | _ => op
  end.

Definition opn_5flags (immed_bound: option wsize) (vi: var_info)
           (cf: lval) (x: lval) tg (o: sopn) (a: pexprs) : seq instr_r * leak_es_i_tr :=
  let f := Lnone_b vi in
  let fopn o a := [:: Copn [:: f ; cf ; f ; f ; f ; x ] tg o a ] in
  match opn_5flags_cases a immed_bound (wsize_of_sopn o) with
  | Opn5f_large_immed x y n z _ _ =>
    let c := {| v_var := {| vtype := sword U64; vname := fresh_multiplicand fv U64 |} ; v_info := vi |} in
    ((Copn [:: Lvar c ] tg (Ox86 (MOV U64)) [:: y] :: fopn (opn_no_imm o) (x :: Pvar c :: z)), LT_iopn5f_large)
  | Opn5f_other => (fopn o a, LT_iopn5f_other)
  end.

Definition reduce_wconst sz (e: pexpr) : pexpr :=
  if e is Papp1 (Oword_of_int sz') (Pconst z)
  then Papp1 (Oword_of_int (cmp_min sz sz')) (Pconst z)
  else e.


(** Need to fix this later: for now commenting it out **) 
Definition lower_cassgn (ii:instr_info) (x: lval) (tg: assgn_tag) (ty: stype) (e: pexpr) : cmd * leak_i_tr :=
  (* x = a == b *)
  (* LT_low_eq *)
  (* LSub[ lx; LSub[la; lb]] *)  
  (* _, _, _, _, x = CMP a b *)
  (* LSub[ LSub[ LEmpty; LEmpty; LEmpty; LEmpty; lx]; LSub[la; lb]] *)
  (* LT_map [ LT_seq [ LT_empty; LT_empty; LT_empty; LT_empty; LT_id ]
            LT_id;
            ] *)


  
  let vi := var_info_of_lval x in
  let f := Lnone_b vi in
  let copn o a := [:: MkI ii (Copn [:: x ] tg o a) ] in
  let inc o a := [:: MkI ii (Copn [:: f ; f ; f ; f ; x ] tg o [:: a ]) ] in
  let szty := wsize_of_stype ty in
  match lower_cassgn_classify szty e x with
  | (LowerMov b, lte) => 
    let e := reduce_wconst szty e in
    if b (*[:: Lopn (LSub [:: LSub [:: le]; LSub [:: LEmpty]]) ; Lopn (LSub [:: LSub [:: LEmpty]; LSub [:: lw]]) *)
    then
      let c := {| v_var := {| vtype := sword szty; vname := fresh_multiplicand fv szty |} ; v_info := vi |} in
      ([:: MkI ii (Copn [:: Lvar c] tg (Ox86 (MOV szty)) [:: e ])
       ; MkI ii (Copn [:: x ] tg (Ox86 (MOV szty)) [:: Pvar c ]) ], LT_ilmov1 (LT_subi 0) (LT_subi 1))
    else
      (* IF e is 0 then use Oset0 instruction *)
      if (e == @wconst szty 0) && ~~ is_lval_in_memory x && options.(use_set0) then
        if (szty <= U64)%CMP then
          ([:: MkI ii (Copn [:: f ; f ; f ; f ; f ; x] tg (Oset0 szty) [::]) ], LT_ilmov2 LT_id)
          (*[:: Lopn (LSub [:: LSub [::]; LSub[:: LEmpty; LEmpty; LEmpty; LEmpty; LEmpty; lw]])]*)
        else 
          ([:: MkI ii (Copn [:: x] tg (Oset0 szty) [::]) ], LT_ilmov3 LT_id) (* [:: Lopn (LSub [:: LSub [::]; LSub [:: lw]])] *)
      else (copn (Ox86 (MOV szty)) [:: e ], LT_ilmov4 (LT_subi 0) (LT_subi 1)) (* [:: Lopn (LSub [:: LSub [:: le]; LSub [:: lw]])] *)
  | (LowerCopn o e, lte) => (copn o e, LT_ilcopn lte (LT_subi 0) (LT_subi 1)) (* [:: Lopn (LSub [:: LSub (unzip2 vs) (* leakage due to exprs *); LSub [:: lw]])] *)
  | (LowerInc o e, lte) => (inc o e, LT_ilinc lte (LT_subi 0) (LT_subi 1)) (* [:: Lopn (LSub [:: LSub (unzip2 vs) (exprs) ; LSub[:: LEmpty; LEmpty; LEmpty; LEmpty; lw (* for x *)]])] *)
  | (LowerFopn o es m, lte) => (map (MkI ii) (opn_5flags m vi f x tg o es).1, LT_ilfopn (opn_5flags m vi f x tg o es).2 lte) (* need to figure out *)
  | (LowerLea sz (MkLea d b sc o), lte) => (* need to figure out *)
    let de := wconst d in
    let sce := wconst sc in
    let b := oapp Pvar (@wconst sz 0) b in
    let o := oapp Pvar (@wconst sz 0) o in
    let lea tt :=
      let ii := warning ii Use_lea in
      let add := Papp2 (Oadd (Op_w sz)) in
      let mul := Papp2 (Omul (Op_w sz)) in
      let e := add de (add b (mul sce o)) in
      [:: MkI ii (Copn [::x] tg (Ox86 (LEA sz)) [:: e])] in
    if options.(use_lea) then (lea tt,  LT_ilea) (* [:: Lopn (LSub [:: LSub (unzip2 (leak due to e); LSub [:: leak due to x]])] *)
    (* d + b + sc * o *)
    else
      if d == 0%R then
        (* b + sc * o *)
        if sc == 1%R then
          (* b + o *) (*[:: Lopn (LSub [:: LSub [:: lb; lo] ; 
                                               LSub [:: LEmpty; LEmpty; LEmpty; LEmpty; LEmpty; lx]])]*)
          ([::MkI ii (Copn [:: f ; f ; f ; f ; f; x ] tg (Ox86 (ADD sz)) [:: b ; o])], LT_ilsc)
        else if b == @wconst sz 0 then
          (* sc * o *)
          let (op, args) := mulr sz o sce in
          (*[:: Lopn (LSub [:: LSub (unzip2 leakage for args); 
                                     LSub [:: LEmpty; LEmpty; LEmpty; LEmpty; LEmpty; lw]])] *) (* opn_5flags_correct lemma *)
          (map (MkI ii) (opn_5flags (Some U32) vi f x tg (Ox86 op.1) op.2).1, LT_ilmul (opn_5flags (Some U32) vi f x tg (Ox86 op.1) op.2).2 args)
        else (lea tt,  LT_ilea) (* [:: Lopn (LSub [:: LSub (unzip2 rs) ; LSub [::lw]])] *)
      else if o == @wconst sz 0 then
          (* d + b *)
          if d == 1%R then (inc (Ox86 (INC sz)) b, LT_ild) (* [:: Lopn (LSub [:: LSub [:: vbl] ; LSub [:: LEmpty; LEmpty; LEmpty; LEmpty; lw]])]. *)
          else
            let w := wunsigned d in
            if check_signed_range (Some U32) sz w
            (* [:: Lopn (LSub [:: LSub [:: vbl; LEmpty] ; 
                                     LSub [:: LEmpty; LEmpty; LEmpty; LEmpty; LEmpty; lw]])] *)
            then ([::MkI ii (Copn [:: f ; f ; f ; f ; f; x ] tg (Ox86 (ADD sz)) [:: b ; de ])], LT_ildc)
            else if w == (wbase U32 / 2)%Z
            (* [:: Lopn (LSub [:: LSub [:: vbl; LEmpty] ; 
                                     LSub [:: LEmpty; LEmpty; LEmpty; LEmpty; LEmpty; lw]])] *)
            then ([::MkI ii (Copn [:: f ; f ; f ; f ; f; x ] tg (Ox86 (SUB sz)) [:: b ; wconst (wrepr sz (-w)) ])], LT_ildc)
            else
            (*[:: Lopn (LSub [:: LSub [:: LEmpty]; LSub [:: LEmpty]]);
                             Lopn (LSub [:: LSub [:: vbl; LEmpty]; 
                                            LSub [:: LEmpty; LEmpty; LEmpty; LEmpty; LEmpty; lw]])]*)
              let c := {| v_var := {| vtype := sword U64; vname := fresh_multiplicand fv U64 |} ; v_info := vi |} in
              ([:: MkI ii (Copn [:: Lvar c ] tg (Ox86 (MOV U64)) [:: de]);
                 MkI ii (Copn [:: f ; f ; f ; f ; f; x ] tg (Ox86 (ADD sz)) [:: b ; Pvar c ])], LT_ildcn)
      else (lea tt,  LT_ilea) (* [:: Lopn (LSub [:: LSub (unzip2 rs) ; LSub [::lw]])] *)
  (* [:: Lopn (LSub [:: LSub (unzip2 vs) (a and b) ; LSub[:: LEmpty; LEmpty; LEmpty; LEmpty; lw (* for x *)]])] *)
  (* x = a == b *)
  | (LowerEq sz a b, lte) => ([:: MkI ii (Copn [:: f ; f ; f ; f ; x ] tg (Ox86 (CMP sz)) [:: a ; b ]) ], LT_ileq lte (LT_subi 0) (LT_subi 1))
  (* [:: Lopn (LSub [:: LSub (unzip2 vs) (a and b) ; LSub[:: LEmpty; lw (* for x *) ; LEmpty; LEmpty; LEmpty]])] *)
  | (LowerLt sz a b, lte) => ([:: MkI ii (Copn [:: f ; x ; f ; f ; f ] tg (Ox86 (CMP sz)) [:: a ; b ]) ], LT_illt lte (LT_subi 0) (LT_subi 1))
  (* [:: Lopn (LSub [:: lb; LSub [:: LEmpty; LEmpty; LEmpty; LEmpty; LEmpty]])] (* produced by lower_condition *) ++ 
     [:: Lopn (LSub [:: LSub [:: le'; l1; l2] ; LSub[:: lw]])] *)
  | (LowerIf t e e1 e2, lte) =>
     (* x = if e then e1 else e2 *)
     (*   lx = Lsub[le; le1; le2] *)
     (* flags = CMP ? ?;
        x = CMOVcc [ cond flags; e1; e2]
     *)
     let (l, e) := lower_condition vi e in
     let sz := wsize_of_lval x in
     ((map (MkI ii) (l.1 ++ [:: Copn [:: x] tg (Ox86 (CMOVcc sz)) [:: e.1; e1; e2]])), 
      LT_ilif l.2 e.2 (LT_subi 0) (LT_subi 1) (LT_subi 2))
  | (LowerDivMod p s sz op a b, lte) =>
    let c := {| v_var := {| vtype := sword sz; vname := fresh_multiplicand fv sz |} ; v_info := vi |} in
    let lv :=
      match p with
      | DM_Fst => ([:: f ; f ; f ; f ; f; x; Lnone vi (sword sz)], LT_dfst) (* LSub [:: LEmpty; LEmpty; LEmpty; LEmpty; LEmpty; lx; LEmpty] *)
      | DM_Snd => ([:: f ; f ; f ; f ; f; Lnone vi (sword sz) ; x], LT_dsnd) (* LSub [:: LEmpty; LEmpty; LEmpty; LEmpty; LEmpty; LEmpty; LEmpty] *)
      end in
    let i1 :=
      match s with
      | Signed => (Copn [:: Lvar c ] tg (Ox86 (CQO sz)) [:: a], LT_ilds) (* Lopn (LSub [:: LSub [:: la]; LSub [:: LEmpty]]) *) 
      | Unsigned => (Copn [:: Lvar c ] tg (Ox86 (MOV sz)) [:: Papp1 (Oword_of_int sz) (Pconst 0)], LT_ildus)
        (* Lopn (LSub [:: LSub [:: LEmpty]; LSub [:: LEmpty]]) *) 
      end in
    (* [:: leak for i1; Lopn (LSub [:: LSub [:: LEmpty; la ; lb] ; LSub lv.2]) *)
    ([::MkI ii i1.1; MkI ii (Copn lv.1 tg op [::Pvar c; a; b]) ], LT_ildiv i1.2 lv.2)

  | (LowerAssgn, lte) => ([::  MkI ii (Cassgn x tg ty e)], LT_ilasgn) (*[:: Lopn (LSub [:: le; lx])]*)
  end.

(* Lowering of Oaddcarry
… = #addc(x, y, false) → ADD(x, y)
… = #addc(?, ?, true) → #error
… = #addc(?, ?, c) → ADC
*)

Definition lower_addcarry_classify (sub: bool) (xs: lvals) (es: pexprs) : option (var_info * (wsize → asm_op) * pexprs * lval * lval) :=
  match xs, es with
  | [:: cf ; r ], [:: x ; y ; Pbool false ] =>
    let vi := var_info_of_lval r in
    Some (vi, if sub then SUB else ADD, [:: x ; y ], cf, r)
  | [:: cf ; r ], [:: _ ; _ ; Pvar cfi ] =>
    let vi := v_info cfi in
    Some (vi, (if sub then SBB else ADC), es, cf, r)
  | _, _ => None
  end.

Definition lower_addcarry sz (sub: bool) (xs: lvals) tg (es: pexprs) : seq instr_r * leak_es_i_tr :=
  if (sz ≤ U64)%CMP then
  match lower_addcarry_classify sub xs es with
  | Some (vi, o, es, cf, r) => opn_5flags (Some U32) vi cf r tg (Ox86 (o sz)) es (*  [:: Lopn (LSub [:: LSub (unzip2 leakage of es); LSub l1''])] *)
  | None => ([:: Copn xs tg ((if sub then Osubcarry else Oaddcarry) sz) es ], LT_ianone)  (* [:: Lopn (LSub [:: LSub (unzip2 leakage of es); LSub (leakage for xs)])]*)
  end
  else ([:: Copn xs tg ((if sub then Osubcarry else Oaddcarry) sz) es ], LT_ianone).

Definition lower_mulu sz (xs: lvals) tg (es: pexprs) : seq instr_r * leak_es_i_tr :=
  if check_size_16_64 sz is Ok _ then
  match xs, es with
  | [:: r1; r2 ], [:: x ; y ] =>
    let vi := var_info_of_lval r2 in
    let f := Lnone_b vi in
    match is_wconst sz x with
    | Some _ =>
      let c := {| v_var := {| vtype := sword sz; vname := fresh_multiplicand fv sz |} ; v_info := vi |} in
      ([:: Copn [:: Lvar c ] tg (Ox86 (MOV sz)) [:: x ] ;
          Copn [:: f ; f ; f ; f ; f ; r1 ; r2 ] tg (Ox86 (MUL sz)) [:: y ; Pvar c ] ], LT_imul1)
      (*  [:: Lopn (LSub [:: LSub [:: le1]; LSub [:: LEmpty]]);
              Lopn (LSub [:: LSub [:: le2; LEmpty]; LSub [:: LEmpty; LEmpty; LEmpty; LEmpty; LEmpty; yl; yl'']])] *)
    | None =>
    match is_wconst sz y with
    | Some _ =>
      let c := {| v_var := {| vtype := sword sz; vname := fresh_multiplicand fv sz |} ; v_info := vi |} in
      ([:: Copn [:: Lvar c ] tg (Ox86 (MOV sz)) [:: y ] ;
          Copn [:: f ; f ; f ; f ; f ; r1 ; r2 ] tg (Ox86 (MUL sz)) [:: x ; Pvar c ] ], LT_imul2)
     (* [:: Lopn (LSub [:: LSub [:: le2]; LSub [:: LEmpty]]); 
            Lopn (LSub [:: LSub [:: le1; LEmpty]; LSub [:: LEmpty; LEmpty; LEmpty; LEmpty; LEmpty; yl; yl'']])]*)
    | None => ([:: Copn [:: f ; f ; f ; f ; f ; r1 ; r2 ] tg (Ox86 (MUL sz)) es ], LT_imul3)
              (* [:: Lopn (LSub [:: LSub [:: le1; le2]; LSub [:: LEmpty; LEmpty; LEmpty; LEmpty; LEmpty; yl; yl'']])] *)
    end end
  | _, _ => ([:: Copn xs tg (Omulu sz) es ], LT_imul4)
  end
  else ([:: Copn xs tg (Omulu sz) es ], LT_imul4).  (* [:: Lopn (LSub [:: LSub (unzip2 vs); LSub l1''])] *)

Definition lower_copn (xs: lvals) tg (op: sopn) (es: pexprs) : seq instr_r * leak_es_i_tr :=
  match op with
  | Oaddcarry sz => lower_addcarry sz false xs tg es
  | Osubcarry sz => lower_addcarry sz true xs tg es
  | Omulu sz     => lower_mulu sz xs tg es
  | _            => ([:: Copn xs tg op es], LT_imul4)
  end.



Definition lower_cmd (lower_i: instr -> cmd * leak_i_tr) (c:cmd) : cmd * leak_c_tr :=
 List.fold_right (fun i c' => let r := lower_i i in
                               ((r.1 ++ c'.1), ([:: r.2] ++ c'.2)))
                      ([::], [::]) c.

(*Definition lower_cmd (lower_i: instr -> cmd) (c:cmd) : cmd :=
  List.fold_right (fun i c' => lower_i i ++ c') [::] c.*)

Fixpoint lower_i (i:instr) : cmd * leak_i_tr :=
  let (ii, ir) := i in
  match ir with
  | Cassgn l tg ty e => lower_cassgn ii l tg ty e 
  | Copn l t o e =>   (map (MkI ii) (lower_copn l t o e).1, LT_icopn (lower_copn l t o e).2) (* need to fix this *)
  | Cif e c1 c2  =>
     let '(pre, e) := lower_condition xH e in
     let rc1 := lower_cmd lower_i c1 in 
     let rc2 := lower_cmd lower_i c2 in
       (map (MkI ii) (rcons pre.1 (Cif e.1 rc1.1 rc2.1)), LT_icondl pre.2 e.2 rc1.2 rc2.2)
  | Cfor v (d, lo, hi) c =>
     let rc := (lower_cmd lower_i c) in 
     ([:: MkI ii (Cfor v (d, lo, hi) rc.1)], LT_ifor LT_id rc.2)
  | Cwhile a c e c' =>
     let '(pre, e) := lower_condition xH e in
     let rc := lower_cmd lower_i c in 
     let rc' := lower_cmd lower_i c' in 
       (map (MkI ii) [:: Cwhile a (rc.1 ++ map (MkI xH) pre.1) e.1 rc'.1], LT_iwhilel pre.2 e.2 rc.2 rc'.2)
  | _ =>   (map (MkI ii) [:: ir], LT_icall LT_id LT_id)
  end.

Definition lower_fd (fd: fundef) : fundef * leak_c_tr :=
let r := lower_cmd lower_i (f_body fd) in 
  ({| f_iinfo := f_iinfo fd;
     f_tyin := f_tyin fd;
     f_params := f_params fd;
     f_body := r.1;
     f_tyout := f_tyout fd;
     f_res := f_res fd
  |}, r.2).

Definition lower_prog (p: prog) : (prog * leak_f_tr) := 
let r := map_prog_leak lower_fd (p_funcs p) in 
({| p_globs := p_globs p; p_funcs := r.1|}, r.2).

End LOWERING.
