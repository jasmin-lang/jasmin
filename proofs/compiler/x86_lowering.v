From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssralg.
From mathcomp Require Import word_ssrZ.
Require Import Utf8.
Require Import
  compiler_util
  expr
  lowering
  lea
  pseudo_operator.
Require Import x86_decl x86_instr_decl x86_extra.

Section Section.

Context {atoI : arch_toIdent}.

Definition is_regx_e (e:pexpr) := 
  if e is Pvar x then is_regx x.(gv)
  else false.

Definition is_regx_l (x:lval) := 
  if x is Lvar x then is_regx x
  else false.

Definition mov_ws ws x y tag :=
  if (is_regx_e y || is_regx_l x) && (U32 ≤ ws)%CMP then 
    Copn [:: x] tag (Ox86 (MOVX ws)) [:: y]
  else
    Copn [:: x] tag (Ox86 (MOV ws)) [:: y].

Section LOWERING.

Record lowering_options : Type :=
  {
    use_lea  : bool;
    use_set0 : bool;
  }.

Context (options : lowering_options).

Context (warning: instr_info -> warning_msg -> instr_info).

Definition vword vt vn := {| vtype := sword vt ; vname := vn |}.

Context (fv: fresh_vars).

Let fresh_flag n := vbool (fv n sbool).
Let fresh_word sz := vword sz (fv "__wtmp__"%string (sword sz)).

Definition fv_of := fresh_flag "__of__".
Definition fv_cf := fresh_flag "__cf__".
Definition fv_sf := fresh_flag "__sf__".
Definition fv_zf := fresh_flag "__zf__".

Definition fvars :=
  foldl (λ s sz, Sv.add (fresh_word sz) s)
    (Sv.add fv_of (Sv.add fv_cf (Sv.add fv_sf (Sv.singleton fv_zf))))
    wsizes.

Definition disj_fvars v := disjoint v fvars.

Context {pT: progT}.

Definition fvars_correct p :=
  [&& disj_fvars (vars_p p),
      fv_of != fv_cf,
      fv_of != fv_sf,
      fv_of != fv_zf,
      fv_cf != fv_sf,
      fv_cf != fv_zf &
      fv_sf != fv_zf].

Definition stype_of_lval (x: lval) : stype :=
  match x with
  | Lnone _ t => t
  | Lvar v | Lmem _ _ v _ | Laset _ _ _ v _ | Lasub _ _ _ v _ => v.(vtype)
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
  | Laset _ _ sz _ _ | Lmem _ sz _ _ => sz
  | Lasub _ _ _ _ _ => U64
  end.

Definition lower_cond_classify vi (e: pexpr) :=
  let fr n := {| v_var := n ; v_info := vi |} in
  let vof := fr fv_of in
  let vcf := fr fv_cf in
  let vsf := fr fv_sf in
  let vzf := fr fv_zf in
  let vflags := map v_var [:: vof; vcf; vsf; vzf ] in

  let lof := Lvar vof in
  let lcf := Lvar vcf in
  let lsf := Lvar vsf in
  let lzf := Lvar vzf in
  let lflags := [:: lof; lcf; lsf; Lnone_b vi; lzf ] in

  let%opt (op, e0, e1) := is_Papp2 e in
  let%opt (cf, ws) := cf_of_condition op in
  Some (lflags, ws, pexpr_of_cf cf vi vflags, e0, e1).

Definition lower_condition vi (pe: pexpr) : seq instr_r * pexpr :=
  match lower_cond_classify vi pe with
  | Some (l, sz, r, x, y) =>
    if (sz ≤ U64)%CMP then
    ([:: Copn l AT_none (Ox86 (CMP sz)) [:: x; y] ], r)
    else ([::], pe)
  | None => ([::], pe)
  end.

(* Lowering of Cassgn *)

Variant add_inc_dec : Type :=
  | AddInc of pexpr
  | AddDec of pexpr
  | AddNone.

Definition add_inc_dec_classify (sz: wsize) (a: pexpr) (b: pexpr) :=
  match a, b with
  | Papp1 (Oword_of_int w) (Pconst 1), y | y, Papp1 (Oword_of_int w) (Pconst 1) =>
    if w == sz then AddInc y else AddNone
  | Papp1 (Oword_of_int w) (Pconst (-1)), y | y, Papp1 (Oword_of_int w) (Pconst (-1)) =>
    if w == sz then AddDec y else AddNone
  | _, _ => AddNone
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
Variant divmod_pos :=
  | DM_Fst
  | DM_Snd.

Variant lower_cassgn_t : Type :=
  | LowerMov of bool (* whether it needs a intermediate register *)
  | LowerCopn of sopn & list pexpr
  | LowerInc  of sopn & pexpr
  | LowerLea of wsize & lea
  | LowerFopn of wsize & sopn & list pexpr & option wsize
  | LowerDiscardFlags of nat & sopn & list pexpr
  | LowerCond
  | LowerIf   of stype & pexpr & pexpr & pexpr
  | LowerDivMod of divmod_pos & signedness & wsize & sopn & pexpr & pexpr
  | LowerConcat of pexpr & pexpr
  | LowerAssgn.

(* -------------------------------------------------------------------- *)

Definition is_lea sz x e :=
  let%opt _ :=
    oassert [&& (U16 ≤ sz)%CMP, (sz ≤ U64)%CMP & ~~ is_lval_in_memory x ]
  in
  let%opt MkLea d b sc o := mk_lea sz e in
  let check o := if o is Some x then ~~ is_var_in_memory x.(v_var) else true in
  (* FIXME: check that d is not to big *)
  let%opt _ := oassert [&& check_scale sc, check b & check o ] in
  Some (MkLea d b sc o).

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
  | Some _ => (IMULri sz, [:: b ; a ])
  | _      =>
    match is_wconst sz b with
    | Some _ => (IMULri sz, [:: a ; b ])
    | _      => (IMULr sz,  [:: a ; b ])
    end
 end.

  Definition check_shift_amount sz e :=
    if is_wconst U8 e is Some n
    then if n == wand n (x86_shift_mask sz) then Some e else None
    else match e with
    | Papp2 (Oland _) a b =>
        if is_wconst U8 b is Some n
        then if n == x86_shift_mask sz then Some a else None
        else None
    | _ => None end.

Definition check_signed_range (m: option wsize) sz' (n: Z) : bool :=
  if m is Some ws then (
      let z := wsigned (wrepr sz' n) in
      let h := wmin_signed ws in
      if h <=? z then z <? -h else false)%Z
  else false.

(* x =(ty) e *)
Definition lower_cassgn_classify ty e x : lower_cassgn_t :=
  let chk (b: bool) r := if b then r else LowerAssgn in
  let kb b sz := chk (b && (sword sz == ty)) in
  let k8 sz := kb (sz ≤ U64)%CMP sz in
  let k16 sz := kb ((U16 ≤ sz) && (sz ≤ U64))%CMP sz in
  let k32 sz := kb ((U32 ≤ sz) && (sz ≤ U64))%CMP sz in
  match e with
  | Pget _ _ sz {| gv := v |} _
  | Pvar {| gv := ({| v_var := {| vtype := sword sz |} |} as v) |} =>
    if (sz ≤ U64)%CMP
    then LowerMov (if is_var_in_memory v then is_lval_in_memory x else false)
    else if ty is sword szo
    then if (U128 ≤ szo)%CMP then LowerCopn (Ox86 (VMOVDQU szo)) [:: e ]
    else if (U32 ≤ szo)%CMP then LowerCopn (Ox86 (MOVV szo)) [:: e ]
    else LowerAssgn
    else LowerAssgn
  | Pload _ sz _ _ =>
      if (sz ≤ U64)%CMP
      then LowerMov (is_lval_in_memory x)
      else kb true sz (LowerCopn (Ox86 (VMOVDQU sz)) [:: e ])

  | Papp1 (Oword_of_int sz) (Pconst z) =>
      if ty is sword sz' then
        chk (sz' ≤ U64)%CMP
          (LowerMov (~~ check_signed_range (Some (cmp_min U32 sz')) sz z))
      else LowerAssgn
  | Papp1 (Olnot sz) a => k8 sz (LowerCopn (Ox86 (NOT sz)) [:: a ])
  | Papp1 (Oneg (Op_w sz)) a => k8 sz (LowerFopn sz (Ox86 (NEG sz)) [:: a] None)
  | Papp1 (Osignext szo szi) a =>
    match szi with
    | U8 => k16 szo
    | U16 => k16 szo
    | U32 => k32 szo
    | _ => chk false
    end (LowerCopn (Ox86 (MOVSX szo szi)) [:: a])
  | Papp1 (Ozeroext szo szi) a =>
    match szi with
    | U8 => k16 szo (LowerCopn (Ox86 (MOVZX szo szi)) [:: a])
    | U16 => k32 szo (LowerCopn (Ox86 (MOVZX szo szi)) [:: a])
    | U32 =>
        match szo with
        | U64 => kb true szo (LowerCopn (Oasm (ExtOp Ox86MOVZX32)) [:: a])
        | U128 => kb true szo (LowerCopn (Ox86 (MOVD szi)) [:: a])
        | U256 => kb true szo (LowerCopn (Oasm (BaseOp (Some szo, VMOV szi))) [:: a])
        | _ => LowerAssgn
        end
    | U64 =>
        match szo with
        | U128 => kb true szo (LowerCopn (Ox86 (MOVD szi)) [:: a])
        | U256 => kb true szo (LowerCopn (Oasm (BaseOp (Some szo, VMOV szi))) [:: a])
        | _ => LowerAssgn
        end
    | _ => LowerAssgn
    end

  | Papp2 op a b =>
    match op with
    | Oadd (Op_w sz) =>
      k8 sz
      match is_lea sz x e with
      | Some l => LowerLea sz l
      | None   =>
        match add_inc_dec_classify sz a b with
        | AddInc y => LowerInc (Ox86 (INC sz)) y
        | AddDec y => LowerInc (Ox86 (DEC sz)) y
        | AddNone  => LowerFopn sz (Ox86 (ADD sz)) [:: a ; b ] (Some U32)
        end
      end
    | Osub (Op_w sz) =>
      k8 sz
      match is_lea sz x e with
      | Some l => LowerLea sz l
      | None   =>
        match sub_inc_dec_classify sz b with
        | SubInc => LowerInc (Ox86 (INC sz)) a
        | SubDec => LowerInc (Ox86 (DEC sz)) a
        | SubNone => LowerFopn sz (Ox86 (SUB sz)) [:: a ; b ] (Some U32)
        end
      end
    | Omul (Op_w sz) =>
      k16 sz
      match is_lea sz x e with
      | Some l => LowerLea sz l
      | _      =>
        let (op, args) := mulr sz a b in
        LowerFopn sz (Ox86 op) args (Some U32)
      end
    | Odiv (Cmp_w u sz) =>
      let opn :=
        match u with
        | Unsigned => Ox86 (DIV sz)
        | Signed   => Ox86 (IDIV sz)
        end in
      k16 sz (LowerDivMod DM_Fst u sz opn a b)

    | Omod (Cmp_w u sz) =>
       let opn :=
        match u with
        | Unsigned => Ox86 (DIV sz)
        | Signed   => Ox86 (IDIV sz)
        end in
      k16 sz (LowerDivMod DM_Snd u sz opn a b)

    | Oland sz =>
      match is_andn a b with
      | Some (a,b) =>
        if (sz ≤ U64)%CMP
        then k32 sz (LowerFopn sz (Ox86 (ANDN sz)) [:: a ; b ] None)
        else kb true sz (LowerCopn (Ox86 (VPANDN sz)) [:: a ; b ])
      | None =>
        if (sz ≤ U64)%CMP
        then k8 sz (LowerFopn sz (Ox86 (AND sz)) [:: a ; b ] (Some U32))
        else kb true sz (LowerCopn (Ox86 (VPAND sz)) [:: a ; b ])
      end


    | Olor sz =>
      if (sz ≤ U64)%CMP
      then k8 sz (LowerFopn sz (Ox86 (OR sz)) [:: a ; b ] (Some U32))
      else kb true sz (LowerCopn (Ox86 (VPOR sz)) [:: a ; b ])
    | Olxor sz =>
      if (sz ≤ U64)%CMP
      then k8 sz (LowerFopn sz (Ox86 (XOR sz)) [:: a ; b ] (Some U32))
      else kb true sz (LowerCopn (Ox86 (VPXOR sz)) [:: a ; b ])
    | Olsr sz => if check_shift_amount sz b is Some b then k8 sz (LowerFopn sz (Ox86 (SHR sz)) [:: a ; b ] (Some U8)) else LowerAssgn
    | Olsl (Op_w sz) => if check_shift_amount sz b is Some b then k8 sz (LowerFopn sz (Ox86 (SHL sz)) [:: a ; b ] (Some U8)) else LowerAssgn
    | Oasr (Op_w sz) => if check_shift_amount sz b is Some b then k8 sz (LowerFopn sz (Ox86 (SAR sz)) [:: a ; b ] (Some U8)) else LowerAssgn
    | Oror sz => if check_shift_amount sz b is Some b then k8 sz (LowerDiscardFlags 2 (Ox86 (ROR sz)) [:: a ; b ]) else LowerAssgn
    | Orol sz => if check_shift_amount sz b is Some b then k8 sz (LowerDiscardFlags 2 (Ox86 (ROL sz)) [:: a ; b ]) else LowerAssgn

    | Olt _ | Ole _ | Oeq _ | Oneq _ | Oge _ | Ogt _ => LowerCond

    | Ovadd ve sz =>
      kb (U128 <= sz)%CMP sz (LowerCopn (Ox86 (VPADD ve sz)) [::a; b])
    | Ovsub ve sz =>
      kb (U128 <= sz)%CMP sz (LowerCopn (Ox86 (VPSUB ve sz)) [::a; b])
    | Ovmul ve sz =>
      kb ((U16 ≤ ve) && (wsize_of_velem ve ≤ U32) && (U128 <= sz))%CMP sz (LowerCopn (Ox86 (VPMULL ve sz)) [::a; b])
    | Ovlsl ve sz =>
      kb ((U16 <= ve) && (U128 <= sz))%CMP sz (LowerCopn (Ox86 (VPSLL ve sz)) [::a; b])
    | Ovlsr ve sz =>
      kb ((U16 <= ve) && (U128 <= sz))%CMP sz (LowerCopn (Ox86 (VPSRL ve sz)) [::a; b])
    | Ovasr ve sz =>
      kb ((U16 <= ve) && (U128 <= sz))%CMP sz (LowerCopn (Ox86 (VPSRA ve sz)) [::a; b])

    | _ => LowerAssgn
    end

  | Pif t e e1 e2 =>
    if stype_of_lval x is sword _ then
      k16 (wsize_of_lval x) (LowerIf t e e1 e2)
    else
      LowerAssgn

  | PappN (Opack U256 PE128) [:: Papp1 (Oint_of_word U128) h ; Papp1 (Oint_of_word U128) (Pvar _ as l) ] =>
    if ty == sword U256 then LowerConcat h l else LowerAssgn

  | _ => LowerAssgn
  end.

(* TODO: other sizes than U64 *)
Variant opn_5flags_cases_t : Type :=
| Opn5f_large_immed : pexpr -> pexpr -> pexprs -> opn_5flags_cases_t
| Opn5f_other : opn_5flags_cases_t.

Definition opn_5flags_cases (a: pexprs) (m: option wsize) (sz: wsize) : opn_5flags_cases_t :=
  match a with
  | x :: y :: z =>
    match is_wconst_of_size U64 y with
    | None => Opn5f_other
    | Some n =>
      if check_signed_range m sz n
      then Opn5f_other
      else Opn5f_large_immed x y z
    end
  | _ => Opn5f_other end.

Definition opn_no_imm op :=
  match op with
  | Oasm (BaseOp (ws, IMULri sz)) => Oasm (BaseOp (ws, IMULr sz))
  | _ => op
  end.

Definition opn_5flags (immed_bound: option wsize) (sopn_wsize: wsize) (vi: var_info)
           (cf: lval) (x: lval) tg (o: sopn) (a: pexprs) : seq instr_r :=
  let f := Lnone_b vi in
  let fopn o a := [:: Copn [:: f ; cf ; f ; f ; f ; x ] tg o a ] in
  match opn_5flags_cases a immed_bound sopn_wsize with
  | Opn5f_large_immed x y z =>
    let c := {| v_var := fresh_word U64 ; v_info := vi |} in
    Copn [:: Lvar c ] tg (Ox86 (MOV U64)) [:: y] :: fopn (opn_no_imm o) (x :: Plvar c :: z)
  | Opn5f_other => fopn o a
  end.

Definition reduce_wconst sz (e: pexpr) : pexpr :=
  if e is Papp1 (Oword_of_int sz') (Pconst z)
  then Papp1 (Oword_of_int (cmp_min sz sz')) (Pconst z)
  else e.

Definition lower_cassgn (ii:instr_info) (x: lval) (tg: assgn_tag) (ty: stype) (e: pexpr) : cmd :=
  let vi := var_info_of_lval x in
  let f := Lnone_b vi in
  let copn o a := [:: MkI ii (Copn [:: x ] tg o a) ] in
  let inc o a := [:: MkI ii (Copn [:: f ; f ; f ; f ; x ] tg o [:: a ]) ] in
  match lower_cassgn_classify ty e x with
  | LowerMov b =>
    let szty := wsize_of_stype ty in
    let e := reduce_wconst szty e in
    if b
    then
      let c := {| v_var := fresh_word szty ; v_info := vi |} in
      [:: MkI ii (Copn [:: Lvar c] tg (Ox86 (MOV szty)) [:: e ])
       ; MkI ii (Copn [:: x ] tg (Ox86 (MOV szty)) [:: Plvar c ]) ]
    else
      (* IF e is 0 then use Oset0 instruction *)
      if (is_zero szty e) && ~~ is_lval_in_memory x && options.(use_set0) then
        if (szty <= U64)%CMP then
          [:: MkI ii (Copn [:: f ; f ; f ; f ; f ; x] tg (Oasm (ExtOp (Oset0 szty))) [::]) ]
        else
          [:: MkI ii (Copn [:: x] tg (Oasm (ExtOp (Oset0 szty))) [::]) ]
      else 
        [:: MkI ii (mov_ws szty x e tg)]
  | LowerCopn o e => copn o e
  | LowerInc o e => inc o e
  | LowerFopn sz o es m => map (MkI ii) (opn_5flags m sz vi f x tg o es)
  | LowerDiscardFlags n op es =>
      let lvs := nseq n (Lnone_b vi) in
      [:: MkI ii (Copn (lvs ++ [:: x ]) tg op es) ]
  | LowerLea sz (MkLea d b sc o) =>
    let de := wconst (wrepr Uptr d) in
    let sce := wconst (wrepr Uptr sc) in
    let b := oapp Plvar (@wconst sz 0) b in
    let o := oapp Plvar (@wconst sz 0) o in
    let lea tt :=
      let ii := warning ii Use_lea in
      let add := Papp2 (Oadd (Op_w sz)) in
      let mul := Papp2 (Omul (Op_w sz)) in
      let e := add de (add b (mul sce o)) in
      [:: MkI ii (Copn [::x] tg (Ox86 (LEA sz)) [:: e])] in
    if options.(use_lea) then lea tt
    (* d + b + sc * o *)
    else
      if d == 0%R then
        (* b + sc * o *)
        if sc == 1%R then
          (* b + o *)
          [::MkI ii (Copn [:: f ; f ; f ; f ; f; x ] tg (Ox86 (ADD sz)) [:: b ; o])]
        else if is_zero sz b then
          (* sc * o *)
          let (op, args) := mulr sz o sce in
          map (MkI ii) (opn_5flags (Some U32) sz vi f x tg (Ox86 op) args)
        else lea tt
      else if is_zero sz o then
          (* d + b *)
          if d == 1%Z then inc (Ox86 (INC sz)) b
          else
            if check_signed_range (Some U32) sz d
            then [::MkI ii (Copn [:: f ; f ; f ; f ; f; x ] tg (Ox86 (ADD sz)) [:: b ; de ])]
            else if d == (wbase U32 / 2)%Z
            then [::MkI ii (Copn [:: f ; f ; f ; f ; f; x ] tg (Ox86 (SUB sz)) [:: b ; wconst (wrepr sz (-d)) ])]
            else
              let c := {| v_var := fresh_word U64 ; v_info := vi |} in
              [:: MkI ii (Copn [:: Lvar c ] tg (Ox86 (MOV U64)) [:: de]);
                 MkI ii (Copn [:: f ; f ; f ; f ; f; x ] tg (Ox86 (ADD sz)) [:: b ; Plvar c ])]
      else lea tt

  | LowerCond =>
    let (i,e') := lower_condition vi e in
    map (MkI ii) (i ++ [::Cassgn x AT_inline ty e'])

  | LowerIf t e e1 e2 =>
     let (l, e) := lower_condition vi e in
     let sz := wsize_of_lval x in
     map (MkI ii) (l ++ [:: Copn [:: x] tg (Ox86 (CMOVcc sz)) [:: e; e1; e2]])

  | LowerDivMod p s sz op a b =>
    let c := {| v_var := fresh_word sz ; v_info := vi |} in
    let lv :=
      match p with
      | DM_Fst => [:: f ; f ; f ; f ; f; x; Lnone vi (sword sz)]
      | DM_Snd => [:: f ; f ; f ; f ; f; Lnone vi (sword sz) ; x]
      end in
    let i1 :=
      match s with
      | Signed => Copn [:: Lvar c ] tg (Ox86 (CQO sz)) [:: a]
      | Unsigned => Copn [:: f ; f ; f ; f ; f ; Lvar c ] tg (Oasm (ExtOp (Oset0 sz))) [::]
      end in

    [::MkI ii i1; MkI ii (Copn lv tg op [::Plvar c; a; b]) ]

  | LowerConcat h l =>
    [:: MkI ii (Copn [:: x ] tg (Oasm (ExtOp Oconcat128)) [:: h ; l ]) ]

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
    Some (vi, if sub then SUB else ADD, [:: x ; y ], cf, r)
  | [:: cf ; r ], [:: _ ; _ ; Pvar {| gv := cfi; gs := Slocal |} ] =>
    let vi := v_info cfi in
    Some (vi, (if sub then SBB else ADC), es, cf, r)
  | _, _ => None
  end.

Definition lower_addcarry sz (sub: bool) (xs: lvals) tg (es: pexprs) : seq instr_r :=
  let op := if sub then sopn_subcarry else sopn_addcarry in
  if (sz ≤ U64)%CMP then
  match lower_addcarry_classify sub xs es with
  | Some (vi, o, es, cf, r) => opn_5flags (Some U32) sz vi cf r tg (Ox86 (o sz)) es
  | None => [:: Copn xs tg (op sz) es ]
  end
  else [:: Copn xs tg (op sz) es ].

Definition lower_mulu sz (xs: lvals) tg (es: pexprs) : seq instr_r :=
  if check_size_16_64 sz is Ok _ then
  match xs, es with
  | [:: r1; r2 ], [:: x ; y ] =>
    let vi := var_info_of_lval r2 in
    let f := Lnone_b vi in
    match is_wconst sz x with
    | Some _ =>
      let c := {| v_var := fresh_word sz ; v_info := vi |} in
      [:: Copn [:: Lvar c ] tg (Ox86 (MOV sz)) [:: x ] ;
          Copn [:: f ; f ; f ; f ; f ; r1 ; r2 ] tg (Ox86 (MUL sz)) [:: y ; Plvar c ] ]
    | None =>
    match is_wconst sz y with
    | Some _ =>
      let c := {| v_var := fresh_word sz ; v_info := vi |} in
      [:: Copn [:: Lvar c ] tg (Ox86 (MOV sz)) [:: y ] ;
          Copn [:: f ; f ; f ; f ; f ; r1 ; r2 ] tg (Ox86 (MUL sz)) [:: x ; Plvar c ] ]
    | None => [:: Copn [:: f ; f ; f ; f ; f ; r1 ; r2 ] tg (Ox86 (MUL sz)) es ]
    end end
  | _, _ => [:: Copn xs tg (sopn_mulu sz) es ]
  end
  else [:: Copn xs tg (sopn_mulu sz) es ].


Definition lower_swap ty (xs: lvals) tg (es: pexprs) : seq instr_r :=
  if is_word_type ty is Some sz then
    if (sz <= U64)%CMP then [:: Copn xs tg (Ox86 (XCHG sz)) es]
    else [:: Copn xs tg (Opseudo_op (Oswap ty)) es]
  else [:: Copn xs tg (Opseudo_op (Oswap ty)) es].

Definition lower_pseudo_operator
  (xs : lvals)
  (tg : assgn_tag)
  (op : pseudo_operator)
  (es : pexprs) :
  seq instr_r :=
  match op with
  | Oaddcarry sz => lower_addcarry sz false xs tg es
  | Osubcarry sz => lower_addcarry sz true xs tg es
  | Omulu sz     => lower_mulu sz xs tg es
  | Oswap ty     => lower_swap ty xs tg es
  | _            => [:: Copn xs tg (Opseudo_op op) es]
  end.

Definition lower_copn (xs: lvals) tg (op: sopn) (es: pexprs) : seq instr_r :=
  match op with
  | Opseudo_op pop => lower_pseudo_operator xs tg pop es
  | _ => [:: Copn xs tg op es]
  end.

Fixpoint lower_i (i:instr) : cmd :=
  let (ii, ir) := i in
  match ir with
  | Cassgn l tg ty e => lower_cassgn ii l tg ty e
  | Copn l t o e => map (MkI ii) (lower_copn l t o e)
  | Cif e c1 c2  =>
     let '(pre, e) := lower_condition (var_info_of_ii ii) e in
       map (MkI ii) (rcons pre (Cif e (conc_map lower_i c1) (conc_map lower_i c2)))
  | Cfor v (d, lo, hi) c =>
     [:: MkI ii (Cfor v (d, lo, hi) (conc_map lower_i c))]
  | Cwhile a c e c' =>
     let '(pre, e) := lower_condition (var_info_of_ii ii) e in
       map (MkI ii) [:: Cwhile a ((conc_map lower_i c) ++ map (MkI dummy_instr_info) pre) e (conc_map lower_i c')]
  | _ =>   map (MkI ii) [:: ir]
  end.

End LOWERING.

End Section.
