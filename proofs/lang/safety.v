From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.
Require Import expr compiler_util word.
Require Export safety_shared.

Module Import E.

  Definition pass : string := "safety".

  Definition ierror msg := {|
    pel_msg      := PPEstring msg;
    pel_fn       := None;
    pel_fi       := None;
    pel_ii       := None;
    pel_vi       := None;
    pel_pass     := Some pass;
    pel_internal := true
  |}.

End E.

Section SAFETY.
Context `{asmop:asmOp} {pd: PointerData} {msfsz : MSFsize}.

Definition sc_var (x:var_i) :=
  if is_sarr (vtype x) then [::]
  else [:: Pis_var_init x].

Definition sc_gvar x :=
  if is_lvar x then sc_var (gv x)
  else [::].

Definition sc_is_aligned_if al aa sz e :=
  if (al == Unaligned) || (aa == AAscale) then [::]
  else [:: eis_aligned e sz].

Definition efalse := Pbool false.
Definition sc_false := [:: efalse].

(* FIXME : find better name *)
Definition sc_in_bound' ty e1 e2 :=
  match ty with
  | sarr len =>
    [:: eand (elei ezero e1) (elei (eaddi e1 e2) (Pconst len))]
  | _ => sc_false
  end.

Definition sc_in_bound ty aa sz e elen :=
  sc_in_bound' ty (emk_scale aa sz e) elen.

Definition type_of_expr (e:pexpr) : stype :=
  match e with
  | Pconst _ => sint
  | Pbool _ => sbool
  | Parr_init len => sarr len
  | Pvar x => vtype (gv x)
  | Pget al aa ws x e => sword ws
  | Psub al ws len x e => sarr (Z.to_pos (arr_size ws len))
  | Pload al ws e => sword ws
  | Papp1 o e => (type_of_op1 o).2
  | Papp2 o e1 e2 => (type_of_op2 o).2
  | PappN o es => (type_of_opN o).2
  | Pif ty e1 e2 e3 => ty
  | Pbig ei o v e es el => (type_of_op2 o).2
  | Pis_var_init _ => sbool
  | Pis_mem_init _ _ => sbool
  end.

Definition sc_arr_init ty x aa sz e :=
  match ty with
  | sarr len =>
    if is_lvar x then
      let lo := emk_scale aa sz e in
      [:: PappN (Ois_arr_init len) [:: Pvar x; lo; Pconst (wsize_size sz)]]
    else
      [::]
  | _ => sc_false
  end.

Definition sc_arr_get (x:gvar) al aa sz e :=
  let ty := vtype (gv x) in
  sc_is_aligned_if al aa sz e ++
  sc_in_bound ty aa sz e (Pconst (wsize_size sz)) ++
  sc_arr_init ty (Pvar x) aa sz e.

Definition sc_mem_valid (e: pexpr) sz := [:: Pis_mem_init e (wsize_size sz)].

(* Req: Pointer Data*)
Definition eint_of_word (sg:signedness) sz e := Papp1 (Oint_of_word sg sz) e.

Definition sc_is_aligned_if_m al sz e :=
  if (al == Unaligned) then [::]
  else [:: eis_aligned (eint_of_word Unsigned Uptr e) sz].
(* ----- *)

Definition toint sg sz e := Papp1 (Owi1 sg (WIint_of_wint sz)) e.

Definition sc_op1 := sc_op1 toint.

Definition sc_op2 o e1 e2 :=
match is_wi2 o with
| Some (sg, sz, o) =>
  let e1 := toint sg sz e1 in
  let e2 := match o with
            | WIshl | WIshr => toint Unsigned U8 e2
            | _ => toint sg sz e2
            end in
  sc_wiop2 sg sz o e1 e2
| _ => match o with
  | Odiv sg (Op_w sz) => sc_divmod sg sz (eint_of_word sg sz e1) (eint_of_word sg sz e2)
  | Omod sg (Op_w sz) => sc_divmod sg sz (eint_of_word sg sz e1) (eint_of_word sg sz e2)
  | _ => [::]
  end
end.

Definition sc_op2_big (o : sop2) :=
  match o with
  | Odiv sg (Op_w sz) => false
  | Omod sg (Op_w sz) => false
  | Owi2 _ _ o' =>
      match o' with
      | WIadd | WImul | WIsub | WIdiv | WImod
      | WIshl => false
      | WIshr | WIeq | WIneq | WIlt | WIle
      | WIgt | WIge => true
      end
  | Obeq | Oand | Oor | Oadd _ | Omul _ | Osub _
  | Oland _ | Olor _ | Olxor _ |  Olsr _ | Olsl _
  | Oasr _ | Oror _ | Orol _ | Oeq _ | Oneq _
  | Olt _ | Ole _ | Ogt _ | Oge _
  | Ovadd _ _ | Ovsub _ _ | Ovmul _ _
  | Ovlsr _ _ | Ovlsl _ _ | Ovasr _ _
  | Odiv _ _ | Omod _ _ => true
  end.

Fixpoint sc_pexpr (e : pexpr) : safety_cond :=
  match e with
  | Pconst _ | Pbool _  | Parr_init _ => [::]
  | Pvar x => sc_gvar x

  | Pget al aa ws x e =>
    let sc_e := sc_pexpr e in
    let sc_arr := sc_arr_get x al aa ws e in
    sc_e ++ sc_arr

  | Psub aa ws len x e =>
    let sc_e := sc_pexpr e in
    let sc_arr := sc_in_bound (vtype (gv x)) aa ws e (Pconst (arr_size ws len)) in
    sc_e ++ sc_arr

  | Pload al ws e =>
    let sc_e := sc_pexpr e in
    let sc_al := sc_is_aligned_if_m al ws e in
    let sc_load := sc_mem_valid e ws in
    sc_e ++ sc_al ++ sc_load

  | Papp1 op e =>
    let sc_e := sc_pexpr e in
    let sc_op := sc_op1 op e in
    sc_e ++ sc_op

  | Papp2 op e1 e2 =>
    let sce1 := sc_pexpr e1 in
    let sce2 := sc_pexpr e2 in
    let sco := sc_op2 op e1 e2 in
    sce1 ++ sce2 ++ sco

  | PappN op es =>
    let scs := conc_map sc_pexpr es in
    scs

  | Pif ty e e1 e2 =>
    let sc_e := sc_pexpr e in
    let sc_e1 := sc_pexpr e1 in
    let sc_e2 := sc_pexpr e2 in
    sc_e ++ sc_e1 ++ sc_e2

  | Pbig idx op x body start len  =>
    let scidx := sc_pexpr idx in
    let scstart := sc_pexpr start in
    let sclen := sc_pexpr len in
    let scbody := sc_pexpr body in
    let scop := Pbool (sc_op2_big op) in
    let scbody := Pbig etrue Oand x (eands scbody) start len in
    scidx ++ scstart ++ sclen ++ [:: scop ; scbody]

  | Pis_var_init x => [::]

  | Pis_mem_init e1 e2 =>
    let sc_e1 := sc_pexpr e1 in
    let sc_e2 := sc_pexpr e2 in
    sc_e1 ++ sc_e2
  end.

Definition sc_arr_set (x:var_i) al aa sz e :=
  sc_is_aligned_if al aa sz e ++
  sc_in_bound (vtype x) aa sz e (Pconst (wsize_size sz)).

Definition sc_lval (lv : lval) : safety_cond :=
  match lv with
  | Lnone _ _ => [::]
  | Lvar x => [::]
  | Lmem al ws x e =>
    let sc_e := sc_pexpr e in
    let sc_al := sc_is_aligned_if_m al ws e in
    let sc_load := sc_mem_valid e ws in
    sc_e ++ sc_al ++ sc_load
  | Laset al aa ws x e =>
    let sc_e := sc_pexpr e in
    let sc_arr := sc_arr_set x al aa ws e in
    sc_e ++ sc_arr
  | Lasub aa ws len x e =>
    let sc_e := sc_pexpr e in
    let sc_arr := sc_in_bound (vtype x) aa ws e (Pconst (arr_size ws len)) in
    sc_e ++ sc_arr
  end.

Definition sc_lvals (lvs:lvals) okmem : safety_cond :=
  let scs := map sc_lval lvs in
   (Pbool (check_xs okmem Sv.empty lvs scs)) :: flatten scs.

Definition safe_cond_to_e vs sc: pexpr :=
  match sc with
  | NotZero ws k =>
      match List.nth_error vs k with
      | Some x => eneqi (eint_of_word Unsigned ws x) (Pconst 0)
      | None => efalse
      end
  | InRangeMod32 ws i j k =>
      match List.nth_error vs k with
      | Some x =>
        let e := emodi Unsigned (eint_of_word Unsigned ws x) (Pconst 32) in
        let e1 := elei (Pconst i) e in
        let e2 := elei e (Pconst j) in
        eand e1 e2
      | None => efalse
      end
  | ULt ws k z =>
      match List.nth_error vs k with
      | Some x => elti (eint_of_word Unsigned ws x) (Pconst z)
      | None => efalse
      end
  | UGe ws z k =>
      match List.nth_error vs k with
      | Some x => elei (Pconst z) (eint_of_word Unsigned ws x)
      | None => efalse
      end
  | UaddLe ws k1 k2 z =>
      match List.nth_error vs k1 with
      | Some x =>
        match List.nth_error vs k2 with
        | Some y => elei (eaddi (eint_of_word Unsigned ws x) (eint_of_word Unsigned ws y)) (Pconst z)
        | None => efalse
        end
      | None => efalse
      end
  | AllInit ws p k =>
      match List.nth_error vs k with
      | Some e =>
        let len := arr_size ws p in
        PappN (Ois_arr_init (Z.to_pos len)) [:: e; Pconst 0; Pconst len]
      | _ => efalse
      end
  | X86Division sz sign =>
    match vs,sign with
      | hi :: lo :: dv :: _, Signed =>
        let hi := eint_of_word Signed sz hi in
        let lo := eint_of_word Unsigned sz lo in
        let szi := wbase sz in
        let dd := eaddi (emuli (Pconst szi) (hi)) lo in
        let dv := eint_of_word Signed sz dv in
        let q  := edivi Signed dd dv in
        let r  := emodi Signed dd dv in
        let ov := eor (elti q (Pconst (wmin_signed sz)))
                      (elti (Pconst (wmax_signed sz)) q) in
        eand (eneqi dv ezero) (enot ov)
      | hi :: lo :: dv :: _, Unsigned =>
        let hi := eint_of_word Unsigned sz hi in
        let lo := eint_of_word Unsigned sz lo in
        let szi := wbase sz in
        let dd := eaddi (emuli (Pconst szi) (hi)) lo in
        let dv := eint_of_word Unsigned sz dv in
        let q  := edivi Unsigned dd dv in
        let r  := emodi Unsigned dd dv in
        let ov := elti (Pconst (wmax_unsigned sz)) q in
        eand (eneqi dv ezero) (enot ov)
      | _,_ => efalse
    end
  | ScFalse => efalse
  end.

Definition get_sopn_safe_conds (es: pexprs) (o: sopn) :=
  let instr_descr := get_instr_desc o in
  map (safe_cond_to_e es) instr_descr.(i_safe).

Definition get_sopn_wt (es: pexprs) (o: sopn) :=
  let instr_descr := get_instr_desc o in
  Pbool (all2 (fun ty e => type_of_expr e == ty) instr_descr.(tin) es).

Fixpoint sc_instr_ir ii (ir : instr_r) : (safety_cond *  instr_r) :=
  match ir with
  | Cassgn lv _ _ e =>
    let sc_lv := sc_lval lv in
    let sc_e := sc_pexpr e in
    (sc_lv ++ sc_e, ir)
  | Copn lvs _ o es  =>
    let sc_wt := get_sopn_wt es o in
    let sc_lvs := sc_lvals lvs true in
    let sc_op := get_sopn_safe_conds es o in
    let sc_es := conc_map sc_pexpr es in
    (sc_wt :: sc_lvs ++ sc_op ++ sc_es, ir)
  | Csyscall lvs _ es =>
    let sc_lvs := sc_lvals lvs true in
    let sc_es := conc_map sc_pexpr es in
    (sc_lvs ++ sc_es, ir)
  | Ccall lvs _ es =>
    let sc_lvs := sc_lvals lvs false in
    let sc_es := conc_map sc_pexpr es in
    (sc_lvs ++ sc_es, ir)
  | Cif e c1 c2 =>
    let sc_e := sc_pexpr e in
    let sc_c1 := conc_map sc_instr c1 in
    let sc_c2 := conc_map sc_instr c2 in
    let ir := Cif e sc_c1 sc_c2 in
    (sc_e, ir)
  | Cfor x (d,e1,e2) c =>
    let sc_c := conc_map sc_instr c in
    let sc_e := sc_pexpr e1 ++ sc_pexpr e2 in
    let ir := Cfor x (d,e1,e2) sc_c in
    (sc_e, ir)
  | Cwhile a c1 e ii_w c2 =>
    let sc_e := safe_assert ii (sc_pexpr e) in
    let sc_c1 := conc_map sc_instr c1 ++ sc_e in
    let sc_c2 := conc_map sc_instr c2 in
    let ir := Cwhile a sc_c1 e ii_w sc_c2 in
    ([::] ,ir)
  | Cassert a =>
    let sc_e := sc_pexpr a.2 in
    (sc_e, ir)
  end
with sc_instr (i:instr) : cmd :=
  let (ii,ir) := i in
  let ir := sc_instr_ir ii ir in
  (rcons (safe_assert ii ir.1) (MkI ii ir.2)).

Definition sc_a_and (a : assertion) :=
  let sc_e := sc_pexpr a.2 in
  (a.1, eands (rcons sc_e a.2)).

Definition sc_ci ci :=
  let ci_pre := map sc_a_and ci.(f_pre) in
  let ci_post := map sc_a_and ci.(f_post) in
  MkContra ci.(f_iparams) ci.(f_ires) ci_pre ci_post.

Definition sc_fun (f: ufundef) :=
  let 'MkFun ii ci tin p c tout r ev := f in
  let ci :=
    match ci with
    | None => None
    | Some ci => Some (sc_ci ci)
    end
  in
  let c := conc_map sc_instr c in
  let es := conc_map sc_var r in
  let sc_res := safe_assert dummy_instr_info es  in
  let c := c ++ sc_res in
  MkFun ii ci tin p c tout r ev.

Definition check_glob (gd : glob_decl) :=
  match gd.2 with
  | Gword _ _ => true
  | Garr len t =>  all (WArray.is_init t) (ziota 0 len)
  end.

Definition sc_prog (p:_uprog) : result pp_error_loc _uprog :=
  Let _ := assert (all check_glob p.(p_globs)) (E.ierror "global arrays not fully initialised"%string) in
  ok (map_prog sc_fun p).

End SAFETY.
