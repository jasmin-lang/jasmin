(* * Generation of the safety conditions of a program.

   [sc_prog] instruments a program with the assertions that must hold for it to
   be safe: array accesses in bounds and initialised, memory accesses valid and
   aligned, no division by zero, no wint overflow.  The instrumented program is
   meant to be discharged under the defensive semantics ([withcatch], see
   [WithCatch] in sem_params.v), which is the one EasyCrypt implements. *)

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.
From Coq Require Import ZArith.
Require Import expr compiler_util word.
Require Export safety_common.
Import Utf8.

Local Open Scope Z_scope.
Local Open Scope seq_scope.

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

(* ------------------------------------------------------------------------- *)
(* Variables                                                                  *)

(* An array variable is always "defined" as a value, the initialisation of its
   cells is checked at each access by [sc_arr_init]. *)
Definition sc_var (x:var_i) : safety_cond :=
  if is_aarr (vtype x) then [::]
  else [:: Pis_var_init x].

Definition sc_gvar (x:gvar) : safety_cond :=
  if is_lvar x then sc_var (gv x)
  else [::].

(* ------------------------------------------------------------------------- *)
(* Arrays and memory                                                          *)

Definition efalse := Pbool false.
Definition sc_false : safety_cond := [:: Pexpr efalse].

Definition sc_is_aligned_if al aa sz e : safety_cond :=
  if (al == Unaligned) || (aa == AAscale) then [::]
  else [:: Pexpr (eis_aligned e sz)].

(* [e1] is the offset in bytes, [e2] the size in bytes of the access. *)
Definition sc_in_bound' ty e1 e2 : safety_cond :=
  match ty with
  | aarr ws len =>
    [:: Pexpr (eand (elei ezero e1) (elei (eaddi e1 e2) (Pconst (arr_size ws len))))]
  | _ => sc_false
  end.

Definition sc_in_bound ty aa sz e elen : safety_cond :=
  sc_in_bound' ty (emk_scale aa sz e) elen.

Definition sc_arr_init ty (x:gvar) aa sz e : safety_cond :=
  match ty with
  | aarr ws len =>
    if is_lvar x then
      let lo := emk_scale aa sz e in
      [:: PappN_safety (Ois_arr_init (arr_size ws len))
            [:: Pvar x; lo; Pconst (wsize_size sz)]]
    else
      (* a global array is fully initialised, [sc_prog] checks it *)
      [::]
  | _ => sc_false
  end.

Definition sc_arr_get (x:gvar) al aa sz e : safety_cond :=
  let ty := vtype (gv x) in
  sc_is_aligned_if al aa sz e ++
  sc_in_bound ty aa sz e (Pconst (wsize_size sz)) ++
  sc_arr_init ty x aa sz e.

Definition sc_arr_set (x:var_i) al aa sz e : safety_cond :=
  sc_is_aligned_if al aa sz e ++
  sc_in_bound (vtype x) aa sz e (Pconst (wsize_size sz)).

Definition sc_mem_valid (e: pexpr) sz : safety_cond :=
  [:: Pis_mem_init e (Pconst (wsize_size sz))].

Definition sc_is_aligned_if_m al sz e : safety_cond :=
  if al == Unaligned then [::]
  else [:: Pexpr (eis_aligned (eint_of_word Unsigned Uptr e) sz)].

(* ------------------------------------------------------------------------- *)
(* Operators                                                                  *)

Definition toint sg sz e := Papp1 (Owi1 sg (WIint_of_wint sz)) e.

Definition sc_op1 := sc_op1 toint.

Definition sc_op2 o e1 e2 : seq pexpr :=
  match is_wi2 o with
  | Some (sg, sz, o) =>
    let e1 := toint sg sz e1 in
    let e2 := match o with
              | WIshl | WIshr => toint Unsigned U8 e2
              | _ => toint sg sz e2
              end in
    sc_wiop2 sg sz o e1 e2
  | _ =>
    match o with
    | Odiv sg (Op_w sz) => sc_divmod sg sz (eint_of_word sg sz e1) (eint_of_word sg sz e2)
    | Omod sg (Op_w sz) => sc_divmod sg sz (eint_of_word sg sz e1) (eint_of_word sg sz e2)
    | _ => [::]
    end
  end.

(* ------------------------------------------------------------------------- *)
(* Expressions                                                                *)

Definition type_of_expr (e:pexpr) : atype :=
  match e with
  | Pconst _ => aint
  | Pbool _ => abool
  | Parr_init ws len => aarr ws len
  | Pvar x => vtype (gv x)
  | Pget al aa ws x e => aword ws
  | Psub aa ws len x e => aarr ws len
  | Pload al ws e => aword ws
  | Papp1 o e => (type_of_op1 o).2
  | Papp2 o e1 e2 => (type_of_op2 o).2
  | PappN o es => (type_of_opN o).2
  | Pif ty e1 e2 e3 => ty
  end.

Fixpoint sc_pexpr (e : pexpr) : safety_cond :=
  match e with
  | Pconst _ | Pbool _ | Parr_init _ _ => [::]
  | Pvar x => sc_gvar x

  | Pget al aa ws x e =>
    sc_pexpr e ++ sc_arr_get x al aa ws e

  | Psub aa ws len x e =>
    sc_pexpr e ++ sc_in_bound (vtype (gv x)) aa ws e (Pconst (arr_size ws len))

  | Pload al ws e =>
    sc_pexpr e ++ sc_is_aligned_if_m al ws e ++ sc_mem_valid e ws

  | Papp1 op e =>
    sc_pexpr e ++ map Pexpr (sc_op1 op e)

  | Papp2 op e1 e2 =>
    sc_pexpr e1 ++ sc_pexpr e2 ++ map Pexpr (sc_op2 op e1 e2)

  | PappN op es => conc_map sc_pexpr es

  | Pif ty e e1 e2 =>
    sc_pexpr e ++ sc_pexpr e1 ++ sc_pexpr e2
  end.

Fixpoint sc_eassert (a : eassert) : safety_cond :=
  match a with
  | Pexpr e => sc_pexpr e
  | PappN_safety _ es => conc_map sc_pexpr es
  | Pis_var_init _ => [::]
  | Pis_mem_init e1 e2 => sc_pexpr e1 ++ sc_pexpr e2
  | Pand a1 a2 => sc_eassert a1 ++ sc_eassert a2
  end.

(* ------------------------------------------------------------------------- *)
(* Left values                                                                *)

Definition sc_lval (lv : lval) : safety_cond :=
  match lv with
  | Lnone _ _ => [::]
  | Lvar x => [::]
  | Lmem al ws x e =>
    sc_pexpr e ++ sc_is_aligned_if_m al ws e ++ sc_mem_valid e ws
  | Laset al aa ws x e =>
    sc_pexpr e ++ sc_arr_set x al aa ws e
  | Lasub aa ws len x e =>
    sc_pexpr e ++ sc_in_bound (vtype x) aa ws e (Pconst (arr_size ws len))
  end.

(* The conditions of the left values are asserted *before* the assignment, so
   they must not read what the assignment writes. [check_xs] checks it. *)
Definition sc_lvals (lvs:lvals) okmem : safety_cond :=
  let scs := map sc_lval lvs in
  Pexpr (Pbool (check_xs read_easserts use_mem_eassert okmem Sv.empty lvs scs))
    :: flatten scs.

(* ------------------------------------------------------------------------- *)
(* Operators of instructions                                                  *)

Definition safe_cond_to_e (vs: pexprs) (sc: safe_cond) : eassert :=
  match sc with
  | NotZero ws k =>
      match List.nth_error vs k with
      | Some x => Pexpr (eneqi (eint_of_word Unsigned ws x) (Pconst 0))
      | None => Pexpr efalse
      end
  | InRangeMod32 ws i j k =>
      match List.nth_error vs k with
      | Some x =>
        let e := emodi Unsigned (eint_of_word Unsigned ws x) (Pconst 32) in
        Pexpr (eand (elei (Pconst i) e) (elei e (Pconst j)))
      | None => Pexpr efalse
      end
  | ULt ws k z =>
      match List.nth_error vs k with
      | Some x => Pexpr (elti (eint_of_word Unsigned ws x) (Pconst z))
      | None => Pexpr efalse
      end
  | UGe ws z k =>
      match List.nth_error vs k with
      | Some x => Pexpr (elei (Pconst z) (eint_of_word Unsigned ws x))
      | None => Pexpr efalse
      end
  | UaddLe ws k1 k2 z =>
      match List.nth_error vs k1, List.nth_error vs k2 with
      | Some x, Some y =>
        Pexpr (elei (eaddi (eint_of_word Unsigned ws x) (eint_of_word Unsigned ws y))
                    (Pconst z))
      | _, _ => Pexpr efalse
      end
  | AllInit ws p k =>
      match List.nth_error vs k with
      | Some e =>
        let len := arr_size ws p in
        PappN_safety (Ois_arr_init len) [:: e; Pconst 0; Pconst len]
      | None => Pexpr efalse
      end
  | X86Division sz sign =>
    match vs, sign with
    | hi :: lo :: dv :: _, Signed =>
      let hi := eint_of_word Signed sz hi in
      let lo := eint_of_word Unsigned sz lo in
      let dd := eaddi (emuli (Pconst (wbase sz)) hi) lo in
      let dv := eint_of_word Signed sz dv in
      let q  := edivi Signed dd dv in
      let ov := eor (elti q (Pconst (wmin_signed sz)))
                    (elti (Pconst (wmax_signed sz)) q) in
      Pexpr (eand (eneqi dv ezero) (enot ov))
    | hi :: lo :: dv :: _, Unsigned =>
      let hi := eint_of_word Unsigned sz hi in
      let lo := eint_of_word Unsigned sz lo in
      let dd := eaddi (emuli (Pconst (wbase sz)) hi) lo in
      let dv := eint_of_word Unsigned sz dv in
      let q  := edivi Unsigned dd dv in
      let ov := elti (Pconst (wmax_unsigned sz)) q in
      Pexpr (eand (eneqi dv ezero) (enot ov))
    | _, _ => Pexpr efalse
    end
  | ScFalse => Pexpr efalse
  end.

Definition get_sopn_safe_conds (es: pexprs) (o: sopn) : safety_cond :=
  map (safe_cond_to_e es) (get_instr_desc o).(i_safe).

(* [exec_sopn] fails with [ErrType] when its arguments are ill-typed; this is
   not a safety condition, but the assertion is emitted so that the instrumented
   program is total. *)
Definition get_sopn_wt (es: pexprs) (o: sopn) : eassert :=
  Pexpr (Pbool (all2 (fun ty e => convertible (type_of_expr e) ty)
                     (get_instr_desc o).(tin) es)).

(* ------------------------------------------------------------------------- *)
(* Instructions                                                               *)

Fixpoint sc_instr_ir ii (ir : instr_r) : (safety_cond * instr_r) :=
  match ir with
  | Cassgn lv _ _ e =>
    (sc_lval lv ++ sc_pexpr e, ir)
  | Copn lvs _ o es =>
    (get_sopn_wt es o :: sc_lvals lvs true ++ get_sopn_safe_conds es o ++
       conc_map sc_pexpr es, ir)
  | Csyscall lvs _ es =>
    (sc_lvals lvs true ++ conc_map sc_pexpr es, ir)
  | Ccall lvs _ es =>
    (sc_lvals lvs false ++ conc_map sc_pexpr es, ir)
  | Cif e c1 c2 =>
    (sc_pexpr e, Cif e (conc_map sc_instr c1) (conc_map sc_instr c2))
  | Cfor x (d,e1,e2) c =>
    (sc_pexpr e1 ++ sc_pexpr e2, Cfor x (d,e1,e2) (conc_map sc_instr c))
  | Cwhile a c1 e ii_w c2 =>
    (* the condition is evaluated at the end of [c1], so its safety conditions
       are asserted there and not in front of the loop *)
    let sc_e := safe_assert ii (sc_pexpr e) in
    ([::], Cwhile a (conc_map sc_instr c1 ++ sc_e) e ii_w (conc_map sc_instr c2))
  | Cassert a =>
    (sc_eassert a.2, ir)
  end
with sc_instr (i:instr) : cmd :=
  let (ii,ir) := i in
  let ir := sc_instr_ir ii ir in
  rcons (safe_assert ii ir.1) (MkI ii ir.2).

(* ------------------------------------------------------------------------- *)
(* Functions and program                                                      *)

(* A contract is asserted as a single [eassert], so its own safety conditions
   are conjoined in front of it rather than emitted as separate assertions. *)
Definition sc_a_and (a : assertion) : assertion :=
  (a.1, aands (rcons (sc_eassert a.2) a.2)).

Definition sc_ci ci :=
  MkContra ci.(f_iparams) ci.(f_ires)
    (map sc_a_and ci.(f_pre)) (map sc_a_and ci.(f_post)).

Definition sc_fun (f: ufundef) : ufundef :=
  let 'MkFun ii ci tin p c tout r ev := f in
  let ci := omap sc_ci ci in
  let c := conc_map sc_instr c in
  (* the results must be initialised on exit *)
  let c := c ++ safe_assert dummy_instr_info (conc_map sc_var r) in
  MkFun ii ci tin p c tout r ev.

Definition check_glob (gd : glob_decl) :=
  match gd.2 with
  | Gword _ _ => true
  | Garr len t => all (WArray.is_init t) (ziota 0 len)
  end.

Definition sc_prog (p:_uprog) : result pp_error_loc _uprog :=
  Let _ := assert (all check_glob p.(p_globs))
                  (E.ierror "global arrays not fully initialised"%string) in
  ok (map_prog sc_fun p).

End SAFETY.
