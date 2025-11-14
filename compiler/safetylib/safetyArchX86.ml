open Jasmin
open Utils
open Prog
open Wsize
open Apron
open SafetyUtils
open SafetyExpr
open SafetyVar
open SafetyConstr
open SafetyArch
open SafetyAbsExpr

(** X86-64 architecture implementation *)
module X86SafetyArch : SafetyArch with type extended_op = X86_extra.x86_extended_op = struct
  type extended_op = X86_extra.x86_extended_op

  let pointer_data = Arch_decl.arch_pd X86_decl.x86_decl

  (* Flag computation helpers *)
  let cf_of_word sz el er =
    let eli = Papp1 (E.uint_of_word sz, el)
    and eri = Papp1 (E.uint_of_word sz, er) in
    let w_i = Papp2 (E.Oadd E.Op_int, eli, eri) in
    let pow_ws = Pconst (Z.pow (Z.of_int 2) (int_of_ws sz)) in
    Some (Papp2 (E.Ole E.Cmp_int, pow_ws, w_i))

  let sf_of_word sz w =
    let u = Papp1 (E.uint_of_word sz, w) in
    let u_min = Pconst (Z.pow (Z.of_int 2) (int_of_ws sz - 1)) in
    Some (Papp2 (E.Ole E.Cmp_int, u_min, u))

  let pf_of_word _sz w =
    let u = Papp1 (E.uint_of_word U8, w) in
    Some (Papp2 (E.Oeq E.Op_int, Papp2(E.Omod (Unsigned, E.Op_int), u, Pconst (Z.of_int 2)), Pconst Z.zero))

  let zf_of_word sz w =
    let u = Papp1 (E.uint_of_word sz, w) in
    Some (Papp2 (E.Oeq E.Op_int, u, Pconst Z.zero))

  let rflags_of_aluop sz w _vu _vs =
    let of_f = None
    and cf = None
    and sf = sf_of_word sz w
    and pf = pf_of_word sz w
    and zf = zf_of_word sz w in
    [of_f; cf; sf; pf; zf]

  let rflags_of_sub sz el er =
    let w = Papp2 (E.Osub (E.Op_w sz), el, er) in
    let eli = Papp1 (E.uint_of_word sz, el)
    and eri = Papp1 (E.uint_of_word sz, er) in
    let cf = Some (Papp2 (E.Olt E.Cmp_int, eli, eri)) in
    let of_f = None
    and sf = sf_of_word sz w
    and pf = pf_of_word sz w
    and zf = zf_of_word sz w in
    [of_f; cf; sf; pf; zf]

  let rflags_of_neg sz w _vs =
    let of_f = None
    and cf = None
    and sf = sf_of_word sz w
    and pf = pf_of_word sz w
    and zf = zf_of_word sz w in
    [of_f; cf; sf; pf; zf]

  let rflags_of_mul (ov : bool option) =
    [Some ov; Some ov; None; None; None]

  let rflags_unknwon = [None; None; None; None; None]

  let rflags_of_div = rflags_unknwon

  let rflags_of_andn sz w =
    let of_f = Some (Pbool false)
    and cf = Some (Pbool false)
    and sf = sf_of_word sz w
    and pf = None
    and zf = zf_of_word sz w in
    [of_f; cf; sf; pf; zf]

  let nocf = function
    | [of_f; _; sf; pf; zf] -> [of_f; sf; pf; zf]
    | _ -> assert false

  let opn_dflt n = List.init n (fun _ -> None)

  let opn_bin_gen f_flags ws op op_int es =
    let el, er = SafetyUtils.as_seq2 es in
    let w = Papp2 (op, el, er) in
    let vu = Papp2 (op_int,
                    Papp1(E.uint_of_word ws, el),
                    Papp1(E.uint_of_word ws, er)) in
    let vs = () in
    let rflags = f_flags ws w vu vs in
    rflags @ [Some w]

  let opn_bin_alu = opn_bin_gen rflags_of_aluop

  let opn_sub sz es =
    let el, er = SafetyUtils.as_seq2 es in
    let w = Papp2 (E.Osub (E.Op_w sz), el, er) in
    let rflags = rflags_of_sub sz el er in
    rflags @ [Some w]

  let split_div sign ws es =
    let n_hi, n_lo, d = SafetyUtils.as_seq3 es in
    let pow_ws = Pconst (Z.pow (Z.of_int 2) (int_of_ws ws)) in
    let n, d_i = match sign with
      | Unsigned ->
        let n_hi_i = Papp1 (E.uint_of_word ws, n_hi)
        and n_lo_i = Papp1 (E.uint_of_word ws, n_lo)
        and d_i = Papp1 (E.uint_of_word ws, d) in
        let n = Papp2 (E.Oadd E.Op_int,
                       Papp2 (E.Omul E.Op_int, n_hi_i, pow_ws),
                       n_lo_i) in
        (n, d_i)
      | Signed ->
        (* For signed division, combine hi and lo words with sign extension *)
        let n_hi_i = Papp1 (E.Oint_of_word (Signed, ws), n_hi)
        and n_lo_i = Papp1 (E.uint_of_word ws, n_lo)
        and d_i = Papp1 (E.Oint_of_word (Signed, ws), d) in
        let n = Papp2 (E.Oadd E.Op_int,
                       Papp2 (E.Omul E.Op_int, n_hi_i, pow_ws),
                       n_lo_i) in
        (n, d_i)
    in
    (n, d_i)

  let is_comparison (opn : extended_op) (es : expr list) : (expr * expr) option =
    match opn with
    | Arch_extra.BaseOp (_, X86_instr_decl.CMP _) ->
      let el, er = SafetyUtils.as_seq2 es in
      Some (el, er)
    | _ -> None

  (** Architecture-specific assembly operation splitting *)
  let split_asm_opn pd asmOp n (opn : extended_op) es =
    match opn with
    | Arch_extra.ExtOp X86_extra.Oset0 ws ->
      let zero = Some (pcast ws (Pconst (Z.of_int 0))) in
      begin match wsize_cmp U64 ws with
      | Lt -> [zero]
      | _ -> [None; None; None; None; None; zero]
      end

    | Arch_extra.ExtOp X86_extra.Ox86MOVZX32 ->
      let e = SafetyUtils.as_seq1 es in
      [Some (Papp1(E.Oword_of_int U64, Papp1(E.uint_of_word U32, e)))]

    | Arch_extra.BaseOp (None, X86_instr_decl.MOVZX (sz_o, sz_i)) ->
      assert (int_of_ws sz_o >= int_of_ws sz_i);
      let e = SafetyUtils.as_seq1 es in
      [Some (Papp1(E.Oword_of_int sz_o, Papp1(E.uint_of_word sz_i, e)))]

    | Arch_extra.BaseOp (_, X86_instr_decl.CMP ws) ->
      let el, er = SafetyUtils.as_seq2 es in
      rflags_of_sub ws el er

    | Arch_extra.BaseOp (None, X86_instr_decl.ADD ws) ->
      opn_bin_alu ws (E.Oadd (E.Op_w ws)) (E.Oadd E.Op_int) es

    | Arch_extra.BaseOp (None, X86_instr_decl.SUB ws) ->
      opn_sub ws es

    | Arch_extra.BaseOp (None, X86_instr_decl.MUL ws)
    | Arch_extra.BaseOp (None, X86_instr_decl.IMUL ws) ->
      let el, er = SafetyUtils.as_seq2 es in
      let w = Papp2 (E.Omul (E.Op_w ws), el, er) in
      let rflags = [None; None; None; None; None] in
      rflags @ [None; Some w]

    | Arch_extra.BaseOp (None, X86_instr_decl.IMULr ws)
    | Arch_extra.BaseOp (None, X86_instr_decl.IMULri ws) ->
      let el, er = SafetyUtils.as_seq2 es in
      let w = Papp2 (E.Omul (E.Op_w ws), el, er) in
      let rflags = [None; None; None; None; None] in
      rflags @ [Some w]

    | Arch_extra.BaseOp (None, X86_instr_decl.DIV ws) ->
      let n, d = split_div Unsigned ws es in
      let w = Papp1 (E.Oword_of_int ws, Papp2 (E.Odiv(Unsigned, E.Op_int), n, d)) in
      let rflags = rflags_of_div in
      rflags @ [None; Some w]

    | Arch_extra.BaseOp (None, X86_instr_decl.IDIV ws) ->
      let n, d = split_div Signed ws es in
      let w = Papp1 (E.Oword_of_int ws, Papp2 (E.Odiv(Unsigned, E.Op_int), n, d)) in
      let rflags = rflags_of_div in
      rflags @ [None; Some w]

    | Arch_extra.BaseOp (None, X86_instr_decl.INC ws) ->
      let e = SafetyUtils.as_seq1 es in
      let w = Papp2 (E.Oadd (E.Op_w ws), e,
                     Papp1(E.Oword_of_int ws, Pconst (Z.of_int 1))) in
      let vu = Papp2 (E.Oadd E.Op_int,
                      Papp1(E.uint_of_word ws, e),
                      Pconst (Z.of_int 1)) in
      let vs = () in
      let rflags = nocf (rflags_of_aluop ws w vu vs) in
      rflags @ [Some w]

    | Arch_extra.BaseOp (None, X86_instr_decl.DEC ws) ->
      let e = SafetyUtils.as_seq1 es in
      let w = Papp2 (E.Osub (E.Op_w ws), e,
                     Papp1(E.Oword_of_int ws, Pconst (Z.of_int 1))) in
      let vu = Papp2 (E.Osub E.Op_int,
                      Papp1(E.uint_of_word ws, e),
                      Pconst (Z.of_int 1)) in
      let vs = () in
      let rflags = nocf (rflags_of_aluop ws w vu vs) in
      rflags @ [Some w]

    | Arch_extra.BaseOp (None, X86_instr_decl.NEG ws) ->
      let e = SafetyUtils.as_seq1 es in
      let w = Papp1 (E.Oneg (E.Op_w ws), e) in
      let vs = () in
      let rflags = rflags_of_neg ws w vs in
      rflags @ [Some w]

    | Arch_extra.BaseOp (None, X86_instr_decl.MOV _) ->
      let e = SafetyUtils.as_seq1 es in
      [Some e]

    | Arch_extra.BaseOp (None, X86_instr_decl.SHL ws) ->
      let e1, e2 = SafetyUtils.as_seq2 es in
      let e = Papp2 (E.Olsl (E.Op_w ws), e1, e2) in
      rflags_unknwon @ [Some e]

    | Arch_extra.BaseOp (None, X86_instr_decl.SHR ws) ->
      let e1, e2 = SafetyUtils.as_seq2 es in
      let e = Papp2 (E.Olsr ws, e1, e2) in
      rflags_unknwon @ [Some e]

    | Arch_extra.BaseOp (None, X86_instr_decl.SAR ws) ->
      let e1, e2 = SafetyUtils.as_seq2 es in
      let e = Papp2 (E.Oasr (E.Op_w ws), e1, e2) in
      rflags_unknwon @ [Some e]

    | Arch_extra.BaseOp (None, X86_instr_decl.CMOVcc sz) ->
      let c, el, er = SafetyUtils.as_seq3 es in
      let e = Pif (Bty (U sz), c, el, er) in
      [Some e]

    | Arch_extra.BaseOp (None, X86_instr_decl.AND ws) ->
      let e1, e2 = SafetyUtils.as_seq2 es in
      let e = Papp2 (E.Oland ws, e1, e2) in
      rflags_unknwon @ [Some e]

    | Arch_extra.BaseOp (None, X86_instr_decl.OR ws) ->
      let e1, e2 = SafetyUtils.as_seq2 es in
      let e = Papp2 (E.Olor ws, e1, e2) in
      rflags_unknwon @ [Some e]

    | Arch_extra.BaseOp (None, X86_instr_decl.XOR ws) ->
      let e1, e2 = SafetyUtils.as_seq2 es in
      let e = Papp2 (E.Olxor ws, e1, e2) in
      rflags_unknwon @ [Some e]

    | Arch_extra.BaseOp (None, X86_instr_decl.NOT ws) ->
      let e1 = SafetyUtils.as_seq1 es in
      let e = Papp1 (E.Olnot ws, e1) in
      [Some e]

    | Arch_extra.BaseOp (_, X86_instr_decl.LEA ws) ->
      let e1 = SafetyUtils.as_seq1 es in
      let e =
        match SafetyUtils.ty_expr e1 with
        | Bty (U ws') when int_of_ws ws < int_of_ws ws' -> Papp1 (E.Ozeroext (ws, ws'), e1)
        | _ -> e1 in
      [Some e]

    | Arch_extra.BaseOp (_, X86_instr_decl.POPCNT ws) ->
      let e1 = SafetyUtils.as_seq1 es in
      let t = Some (Pbool true) in
      [t; t; t; t; zf_of_word ws e1; None]

    | _ ->
      debug (fun () ->
          Format.eprintf "Warning: unknown opn %a, default to ⊤.@."
            (PrintCommon.pp_opn pd asmOp) (Sopn.Oasm opn));
      opn_dflt n

  let post_opn (opn : extended_op) (lvs : int glval list) (es : expr list) : btcons list =
    match opn with
    | Arch_extra.BaseOp (x, X86_instr_decl.POPCNT ws) -> (
        let open Mtexpr in
        match List.last lvs with
        | Lvar x ->
          let xv = L.unloc x in
          let x = Mlocal (Avar xv) in
          let range_btcons x max =
            BLeaf
              (Mtcons.make (binop Sub (var x) (cst (Coeff.i_of_int 0 max))) EQ)
          in
          range_btcons x (int_of_ws ws)
          ::
          (match es with
          | [Pvar e] when not (is_gkvar e && GV.equal (L.unloc e.gv) xv) ->
            let e =
              if is_gkvar e then Mlocal (Avar (L.unloc e.gv))
              else Mglobal (Avar (L.unloc e.gv))
            in
            let e_neg =
              BLeaf
                (Mtcons.make (binop Sub (cst (Coeff.s_of_int 0)) (var e)) SUP)
            in
            let e_large =
              BLeaf
                (Mtcons.make
                   (binop Sub (var e) (cst (Coeff.s_of_int 255)))
                   SUP)
            in
            [BOr (BOr (e_neg, e_large), range_btcons x 8)]
          | _ -> [])
        | _ -> [])
    | _ -> []

  type flags_heur = {
    fh_zf : Mtexpr.t option;
    fh_cf : Mtexpr.t option;
  }

  let opn_heur pd asmOp (opn : extended_op) v es =
    match opn with
    | Arch_extra.BaseOp (x, X86_instr_decl.DEC _) ->
      assert (x = None);
      Some { fh_zf = Some (Mtexpr.var v);
             fh_cf = Some (Mtexpr.binop Texpr1.Add
                             (Mtexpr.var v)
                             (Mtexpr.cst (Coeff.s_of_int 1))); }

    | Arch_extra.BaseOp (x, X86_instr_decl.CMP _) ->
      assert (x = None);
      let exception Opn_heur_failed in
      let rec to_mvar = function
        | Pvar x ->
          Mtexpr.var (mvar_of_var x)
        | Papp1 (E.Oword_of_int _, e) -> to_mvar e
        | Papp1 (E.Oint_of_word (s, _), e) ->
          assert (s = Signed);
          to_mvar e
        | _ -> raise Opn_heur_failed in
      let el, er = SafetyUtils.as_seq2 es in
      begin try
        let el, er = to_mvar el, to_mvar er in
        Some { fh_zf = Some (Mtexpr.binop Texpr1.Sub el er);
               fh_cf = Some (Mtexpr.binop Texpr1.Sub el er); }
      with Opn_heur_failed -> None end

    | _ ->
      debug (fun () ->
          Format.eprintf "No heuristic for the return flags of %a@."
            (PrintCommon.pp_opn pd asmOp) (Sopn.Oasm opn));
      None

  let pp_flags_heur fmt fh =
    Format.fprintf fmt "@[<hv 0>zf: %a;@ cf %a@]"
      (SafetyUtils.pp_opt Mtexpr.print) (fh.fh_zf)
      (SafetyUtils.pp_opt Mtexpr.print) (fh.fh_cf)

  let get_fh_zf fh = fh.fh_zf
  let get_fh_cf fh = fh.fh_cf
end
