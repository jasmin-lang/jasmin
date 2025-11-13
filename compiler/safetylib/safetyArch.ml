open Jasmin
open Utils
open Prog
open Wsize
open Apron
open SafetyUtils
open SafetyExpr
open SafetyVar
open SafetyConstr

(** Architecture abstraction for the safety checker *)
module type SafetyArch = sig
  type extended_op

  val is_comparison : extended_op Sopn.sopn -> expr list -> (expr * expr) option

  val split_opn :
    Wsize.wsize ->
    extended_op Sopn.asmOp ->
    int ->
    extended_op Sopn.sopn ->
    expr list ->
    expr option list

  val post_opn :
    extended_op Sopn.sopn ->
    (int glval) list ->
    expr list ->
    btcons list

  type flags_heur = {
    fh_zf : Mtexpr.t option;
    fh_cf : Mtexpr.t option;
  }

  val opn_heur :
    Wsize.wsize ->
    extended_op Sopn.asmOp ->
    extended_op Sopn.sopn ->
    mvar ->
    expr list ->
    flags_heur option

  val pp_flags_heur : Format.formatter -> flags_heur -> unit
  val get_fh_zf : flags_heur -> Mtexpr.t option
  val get_fh_cf : flags_heur -> Mtexpr.t option
end

(** Generic architecture with default implementations *)
module MakeGenericArch(A : sig
  type extended_op
end) : SafetyArch with type extended_op = A.extended_op = struct
  type extended_op = A.extended_op

  let is_comparison _ _ = None

  let split_opn _pd _asmOp n _opn _es =
    (* Default: all outputs are unknown (Top) *)
    List.init n (fun _ -> None)

  let post_opn _opn _lvs _es = []

  type flags_heur = {
    fh_zf : Mtexpr.t option;
    fh_cf : Mtexpr.t option;
  }

  let opn_heur _pd _asmOp _opn _v _es = None

  let pp_flags_heur fmt fh =
    Format.fprintf fmt "@[<hv 0>zf: %a;@ cf %a@]"
      (SafetyUtils.pp_opt Mtexpr.print) (fh.fh_zf)
      (SafetyUtils.pp_opt Mtexpr.print) (fh.fh_cf)

  let get_fh_zf fh = fh.fh_zf
  let get_fh_cf fh = fh.fh_cf
end

(** X86-64 architecture implementation *)
module X86SafetyArch : SafetyArch with type extended_op = X86_extra.x86_extended_op = struct
  type extended_op = X86_extra.x86_extended_op

  (* Helper functions from safetyInterpreter.ml *)
  let as_seq1 = function [e] -> e | _ -> assert false
  let as_seq2 = function [e1;e2] -> (e1,e2) | _ -> assert false
  let as_seq3 = function [e1;e2;e3] -> (e1,e2,e3) | _ -> assert false

  let pcast ws e = Papp1 (E.Oword_of_int ws, e)

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
    let el, er = as_seq2 es in
    let w = Papp2 (op, el, er) in
    let vu = Papp2 (op_int,
                    Papp1(E.uint_of_word ws, el),
                    Papp1(E.uint_of_word ws, er)) in
    let vs = () in
    let rflags = f_flags ws w vu vs in
    rflags @ [Some w]

  let opn_bin_alu = opn_bin_gen rflags_of_aluop

  let opn_sub sz es =
    let el, er = as_seq2 es in
    let w = Papp2 (E.Osub (E.Op_w sz), el, er) in
    let rflags = rflags_of_sub sz el er in
    rflags @ [Some w]

  let mk_addcarry ws es =
    let el, er, eb = as_seq3 es in
    let w_no_carry = Papp2 (E.Oadd (E.Op_w ws), el, er) in
    let w_carry = Papp2 (E.Oadd (E.Op_w ws),
                         w_no_carry,
                         pcast ws (Pconst (Z.of_int 1))) in

    let eli = Papp1 (E.uint_of_word ws, el)
    and eri = Papp1 (E.uint_of_word ws, er) in
    let w_i = Papp2 (E.Oadd E.Op_int, eli, eri) in
    let pow_ws = Pconst (Z.pow (Z.of_int 2) (int_of_ws ws)) in

    let cf_no_carry = Papp2 (E.Ole E.Cmp_int, pow_ws, w_i) in
    let cf_carry = Papp2 (E.Ole E.Cmp_int,
                          pow_ws,
                          Papp2 (E.Oadd E.Op_int,
                                 w_i,
                                 Pconst (Z.of_int 1))) in

    match eb with
    | Pbool false -> [Some cf_no_carry; Some w_no_carry]
    | Pbool true -> [Some cf_carry; Some w_carry]
    | _ -> [None; None]

  let mk_subcarry ws es =
    let el, er, eb = as_seq3 es in
    let w_no_carry = Papp2 (E.Osub (E.Op_w ws), el, er) in
    let w_carry = Papp2 (E.Osub (E.Op_w ws),
                         w_no_carry,
                         pcast ws (Pconst (Z.of_int 1))) in

    let eli = Papp1 (E.uint_of_word ws, el)
    and eri = Papp1 (E.uint_of_word ws, er) in

    let cf_no_carry = Papp2 (E.Olt E.Cmp_int, eli, eri) in
    let cf_carry = Papp2 (E.Ole E.Cmp_int, eli, eri) in

    match eb with
    | Pbool false -> [Some cf_no_carry; Some w_no_carry]
    | Pbool true -> [Some cf_carry; Some w_carry]
    | _ -> [None; None]

  let split_div sign ws es =
    let n_hi, n_lo, d = as_seq3 es in
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

  let is_comparison (opn : extended_op Sopn.sopn) (es : expr list) : (expr * expr) option =
    match opn with
    | Sopn.Oasm (Arch_extra.BaseOp (_, X86_instr_decl.CMP _) : extended_op) ->
      let el, er = as_seq2 es in
      Some (el, er)
    | _ -> None

  let split_opn pd asmOp n (opn : extended_op Sopn.sopn) es =
    match opn with
    | Sopn.Oasm (Arch_extra.ExtOp X86_extra.Oset0 ws) ->
      let zero = Some (pcast ws (Pconst (Z.of_int 0))) in
      begin match wsize_cmp U64 ws with
      | Lt -> [zero]
      | _ -> [None; None; None; None; None; zero]
      end

    | Sopn.Opseudo_op (Osubcarry ws) -> mk_subcarry ws es

    | Sopn.Opseudo_op (Oaddcarry ws) -> mk_addcarry ws es

    | Sopn.Opseudo_op (Oswap ty) ->
      let x, y = as_seq2 es in
      [Some y; Some x]

    | Sopn.Oasm (Arch_extra.ExtOp X86_extra.Ox86MOVZX32) ->
      let e = as_seq1 es in
      [Some (Papp1(E.Oword_of_int U64, Papp1(E.uint_of_word U32, e)))]

    | Sopn.Oasm (Arch_extra.BaseOp (None, X86_instr_decl.MOVZX (sz_o, sz_i))) ->
      assert (int_of_ws sz_o >= int_of_ws sz_i);
      let e = as_seq1 es in
      [Some (Papp1(E.Oword_of_int sz_o, Papp1(E.uint_of_word sz_i, e)))]

    | Sopn.Oasm (Arch_extra.BaseOp (_, X86_instr_decl.CMP ws)) ->
      let el, er = as_seq2 es in
      rflags_of_sub ws el er

    | Sopn.Oasm (Arch_extra.BaseOp (None, X86_instr_decl.ADD ws)) ->
      opn_bin_alu ws (E.Oadd (E.Op_w ws)) (E.Oadd E.Op_int) es

    | Sopn.Oasm (Arch_extra.BaseOp (None, X86_instr_decl.SUB ws)) ->
      opn_sub ws es

    | Sopn.Oasm (Arch_extra.BaseOp (None, X86_instr_decl.MUL ws))
    | Sopn.Oasm (Arch_extra.BaseOp (None, X86_instr_decl.IMUL ws)) ->
      let el, er = as_seq2 es in
      let w = Papp2 (E.Omul (E.Op_w ws), el, er) in
      let rflags = [None; None; None; None; None] in
      rflags @ [None; Some w]

    | Sopn.Oasm (Arch_extra.BaseOp (None, X86_instr_decl.IMULr ws))
    | Sopn.Oasm (Arch_extra.BaseOp (None, X86_instr_decl.IMULri ws)) ->
      let el, er = as_seq2 es in
      let w = Papp2 (E.Omul (E.Op_w ws), el, er) in
      let rflags = [None; None; None; None; None] in
      rflags @ [Some w]

    | Sopn.Oasm (Arch_extra.BaseOp (None, X86_instr_decl.DIV ws)) ->
      let n, d = split_div Unsigned ws es in
      let w = Papp1 (E.Oword_of_int ws, Papp2 (E.Odiv(Unsigned, E.Op_int), n, d)) in
      let rflags = rflags_of_div in
      rflags @ [None; Some w]

    | Sopn.Oasm (Arch_extra.BaseOp (None, X86_instr_decl.IDIV ws)) ->
      let n, d = split_div Signed ws es in
      let w = Papp1 (E.Oword_of_int ws, Papp2 (E.Odiv(Unsigned, E.Op_int), n, d)) in
      let rflags = rflags_of_div in
      rflags @ [None; Some w]

    | Sopn.Oasm (Arch_extra.BaseOp (None, X86_instr_decl.INC ws)) ->
      let e = as_seq1 es in
      let w = Papp2 (E.Oadd (E.Op_w ws), e,
                     Papp1(E.Oword_of_int ws, Pconst (Z.of_int 1))) in
      let vu = Papp2 (E.Oadd E.Op_int,
                      Papp1(E.uint_of_word ws, e),
                      Pconst (Z.of_int 1)) in
      let vs = () in
      let rflags = nocf (rflags_of_aluop ws w vu vs) in
      rflags @ [Some w]

    | Sopn.Oasm (Arch_extra.BaseOp (None, X86_instr_decl.DEC ws)) ->
      let e = as_seq1 es in
      let w = Papp2 (E.Osub (E.Op_w ws), e,
                     Papp1(E.Oword_of_int ws, Pconst (Z.of_int 1))) in
      let vu = Papp2 (E.Osub E.Op_int,
                      Papp1(E.uint_of_word ws, e),
                      Pconst (Z.of_int 1)) in
      let vs = () in
      let rflags = nocf (rflags_of_aluop ws w vu vs) in
      rflags @ [Some w]

    | Sopn.Oasm (Arch_extra.BaseOp (None, X86_instr_decl.NEG ws)) ->
      let e = as_seq1 es in
      let w = Papp1 (E.Oneg (E.Op_w ws), e) in
      let vs = () in
      let rflags = rflags_of_neg ws w vs in
      rflags @ [Some w]

    | Sopn.Oasm (Arch_extra.BaseOp (None, X86_instr_decl.MOV _)) ->
      let e = as_seq1 es in
      [Some e]

    | Sopn.Oasm (Arch_extra.BaseOp (None, X86_instr_decl.SHL ws)) ->
      let e1, e2 = as_seq2 es in
      let e = Papp2 (E.Olsl (E.Op_w ws), e1, e2) in
      rflags_unknwon @ [Some e]

    | Sopn.Oasm (Arch_extra.BaseOp (None, X86_instr_decl.SHR ws)) ->
      let e1, e2 = as_seq2 es in
      let e = Papp2 (E.Olsr ws, e1, e2) in
      rflags_unknwon @ [Some e]

    | Sopn.Oasm (Arch_extra.BaseOp (None, X86_instr_decl.SAR ws)) ->
      let e1, e2 = as_seq2 es in
      let e = Papp2 (E.Oasr (E.Op_w ws), e1, e2) in
      rflags_unknwon @ [Some e]

    | Sopn.Oasm (Arch_extra.BaseOp (None, X86_instr_decl.CMOVcc sz)) ->
      let c, el, er = as_seq3 es in
      let e = Pif (Bty (U sz), c, el, er) in
      [Some e]

    | Sopn.Oasm (Arch_extra.BaseOp (None, X86_instr_decl.AND ws)) ->
      let e1, e2 = as_seq2 es in
      let e = Papp2 (E.Oland ws, e1, e2) in
      rflags_unknwon @ [Some e]

    | Sopn.Oasm (Arch_extra.BaseOp (None, X86_instr_decl.OR ws)) ->
      let e1, e2 = as_seq2 es in
      let e = Papp2 (E.Olor ws, e1, e2) in
      rflags_unknwon @ [Some e]

    | Sopn.Oasm (Arch_extra.BaseOp (None, X86_instr_decl.XOR ws)) ->
      let e1, e2 = as_seq2 es in
      let e = Papp2 (E.Olxor ws, e1, e2) in
      rflags_unknwon @ [Some e]

    | Sopn.Oasm (Arch_extra.BaseOp (None, X86_instr_decl.NOT ws)) ->
      let e1 = as_seq1 es in
      let e = Papp1 (E.Olnot ws, e1) in
      [Some e]

    | Sopn.Oasm (Arch_extra.BaseOp (_, X86_instr_decl.LEA ws)) ->
      let e1 = as_seq1 es in
      let e =
        match SafetyUtils.ty_expr e1 with
        | Bty (U ws') when int_of_ws ws < int_of_ws ws' -> Papp1 (E.Ozeroext (ws, ws'), e1)
        | _ -> e1 in
      [Some e]

    | Sopn.Oasm (Arch_extra.BaseOp (_, X86_instr_decl.POPCNT ws)) ->
      let e1 = as_seq1 es in
      let t = Some (Pbool true) in
      [t; t; t; t; zf_of_word ws e1; None]

    | Sopn.Oslh op ->
      begin match op with
      | SLHinit -> [Some (pcast U64 (Pconst (Z.of_int 0)))]
      | SLHupdate ->
        let b, msf = as_seq2 es in
        let msf = Pif (Bty (U U64), b, msf, pcast U64 (Pconst (Z.of_int (-1)))) in
        [Some msf]
      | SLHmove -> let msf = as_seq1 es in [Some msf]
      | SLHprotect _ | SLHprotect_ptr _ ->
        let x, _msf = as_seq2 es in
        [Some x]
      | SLHprotect_ptr_fail _ -> assert false
      end

    | _ ->
      debug (fun () ->
          Format.eprintf "Warning: unknown opn %a, default to ⊤.@."
            (PrintCommon.pp_opn pd asmOp) opn);
      opn_dflt n

  let post_opn (opn : extended_op Sopn.sopn) (lvs : int glval list) (es : expr list) : btcons list =
    match opn with
    | Sopn.Oasm (Arch_extra.BaseOp (x, X86_instr_decl.POPCNT ws)) -> (
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

  let opn_heur pd asmOp (opn : extended_op Sopn.sopn) v es =
    match opn with
    | Sopn.Opseudo_op (Osubcarry _) ->
      Some { fh_zf = None;
             fh_cf = Some (Mtexpr.binop Texpr1.Add
                             (Mtexpr.var v)
                             (Mtexpr.cst (Coeff.s_of_int 1))); }

    | Sopn.Oasm (Arch_extra.BaseOp (x, X86_instr_decl.DEC _)) ->
      assert (x = None);
      Some { fh_zf = Some (Mtexpr.var v);
             fh_cf = Some (Mtexpr.binop Texpr1.Add
                             (Mtexpr.var v)
                             (Mtexpr.cst (Coeff.s_of_int 1))); }

    | Sopn.Oasm (Arch_extra.BaseOp (x, X86_instr_decl.CMP _)) ->
      assert (x = None);
      let exception Opn_heur_failed in
      let rec to_mvar = function
        | Pvar x ->
          (* check_is_word x; *)  (* TODO: re-add this sanity check if needed *)
          Mtexpr.var (mvar_of_var x)
        | Papp1 (E.Oword_of_int _, e) -> to_mvar e
        | Papp1 (E.Oint_of_word (s, _), e) ->
          assert (s = Signed);
          to_mvar e
        | _ -> raise Opn_heur_failed in
      let el, er = as_seq2 es in
      begin try
        let el, er = to_mvar el, to_mvar er in
        Some { fh_zf = Some (Mtexpr.binop Texpr1.Sub el er);
               fh_cf = Some (Mtexpr.binop Texpr1.Sub el er); }
      with Opn_heur_failed -> None end

    | _ ->
      debug (fun () ->
          Format.eprintf "No heuristic for the return flags of %a@."
            (PrintCommon.pp_opn pd asmOp) opn);
      None

  let pp_flags_heur fmt fh =
    Format.fprintf fmt "@[<hv 0>zf: %a;@ cf %a@]"
      (SafetyUtils.pp_opt Mtexpr.print) (fh.fh_zf)
      (SafetyUtils.pp_opt Mtexpr.print) (fh.fh_cf)

  let get_fh_zf fh = fh.fh_zf
  let get_fh_cf fh = fh.fh_cf
end

(** ARMv7-M architecture implementation *)
module ARMSafetyArch : SafetyArch with type extended_op = (Arm_decl.register, Arch_utils.empty, Arch_utils.empty, Arm_decl.rflag, Arm_decl.condt, Arm_instr_decl.arm_op, Arm_extra.arm_extra_op) Arch_extra.extended_op = struct
  type extended_op = (Arm_decl.register, Arch_utils.empty, Arch_utils.empty, Arm_decl.rflag, Arm_decl.condt, Arm_instr_decl.arm_op, Arm_extra.arm_extra_op) Arch_extra.extended_op

  (* For now, use generic implementation for ARM *)
  (* Architecture-specific operations can be added incrementally as needed *)
  
  let is_comparison _ _ = None

  let split_opn _pd _asmOp n _opn _es =
    (* Default: all outputs are unknown (Top) *)
    List.init n (fun _ -> None)

  let post_opn _opn _lvs _es = []

  type flags_heur = {
    fh_zf : Mtexpr.t option;
    fh_cf : Mtexpr.t option;
  }

  let opn_heur _pd _asmOp _opn _v _es = None

  let pp_flags_heur fmt fh =
    Format.fprintf fmt "@[<hv 0>zf: %a;@ cf %a@]"
      (SafetyUtils.pp_opt Mtexpr.print) (fh.fh_zf)
      (SafetyUtils.pp_opt Mtexpr.print) (fh.fh_cf)

  let get_fh_zf fh = fh.fh_zf
  let get_fh_cf fh = fh.fh_cf
end

(** RISC-V architecture implementation *)
module RISCVSafetyArch : SafetyArch with type extended_op = (Riscv_decl.register, Arch_utils.empty, Arch_utils.empty, Arch_utils.empty, Riscv_decl.condt, Riscv_instr_decl.riscv_op, Riscv_extra.riscv_extra_op) Arch_extra.extended_op = struct
  type extended_op = (Riscv_decl.register, Arch_utils.empty, Arch_utils.empty, Arch_utils.empty, Riscv_decl.condt, Riscv_instr_decl.riscv_op, Riscv_extra.riscv_extra_op) Arch_extra.extended_op

  (* For now, use generic implementation for RISC-V *)
  (* Architecture-specific operations can be added incrementally as needed *)
  
  let is_comparison _ _ = None

  let split_opn _pd _asmOp n _opn _es =
    (* Default: all outputs are unknown (Top) *)
    List.init n (fun _ -> None)

  let post_opn _opn _lvs _es = []

  type flags_heur = {
    fh_zf : Mtexpr.t option;
    fh_cf : Mtexpr.t option;
  }

  let opn_heur _pd _asmOp _opn _v _es = None

  let pp_flags_heur fmt fh =
    Format.fprintf fmt "@[<hv 0>zf: %a;@ cf %a@]"
      (SafetyUtils.pp_opt Mtexpr.print) (fh.fh_zf)
      (SafetyUtils.pp_opt Mtexpr.print) (fh.fh_cf)

  let get_fh_zf fh = fh.fh_zf
  let get_fh_cf fh = fh.fh_cf
end
