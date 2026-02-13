open Jasmin
open Utils
open Prog
open Apron
open Wsize
open Operators

open SafetyUtils
open SafetyExpr
open SafetyVar
open SafetyConstr
open SafetyArch
open SafetyAbsExpr

(** X86-64 architecture implementation *)
module X86_safety
  (A: Arch_full.Arch
      with type reg = X86_decl.register
       and type regx = X86_decl.register_ext
       and type xreg = X86_decl.xmm_register
       and type rflag = X86_decl.rflag
       and type cond = X86_decl.condt
       and type asm_op = X86_instr_decl.x86_op
       and type extra_op = X86_extra.x86_extra_op)
  : SafetyArch
    with type reg = X86_decl.register
     and type regx = X86_decl.register_ext
     and type xreg = X86_decl.xmm_register
     and type rflag = X86_decl.rflag
     and type cond = X86_decl.condt
     and type asm_op = X86_instr_decl.x86_op
     and type extra_op = X86_extra.x86_extra_op
  = struct

  include A

  (* -------------------------------------------------------------------- *)
  (* Return flags for the different operations.
     This covers a subset of the x86 flags, as described in the Coq
     semantics (x86_instr_decl.v). *)

  (* Carry flag is true if [w] and [vu] are not equal. *)
  let cf_of_word sz w vu =
    Some (Papp2 (Oneq Op_int,
                 Papp1(E.uint_of_word sz,w),
                 vu))

  (* FIXME *)
  let sf_of_word _sz _w = None
  (* msb w. *)

  (* FIXME *)
  let pf_of_word _sz _w = None
  (* lsb w. *)

  let zf_of_word sz w =
    Some (Papp2 (Oeq (Op_w sz),
                 w,
                 pcast sz (Pconst (Z.of_int 0))))

  let rflags_of_aluop sz w vu _vs =
    let of_f = None               (* FIXME *)
    and cf   = cf_of_word sz w vu
    and sf   = sf_of_word sz w
    and pf   = pf_of_word sz w
    and zf   = zf_of_word sz w in
    [of_f;cf;sf;pf;zf]

  (* For the SUB (without carry) and CMP operation, we manually set
     the flags to have simpler and more precise expressions for the
     carry and zero flags. *)
  let rflags_of_sub sz w1 w2 =
    let sub = Papp2 (Osub (Op_w sz), w1, w2) in
    let of_f = None               (* FIXME *)
    and cf   = Some (Papp2 (Olt (Cmp_w (Unsigned, sz)), w1,w2))
    and sf   = sf_of_word sz sub
    and pf   = pf_of_word sz sub
    and zf   = Some (Papp2 (Oeq (Op_w sz), w1,w2))
    in
    [of_f;cf;sf;pf;zf]

  let rflags_of_bwop sz w =
    let of_f = Some (Pbool false)
    and cf   = Some (Pbool false)
    and sf   = sf_of_word sz w
    and pf   = pf_of_word sz w
    and zf   = zf_of_word sz w in
    [of_f;cf;sf;pf;zf]

  let rflags_of_neg sz w _vs =
    let of_f = None               (* FIXME, same than for rflags_of_aluop *)
    and cf   = None               (* FIXME, must be (w != 0)*)
    and sf   = sf_of_word sz w
    and pf   = pf_of_word sz w
    and zf   = zf_of_word sz w in
    [of_f;cf;sf;pf;zf]

  let rflags_of_mul (ov : bool option) =
    (*  OF; CF; SF; PF; ZF *)
    [Some ov; Some ov; None; None; None]

  let rflags_unknwon =
    (*  OF; CF; SF; PF; ZF *)
    [None; None; None; None; None]

  let rflags_of_div =
    (*  OF; CF; SF; PF; ZF *)
    rflags_unknwon

  let rflags_of_andn sz w =
    let of_f = Some (Pbool false)
    and cf   = Some (Pbool false)
    and sf   = sf_of_word sz w
    and pf   = None
    and zf   = zf_of_word sz w in
    [of_f;cf;sf;pf;zf]

  (* Remove the carry flag *)
  let nocf = function
    | [of_f;_;sf;pf;zf] -> [of_f;sf;pf;zf]
    | _ -> assert false

  let opn_dflt n = List.init n (fun _ -> None)

  let opn_bin_gen f_flags ws op op_int es =
    let el,er = as_seq2 es in
    let w = Papp2 (op, el, er) in
    let vu = Papp2 (op_int,
                    Papp1(E.uint_of_word ws,el),
                    Papp1(E.uint_of_word ws,er)) in
    let vs = () in              (* FIXME *)
    let rflags = f_flags ws w vu vs in
    rflags @ [Some w]

  let opn_bin_alu = opn_bin_gen rflags_of_aluop

  let opn_sub sz es =
    let el,er = as_seq2 es in
    let w = Papp2 (Osub (Op_w sz), el, er) in
    let rflags = rflags_of_sub sz el er in
    rflags @ [Some w]

  let is_comparison (opn : extended_op) : bool =
    match opn with
    | Arch_extra.BaseOp (_, X86_instr_decl.CMP _) -> true
    | _ -> false

  let is_conditional lvs tag op es =
    match op with
    | Arch_extra.BaseOp (x, X86_instr_decl.CMOVcc sz) ->
      assert (x = None);
      let c,el,er = as_seq3 es in
      let lv = as_seq1 lvs in
      let cl = [Cassgn (lv, tag, Bty (U sz), el)] in
      let cr = [Cassgn (lv, tag, Bty (U sz), er)] in
      Some (c, cl, cr)
    | _ -> None

  (* -------------------------------------------------------------------- *)
  (* Remark: the assignments must be done in the correct order.
     Bitwise operators are ignored for now (result is soundly set to top).
     See x86_instr_decl.v for a desciption of the operators. *)
  let split_asm_opn n (opn : extended_op) es =
    match opn with
    | Arch_extra.ExtOp X86_extra.Oset0 ws ->
      let zero = Some (pcast ws (Pconst (Z.of_int 0))) in
      begin match wsize_cmp U64 ws with
      | Lt -> [ zero ]
      | _ -> [ None; None; None; None; None; zero ]
      end

    | Arch_extra.ExtOp X86_extra.Ox86MOVZX32 ->
      let e = as_seq1 es in
      (* Cast [e], seen as an U32, to an integer, and then back to an U64. *)
      [Some (Papp1(Oword_of_int U64, Papp1(E.uint_of_word U32, e)))]

    (* Idem than Ox86MOVZX32, but with different sizes. *)
    | Arch_extra.BaseOp (None, X86_instr_decl.MOVZX (sz_o, sz_i)) ->
      assert (int_of_ws sz_o >= int_of_ws sz_i);
      let e = as_seq1 es in
      [Some (Papp1(Oword_of_int sz_o, Papp1(E.uint_of_word sz_i, e)))]

    (* CMP flags are identical to SUB flags. *)
    | Arch_extra.BaseOp (_, X86_instr_decl.CMP ws) ->
      (* Input types: ws, ws *)
      let el,er = as_seq2 es in
      rflags_of_sub ws el er

    (* add unsigned / signed *)
    | Arch_extra.BaseOp (None, X86_instr_decl.ADD ws) ->
      opn_bin_alu ws (Oadd (Op_w ws)) (Oadd Op_int) es

    (* sub unsigned / signed *)
    | Arch_extra.BaseOp (None, X86_instr_decl.SUB ws) ->
      opn_sub ws es

    (* mul unsigned *)
    | Arch_extra.BaseOp (None, X86_instr_decl.MUL ws)

    (* mul signed *)
    (* since, for now, we ignore the upper-bits,
       we do the same thing than for unsigned multiplication. *)
    | Arch_extra.BaseOp (None, X86_instr_decl.IMUL ws) ->
      let el,er = as_seq2 es in
      let w = Papp2 (Omul (Op_w ws), el, er) in
      (* FIXME: overflow bit to have the precise flags *)
      (* let ov = ?? in
       * let rflags = rflags_of_mul ov in *)
      let rflags = [None; None; None; None; None] in
      (*          high, low   *)
      rflags @ [  None; Some w]

    (* mul signed, no higher-bits *)
    | Arch_extra.BaseOp (None, X86_instr_decl.IMULr ws)
    | Arch_extra.BaseOp (None, X86_instr_decl.IMULri ws) ->
      let el,er = as_seq2 es in
      let w = Papp2 (Omul (Op_w ws), el, er) in
      (* FIXME: overflow bit to have the precise flags *)
      (* let ov = ?? in
       * let rflags = rflags_of_mul ov in *)
      let rflags = [None; None; None; None; None] in
      (*        low   *)
      rflags @ [Some w]

    (* div unsigned *)
    | Arch_extra.BaseOp (None, X86_instr_decl.DIV ws) ->
      let n, d = split_div Unsigned ws es in
      let w = Papp1 (Oword_of_int ws, Papp2 (Odiv(Unsigned, Op_int), n, d)) in
      let rflags = rflags_of_div in
      rflags @ [None; Some w]

    (* div signed *)
    | Arch_extra.BaseOp (None, X86_instr_decl.IDIV ws) ->
      let n, d = split_div Signed ws es in
      let w = Papp1 (Oword_of_int ws, Papp2 (Odiv(Unsigned, Op_int), n, d)) in
      let rflags = rflags_of_div in
      rflags @ [None; Some w]

    (* increment *)
    | Arch_extra.BaseOp (None, X86_instr_decl.INC ws) ->
      let e = Utils.as_seq1 es in
      let w = Papp2 (Oadd (Op_w ws), e,
                     Papp1(Oword_of_int ws, Pconst (Z.of_int 1))) in
      let vu = Papp2 (Oadd Op_int,
                      Papp1(E.uint_of_word ws,e),
                      Pconst (Z.of_int 1)) in
      let vs = () in
      let rflags = nocf (rflags_of_aluop ws w vu vs) in
      rflags @ [Some w]

    (* decrement *)
    | Arch_extra.BaseOp (None, X86_instr_decl.DEC ws) ->
      let e = as_seq1 es in
      let w = Papp2 (Osub (Op_w ws), e,
                     Papp1(Oword_of_int ws,Pconst (Z.of_int 1))) in
      let vu = Papp2 (Osub Op_int,
                      Papp1(E.uint_of_word ws,e),
                      Pconst (Z.of_int 1)) in
      let vs = () in
      let rflags = nocf (rflags_of_aluop ws w vu vs) in
      rflags @ [Some w]

    (* negation *)
    | Arch_extra.BaseOp (None, X86_instr_decl.NEG ws) ->
      let e = as_seq1 es in
      let w = Papp1 (Oneg (Op_w ws), e) in
      let vs = () in
      let rflags = rflags_of_neg ws w vs in
      rflags @ [Some w]

    (* copy *)
    | Arch_extra.BaseOp (None, X86_instr_decl.MOV _) ->
      let e = as_seq1 es in
      [Some e]

    (* shift, unsigned / left  *)
    | Arch_extra.BaseOp (None, X86_instr_decl.SHL ws) ->
      let e1, e2 = as_seq2 es in
      let e = Papp2 (Olsl (Op_w ws), e1, e2) in
      rflags_unknwon @ [Some e]

    (* shift, unsigned / right  *)
    | Arch_extra.BaseOp (None, X86_instr_decl.SHR ws) ->
      let e1, e2 = as_seq2 es in
      let e = Papp2 (Olsr ws, e1, e2) in
      rflags_unknwon @ [Some e]

    (* shift, signed / right  *)
    | Arch_extra.BaseOp (None, X86_instr_decl.SAR ws) ->
      let e1, e2 = as_seq2 es in
      let e = Papp2 (Oasr (Op_w ws), e1, e2) in
      rflags_unknwon @ [Some e]

    (* FIXME: adding bit shift with flags *)
    (*
    | ROR    of wsize    (* rotation / right *)
    | ROL    of wsize    (* rotation / left  *)
    | RCR    of wsize    (* rotation / right with carry *)
    | RCL    of wsize    (* rotation / left  with carry *)
    | SHL    of wsize    (* unsigned / left  *)
    | SHR    of wsize    (* unsigned / right *)
    | SAL    of wsize    (*   signed / left; synonym of SHL *)
    | SAR    of wsize    (*   signed / right *)
    | SHLD   of wsize    (* unsigned (double) / left *)
    | SHRD   of wsize    (* unsigned (double) / right *)
    | MULX    of wsize  (* mul unsigned, doesn't affect arithmetic flags *)
    | ADCX    of wsize  (* add with carry flag, only writes carry flag *)
    | ADOX    of wsize  (* add with overflow flag, only writes overflow flag *)
    *)

    (* conditional copy *)
    | Arch_extra.BaseOp (None, X86_instr_decl.CMOVcc sz) ->
      let c,el,er = as_seq3 es in
      let e = Pif (Bty (U sz), c, el, er) in
      [Some e]

    (* bitwise operators *)
    | Arch_extra.BaseOp (None, X86_instr_decl.AND ws) ->
      let e1, e2 = as_seq2 es in
      let e = Papp2 (Oland ws, e1, e2) in
      rflags_unknwon @ [Some e]

    | Arch_extra.BaseOp (None, X86_instr_decl.OR ws) ->
      let e1, e2 = as_seq2 es in
      let e = Papp2 (Olor ws, e1, e2) in
      rflags_unknwon @ [Some e]

    | Arch_extra.BaseOp (None, X86_instr_decl.XOR ws) ->
      let e1, e2 = as_seq2 es in
      let e = Papp2 (Olxor ws, e1, e2) in
      rflags_unknwon @ [Some e]

    | Arch_extra.BaseOp (None, X86_instr_decl.NOT ws) ->
      let e1 = as_seq1 es in
      let e = Papp1 (Olnot ws, e1) in
      [Some e]

    | Arch_extra.BaseOp (_, X86_instr_decl.LEA ws) ->
      let e1 = as_seq1 es in
      let e =
        match ty_expr e1 with
        | Bty (U ws') when int_of_ws ws < int_of_ws ws' -> Papp1 (Ozeroext (ws, ws'), e1)
        | _ -> e1 in
      [Some e]

    | Arch_extra.BaseOp (_, X86_instr_decl.POPCNT ws) ->
      let e1 = as_seq1 es in
      let t = Some (Pbool true) in
      [ t; t; t; t; zf_of_word ws e1; None ]

    | _ ->
      debug (fun () ->
          Format.eprintf "Warning: unknown opn %a, default to ⊤.@."
            (PrintCommon.pp_opn pointer_data msf_size asmOp) (Sopn.Oasm opn));
      opn_dflt n

  (* Post-conditions of operators, that cannot be precisely expressed as an expression of the arguments *)
  let post_opn opn lvs es : btcons list =
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
            | [ Pvar e ] when not (is_gkvar e && GV.equal (L.unloc e.gv) xv)->
               (* Only sound when destination [x] does not occur in the argument [e] *)
                let e =
                  if is_gkvar e then Mlocal (Avar (L.unloc e.gv))
                  else Mglobal (Avar (L.unloc e.gv))
                in
                (* -e > 0 ∨ e - 255 > 0 ∨ x - [0; 8] = 0 *)
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
                [ BOr (BOr (e_neg, e_large), range_btcons x 8) ]
            | _ -> [])
        | _ -> [])
    | _ -> []

  (* [v] is the variable receiving the assignment. *)
  let opn_heur (opn : extended_op) v es =
    match opn with
    (* decrement *)
    | Arch_extra.BaseOp (x, X86_instr_decl.DEC _) ->
      assert (x = None);
      Some { fh_zf = Some (Mtexpr.var v);
             fh_cf = Some (Mtexpr.binop Texpr1.Add
                             (Mtexpr.var v)
                             (Mtexpr.cst (Coeff.s_of_int 1))); }

    (* compare *)
    | Arch_extra.BaseOp (x, X86_instr_decl.CMP _) ->
      assert (x = None);
      let exception Opn_heur_failed in
      let rec to_mvar = function
        | Pvar x ->
          check_is_word x;
          Mtexpr.var (mvar_of_var x)
        | Papp1 (Oword_of_int _, e) -> to_mvar e
        | Papp1 (Oint_of_word (s, _), e) ->
          assert (s = Signed); (* FIXME wint2 *)
          to_mvar e
        | _ -> raise Opn_heur_failed in
      let el, er = as_seq2 es in
      begin try
        let el, er = to_mvar el, to_mvar er in
        Some { fh_zf = Some (Mtexpr.binop Texpr1.Sub el er);
               fh_cf = Some (Mtexpr.binop Texpr1.Sub el er); }
      with Opn_heur_failed -> None end

    (* (\* sub with borrow *\)
     * | Arch_extra.BaseOp (X86_instr_decl.SBB _) *)
    | _ ->
      debug (fun () ->
          Format.eprintf "No heuristic for the return flags of %a@."
            (PrintCommon.pp_opn pointer_data msf_size asmOp) (Sopn.Oasm opn));
      None

end
