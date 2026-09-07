(* ARMv8-A (AArch64) architecture parameters for the compiler passes. *)

From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype.
From mathcomp Require Import ssralg.
From mathcomp Require Import word_ssrZ.

Require Import
  arch_params
  compiler_util
  constant_prop
  expr
  fexpr
  shift_kind.
Require Import
  lea
  linearization
  lowering
  stack_alloc_params
  stack_zeroization
  slh_lowering.
Require Import
  arch_decl
  arch_extra
  asm_gen.
Require Import
  armv8a_decl
  armv8a_extra
  armv8a_instr_decl
  armv8a_params_core
  armv8a_lowering
  armv8a_stack_zeroization.

Section Section.
Context {atoI : arch_toIdent}.

(* Wrappers turning [ARMv8AFopn_core] argument triples into [fopn_args]. *)
Definition to_opn '(d, o, e) : fopn_args := (d, Oarmv8a o, e).

Definition ARMv8AFopn_mov x y   := to_opn (ARMv8AFopn_core.mov x y).
Definition ARMv8AFopn_addi x y imm := to_opn (ARMv8AFopn_core.addi x y imm).
Definition ARMv8AFopn_subi x y imm := to_opn (ARMv8AFopn_core.subi x y imm).
Definition ARMv8AFopn_align x y al := to_opn (ARMv8AFopn_core.align x y al).

Definition ARMv8AFopn_smart_addi x y imm :=
  map to_opn (ARMv8AFopn_core.smart_addi x y imm).

Definition ARMv8AFopn_smart_subi x y imm :=
  map to_opn (ARMv8AFopn_core.smart_subi x y imm).

Definition ARMv8AFopn_smart_addi_tmp x tmp imm :=
  map to_opn (ARMv8AFopn_core.smart_addi_tmp x tmp imm).

Definition ARMv8AFopn_smart_subi_tmp x tmp imm :=
  map to_opn (ARMv8AFopn_core.smart_subi_tmp x tmp imm).

(* ------------------------------------------------------------------------ *)
(* Stack alloc parameters. *)

Definition armv8a_mov_ofs
  (x : lval) (tag : assgn_tag) (movk : mov_kind) (y : pexpr) (ofs : pexpr) :
  option instr_r :=
  let mk oa :=
    let: (op, args) := oa in
     Some (Copn [:: x ] tag (Oarmv8a (ARMv8A_op op default_opts)) args) in
  match movk with
  | MK_LEA => mk (ADR, [:: if is_zero Uptr ofs then y else add y ofs ])
  | MK_MOV =>
    match x with
    | Lvar x_ =>
      if is_Pload y then
        if is_zero Uptr ofs then mk (LDR, [:: y ]) else None
      else
        match mk_lea Uptr (add y ofs) with
        | None => None
        | Some lea =>
          match lea.(lea_base), lea.(lea_offset) with
          | None, _ => None (* impossible *)
          | Some base, None =>
            if lea.(lea_disp) == 0%Z then mk (MOV, [:: Plvar base ])
            else
              (* This allows to remove constraint in register allocation *)
              if is_arith_small lea.(lea_disp) then mk (ADD, [:: Plvar base; cast_const lea.(lea_disp) ])
              else
                Some (Copn [:: x ] tag (Oasm (ExtOp Oarmv8a_add_large_imm)) [:: Plvar base; cast_const lea.(lea_disp) ])
          | Some base, Some off =>
            if lea.(lea_disp) == 0%Z then
              let%opt scale := Option.map Z.of_nat (shift_of_scale lea.(lea_scale)) in
              if scale == 0%Z then
                (* we have a special case to avoid a trivial shift of 0 *)
                mk (ADD, [:: Plvar base; Plvar off ])
              else
                let opts := {| has_shift := Some SLSL; opts_size := U64 |} in
                Some (Copn [:: x ] tag (Oarmv8a (ARMv8A_op ADD opts)) [:: Plvar base; Plvar off; eword_of_int U8 scale ])
            else None
          end
        end
    | Lmem _ _ _ _ =>
      if is_zero Uptr ofs then mk (STR, [:: y ]) else None
    | _ => None
    end
  end.

Definition armv8a_immediate (x : var_i) z :=
  Copn [:: Lvar x ] AT_none (Oasm (ExtOp (Oarmv8a_smart_li reg_size))) [:: cast_const z ].

Definition armv8a_swap t (x y z w : var_i) :=
  Copn [:: Lvar x; Lvar y] t (Oasm (ExtOp (Oarmv8a_swap reg_size))) [:: Plvar z; Plvar w].

Definition armv8a_saparams : stack_alloc_params :=
  {|
    sap_mov_ofs := armv8a_mov_ofs;
    sap_immediate := armv8a_immediate;
    sap_swap := armv8a_swap;
  |}.

(* ------------------------------------------------------------------------ *)
(* Linearization parameters. *)

Section LINEARIZATION.

(* X16 and X17 are the AAPCS64 intra-procedure-call scratch registers. *)
Notation vtmpi  := (mk_var_i (to_var R16)).
Notation vtmp2i := (mk_var_i (to_var R17)).

(* --- SP 16-byte alignment invariant --------------------------------------

   On AArch64 the stack pointer must be quadword (16-byte) aligned whenever it
   is used as the base of a memory access. This is an architectural check, not
   merely an ABI convention:

     "When the SP is used as the base address of a calculation, regardless of
      any offset applied by the instruction, if bits [3:0] of the SP are not
      0b0000, there is a misaligned SP." (Arm ARM DDI0487M.a, D1.4.10.2 "SP
      alignment checking", rule RRDMXG, p. D1-7135.)
     "If SP alignment checking is enabled, then the execution of a load or store
      using the SP with a misaligned SP generates a synchronous SP Alignment
      exception on that load or store." (ibid., rule RTFVSM.)

   The check is enabled by SCTLR_ELx.SA / SCTLR_EL1.SA0 (ibid., rule RSTDYJ) and
   is on for EL0 on the platforms we target (e.g. Linux, Apple). See also the
   16-byte stack-alignment requirement of the AAPCS64 (Arm IHI 0055F, "The
   stack", "SP mod 16 = 0" at a public interface), referenced from DDI0487M.a
   B1.2, p. B1-203.

   Jasmin sizes each stack frame to the alignment of the objects it holds
   (sao_align), which for pure 64-bit code would be only 8 bytes, so a raw
   frame size need not be a multiple of 16. The invariant is maintained on
   the oracle side: the stack-alloc oracle raises every function's
   [sao_align] to at least U128 ([sp_min_align] in
   compiler/src/arch_full.ml, applied in varalloc.ml), and frame
   allocations are rounded up to the frame alignment
   ([stack_frame_allocation_size], linearization.v), so every SP
   adjustment is a multiple of 16 and export entry alignment (guaranteed
   16-byte by the platform) is preserved across calls. The operations
   below therefore adjust SP by exactly the size they are given, as the
   [h_linearization_params] specification requires. *)

Definition armv8a_allocate_stack_frame (rspi : var_i) (tmp : option var_i) (sz : Z) :=
  if tmp is Some aux then
    ARMv8AFopn_smart_subi_tmp rspi aux sz
  else
    [:: ARMv8AFopn_subi rspi rspi sz].

Definition armv8a_free_stack_frame (rspi : var_i) (tmp : option var_i) (sz : Z) :=
  if tmp is Some aux then
    ARMv8AFopn_smart_addi_tmp rspi aux sz
  else
    [:: ARMv8AFopn_addi rspi rspi sz].

Definition armv8a_set_up_sp_register
  (rspi : var_i)
  (sf_sz : Z)
  (al : wsize)
  (r : var_i)
  (tmp : var_i) :
  seq fopn_args :=
  (* [al] is the frame's [sao_align], which the oracle guarantees is at
     least U128 (16 bytes); see the SP alignment invariant above. *)
  let load_imm := ARMv8AFopn_smart_subi tmp rspi sf_sz in
  let i0 := ARMv8AFopn_align tmp tmp al in
  let i1 := ARMv8AFopn_mov r rspi in
  let i2 := ARMv8AFopn_mov rspi tmp in
  load_imm ++ [:: i0; i1; i2 ].

Definition armv8a_tmp  : Ident.ident := vname (v_var vtmpi).
Definition armv8a_tmp2 : Ident.ident := vname (v_var vtmp2i).

Definition armv8a_lmove (_ : wsize) (xd xs : var_i) :=
  ([:: LLvar xd], Oarmv8a (ARMv8A_op MOV default_opts), [:: Rexpr (Fvar xs)]).

Definition armv8a_check_ws ws := ws == reg_size.

Definition armv8a_lstore (ws : wsize) (xd : var_i) (ofs : Z) (xs : var_i) :=
  let mn := STR in
  ([:: Store Aligned ws (faddv Uptr xd (fconst ws ofs))], Oarmv8a (ARMv8A_op mn default_opts), [:: Rexpr (Fvar xs)]).

Definition armv8a_lload (ws : wsize) (xd : var_i) (xs : var_i) (ofs : Z) :=
  let mn := LDR in
  ([:: LLvar xd], Oarmv8a (ARMv8A_op mn default_opts), [:: Load Aligned ws (faddv Uptr xs (fconst ws ofs))]).

(* Restore saved values from the stack. Unlike ARMv7 (where SP/R13 is an
   ordinary register that LDR can target), an A64 load writes its result through
   the general-purpose (X[]) register accessor, for which register number 31 is
   the zero register ZR, not SP (Arm ARM DDI0487M.a, B1.2, p. B1-206; and the
   LDR encoding takes <Xt>, never <Xt|SP>). The stack-pointer slot therefore
   cannot be reloaded directly: the saved registers are restored first (relative
   to the still-live SP), then the saved stack pointer is loaded into the scratch
   register X17 and copied to SP with a MOV (which reaches SP via the SP[]
   accessor). Large offsets are materialized into X17 as in [lloads_imm_dfl]. *)
Definition armv8a_lloads (rspi : var_i) (to_restore : seq (var * Z)) (spofs : Z) :
    seq fopn_args :=
  let restore_regs :=
    if all (fun '(_, ofs) => is_arith_small ofs) to_restore then
      map (fun '(x, ofs) =>
             armv8a_lload (wsize_of_atype (vtype x)) (VarI x dummy_var_info) rspi ofs)
          to_restore
    else
      let ofs0 := snd (head (v_var rspi, 0%Z) to_restore) in
      let to_restore := map (fun '(x, ofs) => (x, ofs - ofs0)%Z) to_restore in
      ARMv8AFopn_smart_addi vtmp2i rspi ofs0
        ++ map (fun '(x, ofs) =>
                  armv8a_lload (wsize_of_atype (vtype x)) (VarI x dummy_var_info) vtmp2i ofs)
               to_restore
  in
  let restore_sp :=
    if is_arith_small spofs then
      [:: armv8a_lload Uptr vtmp2i rspi spofs; armv8a_lmove Uptr rspi vtmp2i ]
    else
      ARMv8AFopn_smart_addi vtmp2i rspi spofs
        ++ [:: armv8a_lload Uptr vtmp2i vtmp2i 0; armv8a_lmove Uptr rspi vtmp2i ]
  in
  restore_regs ++ restore_sp.

Definition armv8a_liparams : linearization_params :=
  {|
    lip_tmp  := armv8a_tmp;
    lip_tmp2 := armv8a_tmp2;
    lip_not_saved_stack := [:: armv8a_tmp ];
    lip_allocate_stack_frame := armv8a_allocate_stack_frame;
    lip_free_stack_frame := armv8a_free_stack_frame;
    lip_set_up_sp_register := armv8a_set_up_sp_register;
    lip_lmove := armv8a_lmove;
    lip_check_ws := armv8a_check_ws;
    lip_lstore  := armv8a_lstore;
    lip_lload := armv8a_lload;
    lip_lstores := lstores_imm_dfl armv8a_tmp2 armv8a_lstore ARMv8AFopn_smart_addi is_arith_small;
    lip_lloads  := armv8a_lloads;
  |}.

End LINEARIZATION.


(* ------------------------------------------------------------------------ *)
(* Lowering parameters. *)

#[ local ]
Definition armv8a_fvars_correct
  (fv : fresh_vars)
  {pT : progT}
  (fds : seq fun_decl) :
  bool :=
  fvars_correct (all_fresh_vars fv) (fvars fv) fds.

Definition armv8a_loparams : lowering_params :=
  {|
    lop_lower_i _ := lower_i;
    lop_fvars_correct := armv8a_fvars_correct;
  |}.


(* ------------------------------------------------------------------------ *)
(* Speculative execution operator lowering parameters. *)

Definition armv8a_shparams : sh_params :=
  {|
    shp_lower := fun _ _ _ => None;
  |}.

(* ------------------------------------------------------------------------ *)
(* Assembly generation parameters. *)

Definition condt_of_rflag (r : rflag) : condt :=
  match r with
  | NF => MI_ct
  | ZF => EQ_ct
  | CF => CS_ct
  | VF => VS_ct
  end.

Definition condt_not (c : condt) : condt :=
  match c with
  | EQ_ct => NE_ct
  | NE_ct => EQ_ct
  | CS_ct => CC_ct
  | CC_ct => CS_ct
  | MI_ct => PL_ct
  | PL_ct => MI_ct
  | VS_ct => VC_ct
  | VC_ct => VS_ct
  | HI_ct => LS_ct
  | LS_ct => HI_ct
  | GE_ct => LT_ct
  | LT_ct => GE_ct
  | GT_ct => LE_ct
  | LE_ct => GT_ct
  end.

Definition condt_and (c0 c1 : condt) : option condt :=
  match c0, c1 with
  | CS_ct, NE_ct => Some HI_ct
  | NE_ct, CS_ct => Some HI_ct
  | NE_ct, GE_ct => Some GT_ct
  | GE_ct, NE_ct => Some GT_ct
  | _, _ => None
  end.

Definition condt_or (c0 c1 : condt) : option condt :=
  match c0, c1 with
  | CC_ct, EQ_ct => Some LS_ct
  | EQ_ct, CC_ct => Some LS_ct
  | EQ_ct, LT_ct => Some LE_ct
  | LT_ct, EQ_ct => Some LE_ct
  | _, _ => None
  end.

Definition is_rflags_GE (r0 r1 : rflag) : bool :=
  match r0, r1 with
  | NF, VF => true
  | VF, NF => true
  | _, _ => false
  end.

Fixpoint assemble_cond ii (e : fexpr) : cexec condt :=
  match e with
  | Fvar v =>
      Let r := of_var_e ii v in ok (condt_of_rflag r)

  | Fapp1 Onot e =>
      Let c := assemble_cond ii e in ok (condt_not c)

  | Fapp2 Oand e0 e1 =>
      Let c0 := assemble_cond ii e0 in
      Let c1 := assemble_cond ii e1 in
      if condt_and c0 c1 is Some ct
      then ok ct
      else Error (E.berror ii e "Invalid condition (AND)")

  | Fapp2 Oor e0 e1 =>
      Let c0 := assemble_cond ii e0 in
      Let c1 := assemble_cond ii e1 in
      if condt_or c0 c1 is Some ct
      then ok ct
      else Error (E.berror ii e "Invalid condition (OR)")

  | Fapp2 Obeq (Fvar x0) (Fvar x1) =>
      Let r0 := of_var_e ii x0 in
      Let r1 := of_var_e ii x1 in
      if is_rflags_GE r0 r1
      then ok GE_ct
      else Error (E.berror ii e "Invalid condition (EQ).")

  | _ =>
      Error (E.berror ii e "Can't assemble condition.")
  end.

Definition is_valid_address (addr : reg_address) :=
  match addr.(ad_disp) != 0%w, isSome addr.(ad_offset), addr.(ad_scale) != 0 with
  | false, false, false => true
  | true, false, false => true
  | false, true, false => true
  | false, true, true => true
  | _, _, _ => false
  end.

Definition armv8a_agparams : asm_gen_params :=
  {|
    agp_assemble_cond := assemble_cond;
    agp_is_valid_address := is_valid_address;
  |}.

(* ------------------------------------------------------------------------ *)
(* Stack zeroization parameters. *)

Definition armv8a_szparams : stack_zeroization_params :=
  {|
    szp_cmd := stack_zeroization_cmd;
  |}.

(* ------------------------------------------------------------------------ *)
(* Shared parameters. *)

Definition armv8a_is_move_op (o : asm_op_t) : bool :=
  match o with
  | BaseOp (None, ARMv8A_op o opts) =>
    if o \in [:: MOV; LDR; STR; STRH; STRB ] then
      ~~ has_shift opts
    else false

  | _ =>
      false
  end.

Definition armv8a_params : architecture_params :=
  {|
    ap_sap := armv8a_saparams;
    ap_lip := armv8a_liparams;
    ap_plp := false;
    ap_lop := armv8a_loparams;
    ap_lap := {| lap_lower_address := fun _ p => ok p |};
    ap_agp := armv8a_agparams;
    ap_szp := armv8a_szparams;
    ap_shp := armv8a_shparams;
    ap_is_move_op := armv8a_is_move_op;
  |}.

End Section.
