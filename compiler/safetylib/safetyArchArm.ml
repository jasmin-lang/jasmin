open Jasmin
open SafetyExpr
open SafetyArch

(** ARMv7-M architecture implementation *)
module ARMSafetyArch : SafetyArch with type extended_op = (Arm_decl.register, Arch_utils.empty, Arch_utils.empty, Arm_decl.rflag, Arm_decl.condt, Arm_instr_decl.arm_op, Arm_extra.arm_extra_op) Arch_extra.extended_op = struct
  type extended_op = (Arm_decl.register, Arch_utils.empty, Arch_utils.empty, Arm_decl.rflag, Arm_decl.condt, Arm_instr_decl.arm_op, Arm_extra.arm_extra_op) Arch_extra.extended_op

  let pointer_data = Arch_decl.arch_pd Arm_decl.arm_decl

  (* For now, use generic implementation for ARM *)
  (* Architecture-specific operations can be added incrementally as needed *)
  
  let is_comparison _ _ = None

  (** Architecture-specific assembly operation splitting *)
  let split_asm_opn _pd _asmOp n _opn _es =
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
