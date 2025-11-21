open Jasmin
open Prog
open SafetyExpr
open SafetyVar
open SafetyConstr

(* Ugly handling of flags to build.
   When adding new flags, update [find_heur]. *)
type flags_heur = {
    fh_zf : Mtexpr.t option;
    fh_cf : Mtexpr.t option;
}

let pp_flags_heur fmt fh =
  Format.fprintf fmt "@[<hv 0>zf: %a;@ cf %a@]"
    (SafetyUtils.pp_opt Mtexpr.print) (fh.fh_zf)
    (SafetyUtils.pp_opt Mtexpr.print) (fh.fh_cf)

let get_fh_zf fh = fh.fh_zf
let get_fh_cf fh = fh.fh_cf

(** Architecture abstraction for the safety checker *)
module type SafetyArch = sig
  include Arch_full.Arch

  val is_comparison : extended_op -> expr list -> (expr * expr) option

  val is_conditional :
    lvals -> Expr.assgn_tag -> extended_op -> exprs -> (expr * ('info, extended_op) instr_r list * ('info, extended_op) instr_r list) option

  (** Architecture-specific assembly operation splitting *)
  val split_asm_opn :
    int ->
    extended_op ->
    expr list ->
    expr option list

  val post_opn :
    extended_op ->
    (int glval) list ->
    expr list ->
    btcons list

  val opn_heur :
    extended_op ->
    mvar ->
    expr list ->
    flags_heur option
end
