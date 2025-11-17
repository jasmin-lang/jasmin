open Jasmin
open Prog
open SafetyExpr
open SafetyVar
open SafetyConstr

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
  type extended_op

  val pointer_data : Wsize.wsize

  val is_comparison : extended_op -> expr list -> (expr * expr) option

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
