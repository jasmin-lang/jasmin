open Jasmin
open Prog
open SafetyExpr
open SafetyVar
open SafetyConstr

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

  type flags_heur = {
    fh_zf : Mtexpr.t option;
    fh_cf : Mtexpr.t option;
  }

  val opn_heur :
    extended_op ->
    mvar ->
    expr list ->
    flags_heur option

  val pp_flags_heur : Format.formatter -> flags_heur -> unit
  val get_fh_zf : flags_heur -> Mtexpr.t option
  val get_fh_cf : flags_heur -> Mtexpr.t option
end


