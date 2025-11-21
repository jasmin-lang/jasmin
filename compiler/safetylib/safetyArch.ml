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

(** Architecture abstraction for the safety checker *)
module type SafetyArch = sig
  include Arch_full.Arch

  val is_comparison : extended_op -> bool

  val is_conditional :
    lvals -> Expr.assgn_tag -> extended_op -> exprs ->
    (expr * ('info, extended_op) instr_r list * ('info, extended_op) instr_r list) option
  (** [is_conditional lvs tag opn es] analyzes instruction [Copn lvs tag opn es],
      and specifies whether it is a conditional instruction.
      If it is not, it returns [None].
      If it is, it returns [Some (b, c1, c2)], where [b] is the condition,
      [c1] is an equivalent code when [b] is true, and [c2] is an equivalent
      code when [b] is false. Intuitively, the execution of [Copn lvs tag opn es]
      is equivalent to "if b then c1 else c2".
      This function is used only when option [Safety_config.sc_pif_movecc_as_if ()] is set. *)

  val split_asm_opn :
    int ->
    extended_op ->
    expr list ->
    expr option list
  (** Architecture-specific assembly operation splitting *)

  val post_opn :
    extended_op ->
    (int glval) list ->
    expr list ->
    btcons list
  (** Post-conditions of operators, that cannot be precisely expressed as an expression of the arguments *)

  val opn_heur :
    extended_op ->
    mvar ->
    expr list ->
    flags_heur option
  (** Heuristic for flags *)
end
