open Prog

type minfo = { i_instr_number : int; }

module MkUniq : sig
  val mk_uniq :
    unit func -> unit prog -> minfo func * minfo prog
end

module Pa : sig
  type dp = Sv.t Mv.t
  type cfg = Sf.t Mf.t
  type pa_res = {
    pa_dp : dp;
    pa_cfg : cfg;
    while_vars : Sv.t;
    if_conds : expr list;
  }
  val dp_v : dp -> var -> Sv.t
  val pa_make : 'info func -> 'info prog option -> pa_res
  val print_dp : Format.formatter -> dp -> unit
  val print_cfg : Format.formatter -> cfg -> unit
end

module FSPa : sig
  val fs_pa_make : 'info func -> unit func * Pa.pa_res
end

(*---------------------------------------------------------------*)
val trans_closure : Pa.dp -> Pa.dp
val flow_to       : Pa.dp -> Sv.t -> Sv.t
val flowing_to    : Pa.dp -> Sv.t -> Sv.t
