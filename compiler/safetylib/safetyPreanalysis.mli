open Jasmin
open Prog

type minfo = { i_instr_number : int; }

module MkUniq : sig
  val mk_uniq :
    (unit, 'asm) func -> (unit, 'asm) prog -> (minfo, 'asm) func * (minfo, 'asm) prog
end

module type PreAnalysisSig = sig
  type extended_op

  type dp = Sv.t Mv.t
  type cfg = Sf.t Mf.t
  type pa_res = {
    pa_dp : dp;
    pa_cfg : cfg;
    while_vars : Sv.t;
    if_conds : expr list;
  }
  
  val dp_v : dp -> var -> Sv.t
  val pa_make :
    ('info, extended_op) func -> ('info, extended_op) prog option -> pa_res
  val print_dp : Format.formatter -> dp -> unit
  val print_cfg : Format.formatter -> cfg -> unit
end

module MakePreAnalysis(Arch : SafetyArch.SafetyArch) : PreAnalysisSig with type extended_op = Arch.extended_op

(* Generic flow-sensitive pre-analysis functor *)
module MakeFSPreAnalysis(Arch : SafetyArch.SafetyArch) : sig
  module Pa : PreAnalysisSig with type extended_op = Arch.extended_op

  val fs_pa_make :
    Wsize.wsize ->
    ('info, Arch.extended_op) func -> (unit, Arch.extended_op) func * Pa.pa_res

(*---------------------------------------------------------------*)
val trans_closure : Sv.t Mv.t -> Sv.t Mv.t
val flow_to       : Sv.t Mv.t -> Sv.t -> Sv.t
val flowing_to    : Sv.t Mv.t -> Sv.t -> Sv.t
val leads_to      : Sv.t Mv.t -> Sv.t -> Sv.t

end 
    
val decompose_address : 'a gexpr -> 'a gvar * 'a gexpr