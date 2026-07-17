open Jasmin

module type ArchWithAnalyze = sig
  module A : Arch_full.Arch

  val analyze :
    ?fmt:Format.formatter ->
    safety_param:string option ->
    (unit, A.extended_op) Prog.func ->
    (unit, A.extended_op) Prog.prog ->
    bool
end

val get_arch_with_analyze :
  Utils.architecture -> Glob_options.call_conv -> (module ArchWithAnalyze)
