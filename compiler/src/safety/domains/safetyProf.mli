open SafetyInterfaces

module Prof : sig
  val record : string -> unit
  val is_recorded : string -> bool
  val call : string -> float -> unit
  val reset_all : unit -> unit

  val print : Format.formatter -> unit -> unit
end

(*------------------------------------------------------------*)
(* Numerical Domain With Profiling *)

module type NumWrap = sig
  val prefix : string
  module Num : AbsNumType
end

module MakeAbsNumProf (A : NumWrap) : AbsNumType

(*---------------------------------------------------------------*)
(* Disjunctive Domain With Profiling *)
                                                                 
module type DisjWrap = sig
  val prefix : string
  module Num : AbsDisjType
end

module MakeAbsDisjProf (A : DisjWrap) : AbsDisjType
