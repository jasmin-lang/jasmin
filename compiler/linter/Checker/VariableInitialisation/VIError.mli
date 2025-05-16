open Jasmin.Prog
open Error.CompileError

(**
Error representation for uninitialised variables
*)
module VIError :
  functor
    (P : sig val payload : var val loc : Jasmin.Location.t end)
    -> Error.CompileError.CompileError


val create_vi_error :
  var -> Jasmin.Location.t -> compile_error
