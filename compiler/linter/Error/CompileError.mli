
(**
Error type using first-class modules to allow better composability.
It introduce :
 - [code] for error (useful for documentations)
 - [error_strategy] A strategy which tells the program how to handle error (as warning, as a recoverable error, etc.)
 - [to_text] A function to convert the error to a human-readable format
To build a new error, you need to implement a module matching the [CompileError] signature.
*)
module type CompileError = sig
    type payload
    val payload : payload
    val location : Jasmin.Location.t
    val error_strategy : Recover.recover_flags
    val code : string
    val to_text : Format.formatter -> unit -> unit
end

type compile_error = (module CompileError)
