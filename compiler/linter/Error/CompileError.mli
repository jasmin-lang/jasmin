(**
Error handling strategies for the compiler
*)

type recover_flags = Fail | Recoverable | AlwaysWarn
(**
Error type :
 - [code] for error (useful for documentations)
 - [error_strategy] A strategy which tells the program how to handle error (as warning, as a recoverable error, etc.)
 - [to_text] A function to convert the error to a human-readable format
*)
type t = {
  location : Jasmin.Location.t;
  error_strategy : recover_flags;
  code : string;
  to_text : Format.formatter -> unit;
}
