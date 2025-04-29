open Recover

type t = {
  location : Jasmin.Location.t;
  error_strategy : recover_flags;
  code : string;
  to_text : Format.formatter -> unit -> unit;
}
