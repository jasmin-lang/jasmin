(* -------------------------------------------------------------------- *)
exception ParseError of Location.t * string option

let parse_error ?msg loc =
  raise (ParseError (loc, msg))

(* -------------------------------------------------------------------- *)
type pprogram = unit
