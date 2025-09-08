type t = {
  location : Jasmin.Location.t;
  level : int;
  code : string;
  to_text : Format.formatter -> unit;
}
(** Error type :
    - [code] for error (useful for documentations)
    - [level] describes the minimal reporting level for this error
    - [to_text] A function to convert the error to a human-readable format *)
