type t = {
  location : Jasmin.Location.t;
  level : int;
  code : string;
  to_text : Format.formatter -> unit;
}
