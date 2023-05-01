type t = int

let compare (x:t) (y:t) =
  let c = x - y in
    if c = 0 then Datatypes.Eq
    else if c < 0 then Datatypes.Lt
    else Datatypes.Gt

let equal (x:t) (y:t) = x = y

