type t = Location.i_loc * Annotations.annotations
let dummy = Location.i_dummy, []
let with_location (l, _) = (l, [])
let is_inline (_, annot) = Annotations.has_symbol "inline" annot
let is_unlikely (_, annot) =
  if Annotations.has_symbol "unlikely" annot then Some true
  else if Annotations.has_symbol "likely" annot then Some false
  else None

let var_info_of_ii (l, _) = Location.(l.base_loc)
