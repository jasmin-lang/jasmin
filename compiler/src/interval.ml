type interval = { min : Z.t; max : Z.t }
type t = interval

let size i = Z.(i.max - i.min)

let pp_interval ?(closed=false) fmt { min ; max } =
  Format.fprintf fmt "[%a; %a%s" Z.pp_print min Z.pp_print max (if closed then "]" else "[")
