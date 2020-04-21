type interval = { min : int; max : int }
type t = interval

let pp_interval ?(closed=false) fmt { min ; max } =
  Format.fprintf fmt "[%d; %d%s" min max (if closed then "]" else "[")
