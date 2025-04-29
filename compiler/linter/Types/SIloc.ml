include Set.Make (struct
  type t = Iloc.t

  let compare = Iloc.compare
end)
