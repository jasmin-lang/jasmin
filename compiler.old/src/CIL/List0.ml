(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map f = function
| [] -> []
| a :: t -> (f a) :: (map f t)

(** val fold_right : ('a2 -> 'a1 -> 'a1) -> 'a1 -> 'a2 list -> 'a1 **)

let rec fold_right f a0 = function
| [] -> a0
| b :: t -> f b (fold_right f a0 t)

(** val split : ('a1 * 'a2) list -> 'a1 list * 'a2 list **)

let rec split = function
| [] -> ([], [])
| p :: tl ->
  let (x, y) = p in
  let (left, right) = split tl in ((x :: left), (y :: right))
