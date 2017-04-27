module Option =
 struct
  (** val apply : ('a1 -> 'a2) -> 'a2 -> 'a1 option -> 'a2 **)

  let apply f x = function
  | Some y -> f y
  | None -> x

  (** val bind : ('a1 -> 'a2 option) -> 'a1 option -> 'a2 option **)

  let bind f =
    apply f None

  (** val map : ('a1 -> 'a2) -> 'a1 option -> 'a2 option **)

  let map f =
    bind (fun x -> Some (f x))
 end

type ('aT, 'rT) simpl_fun = ('aT, 'rT) __simpl_fun Lazy.t
and ('aT, 'rT) __simpl_fun =
| SimplFun of ('aT -> 'rT)

(** val fun_of_simpl : ('a1, 'a2) simpl_fun -> 'a1 -> 'a2 **)

let fun_of_simpl f x =
  let SimplFun lam = Lazy.force f in lam x
