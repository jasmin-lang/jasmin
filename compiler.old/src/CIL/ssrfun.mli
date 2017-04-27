module Option :
 sig
  val apply : ('a1 -> 'a2) -> 'a2 -> 'a1 option -> 'a2

  val bind : ('a1 -> 'a2 option) -> 'a1 option -> 'a2 option

  val map : ('a1 -> 'a2) -> 'a1 option -> 'a2 option
 end

type ('aT, 'rT) simpl_fun = ('aT, 'rT) __simpl_fun Lazy.t
and ('aT, 'rT) __simpl_fun =
| SimplFun of ('aT -> 'rT)

val fun_of_simpl : ('a1, 'a2) simpl_fun -> 'a1 -> 'a2
