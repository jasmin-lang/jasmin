
val parse_file :
  ('a, 'b, 'c, 'd, 'e, 'f, 'g) Pretyping.arch_info ->
  (string*string) list ->
  string ->
  string list list
  * (Prog.funname * (Z.t * Z.t) list) Location.located list
  * (unit, ('a, 'b, 'c, 'd, 'e, 'f, 'g) Arch_extra.extended_op) Prog.pmod_item
    list

