
val parse_file :
  'asm Prog.arch_info ->
  (string*string) list ->
  string ->
  string list list
  * (Prog.funname * (Z.t * Z.t) list) Location.located list
  * (unit, ('a, 'b, 'c, 'd, 'e, 'f, 'g) Arch_extra.extended_op) Prog.pmod_item
    list

