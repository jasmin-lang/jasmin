(** Assembly code type. Common interface produced by all existing architectures
*)
type asm_element =
  | Header of string * string list
  | Label of string
  | Dwarf of string (* Debug info in std dwarf format*)
  | Instr of string * string list
  | Comment of string
  | Bytes of string list

val pp_asm : Format.formatter -> asm_element list -> unit
(** Pretty print assembly code *)
