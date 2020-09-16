(**  Representation of programs  **)

type operand = Value | Register of string | MemoryAt of string

type instr = {
  instr_id: string;
  instr_inputs: operand list;
  instr_outputs: operand list
}

module ProgPointMap : Map.S with type key = string

type checkpoint = int

type program =
  | Skip
  | Bloc of checkpoint * instr list
  | Seq of program list
  | Cond of operand list * program * program
  | Loop of operand list * program

(* Static informations *)
val get_all_instr_in : program -> string list

(** Display **)
val operand_to_string : operand -> string
val instr_to_string : instr -> string

val store_prgm : program -> string

val to_atomic : string -> operand list -> operand list -> instr