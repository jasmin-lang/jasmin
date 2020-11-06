(**  Representation of programs  **)

type operand = Value | Register of string | MemoryAt of string

type instr = {
  instr_id: string;
  instr_inputs: operand list;
  instr_outputs: operand list;
  (* MemoryAt that may alias with the operands.
     Must be released before fetching the instruction *)
  instr_may_inputs: operand list;
  instr_may_outputs: operand list 
}

val instr_inputs : instr -> operand list
val instr_outputs : instr -> operand list

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
val print_prog_struct : program -> unit

val to_atomic : string -> operand list -> operand list -> operand list -> operand list -> instr
(* For all sequences, join adjacent blocs *)
val compact : program -> program