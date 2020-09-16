
type operand = Value | Register of string | MemoryAt of string

type instr = {
  instr_id: string;
  instr_inputs: operand list;
  instr_outputs: operand list
}

module ProgPointMap = Map.Make (struct type t = string let compare = compare end)

type checkpoint = int

type program =
  | Skip
  | Bloc of checkpoint * instr list
  | Seq of program list
  | Cond of operand list * program * program
  | Loop of operand list * program

let get_all_instr_in p =
  let rec aux = function
    | Skip -> []
    | Bloc (_, l) -> List.map (fun i -> i.instr_id) l
    | Seq l -> List.flatten (List.map aux l)
    | Cond (_, cif, celse) -> (aux celse) @ (aux cif)
    | Loop (_, cbody) -> aux cbody
  in
  List.sort_uniq String.compare (aux p)

let operand_to_string o = match o with
    | Value -> "0"
    | Register r -> "\\\"" ^ r ^ "\\\""
    | MemoryAt r -> "[" ^ r ^ "]"

let instr_to_string i = 
  List.fold_left (^) "" (List.map (fun v -> (operand_to_string v) ^ " ") i.instr_outputs) ^
  "<- " ^ i.instr_id ^ "( " ^
  List.fold_left (^) ""  (List.map (fun v -> (operand_to_string v) ^ " ") i.instr_inputs) ^
  ")"

let rec store_prgm p = match p with
  | Skip -> "\"Skip\""
  | Bloc (_, l) -> "[" ^ List.fold_left (fun buf -> fun i -> buf ^ "\"" ^ instr_to_string i ^ "\", ") "" l ^ "]"
  | Seq l -> "[" ^ List.fold_left (fun buf -> fun p' -> buf ^ (store_prgm p') ^ ", ") "" l ^ "]"
  | Cond (c :: _, t, e) -> "{ if: \"" ^ (operand_to_string c) ^ "\", then:" ^ (store_prgm t) ^ ", else: " ^ (store_prgm e) ^ "}"
  | Cond ([], t, e) -> "{ if: \"\", then:" ^ (store_prgm t) ^ ", else: " ^ (store_prgm e) ^ "}"
  | Loop (c :: _, body) -> "{ while: \"" ^ (operand_to_string c) ^ "\", body:" ^ (store_prgm body) ^ "}"
  | Loop ([], body) -> "{ while: \"\", body:" ^ (store_prgm body) ^ "}"

let to_atomic name inputs outputs = {
    instr_id = name; instr_inputs = inputs; instr_outputs = outputs
}