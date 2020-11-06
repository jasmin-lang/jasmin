
type operand = Value | Register of string | MemoryAt of string

type instr = {
  instr_id: string;
  instr_inputs: operand list;
  instr_outputs: operand list;
  instr_may_inputs: operand list;
  instr_may_outputs: operand list
}

let instr_inputs i = i.instr_inputs
let instr_outputs i = i.instr_outputs

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
    | Register r -> r
    | MemoryAt r -> "[" ^ r ^ "]"

let instr_to_string i = 
  (* Outputs *)
  List.fold_left (^) "" (List.map (fun v -> (operand_to_string v) ^ " ") i.instr_outputs) ^
  (* Alias Outputs *)
  List.fold_left (^) "+ " (List.map (fun v -> (operand_to_string v) ^ " ") i.instr_may_outputs) ^
  (* Id *)
  "<- " ^ i.instr_id ^ "( " ^
  (* Inputs *)
  List.fold_left (^) ""  (List.map (fun v -> (operand_to_string v) ^ " ") i.instr_inputs) ^
  (* Alias Inputs *)
  List.fold_left (^) "+ " (List.map (fun v -> (operand_to_string v) ^ " ") i.instr_may_inputs) ^
  ")"

let rec store_prgm p = match p with
  | Skip -> "\"Skip\""
  | Bloc (_, l) -> "Bloc [" ^ List.fold_left (fun buf -> fun i -> buf ^ "\"" ^ instr_to_string i ^ "\", ") "" l ^ "]"
  | Seq l -> "[" ^ List.fold_left (fun buf -> fun p' -> buf ^ (store_prgm p') ^ ", ") "" l ^ "]"
  | Cond (c :: _, t, e) -> "{ if: \"" ^ (operand_to_string c) ^ "\", then:" ^ (store_prgm t) ^ ", else: " ^ (store_prgm e) ^ "}"
  | Cond ([], t, e) -> "{ if: \"\", then:" ^ (store_prgm t) ^ ", else: " ^ (store_prgm e) ^ "}"
  | Loop (c :: _, body) -> "{ while: \"" ^ (operand_to_string c) ^ "\", body:" ^ (store_prgm body) ^ "}"
  | Loop ([], body) -> "{ while: \"\", body:" ^ (store_prgm body) ^ "}"

let rec print_prog_struct p = match p with
  | Skip ->
      Format.eprintf "@ Skip"
  | Bloc (i, []) ->
      Format.eprintf "@ Bloc %d []" i
  | Bloc (i, _) ->
      Format.eprintf "@ Bloc %d" i
  | Seq l ->
      List.iter print_prog_struct l
  | Cond (_, t, e) -> begin
      Format.eprintf "@ If () Then@ @[<v 2>";
      print_prog_struct t;
      Format.eprintf "@]@ Else@ @[<v 2>";
      print_prog_struct e;
      Format.eprintf "@]@ EndIf"
    end
  | Loop (_, body) -> begin
      Format.eprintf "@ While ()@ @[<v 2>";
      print_prog_struct body;
      Format.eprintf "@]@ EndWhile"
    end


let to_atomic name inputs outputs read_alias write_alias = {
    instr_id = name;
    instr_inputs = inputs;
    instr_outputs = outputs;
    instr_may_inputs = read_alias;
    instr_may_outputs = write_alias
}

let compact p =
  let rec aux = function
    | Skip -> Skip
    | Bloc (c, l) -> Bloc (c, l)
    | Seq l -> begin
        (* If l = [Bloc 1 l1, Bloc 2 l2, Loop, Bloc 3 l3, Bloc 4 l4]
          -> [Bloc 1 l1 @ l2, Bloc 2 [], Loop, Bloc 3 l3 @ l4, Bloc 4 [] *)
        let pending_bloc_indexes = ref [] in
        let pending_bloc_instructions = ref [] in
        let new_seq = ref [] in
        let close_bloc_seq () =
            if !pending_bloc_indexes <> []
            then begin
              let empty_blocs =
                List.map (fun i -> Bloc (i, []))
                         (List.tl !pending_bloc_indexes)
              in
              new_seq := !new_seq @ (Bloc (List.hd !pending_bloc_indexes, !pending_bloc_instructions) :: empty_blocs);
              pending_bloc_indexes := [];
              pending_bloc_instructions := []
            end
        in
        let examine sub_p = match sub_p with
          | Bloc (c', l') -> begin
            pending_bloc_indexes := !pending_bloc_indexes @ [c'];
            pending_bloc_instructions := !pending_bloc_instructions @ l'
          end
          | _ -> begin
            close_bloc_seq ();
            new_seq := !new_seq @ [aux sub_p]
          end
        in
        List.iter examine l;
        close_bloc_seq ();
        Seq !new_seq
      end
    | Cond (c, t, e) -> Cond (c, aux t, aux e)
    | Loop (c, b) -> Loop (c, aux b)
  in
  aux p