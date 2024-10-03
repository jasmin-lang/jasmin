open Utils
open Prog
open PrintCommon

(** Assembly code lines. *)
type asm_line =
  | LLabel of string
  | LInstr of string * string list
  | LByte of string

let iwidth = 4

let print_asm_line fmt ln =
  match ln with
  | LLabel lbl -> Format.fprintf fmt "%s:" lbl
  | LInstr (s, []) -> Format.fprintf fmt "\t%s" s
  | LInstr (s, args) ->
      Format.fprintf fmt "\t%-*s\t%s" iwidth s (String.concat ", " args)
  | LByte n -> Format.fprintf fmt "\t.byte\t%s" n

let print_asm_lines fmt lns =
  List.iter (Format.fprintf fmt "%a\n%!" print_asm_line) lns

(* -------------------------------------------------------------------- *)
let string_of_label name p =
  Format.asprintf "L%s$%d" (escape name) (Conv.int_of_pos p)

let string_of_glob occurrences x =
  Hash.modify_def (-1) x.v_name Stdlib.Int.succ occurrences;
  let count =  Hash.find occurrences x.v_name in
  (* Adding the number of occurrences to the label to avoid names conflict *)
  let suffix = if count > 0 then Format.asprintf "$%d" count else "" in
  Format.asprintf "G$%s%s" (escape x.v_name) suffix

let byte_label global_datas i =
  Format.asprintf "%s_%a" global_datas Z.pp_print i

(* -------------------------------------------------------------------- *)
let format_glob_data_entry global_datas i olabel b =
  let lbl =
    match olabel with
    | Some x -> [ LLabel x ]
    | None -> []
  in
  lbl @ [ LLabel(byte_label global_datas (Z.of_int i)); LByte(b) ]

let format_glob_data global_datas globs names =
  (* Creating a Hashtable to count occurrences of a label name*)
  let occurrences = Hash.create 42 in
  let names =
    List.map (fun ((x, _), p) -> (Conv.var_of_cvar x, Conv.z_of_cz p)) names
  in
  let doit i b =
    let olabel =
      match List.find (fun (_, p) -> Z.equal p (Z.of_int i)) names with
      | x, _ -> Some (string_of_glob occurrences x)
      | exception Not_found -> None
    in
    let b = Conv.z_of_int8 b |> Z.to_string in
    format_glob_data_entry global_datas i olabel b
  in
  List.flatten (List.mapi doit globs)
