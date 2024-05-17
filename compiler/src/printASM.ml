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

let string_of_glob x =
  Format.asprintf "G$%s" (escape x.v_name)

(* -------------------------------------------------------------------- *)
let format_glob_data globs names =
  let names =
    List.map (fun ((x, _), p) -> (Conv.var_of_cvar x, Conv.z_of_cz p)) names
  in
  List.flatten
    (List.mapi
       (fun i b ->
         let b = LByte (Z.to_string (Conv.z_of_int8 b)) in
         match List.find (fun (_, p) -> Z.equal (Z.of_int i) p) names with
         | exception Not_found -> [ b ]
         | x, _ -> [ LLabel (string_of_glob x); b ])
       globs)
