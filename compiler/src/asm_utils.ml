open Arch_decl
open PrintCommon
open Prog
open Utils
open PrintASM

let global_datas_label = "glob_data"

let pp_syscall (o : _ Syscall_t.syscall_t) =
  match o with
  | Syscall_t.RandomBytes _ -> "__jasmin_syscall_randombytes__"

let string_of_label name p = Format.asprintf "L%s$%d" (escape name) (Conv.int_of_pos p)

let pp_remote_label (fn, lbl) =
  string_of_label fn.fn_name lbl

let mangle x = Format.asprintf "_%s" x

let string_of_glob occurrences x =
  Hash.modify_def (-1) x.v_name Stdlib.Int.succ occurrences;
  let count =  Hash.find occurrences x.v_name in
  (* Adding the number of occurrences to the label to avoid names conflict *)
  let suffix = if count > 0 then Format.asprintf "$%d" count else "" in
  Format.asprintf "G$%s%s" (escape x.v_name) suffix

let format_glob_data globs names =
  (* Creating a Hashtable to count occurrences of a label name*)
  let occurrences = Hash.create 42 in
  let names =
    List.map (fun ((x, _), p) -> (Conv.var_of_cvar x, Conv.z_of_cz p)) names
  in
  let init = [], [] in
  let close (bytes, acc) = if bytes = [] then acc else Bytes (List.rev bytes) :: acc in
  let push b (bytes, acc) = (b :: bytes, acc) in
  let add_label x s = ([], Label x :: close s) in
  let finish s = s |> close |> List.rev in
  List.fold_lefti (fun s i b ->
      let b = Z.format "%3i" (Conv.z_unsigned_of_word U8 b) in
      match List.find (fun (_, p) -> Z.equal (Z.of_int i) p) names with
      | exception Not_found -> s |> push b
      | x, _ -> s |> add_label (string_of_glob occurrences x) |> push b
    ) init globs
  |> finish

(* TODO : Move*)
let hash_to_string (to_string : 'a -> string) =
  let tbl = Hashtbl.create 17 in
  fun r ->
    try Hashtbl.find tbl r
    with Not_found ->
      let s = to_string r in
      Hashtbl.add tbl r s;
      s

let pp_imm imm_pre imm = Format.asprintf "%s%s" imm_pre (Z.to_string imm)

let pp_rip_address p : string =
  Format.asprintf "%s+%a" global_datas_label Z.pp_print (Conv.z_of_int32 p)

let pp_register arch = hash_to_string arch.toS_r.to_string

type parsed_reg_address = {
  base : string;
  displacement : string option;
  offset : string option;
  scale : string option;
}

let parse_reg_address (arch : ('a, 'b, 'c, 'd, 'e) arch_decl) addr =
  match addr.ad_base with
  | None -> failwith (Format.asprintf "TODO_RISC: pp_reg_address")
  | Some r ->
      let base = pp_register arch r in
      let displacement = Conv.z_of_word (arch_pd arch) addr.ad_disp in
      let displacement =
        if Z.equal displacement Z.zero then None
        else Some (Z.to_string displacement)
      in
      let offset = Option.map (pp_register arch) addr.ad_offset in
      let scale = Conv.z_of_nat addr.ad_scale in
      let scale =
        if Z.equal scale Z.zero then None else Some (Z.to_string scale)
      in
      { base; displacement; offset; scale }
