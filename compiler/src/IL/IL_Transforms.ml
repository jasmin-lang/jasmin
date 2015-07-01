open Core.Std
open Util
open IL_Lang
open IL_Utils
open IL_Compile

(* ------------------------------------------------------------------------ *)
(* Apply transformations in sequence. *)

(* wrapper for liveness analysis that puts live sets into comments *)
let transform_register_liveness efunc =
  let bis =
    List.concat_map (register_liveness efunc)
      ~f:(fun {li_bi = i; li_read_after_rhs = read} ->
        [Comment (fsprintf "live: %a" (pp_list "," pp_preg) (Set.to_list read)); i])
  in
  { efunc with
    ef_body = base_instrs_to_stmt bis }

let strip_comments bis = 
  List.filter ~f:(function Comment(_) -> false | _ -> true) bis


type asm_lang = X64

type transform =
  | MacroExpand of (string * Big_int.big_int) list
  | SSA
  | Print of string
  | Save of string
  | RegisterAlloc of int
  | RegisterLiveness
  | StripComments
  | Asm of asm_lang

let ptrafo =
  let open MP in
  let mapping =
    many1 letter >>= fun s ->
    char '=' >>
    many1 digit >>= fun i ->
    return (String.of_char_list s,Big_int.big_int_of_string (String.of_char_list i))
  in
  let register_num =
    char '[' >> MParser.many1 digit >>= fun x -> 
    char ']' >>$ (int_of_string (String.of_char_list x))
  in
  let mappings =
    char '[' >> sep_by mapping (char ',') >>= fun l ->
    char ']' >>$ l
  in
  let asm_lang =
    choice [ string "x86-64" >>$ X64 ]
  in
  let pname =
    many1 (MParser.none_of "]") >>= fun l -> return (String.of_char_list l)
  in
  choice
    [ string "ssa" >>$ SSA
    ; (string "print" >> char '[' >> pname >>= (fun name -> char ']' >>$ (Print(name))))
    ; (string "save" >> char '[' >> pname >>= (fun name -> char ']' >>$ (Save(name))))
    ; string "register_liveness" >>$ RegisterLiveness
    ; string "strip_comments" >>$  StripComments
    ; (string "register_allocate" >> register_num >>= fun l ->
       return (RegisterAlloc(l)))
    ; string "asm" >> char '[' >> asm_lang >>= (fun l -> char ']' >>$ (Asm(l)))
    ; string "expand" >> mappings >>= fun m -> return (MacroExpand(m)) ]

let parse_trafo s =
  let open MP in
  match parse_string (sep_by ptrafo (char ',') >>= fun x -> eof >>$ x) s () with
  | Success t ->
    begin match List.rev t with
    | Asm(l)::rest ->
      if List.exists ~f:(function Asm(_) -> true | _ -> false) rest then (
        eprintf "asm[_] transformation must be last transformation";
        exit 1
      );
      (List.rev rest,Some l)
    | _ -> (t,None)
    end
  | Failed(s,_) ->
    eprintf "parsing transformation string failed: %s.\n%!" s;
    exit 1

let apply_transform trafo efun0 =
  let conv_trans f efun =
    { efun with
      ef_body = 
        stmt_to_base_instrs efun.ef_body |> f |> base_instrs_to_stmt
    }
  in
  let app_trafo efun t =
    match t with
    | SSA              -> transform_ssa efun
    | StripComments    -> conv_trans strip_comments efun
    | Print(name)      -> F.printf ">> %s:@\n%a@\n@\n" name pp_efun efun; efun
    | Save(fname)      ->
      Out_channel.write_all fname ~data:(fsprintf "%a" pp_efun efun); efun
    | RegisterAlloc(n) -> register_allocate (min 15 n) efun
    | RegisterLiveness -> transform_register_liveness efun
    | MacroExpand(m) ->
      { efun with
        ef_body =
          macro_expand (String.Map.of_alist_exn m) efun.ef_body |> base_instrs_to_stmt
      }
    | Asm(_) -> assert false
  in
  List.fold_left trafo ~init:efun0 ~f:app_trafo

let apply_transform_asm strafo efun =
  let (trafo,mlang) = parse_trafo strafo in
  let efun = apply_transform trafo efun in
  match mlang with
  | None     -> `IL efun
  | Some X64 -> `Asm_X64 (to_asm_x64 efun)
