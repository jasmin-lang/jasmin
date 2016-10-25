(* * Apply transformations to IL *)
 

(* ** Imports *)
open Core_kernel.Std
open Util
open IL_Lang
open IL_Utils
open IL_Compile
open IL_Expand
open Arith

(* ** Apply transformations in sequence.
 * ------------------------------------------------------------------------ *)

(* wrapper for liveness analysis that puts live sets into comments *)
let transform_register_liveness modul fname =
  let live_info = compute_liveness_modul modul fname in
  (* F.printf "%a" LI.pp live_info; *)
  let _mk_fn suffix = "/tmp/a"^suffix in
  let _dot = ".dot" in
  let _svg = ".svg" in
  F.printf "dumping dot file\n%!";
  (* LI.dump ~verbose:true live_info (mk_fn dot); *)
  (* F.printf "calling dot\n%!"; *)
  (* let res = Unix.system (fsprintf "dot %s -o%s -Tsvg" (mk_fn dot) (mk_fn svg)) in *)
  (* if res <> Unix.WEXITED(0) then *)
  (*   failwith "dot failed some error code\n"; *)
  (* F.printf "dot finished\n%!"; *)
  let func = List.find_exn ~f:(fun f -> f.f_name = fname) modul.m_funcs in
  let fd = get_fundef ~err_s:"" func in
  let denv = IT.denv_of_func func (IT.extract_decls func.f_args fd) in
  let add_liveness pos instr =
    let filter_reg =
      SS.filter ~f:(fun n -> let (t,s) = Map.find_exn denv n in s = Reg && t = U64)
    in
    let l_before = LI.get_live_before live_info pos |> filter_reg in
    let l_after = LI.get_live_after live_info pos |> filter_reg  in
    let use = LI.get_use live_info pos |> filter_reg in
    let def = LI.get_def live_info pos |> filter_reg in
    [ Binstr (Comment (fsprintf "%a before: %a || use: %a"
                         pp_pos pos pp_set_string l_before pp_set_string use))
    ; instr
    ; Binstr (Comment (fsprintf "%a after: %a || def: %a" pp_pos pos pp_set_string l_after
                         pp_set_string def))
    ]
  in
  concat_map_modul modul fname ~f:add_liveness

let strip_comments bis =
  List.filter ~f:(function Comment(_) -> false | _ -> true) bis

type asm_lang = X64

type transform =
  | MacroExpand of string * u64 String.Map.t
  | ArrayAssignExpand of string
  | ArrayExpand of string
  | LocalSSA of string
  | Type
  | Print of string * string option
  | Save of string * string option
  | RegisterAlloc of string * int
  | InlineCalls of string
  | RegisterLiveness of string
  | RemoveEqConstrs of string
  | StripComments of string
  | Asm of asm_lang
  | Interp of string * u64 String.Map.t * u64 U64.Map.t * value list
    (* Interp(pmap,mmap,alist,fun):
         interpret call of function fun() with parameters pmap, memory mmap,
         argument list alist *)

let ptrafo =
  let open MP in
  let ident = many1 (MParser.none_of "]=") >>= fun l -> return (String.of_char_list l) in
  let asm_lang = choice [ string "x86-64" >>$ X64 ] in
  let enclosed p pstart pend = pstart >> p >>= fun x -> pend >>$ x in
  let bracketed p = enclosed p (char '[') (char ']') in
  let u64 = many1 digit >>= fun s -> return (U64.of_string (String.of_char_list s)) in
  let int = many1 digit >>= fun s -> return (int_of_string (String.of_char_list s)) in
  let value () =
    choice
      [ (u64 >>= fun u -> return (Vu64 u))
      ; (char '[' >>= fun _ ->
        (sep_by u64 (char ',')) >>= fun vs ->
        char ']' >>= fun _ ->
        let vs = U64.Map.of_alist_exn (List.mapi vs ~f:(fun i v -> (U64.of_int i, v))) in
        return (Varr(vs))) ]
  in
  let pmapping =
    ident >>= fun s -> char '=' >> u64 >>= fun u -> return (s,u)
  in
  let mmapping =
    u64 >>= fun s -> char '=' >> u64 >>= fun u -> return (s,u)
  in
  let inline_args = bracketed ident in
  let register_num = bracketed int in
  let mappings p mc =
    bracketed (sep_by p (char ',') >>= fun l -> return (mc l))
  in
  let fname = bracketed ident in
  let args = bracketed (sep_by (value ()) (char ',')) in
  let pmap = mappings pmapping String.Map.of_alist_exn in
  let mmap = mappings mmapping U64.Map.of_alist_exn in
  let interp_args =
    pmap  >>= fun mparam ->
    mmap  >>= fun mmem ->
    fname >>= fun fn ->
    args  >>= fun args ->
    return (fn,mparam,mmem,args)
  in
  choice
    [ (string "typecheck" >>$ Type)
    ; (string "array_assign_expand" >> (bracketed ident) >>= fun fn ->
       return (ArrayAssignExpand fn))
    ; (string "array_expand" >> (bracketed ident) >>= fun fn ->
       return (ArrayExpand fn))
    ; (string "local_ssa" >> (bracketed ident) >>= fun fn ->
       return (LocalSSA fn))
    ; (string "print" >> (bracketed ident) >>= fun name ->
       option (bracketed ident) >>= fun fname -> return (Print(name,fname)))
    ; (string "save"  >> (bracketed ident) >>= fun name ->
       option (bracketed ident) >>= fun fname -> return (Save(name,fname)))
    ; (string "register_liveness" >> (bracketed ident) >>= fun fn ->
       return (RegisterLiveness fn))
    ; (string "strip_comments" >> (bracketed ident) >>= fun fn ->
       return (StripComments(fn)))
    ; (string "remove_eq_constrs" >> (bracketed ident) >>= fun fn ->
       return (RemoveEqConstrs(fn)))
    ; (string "register_allocate" >> (bracketed ident) >>= fun fn ->
       register_num >>= fun l ->
       return (RegisterAlloc(fn,l)))
    ; string "asm" >> char '[' >> asm_lang >>= (fun l -> char ']' >>$ (Asm(l)))
    ; (string "expand" >> bracketed ident >>= fun fname ->
       pmap >>= fun m -> return (MacroExpand(fname,m)))
    ; (string "inline" >> inline_args >>= fun fname -> return (InlineCalls(fname)))
    ; string "interp" >> interp_args >>=
        fun (fn,mp,mm,args) -> return (Interp(fn,mp,mm,args)) ]

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

let apply_transform trafo (modul0 : 'info modul_u) =
  let modul0 = IL_Typing.inline_decls_modul modul0 in
  let filter_fn modul ofname =
    match ofname with
    | Some fn ->
      { modul with
        m_funcs = List.filter modul.m_funcs ~f:(fun f -> f.f_name = fn) }
    | None ->
      modul
  in
  let app_trafo modul t =
    let notify s fname =
      F.printf "%s in function %a\n%!" s pp_string fname
    in
    match t with
    | InlineCalls(fname) ->
      notify "inlining all calls" fname;
      inline_calls_modul modul fname
    | ArrayExpand(fname) ->
      notify "expanding register arrays" fname;
      array_expand_modul modul fname
    | LocalSSA(fname) ->
      notify "transforming into local SSA form" fname;
      local_ssa_modul modul fname
    | ArrayAssignExpand(fname) ->
      notify "expanding array assignments" fname;
      array_assign_expand_modul modul fname
    | StripComments(fname) ->
      notify "stripping comments" fname;
      strip_comments_modul modul fname
    | RemoveEqConstrs(fname) ->
      notify "removing equality constraints" fname;
      remove_eq_constrs_modul modul fname
    | Print(name,ofname) ->
      let modul_ = filter_fn modul ofname in
      F.printf ">> %s:@\n%a@\n@\n" name pp_modul modul_; modul
    | Save(fname,ofname) ->
      let modul_ = filter_fn modul ofname in
      Out_channel.write_all fname ~data:(fsprintf "%a" pp_modul modul_); modul
    | RegisterAlloc(fname,n) ->
      notify "performing register allocation" fname;
      reg_alloc_modul (min 15 n) modul fname
    | RegisterLiveness(fname) ->
      transform_register_liveness modul fname
    | MacroExpand(fname,m) ->
      notify "expanding macros" fname;
      macro_expand_modul m modul fname
    | Asm(_) -> assert false
    | Type ->
      F.printf "type checking module\n%!" ;
      IL_Typing.typecheck_modul modul;
      modul
    | Interp(fname,pmap,mmap,args) ->
      notify "interpreting" fname;
      IL_Interp.interp_modul modul pmap mmap args fname
  in
  List.fold_left trafo ~init:modul0 ~f:app_trafo

let apply_transform_asm strafo modul =
  let (trafo,mlang) = parse_trafo strafo in
  let modul = apply_transform trafo modul in
  match mlang with
  | None     -> `IL modul
  | Some X64 -> assert false (* `Asm_X64 (List.map ~f:to_asm_x64 modul) *)
