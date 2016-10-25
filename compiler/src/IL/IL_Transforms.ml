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
let liveness_to_comments modul fname =
  let func = List.find_exn ~f:(fun f -> f.f_name = fname) modul.m_funcs in
  let fd = get_fundef ~err_s:"" func in
  let denv = IT.denv_of_func func (IT.extract_decls func.f_args fd) in
  let add_liveness denv pos loc info instr =
    let is_first = true (*
      match List.rev pos with
      | x::_ when x=0 -> true
      | _ -> begin match instr with
             | If(_,_,_) -> true
             | While(_,_,_) -> true
             | _ -> false
             end *)
    in
    let filter_reg =
      SS.filter ~f:(fun n -> let (t,s) = Map.find_exn denv n in s = Reg && t = U64)
    in
    let l_before = filter_reg info.LV.live_before in
    let l_after = filter_reg info.LV.live_after in
    let use = use_instr instr in
    let def = def_instr instr in
    let before =
      [ Binstr (Comment (fsprintf "%a before: %a"
                           pp_pos pos pp_set_string l_before)) ]
    in
    let after =
      [ instr
      ; Binstr (Comment (fsprintf "%a after:  %a || def: %a || use: %a"
                           pp_pos pos pp_set_string l_after
                           pp_set_string def pp_set_string use))
      ]
    in
    List.map
      ((if is_first then before else [])@after)
      ~f:(fun i -> { i_val = i; i_loc = loc; i_info = info })
  in
  concat_map_modul modul fname ~f:(add_liveness denv)

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
  | CommentsLiveness of string
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
    ; (string "liveness_comments" >> (bracketed ident) >>= fun fn ->
       return (CommentsLiveness fn))
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

type modules =
  | U of unit modul_t
  | L of LV.t modul_t

let apply_transform trafos (modul0 : unit modul_u) =
  let modul0 : unit modul_t = IL_Typing.inline_decls_modul modul0 in
  let map_module m ~f =
    match m with
    | L m -> L(f m)
    | U m -> L(f @@ LV.add_initial_liveness_modul m)
  in
  let filter_fn m ofname =
    match ofname with
    | Some fn ->
      { m with
        m_funcs = List.filter m.m_funcs ~f:(fun f -> f.f_name = fn) }
    | None -> m
  in
  let notify s fn ~f =
    let start = Unix.gettimeofday () in
    F.printf "%s in function %s\n%!" s fn;
    let res = f () in
    let stop = Unix.gettimeofday () in
    F.printf "   %fs\n%!" (stop -. start);
    res
  in

  let app_trafo modul trafo =
    let inline fn m =
      notify "inlining all calls" fn
        ~f:(fun () -> inline_calls_modul m fn)
    in
    let arr_exp fn m =
      notify "expanding register arrays" fn
        ~f:(fun () -> array_expand_modul m fn)
    in
    let local_ssa fn m =
      notify "transforming into local SSA form" fn
        ~f:(fun () -> local_ssa_modul m fn)
    in
    let save fn ofn m =
      let m_ = filter_fn m ofn in
      Out_channel.write_all fn ~data:(fsprintf "%a" pp_modul m_);
      m
    in
    let print n ofn m =
      let m_ = filter_fn m ofn in
      F.printf ">> %s:@\n%a@\n@\n" n pp_modul m_;
      m
    in
    let interp fn pmap mmap args m =
      notify "interpreting" fn
        ~f:(fun () -> IL_Interp.interp_modul m pmap mmap args fn)
    in
    let array_expand_modul fn m =
      notify "expanding array assignments" fn
        ~f:(fun () -> array_assign_expand_modul m fn)
    in
    let remove_eq_constrs fn m =
      notify "removing equality constraints" fn
        ~f:(fun () -> remove_eq_constrs_modul m fn)
    in
    let strip_comments fn m =
      notify "stripping comments" fn
        ~f:(fun () -> strip_comments_modul m fn)
    in
    let typecheck m =
      notify "type checking module" "all functions"
        ~f:(fun () -> IL_Typing.typecheck_modul m; m)
    in
    let register_alloc fn n m = 
      notify "performing register allocation" fn
        ~f:(fun () -> reg_alloc_modul (min 15 n) m fn)
    in
    let register_liveness fn m =
      notify "adding register liveness information" fn
        ~f:(fun () -> add_liveness_modul m fn)
    in
    let comments_liveness fn m =
      notify "adding comments for liveness information" fn
        ~f:(fun () -> liveness_to_comments m fn)
    in
    let macro_expand fn map m = 
      notify "expanding macros" fn
        ~f:(fun () -> macro_expand_modul map m fn)
    in
    match trafo with
    | InlineCalls(fn)           -> map_module modul ~f:(inline fn)
    | ArrayExpand(fn)           -> map_module modul ~f:(arr_exp fn)
    | LocalSSA(fn)              -> map_module modul ~f:(local_ssa fn)
    | Print(n,ofn)              -> map_module modul ~f:(print n ofn)
    | Interp(fn,pmap,mmap,args) -> map_module modul ~f:(interp fn pmap mmap args)
    | ArrayAssignExpand(fn)     -> map_module modul ~f:(array_expand_modul fn)
    | StripComments(fn)         -> map_module modul ~f:(strip_comments fn)
    | RemoveEqConstrs(fn)       -> map_module modul ~f:(remove_eq_constrs fn)
    | RegisterAlloc(fn,n)       -> map_module modul ~f:(register_alloc fn n)
    | MacroExpand(fn,map)       -> map_module modul ~f:(macro_expand fn map)
    | Type                      -> map_module modul ~f:typecheck
    | RegisterLiveness(fn)      -> map_module modul ~f:(register_liveness fn)
    | CommentsLiveness(fn)      -> map_module modul ~f:(comments_liveness fn)
    | Save(fn,ofn)              ->
      begin match modul with
      | U m -> ignore(save fn ofn m)
      | L m -> ignore(save fn ofn m)
      end;
      modul
    | Asm(_)                    -> assert false
  in
  List.fold_left trafos ~init:(U modul0) ~f:app_trafo

let apply_transform_asm strafo modul =
  let (trafo,mlang) = parse_trafo strafo in
  let modul = apply_transform trafo modul in
  match mlang with
  | None     -> `IL (match modul with U m -> m | L m -> LV.remove_liveness_modul m)
  | Some X64 -> assert false (* `Asm_X64 (List.map ~f:to_asm_x64 modul) *)
