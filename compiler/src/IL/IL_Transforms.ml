(* * Apply transformations to IL *)
 

(* ** Imports *)
open Core_kernel.Std
open Util
open IL_Lang
open IL_Pprint
open IL_Compile
open IL_Expand
open Arith

(* ** Apply transformations in sequence.
 * ------------------------------------------------------------------------ *)

type asm_lang = X64

type pprint_opt = {
  pp_fname : Fname.t option;
  pp_info  : bool;
  pp_num   : bool;
  pp_types : bool;
}

let mk_pprint_opt ofn = {
  pp_fname = ofn;
  pp_info  = false;
  pp_num   = false;
  pp_types = true;
}

type transform =
  | MergeBlocks of Fname.t option
  | MacroExpand of Fname.t * u64 Ident.Map.t
  | ArrayAssignExpand of Fname.t
  | ArrayExpand of Fname.t
  | LocalSSA of Fname.t
  | RegisterAlloc of Fname.t * int
  | InlineCalls of Fname.t
  | RegisterLiveness of Fname.t
  | RemoveEqConstrs of Fname.t
  | RenumberIdents
  | Asm of asm_lang
  (* debugging *)
  | Type
  | Print of string * pprint_opt
  | Save  of string * pprint_opt
  | StripComments of Fname.t
  | Interp of Fname.t * u64 Ident.Map.t * u64 U64.Map.t * value list
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
    ident >>= fun _s -> char '=' >> u64 >>= fun u -> return (undefined (),u)
  in
  let mmapping =
    u64 >>= fun s -> char '=' >> u64 >>= fun u -> return (s,u)
  in
  let register_num = bracketed int in
  let mappings p mc =
    bracketed (sep_by p (char ',') >>= fun l -> return (mc l))
  in
  let fname = bracketed (ident >>= fun s -> return @@ Fname.mk s) in
  let args = bracketed (sep_by (value ()) (char ',')) in
  let pmap = mappings pmapping Pname.Map.of_alist_exn in
  let mmap = mappings mmapping U64.Map.of_alist_exn in
  let interp_args =
    pmap  >>= fun mparam ->
    mmap  >>= fun mmem ->
    fname >>= fun fn ->
    args  >>= fun args ->
    return (fn,mparam,mmem,args)
  in
  let pprint_opt =
    choice
      [ (string "info" >>$ `Info)
      ; (string "num" >>$ `Num)
      ; (string "types" >>$ `Types)
      ; (string "fun=" >> ident >>= fun s -> return (`Fun (Fname.mk s)))
      ]
  in
  let pprint_opts =
    bracketed (sep_by pprint_opt (char ',')) >>= fun upds -> return @@
    List.fold ~init:(mk_pprint_opt None)
      ~f:(fun ppo opt ->
            match opt with
            | `Info   -> { ppo with pp_info  = true }
            | `Num    -> { ppo with pp_num   = true }
            | `Types  -> { ppo with pp_types = true }
            | `Fun fn -> { ppo with pp_fname = Some(fn) })
      upds
  in
  let get_pp_opts = get_opt (mk_pprint_opt None) in
  choice
    [ (string "typecheck" >>$ Type)
    ; (string "renumber_idents" >>$ RenumberIdents)
    ; (string "merge_blocks" >> option fname >>= fun ofn ->
       return (MergeBlocks ofn))
    ; (string "array_assign_expand" >> fname >>= fun fn ->
       return (ArrayAssignExpand fn))
    ; (string "array_expand" >> fname >>= fun fn ->
       return (ArrayExpand fn))
    ; (string "local_ssa" >> fname >>= fun fn ->
       return (LocalSSA fn))
    ; (string "print" >> (bracketed ident) >>= fun name ->
       (option pprint_opts) >>= fun pp_opts -> return (Print(name,get_pp_opts pp_opts)))
    ; (string "save"  >> (bracketed ident) >>= fun name ->
       (option pprint_opts) >>= fun pp_opts -> return (Save(name,get_pp_opts pp_opts)))
    ; (string "register_liveness" >> fname >>= fun fn ->
       return (RegisterLiveness fn))
    ; (string "strip_comments" >> fname >>= fun fn ->
       return (StripComments(fn)))
    ; (string "remove_eq_constrs" >> fname >>= fun fn ->
       return (RemoveEqConstrs(fn)))
    ; (string "register_allocate" >> fname >>= fun fn ->
       register_num >>= fun l ->
       return (RegisterAlloc(fn,l)))
    ; string "asm" >> char '[' >> asm_lang >>= (fun l -> char ']' >>$ (Asm(l)))
    ; (string "expand" >> fname >>= fun fname ->
       pmap >>= fun _m -> return (MacroExpand(fname,undefined ())))
    ; (string "inline" >> fname >>= fun fname -> return (InlineCalls(fname)))
    ; string "interp" >> interp_args >>=
        fun (fn,_mp,mm,args) -> return (Interp(fn,undefined () (*mp*)
                                             ,mm,args)) ]

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
  | U of unit modul
  | L of LV.t modul

type map_mod = {
  f : 'a. 'a modul -> 'a modul
}

let map_module m (mf : map_mod) =
  match m with
  | L m -> L(mf.f m)
  | U m -> U(mf.f m)

let apply_transform trafos (modul0 : unit modul) =
  (* let modul0 : unit modul_t = IL_Typing.inline_decls_modul modul0 in *)
  let filter_fn m ofname =
    match ofname with
    | Some fn ->
      { m with
        m_funcs = Map.filter_keys m.m_funcs ~f:(fun n -> n = fn) }
    | None -> m
  in
  let notify s fn ~f =
    let start = Unix.gettimeofday () in
    F.printf "%s in %s function(s)\n%!" s (Fname.to_string fn);
    let res = f () in
    let stop = Unix.gettimeofday () in
    F.printf "   %fs\n%!" (stop -. start);
    res
  in
  let all_fn = Fname.mk "all" in
  let pp_info = function
    | BlockStart -> fun fmt _info -> pp_string fmt "// START"
    | BlockEnd   -> fun fmt _info -> pp_string fmt "// END"
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
    let save fn ppo m =
      let m = map_module m { f = fun m -> filter_fn m ppo.pp_fname } in
      let go m pp = Out_channel.write_all fn ~data:(fsprintf "%a" pp m) in
      let ppm ppi = pp_modul ?pp_info:ppi ~pp_types:ppo.pp_info in
      match m, ppo.pp_info with
      | U m, true  -> go m (ppm (Some(pp_info)))
      | U m, false -> go m (ppm None)
      | L m, _     -> go m (ppm None)
    in
    let print n ppo m =
      let m_ = filter_fn m ppo.pp_fname in
      F.printf ">> %s:@\n%a@\n@\n" n (pp_modul ?pp_info:None ~pp_types:ppo.pp_types) m_;
      m
    in
    let interp fn _pmap _mmap _args m =
      notify "interpreting" fn
        ~f:(fun () -> undefined () (*IL_Interp.interp_modul m pmap mmap args fn;*); m)
    in
    let array_expand_modul fn m =
      notify "expanding array assignments" fn
        ~f:(fun () -> array_assign_expand_modul m fn)
    in
    let remove_eq_constrs fn _m =
      notify "removing equality constraints" fn
        ~f:(fun () -> undefined () (*remove_eq_constrs_modul m fn *))
    in
    let strip_comments fn m =
      notify "stripping comments" fn
        ~f:(fun () -> strip_comments_modul m fn)
    in
    let typecheck m =
      notify "type checking module" all_fn
        ~f:(fun () -> IL_Typing.typecheck_modul m; m)
    in
    let register_alloc fn _n _m = 
      notify "performing register allocation" fn
        ~f:(fun () -> undefined () (*reg_alloc_modul (min 15 n) m fn*))
    in
    let register_liveness fn _m =
      notify "adding register liveness information" fn
        ~f:(fun () -> undefined () (*add_liveness_modul m fn*))
    in
    let macro_expand fn map m = 
      notify "expanding macros" fn
        ~f:(fun () -> macro_expand_modul map m fn)
    in
    let merge_blocks ofn m =
      match ofn with
      | None     ->
        notify "merging basic blocks" all_fn ~f:(fun () -> merge_blocks_modul_all m)
      | Some(fn) ->
        notify "merging basic blocks" fn ~f:(fun () -> merge_blocks_modul m fn)
    in
    let renumber_idents _m =
      notify "renumbering identifiers apart" all_fn
        ~f:(fun () -> undefined () (*renumber_idents_modul_all m*))
    in
    match trafo with
    | InlineCalls(fn)           -> map_module modul {f = fun m -> inline fn m}
    | ArrayExpand(fn)           -> map_module modul {f = fun m -> arr_exp fn m}
    | LocalSSA(fn)              -> map_module modul {f = fun m -> local_ssa fn m}
    | Print(n,ppo)              -> map_module modul {f = fun m -> print n ppo m}
    | Interp(fn,pmap,mmap,args) -> map_module modul {f = fun m -> interp fn pmap mmap args m}
    | ArrayAssignExpand(fn)     -> map_module modul {f = fun m -> array_expand_modul fn m}
    | StripComments(fn)         -> map_module modul {f = fun m -> strip_comments fn m}
    | RemoveEqConstrs(fn)       -> map_module modul {f = fun m -> remove_eq_constrs fn m}
    | RegisterAlloc(fn,n)       -> map_module modul {f = fun m -> register_alloc fn n m}
    | MacroExpand(fn,map)       -> map_module modul {f = fun m -> macro_expand fn map m}
    | Type                      -> map_module modul {f = fun m -> typecheck m}
    | RenumberIdents            -> map_module modul {f = fun m -> renumber_idents m}
    | RegisterLiveness(fn)      -> map_module modul {f = fun m -> register_liveness fn m}
    | MergeBlocks(ofn)          -> map_module modul {f = fun m -> merge_blocks ofn m}
    | Save(fn,ppo)              -> save fn ppo modul; modul
    | Asm(_)                    -> assert false
  in
  List.fold_left trafos ~init:(U modul0) ~f:app_trafo

let apply_transform_asm strafo modul =
  let (trafo,mlang) = parse_trafo strafo in
  let modul = apply_transform trafo modul in
  match mlang with
  | None     -> `IL (match modul with U m -> m | L m -> reset_info_modul m)
  | Some X64 -> assert false (* `Asm_X64 (List.map ~f:to_asm_x64 modul) *)
