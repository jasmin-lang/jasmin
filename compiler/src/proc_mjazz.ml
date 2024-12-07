(* -------------------------------------------------------------------- *)
open Utils
open Pretyping
module Path = BatPathGen.OfString
module F = Format
module L = Location
module A = Annotations
module S = Syntax
module E = Expr
module P = Prog
module M = Mprog
module W = Wsize
module T = Type

(* -------------------------------------------------------------------- *)
(*                      MJazz Errors                                    *)
(* -------------------------------------------------------------------- *)

(* just a copy of Pretyping.string_error !!! *)
let string_error fmt =
  let buf  = Buffer.create 127 in
  let bfmt = Format.formatter_of_buffer buf in
  Format.kfprintf
    (fun bfmt ->
      Format.pp_print_flush bfmt ();
      (StringError (Buffer.contents buf)))
    bfmt fmt

type mjazzerror =
  | MJazzIncompatibleNS
  | NonToplevelRequire
  | NonExistentMod of M.modulename
  | MJazzNYS
  | MJazzInternal of string
  | MJazzStringError of string

exception MJazzError of L.t * mjazzerror

let mjazz_string_error fmt =
  let buf  = Buffer.create 127 in
  let bfmt = Format.formatter_of_buffer buf in
  Format.kfprintf
    (fun bfmt ->
      Format.pp_print_flush bfmt ();
      (MJazzStringError (Buffer.contents buf)))
    bfmt fmt

let mjazzerror ~loc (code: mjazzerror) =
  MJazzError (loc, code)

let rs_mjazzerror ~loc (code: mjazzerror) =
  raise (mjazzerror ~loc code)

let pp_mjazzerror fmt = function
  | MJazzIncompatibleNS ->
    F.fprintf fmt "'NameSpace' feature incompatible with MJazz"
  | NonToplevelRequire ->
    F.fprintf fmt "'require' clause in MJazz should be at toplevel"
  | NonExistentMod m ->
    F.fprintf fmt "non existent module %s" m
  | MJazzNYS ->
    F.fprintf fmt "feature not yet supported in MJazz"
  | MJazzInternal s ->
    F.fprintf fmt "%s" s
  | MJazzStringError s ->
    F.fprintf fmt "%s" s

(* -------------------------------------------------------------------- *)
(*                      Load & Parse                                    *)
(* -------------------------------------------------------------------- *)

(* Combines a [mpath] into a [mname]
  (e.g. mname_from_mpath ["M2";"M1"] = "M1::M2")                        *)
let mname_from_mpath (mpath: M.modulename list): M.modulename =
  List.fold_left (fun r m -> r ^ ("::" ^ m)) "" mpath

(* reconstructs the [mpath] from a [mname]
  (e.g. mname_to_mpath "M1::M2" = ["M2";"M1"])                          *)
let mname_to_mpath (mname: M.modulename): M.modulename list =
  BatString.split_on_string ~by:"::" mname


(* splits a [mname] into toplmost module/qualifier and remainder
  (e.g. mname_split "M1::M2::M3" = ("M1";"M2::M3"])                     *)
let mname_split (mname: M.modulename): (string*M.modulename) option =
  try let qname = BatString.split mname ~by:"::" in Some qname
  with Not_found -> None

(* Each file is implicitly a module. Its name is derived directly from
  the filename (ignoring the 'from'-key)                                *)
let fmodule_name (fname: string) : M.modulename =
  let _, mname, _ = Path.split (Path.of_string fname) in
  String.capitalize_ascii mname


(** Registers a new "from_key" *)
let add_from idir from_map (name, filename) = 
  let p = Path.of_string filename
  in let ap = 
    if Path.is_absolute p then p
    else Path.concat idir p
  in begin match Map.find name from_map with
  | ap' -> 
    if ap <> ap' then 
      hierror ~loc:Lnone ~kind:"compilation" "cannot bind %s with %s it is already bound to %s"
        name (Path.to_string ap) (Path.to_string ap')
  | exception Not_found -> ()
  end;
  Map.add name ap from_map

(** Loads & Parses a file
  Please note:
   - full modulename is always non-qualified
                                                                        *)
let load_fname from_map visited processed from loc fname
  : ((M.modulename*Path.t)*Syntax.pprogram) option =
  let modname = 
    if !Glob_options.debug then Printf.eprintf "PROCESSING \"%s\" \n%!" fname;
    fmodule_name fname
  in let ploc = match loc with None -> Lnone | Some l -> Lone l
  in let p = Path.of_string fname
  in let current_dir =
    match from with
    | None -> snd (List.hd visited)
    | Some name -> 
        if Path.is_absolute p then 
          hierror ~loc:ploc ~kind:"typing" 
            "cannot use absolute path in 'from %s require \"%s\"'" 
            (L.unloc name) fname;
        try Map.find (L.unloc name) from_map 
        with Not_found ->
          raise (tyerror ~loc:(L.loc name)
                   (string_error "unknown from-key name %s" (L.unloc name)))
  in let p = if Path.is_absolute p then p else Path.concat current_dir p
  in let p = Path.normalize_in_tree p
  in let ap =
       if Path.is_absolute p
       then p
       else (* ?deadcode? *) Path.concat (snd (BatList.last visited)) p
  in let ap = Path.normalize_in_tree ap
  in (if Option.is_some (List.find_opt (fun x -> modname=(fst x)) visited)
      then
        hierror ~loc:ploc ~kind:"dependencies"
          "circular dependency detected on module \"%s\"\n(please note that MJazz does not support equal filenames)\n" 
          modname);
     if Ss.mem modname processed
     then (if !Glob_options.debug
           then Printf.eprintf "reusing AST for \"%s\" \n%!" modname;
           None)
     else
       let ast = Parseio.parse_program ~name:(Path.to_string p)
       in let ast =
         try BatFile.with_file_in fname ast
         with Sys_error(err) ->
           let loc = Option.map_default (fun l -> Lone l) Lnone loc
           in hierror ~loc ~kind:"typing" "error reading file %S (%s)" fname err
       in Some ((modname,ap), ast)


(* -------------------------------------------------------------------- *)
(*                      Environment                                     *)
(* -------------------------------------------------------------------- *)


(* obs:
   "e_bindings env" is used differently from pretyping. Instead of
   keeping namespace-path bindings, it is used to access visible symbols
   from opened modules.
       "(cur_moodname,cur_bindings)::opened_modules, global_bindings"
   Symbols visible through open modules never hide symbols from current
   module!                                                              *)

module MEnv = struct

  type 'asm mod_info =
    { mi_gb : 'asm Env.global_bindings
   (* ; mi_decls : (P.pexpr, unit, 'asm) M.gmodule_item list*)
    }

  type 'asm menv =
    { me_mpath : M.modulename list
    ; me_cur : 'asm Env.env
    ; me_decls : (P.pexpr_, unit, 'asm) M.gmodule_item list
    ; me_env : (M.modulename, 'asm mod_info) Map.t
(*    ; me_visited :  *)
    }

  let empty =
    { me_mpath = [] 
    ; me_cur = Env.empty
    ; me_decls = []
    ; me_env = Map.empty
    }

  let push_mpath menv mname =
    { menv with me_mpath = mname::menv.me_mpath }

  (* injects decls. accumulated in me_cur into me_decls *)
  let flush_decls menv =
    { menv with
      me_decls = List.map (fun x->M.MdItem x) menv.me_cur.e_decls @ menv.me_decls
    ; me_cur = { menv.me_cur with e_decls = [] }
    }

  module Vars = struct
(*
    let push_param menv (x, e) =
      let name = x.P.v_name in
      let x = rename_var (fully_qualified (fst env.e_bindings) name) x in
      let env = push_core env name x Slocal in
      { env with e_decls = P.MIparam (x, e) :: env.e_decls }
*)
  end
    
  let upd_cur menv env = { menv with me_cur = env }

  let push_open menv mname gb =
    let stack, bot = menv.me_cur.e_bindings
    in let new_stack =
         match stack with
         | [] ->
           rs_mjazzerror ~loc:(L.loc mname) (MJazzInternal "malformed e_bindings")
         | top::rest -> top::(L.unloc mname, gb)::rest
    in { menv with me_cur = { menv.me_cur with e_bindings = new_stack, bot } }
end



(* -------------------------------------------------------------------- *)
(*                      Processing                                      *)
(* -------------------------------------------------------------------- *)

(*

- "require" só são suportados no top-level
- "visit_file" produz uma lista de top-level modules (reverse order)
- 

*)

(* -------------------------------------------------------------------- *)

(*
let mt_var_core (mode:tt_mode) (menv : 'asm Env.env) { L.pl_desc = x; L.pl_loc = lc; } = 
  let v, _ as vs =
    match MEnv.Vars.find x env with
    | Some vs -> vs
    | None -> rs_tyerror ~loc:lc (UnknownVar x) in
  begin match mode with
  | `OnlyParam ->
    if v.P.v_kind <> W.Const then
      rs_tyerror ~loc:lc (StringError "only param variables are allowed here")
  | `NoParam -> 
    if v.P.v_kind = W.Const then
      rs_tyerror ~loc:lc (StringError "param variables are not allowed here")
  | `AllVar -> ()
  end;
  vs

let tt_var (mode:tt_mode) (env : 'asm Env.env) x = 
  let v, s = tt_var_core mode env x in
  if s = Sglob then 
    rs_tyerror ~loc:(L.loc x) (StringError "global variables are not allowed here");
  v

let tt_var_global (mode:tt_mode) (env : 'asm Env.env) v = 
  let lc = v.L.pl_loc in
  let x, s = tt_var_core mode env v in
  { P.gv = L.mk_loc lc x; P.gs = s }, x.P.v_ty



(* -------------------------------------------------------------------- *)
let tt_fun (env : 'asm Env.env) { L.pl_desc = x; L.pl_loc = loc; } =
  Env.Funs.find x env |> oget ~exn:(tyerror ~loc (UnknownFun x))




let tt_param pd (menv : 'asm MEnv.menv) _loc (pp : S.pparam) : 'asm MEnv.menv =
  let ty = tt_type pd menv.me_cur pp.ppa_ty in
  let pe, ety = tt_expr ~mode:`OnlyParam pd env pp.S.ppa_init in

  check_ty_eq ~loc:(L.loc pp.ppa_init) ~from:ty ~to_:ety;

  let x = P.PV.mk (L.unloc pp.ppa_name) W.Const ty (L.loc pp.ppa_name) [] in
  let env = Env.Vars.push_param env (x,pe) in
  env
*)

let rec mt_item arch_info (menv: 'asm MEnv.menv) mitem : 'asm MEnv.menv =
  match L.unloc mitem with
  | S.PModule (mname, mparams, body) ->
(*  let modname = current_module menv
    in let env = newmodule_env mparams
    in*) MEnv.empty
    (* MdFunctor funcdef *)
  | S.PModuleApp (mname, modfun, margs) ->
    MEnv.empty
    (* MdModApp modapp *)
  | S.POpen (mname, None) ->
    begin match Map.find (L.unloc mname) menv.me_env with
      | exception Not_found -> rs_mjazzerror ~loc:(L.loc mname) (NonExistentMod (L.unloc mname))
      | minfo -> MEnv.push_open menv mname minfo.mi_gb
    end
  | S.POpen (mname, qual) -> rs_mjazzerror ~loc:(L.loc mname) MJazzNYS
  | S.Prequire (from, fs) ->
    begin match menv.me_mpath with
      | [modname] ->
        MEnv.empty
        (* load & parse & process *)
      | _ -> rs_mjazzerror ~loc:(L.loc mitem) NonToplevelRequire
    end
  | S.PNamespace (ns, _) -> rs_mjazzerror ~loc:(L.loc ns) MJazzIncompatibleNS
  | S.Pexec pf -> rs_mjazzerror ~loc:(L.loc pf.pex_name) MJazzNYS
  (* similar to Pretyping... *)
  | S.PTypeAlias (id,ty) ->
    MEnv.upd_cur menv (tt_typealias arch_info menv.me_cur id ty)
  | S.PParam pp -> 
    MEnv.upd_cur menv (tt_param arch_info.pd menv.me_cur (L.loc mitem) pp)
  | S.PGlobal pg ->
    MEnv.upd_cur menv (tt_global arch_info.pd menv.me_cur (L.loc mitem) pg)
  | S.PFundef pf ->
    MEnv.upd_cur menv (tt_fundef arch_info menv.me_cur (L.loc mitem) pf)

and mt_file_loc arch_info from menv fname =
  fst (mt_file arch_info menv from (Some (L.loc fname)) (L.unloc fname))

and mt_file arch_info menv from loc fname =
  MEnv.empty, []

let tt_mprogram arch_info menv (fname: string) =
  let menv = mt_file arch_info menv None None fname
  in menv



(* -------------------------------------------------------------------- *)
(*                      External API                                    *)
(* -------------------------------------------------------------------- *)

let parse_mfile arch_info idirs fname =
  let menv, mprog = [], []
  in menv, mprog

let instantiate_mprog menv mprog =
  []

(** Parses (modular) program and resolves instantiation *)
let parse_file arch_info idirs fname =
  let menv, mprog = [], []
  in menv, [], instantiate_mprog menv mprog

