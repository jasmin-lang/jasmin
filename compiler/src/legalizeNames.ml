open Utils
open Prog

let is_valid_lident (s : string) : bool =
  String.length s > 0
  && (let c = s.[0] in
      c >= 'a' && c <= 'z')
  && String.for_all
       (fun c ->
         (c >= 'a' && c <= 'z')
         || (c >= 'A' && c <= 'Z')
         || (c >= '0' && c <= '9')
         || c = '_')
       s

let normalize_base (n : string) : string =
  let n = PrintCommon.escape n in
  let n = String.uncapitalize_ascii n in
  if is_valid_lident n then n else "aux"

let create_name (reserved : Ss.t ref) (s : string) : string =
  if not (Ss.mem s !reserved) then s
  else
    let rec aux i =
      let s' = Format.sprintf "%s_%i" s i in
      if Ss.mem s' !reserved then aux (i + 1) else s'
    in
    aux 0

let mk_name (reserved : Ss.t ref) (n : string) : string =
  let s = create_name reserved (normalize_base n) in
  reserved := Ss.add s !reserved;
  s

(* Base reserved set shared by every function: EasyCrypt keywords, the
   module name, and the (already-legalized) names of every function and
   global -- so the printer's own later allocations for those cannot
   collide with a variable renamed here. Deliberately NOT threaded across
   sibling functions' own local variables: each function gets an
   independent copy of this base (see [get_scope] below), matching the
   printer's own per-function [Env.new_fun] scoping (`toEC.ml`'s
   [toec_fun]) -- two unrelated functions reusing the same local variable
   name (e.g. two loops each introducing their own fresh "i_ftw" bound
   variable) must not be forced to diverge into "i_ftw"/"i_ftw_0". *)
let initial_reserved
    (globs : global_decl list) (funcs : ('info, 'asm) func list) : Ss.t =
  let reserved = ref (Ss.add "M" ToEC.keywords) in
  List.iter (fun fd -> ignore (mk_name reserved fd.f_name.fn_name)) funcs;
  List.iter (fun (x, _) -> ignore (mk_name reserved x.v_name)) globs;
  !reserved

(* Per-function renaming scope: a private copy of the base reserved set
   together with the memoization table for variables already renamed in
   this function. Lazily created (keyed by [funname]) the first time a
   given function is encountered. *)
type scope = { reserved : Ss.t ref; memo : var Mv.t ref }

let build_rename ((globs, funcs) : (unit, 'asm) Prog.prog) :
    funname -> Var0.Var.var -> Ident.Ident.ident =
  let base_reserved = initial_reserved globs funcs in
  let scopes : scope Mf.t ref = ref Mf.empty in
  let get_scope (fn : funname) : scope =
    match Mf.find_opt fn !scopes with
    | Some s -> s
    | None ->
        let s = { reserved = ref base_reserved; memo = ref Mv.empty } in
        scopes := Mf.add fn s !scopes;
        s
  in
  fun (fn : funname) (x : Var0.Var.var) ->
    let s = get_scope fn in
    let v = Conv.var_of_cvar x in
    match Mv.find_opt v !(s.memo) with
    | Some v' -> v'
    | None ->
        let name = mk_name s.reserved v.v_name in
        let v' = V.mk name v.v_kind v.v_ty v.v_dloc v.v_annot in
        s.memo := Mv.add v v' !(s.memo);
        v'
