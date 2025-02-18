(* -------------------------------------------------------------------- *)
open Utils
module Path = BatPathGen.OfString
module F = Format
module L = Location
module A = Annotations
module S = Syntax
module E = Expr
module P = Prog
module W = Wsize
module T = Type

(* -------------------------------------------------------------------- *)
let loc_of_tuples default locs =
  List.fold_left L.merge default locs

(* -------------------------------------------------------------------- *)
type sop = [ `Op2 of S.peop2 | `Op1 of S.peop1]

type tyerror =
  | UnknownVar          of A.symbol
  | UnknownFun          of A.symbol
  | InvalidArrayType    of P.epty
  | TypeMismatch        of P.epty pair
  | NoOperator          of sop * P.epty list
  | InvalidOperator     of sop
  | NoReturnStatement   of P.funname * int
  | InvalidReturnStatement of P.funname * int * int
  | InvalidSignatureStorage of P.funname * S.pstorage * A.symbol * W.v_kind
  | InvalidArgCount     of int * int
  | InvalidLvalCount    of int * int
  | DuplicateFun        of A.symbol * L.t
  | DuplicateAlias      of A.symbol * P.epty L.located * P.epty L.located
  | TypeNotFound        of A.symbol
  | InvalidTypeAlias    of A.symbol L.located option * P.epty
  | InvalidCast         of P.epty pair
  | InvalidTypeForGlobal of P.epty
  | GlobArrayNotWord
  | GlobWordNotArray
  | EqOpWithNoLValue
  | CallNotAllowed
  | PrimNotAllowed
  | Unsupported         of string
  | UnknownPrim of A.symbol * string
  | PrimWrongSuffix of A.symbol * Sopn.prim_x86_suffix list
  | PtrOnlyForArray
  | PackSigned
  | PackWrongWS of int
  | PackWrongPE of int
  | PackWrongLength of int * int
  | UnsupportedZeroExtend of (F.formatter -> unit)
  | InvalidZeroExtend of W.wsize * W.wsize * (F.formatter -> unit)
  | StringError of string

exception TyError of L.t * tyerror

let string_error fmt =
  let buf  = Buffer.create 127 in
  let bfmt = Format.formatter_of_buffer buf in
  Format.kfprintf
    (fun bfmt ->
      Format.pp_print_flush bfmt ();
      (StringError (Buffer.contents buf)))
    bfmt fmt

let tyerror ~loc (code : tyerror) =
  TyError (loc, code)

let rs_tyerror ~loc (code : tyerror) =
  raise (tyerror ~loc code)

(* -------------------------------------------------------------------- *)
let pp_suffix fmt =
  let open Sopn in
  let open PrintCommon in
  function
  | PVp sz -> F.fprintf fmt "_%a" pp_wsize sz
  | PVs (sg, sz) -> F.fprintf fmt "_%s%a" (string_of_signess sg) pp_wsize sz
  | PVv (ve, sz) -> F.fprintf fmt "_%s" (string_of_velem Unsigned sz ve)
  | PVsv (sg, ve, sz) -> F.fprintf fmt "_%s" (string_of_velem sg sz ve)
  | PVx (szo, szi) -> F.fprintf fmt "_u%au%a" pp_wsize szo pp_wsize szi
  | PVvv (ve, sz, ve', sz') -> F.fprintf fmt "_%s_%s" (string_of_velem Unsigned sz ve) (string_of_velem Unsigned sz' ve')

let pp_tyerror fmt (code : tyerror) =
  match code with
  | UnknownVar x ->
      F.fprintf fmt "unknown variable: `%s'" x

  | UnknownFun x ->
      F.fprintf fmt "unknown function: `%s'" x

  | InvalidArrayType ty ->
    F.fprintf fmt "the expression has type %a instead of array"
       Printer.pp_eptype ty

  | TypeMismatch (t1,t2) ->
    F.fprintf fmt
      "the expression has type %a instead of %a"
      Printer.pp_eptype t1 Printer.pp_eptype t2

  | InvalidCast (t1,t2) ->
    F.fprintf fmt "can not implicitly cast %a into %a"
      Printer.pp_eptype t1 Printer.pp_eptype t2

  | InvalidTypeForGlobal ty ->
      F.fprintf fmt "globals should have type word; found: ‘%a’"
        Printer.pp_eptype ty

  | GlobArrayNotWord ->
    F.fprintf fmt "the definition is an array and not a word"

  | GlobWordNotArray ->
    F.fprintf fmt "the definition is a word and not an array"

  | InvalidOperator o ->
    F.fprintf fmt "invalid operator %s"
      (match o with
       | `Op2 o -> (S.string_of_peop2 o)
       | `Op1 o -> (S.string_of_peop1 o))

  | NoOperator (`Op2 o, ts) ->
      F.fprintf fmt
        "no operator %s for these types %a"
        (S.string_of_peop2 o)
        (pp_list " * " Printer.pp_eptype) ts

  | NoOperator (`Op1 o, ts) ->
      F.fprintf fmt
        "no operator %s for these type %a"
        (S.string_of_peop1 o)
        (pp_list " * " Printer.pp_eptype) ts

  | NoReturnStatement (name, expected) ->
     F.fprintf fmt "function “%s” has no return statement (but its signature claims that %d values should be returned)" name.P.fn_name expected

  | InvalidReturnStatement (name, given, expected) ->
      F.fprintf fmt "return statement of function %s has %d values instead of %d (as claimed by the signature)" name.P.fn_name given expected

  | InvalidSignatureStorage (fname, sto, var_name, var_kind) ->
      F.fprintf fmt "In function “%s”, return statement variable “%s” has storage type “%a”, which differs from declared return storage type “%s”"
        fname.P.fn_name
        var_name
        PrintCommon.pp_kind var_kind
        (S.pp_storage sto)

  | InvalidArgCount (n1, n2) ->
      F.fprintf fmt
        "invalid number of arguments, %d provided instead of %d" n1 n2

  | InvalidLvalCount (n1, n2) ->
      F.fprintf fmt
        "invalid number of lvalues, %d provided instead of %d" n1 n2

  | DuplicateFun (f, loc) ->
      F.fprintf fmt
        "The function %s is already declared at %s"
        f (L.tostring loc)

  | DuplicateAlias (id, newtype, oldtype) ->
      F.fprintf fmt
        "Type '%s' (ie: '%a') is already declared at %s (with type : '%a')"
        id
        Printer.pp_eptype (L.unloc newtype)
        (L.tostring (L.loc oldtype))
        Printer.pp_eptype (L.unloc oldtype)

  | TypeNotFound (id) ->
      F.fprintf fmt
      "Type '%s' not found"
      id

  | InvalidTypeAlias (id,typ) ->
      let pp_id fmt (id, typ) =
        match id with
        | None -> F.fprintf fmt "'%a'" Printer.pp_eptype typ
        | Some id ->
            F.fprintf fmt "'%s' (ie: '%a'), defined at %s," (L.unloc id) Printer.pp_eptype typ
               (L.tostring (L.loc id)) in
      F.fprintf fmt
      "Type %a is not allowed as array element. Only machine words (w8, w16 ...) allowed"
      pp_id (id, typ)

  | EqOpWithNoLValue ->
      F.fprintf fmt
        "operator-assign requires a lvalue"

  | CallNotAllowed ->
      F.fprintf fmt
        "function calls not allowed at that point"

  | PrimNotAllowed ->
      F.fprintf fmt
        "primitive calls not allowed at that point"

  | Unsupported s ->
      F.fprintf fmt "%s" s
  | UnknownPrim(s, msg) ->
      F.fprintf fmt "unknown primitive: \"%s\"%s" s msg

  | PrimWrongSuffix (s, []) ->
      F.fprintf fmt "primitive accepts no size annotation: `%s'" s

  | PrimWrongSuffix (s, sfxs) ->
     F.fprintf fmt "primitive “%s” only accepts the following size annotations: %a" s
       (pp_list ",@ " pp_suffix) sfxs

  | PtrOnlyForArray ->
    F.fprintf fmt "Pointer allowed only on array"

  | PackSigned ->
    F.fprintf fmt "packs should be unsigned"

  | PackWrongWS n ->
    F.fprintf fmt "wrong word-size (%d) in pack" n

  | PackWrongPE n ->
    F.fprintf fmt "wrong element-size (%d) in pack" n

  | PackWrongLength (e, f) ->
    F.fprintf fmt "wrong length of pack; expected: %d; found: %d" e f

  | UnsupportedZeroExtend name ->
      F.fprintf fmt "primitive operator %t does not support zero-extension" name

  | InvalidZeroExtend (src, dst, name) ->
      F.fprintf fmt "primitive operator %t returns an output of size %a; it cannot be zero-extended to size %a" name PrintCommon.pp_wsize src PrintCommon.pp_wsize dst

  | StringError s ->
    F.fprintf fmt "%s" s

(* -------------------------------------------------------------------- *)
(* Utility functions related to name spaces *)
let qualify ns n = Format.asprintf "%s::%s" ns n

let fully_qualified (stack: (A.symbol * 'a) list) n =
  List.fold_left (fun n (ns, _) -> qualify ns n) n stack

(* -------------------------------------------------------------------- *)

type fun_sig = { fs_tin : P.epty list ; fs_tout : P.epty list }

module Env : sig
  type 'asm env

  val empty : 'asm env

  val decls : 'asm env -> (unit, 'asm) P.pmod_item list

  val add_from : 'asm env -> string * string -> 'asm env

  val enter_file : 'asm env -> A.pident option -> L.t option -> string -> ('asm env * string) option
  val exit_file  : 'asm env -> 'asm env

  val dependencies : 'asm env -> Path.t list

  val add_reserved : 'asm env -> string -> 'asm env
  val is_reserved : 'asm env -> string -> bool

  val set_known_implicits : 'asm env -> (string * string) list -> 'asm env
  val get_known_implicits : 'asm env -> (string * string) list

  val enter_namespace : 'asm env -> A.pident -> 'asm env
  val exit_namespace : 'asm env -> 'asm env

  module Vars : sig
    val push_global   : 'asm env -> (P.pvar * P.epty * P.pexpr_ P.ggexpr ) -> 'asm env
    val push_param    : 'asm env -> (P.pvar * P.epty * P.pexpr) -> 'asm env
    val push_local    : 'asm env -> P.pvar * P.epty -> 'asm env
    val push_implicit : 'asm env -> P.pvar * P.epty -> 'asm env

    val find : A.symbol -> 'asm env -> (P.pvar * P.epty * E.v_scope) option

    val iter_locals  : (P.pvar -> unit) -> 'asm env -> unit
    val clear_locals : 'asm env -> 'asm env
  end

  module TypeAlias : sig
    val push : 'asm env -> A.pident -> P.epty -> 'asm env
    val get : 'asm env -> A.pident -> P.epty L.located
  end

  module Funs : sig
    val push : 'asm env -> (unit, 'asm) P.pfunc -> fun_sig -> 'asm env
    val find : A.symbol -> 'asm env -> ((unit, 'asm) P.pfunc * fun_sig) option
  end

  module Exec : sig
    val push : L.t -> P.funname -> (Z.t * Z.t) list -> 'asm env -> 'asm env
    val get  : 'asm env -> (P.funname * (Z.t * Z.t) list) L.located list
  end

end  = struct

  type loader =
    { loaded : (A.symbol, Path.t list) Map.t (* absolute path loaded in each namespace *)
    ; idir   : Path.t      (* absolute initial path *)
    ; dirs   : Path.t list
    ; from   : (A.symbol, Path.t) Map.t
    }

  type 'asm global_bindings = {
      gb_types : (A.symbol, P.epty L.located) Map.t;
      gb_vars : (A.symbol, P.pvar * P.epty * E.v_scope) Map.t;
      gb_funs : (A.symbol, (unit, 'asm) P.pfunc * fun_sig) Map.t;
    }

  type 'asm env = {
    e_bindings : (A.symbol * 'asm global_bindings) list * 'asm global_bindings;
    e_decls   : (unit, 'asm) P.pmod_item list;
    e_exec    : (P.funname * (Z.t * Z.t) list) L.located list;
    e_loader  : loader;
    e_declared : P.Spv.t ref; (* Set of local variables declared somewhere in the function *)
    e_reserved : Ss.t;     (* Set of string (variable name) declared by the user,
                              fresh variables introduced by the compiler
                              should be disjoint from this set *)
    e_known_implicits : (string * string) list;  (* Association list for implicit flags *)
  }

  let empty_loader =
    { loaded = Map.empty
    ; idir = Path.of_string (Sys.getcwd ())
    ; dirs = [[]]
    ; from = Map.empty
    }

  let empty_gb = { gb_vars = Map.empty ; gb_funs = Map.empty; gb_types = Map.empty }

  let empty : 'asm env =
    { e_bindings = [], empty_gb
    ; e_decls   = []
    ; e_exec    = []
    ; e_loader  = empty_loader
    ; e_declared = ref P.Spv.empty
    ; e_reserved = Ss.empty
    ; e_known_implicits = [];
    }

  let add_reserved env s =
    { env with e_reserved = Ss.add s env.e_reserved }

  let is_reserved env s =
    Ss.mem s env.e_reserved

  let set_known_implicits env known_implicits = { env with e_known_implicits = known_implicits }
  let get_known_implicits env = env.e_known_implicits

  let enter_namespace env ns =
    let stack, bot = env.e_bindings in
    { env with e_bindings = (L.unloc ns, empty_gb) :: stack, bot }

  let merge_bindings on_duplicate ns =
    Map.foldi (fun n v dst ->
        let n = qualify ns n in
        begin match Map.find n dst with
        | exception Not_found -> ()
        | k -> on_duplicate n v k end;
        Map.add n v dst)

  let warn_duplicate_var name (v, _, _) (v', _, _) =
    warning DuplicateVar (L.i_loc0 v.P.v_dloc)
      "the variable %s is already declared at %a"
      name L.pp_loc v'.P.v_dloc

  let err_duplicate_fun name (v, _) (fd, _) =
    rs_tyerror ~loc:v.P.f_loc (DuplicateFun(name, fd.P.f_loc))

  let err_duplicate_type name t1 t2 =
    rs_tyerror ~loc:(L.loc t2) (DuplicateAlias (name,t1,t2))

  let merge_bindings (ns, src) dst =
    { gb_vars = merge_bindings warn_duplicate_var ns src.gb_vars dst.gb_vars
    ; gb_funs = merge_bindings err_duplicate_fun ns src.gb_funs dst.gb_funs
    ; gb_types = merge_bindings err_duplicate_type ns src.gb_types dst.gb_types
    }

  let exit_namespace env =
    match env.e_bindings with
    | [], _ -> assert false
    | top :: [], bot ->
       let merged = merge_bindings top bot in
       { env with e_bindings = [], merged }
    | top :: (ns, next) :: stack, bot ->
       let merged = merge_bindings top next in
       { env with e_bindings = (ns, merged) :: stack, bot }

  let add_from env (name, filename) =
    let p = Path.of_string filename in
    let ap =
      if Path.is_absolute p then p
      else Path.concat env.e_loader.idir p in
    begin match Map.find name env.e_loader.from with
    | ap' ->
      if ap <> ap' then
        hierror ~loc:Lnone ~kind:"compilation" "cannot bind %s with %s it is already bound to %s"
          name (Path.to_string ap) (Path.to_string ap')
    | exception Not_found -> ()
    end;
    {env with e_loader =
       { env.e_loader with from = Map.add name ap env.e_loader.from }}

  let enter_file env from ploc filename =
    let ploc = match ploc with None -> Lnone | Some l -> Lone l in
    let p = Path.of_string filename in
    let loader = env.e_loader in
    let current_dir =
      match from with
      | None -> List.hd loader.dirs
      | Some name ->
          if Path.is_absolute p then
            hierror ~loc:ploc ~kind:"typing"
              "cannot use absolute path in from %s require \"%s\""
                 (L.unloc name) filename;
          try Map.find (L.unloc name) env.e_loader.from
          with Not_found ->
            rs_tyerror ~loc:(L.loc name) (string_error "unknown name %s" (L.unloc name)) in
    let p =
      if Path.is_absolute p then p
      else Path.concat current_dir p in
    let p = Path.normalize_in_tree p in
    let ap =
      if Path.is_absolute p then p
      else Path.concat loader.idir p in
    let ap = Path.normalize_in_tree ap in
    let namespace = fully_qualified (fst env.e_bindings) "<>" in
    if List.mem ap (Map.find_default [] namespace loader.loaded) then None
    else
      let e_loader =
        { loader with
          loaded = Map.modify_def [] namespace (List.cons ap) loader.loaded;
          dirs = List.tl p :: loader.dirs } in
      Some({ env with e_loader }, Path.to_string p)

  let exit_file env =
    { env with
      e_loader = { env.e_loader with dirs = List.tl env.e_loader.dirs }}

  let decls env = env.e_decls

  let dependencies env =
    Map.fold ( @ ) env.e_loader.loaded []

  let find (proj: 'asm global_bindings -> (A.symbol, 'a) Map.t) (x: A.symbol) (env: 'asm env) : 'a option =
    let stack, bot = env.e_bindings in
    let rec loop x =
      function
      | [] -> None
      | (_, top) :: stack ->
         match Map.find x (proj top) with
         | exception Not_found -> loop x stack
         | v -> Some v
    in match loop x stack with
       | None -> Map.Exceptionless.find x (proj bot)
       | r -> r

  (* Local variables *)

  module Vars = struct

    let find (x : A.symbol) (env : 'asm env) =
      find (fun b -> b.gb_vars) x env

    let warn_double_decl v map =
      let name = v.P.v_name in
      match Map.find name map with
      | exception Not_found -> ()
      | v' -> warn_duplicate_var name (v, (), ()) v'

    let push_core (env : 'asm env) (name: P.Name.t) (v : P.pvar) (ty: P.epty) (s : E.v_scope)  =
      let doit m =
        warn_double_decl v m.gb_vars;
        { m with gb_vars = Map.add name (v, ty, s) m.gb_vars }
      in
      let e_bindings =
        match env.e_bindings with
        | [], bot -> [], doit bot
        | (ns, top) :: stack, bot ->
           (ns, doit top) :: stack, bot
      in
      { env with e_bindings; e_reserved = Ss.add name env.e_reserved;}

    let rename_var name x =
      P.GV.mk name x.P.v_kind x.P.v_ty x.P.v_dloc x.P.v_annot

    let push_global env (x, ty, e) =
      let name = x.P.v_name in
      let x = rename_var (fully_qualified (fst env.e_bindings) name) x in
      let env = push_core env name x ty Sglob in
      { env with e_decls = P.MIglobal (x, e) :: env.e_decls }

    let push_param env (x, ty, e) =
      let name = x.P.v_name in
      let x = rename_var (fully_qualified (fst env.e_bindings) name) x in
      let env = push_core env name x ty Slocal in
      { env with e_decls = P.MIparam (x, e) :: env.e_decls }

    let push_local (env : 'asm env) ((v,ty) : P.pvar * P.epty) =
      env.e_declared := P.Spv.add v !(env.e_declared);
      push_core env v.P.v_name v ty Slocal

    let push_implicit (env : 'asm env) ((v,ty) : P.pvar * P.epty) =
      let vars = match env.e_bindings with (_, b) :: _, _ | [], b -> b.gb_vars in
      assert (not (Map.mem v.P.v_name vars));
      push_core env v.P.v_name v ty Slocal

    let iter_locals f (env : 'asm env) =
      P.Spv.iter f !(env.e_declared)

    let clear_locals (env : 'asm env) =
      { env with e_declared = ref P.Spv.empty }

  end

  module TypeAlias = struct

    let push (env: 'asm env) (id: A.pident) (ty: P.epty) : 'asm env =
      match find (fun x -> x.gb_types) (L.unloc id) env with
      | Some alias ->
         rs_tyerror  ~loc:(L.loc id)  (DuplicateAlias (L.unloc id, (L.mk_loc (L.loc id) ty) ,alias) )
      | None ->
          let ty = L.mk_loc (L.loc id) ty in
          let doit v = {v with gb_types = Map.add (L.unloc id) ty v.gb_types }
          in let binds =
          match env.e_bindings with
          | ([],gb) -> [],doit gb
          | ((ns,gb):: stack, glob) -> (ns,doit gb):: stack , glob
          in
          {env with e_bindings = binds}

    let get (env: 'asm env) (id: A.pident) : P.epty L.located =
      let typea = find (fun b -> b.gb_types) (L.unloc id) env in
      match typea with
      | None ->
        rs_tyerror  ~loc:(L.loc id) (TypeNotFound (L.unloc id))
      | Some e -> e

  end

  module Funs = struct
    let find (x : A.symbol) (env : 'asm env) =
      find (fun b -> b.gb_funs) x env

    let push env (v : (unit, 'asm) P.pfunc) rty =
      let name = v.P.f_name.P.fn_name in
      let v = { v with P.f_name = P.F.mk (fully_qualified (fst env.e_bindings) name) } in
      match find name env with
      | None ->
         let doit m =
           { m with gb_funs = Map.add name (v, rty) m.gb_funs }
         in
         let e_bindings =
           match env.e_bindings with
           | [], bot -> [], doit bot
           | (ns, top) :: stack, bot ->
              (ns, doit top) :: stack, bot
      in
      { env with e_bindings; e_decls = P.MIfun v :: env.e_decls }
      | Some fd ->
         err_duplicate_fun name (v, ()) fd

  end

  module Exec = struct
    let push loc f m env = { env with e_exec = L.mk_loc loc (f, m) :: env.e_exec }
    let get env = List.rev env.e_exec
  end

end

(* -------------------------------------------------------------------- *)
let tt_pointer dfl_writable (p:S.ptr) : W.reference =
  match p with
  | `Pointer (Some `Writable) -> W.Pointer W.Writable
  | `Pointer (Some `Constant) -> W.Pointer W.Constant
  | `Pointer None             ->
    W.Pointer (if dfl_writable then W.Writable else W.Constant)
  | `Direct  -> W.Direct

let tt_reg_kind annot =
  match Annot.ensure_uniq1 "mmx" Annot.none annot with
  | Some () -> W.Extra
  | None    -> W.Normal

let tt_sto regkind dfl_writable (sto : S.pstorage) : W.v_kind =
  match sto with
  | `Inline  -> W.Inline
  | `Reg   p -> W.Reg (regkind, tt_pointer dfl_writable p)
  | `Stack p -> W.Stack (tt_pointer dfl_writable p)
  | `Global  -> W.Global

type tt_mode = [
  | `AllVar
  | `OnlyParam
  | `NoParam
  ]

(* -------------------------------------------------------------------- *)

let tt_var_core (mode:tt_mode) (env : 'asm Env.env) { L.pl_desc = x; L.pl_loc = lc; } =
  let v, _, _ as vs =
    match Env.Vars.find x env with
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
  let v, ty, s = tt_var_core mode env x in
  if s = Sglob then
    rs_tyerror ~loc:(L.loc x) (StringError "global variables are not allowed here");
  v, ty

let tt_var_global (mode:tt_mode) (env : 'asm Env.env) v =
  let lc = v.L.pl_loc in
  let x, ty, s = tt_var_core mode env v in
  { P.gv = L.mk_loc lc x; P.gs = s }, ty

(* -------------------------------------------------------------------- *)
let tt_fun (env : 'asm Env.env) { L.pl_desc = x; L.pl_loc = loc; } =
  Env.Funs.find x env |> oget ~exn:(tyerror ~loc (UnknownFun x))

(* -------------------------------------------------------------------- *)
let check_ty_eq ~loc ~(from : P.epty) ~(to_ : P.epty) =
  if not (P.epty_equal from to_) then
    match from, to_ with
    | ETarr _, ETarr _ -> () (* we delay typechecking until we know the lengths *)
    | _, _ -> rs_tyerror ~loc (TypeMismatch (from, to_))

let check_ty_ptr pd ~loc ty =
  check_ty_eq ~loc ~from:ty ~to_:(P.etw pd)

let check_ty_bool ~loc ty =
  check_ty_eq ~loc ~from:ty ~to_:P.etbool

(* -------------------------------------------------------------------- *)
let check_return_statement ~loc name (declared : P.epty list) (given : (L.t * P.epty) list) : unit =
  let given_size = List.length given in
  let declared_size = List.length declared in
  if Stdlib.Int.equal 0 given_size
  then
    (if not (Stdlib.Int.equal 0 declared_size)
     then rs_tyerror ~loc (NoReturnStatement (name, declared_size)))
  else
    if not (Stdlib.Int.equal given_size declared_size)
    then rs_tyerror ~loc:(loc_of_tuples loc (List.rev_map fst given)) (InvalidReturnStatement (name, given_size, declared_size));
  List.iter2
    (fun ty1 (loc, ty2) -> check_ty_eq ~loc ~from:ty2 ~to_:ty1)
    declared given

let check_return_storage ~loc fname =
  List.iter2 (
    fun sto (y:'len P.gvar_i) ->
      match sto, (L.unloc y).v_kind with
      | `Inline, W.Inline -> ()
      | `Reg ptr, W.Reg (_, ref) | `Stack ptr, W.Stack ref -> (
        match ptr, ref with
        (* Valid type rule *)
        | `Pointer (Some `Writable), W.Pointer W.Writable
        | `Pointer (Some `Constant), W.Pointer W.Constant
        | `Pointer None, W.Pointer _
        | `Direct, W.Direct -> ()

        (* Invalid type rule *)
        | `Pointer (Some `Writable), (W.Pointer W.Constant | W.Direct)
        | `Pointer (Some `Constant), (W.Pointer W.Writable | W.Direct)
        | `Pointer None, W.Direct
        | `Direct, W.Pointer _
        -> rs_tyerror ~loc (InvalidSignatureStorage(fname, sto, (L.unloc y).v_name, (L.unloc y).v_kind))
      )
      (* Global should never be returned, it is checked before this function is called in tt_fundef *)
      | _ , W.Global -> assert false
      | `Global , _ -> assert false

      (* Invalid type rule *)
      | `Reg _,   (W.Stack _ | W.Inline  | W.Const)
      | `Stack _, (W.Reg _   | W.Inline  | W.Const)
      | `Inline,  (W.Reg _   | W.Stack _ | W.Const)
      -> rs_tyerror ~loc (InvalidSignatureStorage(fname, sto, (L.unloc y).v_name,(L.unloc y).v_kind))
    )

(* -------------------------------------------------------------------- *)
let check_sig_lvs loc sig_ lvs =
  let loc () = loc_of_tuples loc (List.map (fun (l,_,_) -> l) lvs) in

  let nsig_ = List.length sig_ in
  let nlvs  = List.length lvs  in

  if nlvs <> nsig_ then
    rs_tyerror ~loc:(loc ()) (InvalidLvalCount(nlvs, nsig_));

  List.iter2
    (fun ty (loc, _, lty) -> lty
      |> Option.may (fun lty -> check_ty_eq ~loc ~from:ty ~to_:lty))
     sig_ lvs;

  List.map2 (fun ty (_,flv,_) -> flv ty) sig_ lvs


(* -------------------------------------------------------------------- *)
let tt_sign = function
  | `Signed -> W.Signed
  | `Unsigned -> W.Unsigned

(* -------------------------------------------------------------------- *)
let tt_as_array ((loc, ty) : L.t * P.epty) : P.epty * P.pexpr_ =
  match ty with
  | ETarr (ws, n) -> P.etw ws, n
  | _ -> rs_tyerror ~loc (InvalidArrayType ty)

(* -------------------------------------------------------------------- *)

let wsize_le = Utils0.cmp_le W.wsize_cmp
let wsize_min = Utils0.cmp_min W.wsize_cmp
let wsize_max s1 s2 = if wsize_le s1 s2 then s2 else s1

let max_ty ty1 ty2 =
  if P.epty_equal ty1 ty2 then Some ty1 else
  match ty1, ty2 with
  | ETint, ETword _ -> Some ty2
  | ETword _, ETint -> Some ty1
  | ETword(None, w1), ETword(None, w2) ->
      Some(ETword(None, Utils0.cmp_min W.wsize_cmp w1 w2))
  (* Do not allow implicite cast on wint, this is important for the pass wint_int *)
  | ETword(Some _b, w1), ETword(Some _b2, _w2) -> None
  | _, _ -> None

let tt_vsize_op loc op (vs:S.vsize) (ve:S.vesize)  =
  match vs, ve with
  (* 128 *)
  | `V16, `W8  -> W.VE8 , W.U128
  | `V8 , `W16 -> W.VE16, W.U128
  | `V4 , `W32 -> W.VE32, W.U128
  | `V2 , `W64 -> W.VE64, W.U128
  (* 256 *)
  | `V32, `W8  -> W.VE8 , W.U256
  | `V16, `W16 -> W.VE16, W.U256
  | `V8 , `W32 -> W.VE32, W.U256
  | `V4 , `W64 -> W.VE64, W.U256
  | _   ,  _   -> rs_tyerror ~loc (InvalidOperator op)

type word_kind =
  | Word
  | WInt

type eop_kind =
  | EOp_int
  | EOp_w of word_kind * W.wsize

type ty_op_kind =
  | OpKE of W.signedness * eop_kind
  | OpKV of W.signedness * W.velem * W.wsize

let check_osign exn os (s:W.signedness) =
  match os with
  | None -> ()
  | Some s' -> if s <> s' then raise exn

type op_ok_on = {
  intok  : bool;
  wintok : bool;
}

let op_info_dfl exn ty s ((o_ok : op_ok_on), (minws, maxws)) =
  match ty with
  | P.ETword (None, ws) ->
    let ws = wsize_max minws ws in
    let ws = wsize_min ws maxws in
    let s = Option.default W.Unsigned s in
    OpKE (s, EOp_w (Word, ws))

  | P.ETword (Some s', ws) ->
    if not (o_ok.wintok) then raise exn;
    let ws = wsize_max minws ws in
    let ws = wsize_min ws maxws in
    check_osign exn s s';
    OpKE (s', EOp_w (WInt, ws))

  | _          ->
    if not (o_ok.intok) then raise exn;
    let s = Option.default W.Unsigned s in
    OpKE (s, EOp_int)

let check_size_op loc op sz (min, max) =
  if not (wsize_le min sz && wsize_le sz max) then
    rs_tyerror ~loc (InvalidOperator op)

let check_op_w loc op ty s (o_ok, cmp) =
  match ty with
  | None, ws ->
    check_size_op loc op ws cmp;
    let s =  Option.default W.Unsigned s in
    OpKE (s, EOp_w (Word, ws))
  | Some s', ws ->
     if not (o_ok.wintok) then rs_tyerror ~loc (InvalidOperator op);
     check_osign  (tyerror ~loc (InvalidOperator op)) s s';
     OpKE (s', EOp_w (WInt, ws))

let check_op_vec loc op cmp sz =
  match cmp with
  | None -> rs_tyerror ~loc (InvalidOperator op)
  | Some (min, max) ->
    if not (wsize_le min sz && wsize_le sz max) then
      rs_tyerror ~loc (InvalidOperator op)

let tt_osign = Option.map tt_sign

let tt_swsize (sz, sg) =
  match sg with
  | `Word _ -> P.etw sz
  | `WInt s -> P.etwi (tt_sign s) sz

let tt_swsize_op (swz:S.swsize) =
  let (ws, s) = swz in
  match s with
  | `Word s -> tt_osign s, (None, ws)
  | `WInt s -> let s = tt_sign s in Some s, (Some s, ws)

let op_info exn op (s : W.signedness option) (castop:S.castop) ty ws_cmp vs_cmp =
  match castop with
  | None                ->
    op_info_dfl exn ty s ws_cmp

  | Some c ->
    let loc = L.loc c in
    match L.unloc c with
    | CSS swz ->
      let s1, ty = tt_swsize_op swz in
      let s =
        match s, s1 with
        | Some s, Some s1 -> if s = s1 then Some s else rs_tyerror ~loc (InvalidOperator op)
        | Some _, None -> s
        | None, Some _ -> s1
        | None, None -> None
      in
      check_op_w loc op ty s ws_cmp

    | CVS(vs,s,ve) ->
      let s = tt_sign s in
      let ve, ws = tt_vsize_op loc op vs ve in
      check_op_vec loc op vs_cmp (W.wsize_of_velem ve);
      OpKV(s, ve, ws)



(* -------------------------------------------------------------------- *)
type 'o op_info = {
    opi_op   : ty_op_kind -> 'o;
    opi_wcmp : op_ok_on * (W.wsize * W.wsize);
    opi_vcmp : (W.wsize * W.wsize) option;
  }

let cmp_8_64 = (W.U8, W.U64)
let cmp_8_256 = (W.U8, W.U256)

let mk_op_kind eop vop = function
    | OpKE(s, k) -> eop s k
    | OpKV(s, ve, ws) -> vop s ve ws

let mk_op_s_k_info eop =
  { opi_op = mk_op_kind eop (fun _ _ _ -> assert false)
  ; opi_wcmp =  {intok = true; wintok = true}, cmp_8_256
  ; opi_vcmp = None }


let mk_op_k_info eop vop =
  { opi_op = mk_op_kind (fun s k -> eop s k) vop
  ; opi_wcmp =  {intok = true; wintok = true}, cmp_8_256
  ; opi_vcmp = Some cmp_8_64 }

let mk_op_k_info_no_vec eop =
  { opi_op = mk_op_kind (fun s k -> eop s k) (fun _ _ _ -> assert false)
  ; opi_wcmp = {intok = true; wintok = true}, cmp_8_256
  ; opi_vcmp = None }

let mk_logic_ws eop = function
  | OpKE (_, EOp_w (Word, ws))
  | OpKV (_,_, ws) -> eop ws
  | _ -> assert false

let mk_logic_info eop =
  { opi_op = mk_logic_ws eop;
    opi_wcmp = {intok = false; wintok = false}, cmp_8_256;
    opi_vcmp = Some (cmp_8_64); }

let mk_rot_info eop =
  { opi_op = mk_logic_ws eop;
    opi_wcmp = {intok = false; wintok = false}, cmp_8_64;
    opi_vcmp = None; }

(* -------------------------------------------------------------------- *)

let op1_of_ty exn op castop ty (info:E.sop1 op_info) =
  let tok = op_info exn (`Op1 op) None castop ty info.opi_wcmp info.opi_vcmp in
  info.opi_op tok

let lnot_info = mk_logic_info (fun ws -> E.Olnot ws)

let mk_op1 op_k op_wi s = function
  | EOp_int -> op_k E.Op_int
  | EOp_w (Word, sz) -> op_k (E.Op_w sz)
  | EOp_w (WInt, sz) -> E.Owi1 (s, op_wi sz)

let  neg_info =
  mk_op_k_info_no_vec (mk_op1 (fun k -> E.Oneg k) (fun sz -> E.WIneg sz))

(* -------------------------------------------------------------------- *)

let mk_op2 op_k op_wi s = function
  | EOp_int -> op_k s E.Op_int
  | EOp_w (Word, sz) -> op_k s (E.Op_w sz)
  | EOp_w (WInt, sz) -> E.Owi2 (s, sz, op_wi)

let add_info : E.sop2 op_info =
  mk_op_k_info (mk_op2 (fun _ k -> E.Oadd k) E.WIadd) (fun _s ve ws -> E.Ovadd(ve,ws))

let sub_info =
  mk_op_k_info (mk_op2 (fun _ k -> E.Osub k) E.WIsub) (fun _s ve ws -> E.Ovsub(ve,ws))

let mul_info =
  mk_op_k_info (mk_op2 (fun _ k -> E.Omul k) E.WImul) (fun _s ve ws -> E.Ovmul(ve,ws))

let div_info = mk_op_s_k_info (mk_op2 (fun s k -> E.Odiv(s, k)) E.WIdiv)
let mod_info = mk_op_s_k_info (mk_op2 (fun s k -> E.Omod(s, k)) E.WImod)

let land_info = mk_logic_info (fun k -> E.Oland k)
let lor_info  = mk_logic_info (fun k -> E.Olor  k)
let lxor_info = mk_logic_info (fun k -> E.Olxor k)

let shr_info =
  mk_op_k_info
   (mk_op2
     (fun s k ->
       match k with
       | E.Op_int -> E.Oasr k
       | E.Op_w ws -> if s = W.Unsigned then E.Olsr ws else E.Oasr k) E.WIshr)
     (fun s ve ws -> if s = W.Unsigned then E.Ovlsr(ve,ws) else E.Ovasr(ve,ws))

let shl_info =
  mk_op_k_info (mk_op2 (fun _ k -> E.Olsl k) E.WIshl)  (fun _s ve ws -> E.Ovlsl(ve,ws))

let ror_info = mk_rot_info (fun ws -> E.Oror ws)
let rol_info = mk_rot_info (fun ws -> E.Orol ws)

let eq_info  =  mk_op_k_info_no_vec (mk_op2 (fun _s k -> E.Oeq k) E.WIeq)
let neq_info =  mk_op_k_info_no_vec (mk_op2 (fun _s k -> E.Oneq k) E.WIneq)

let cmp_of_op_k s = function
  | E.Op_int -> E.Cmp_int
  | E.Op_w sz -> E.Cmp_w(s, sz)

let lt_info  =  mk_op_k_info_no_vec (mk_op2 (fun s k -> E.Olt (cmp_of_op_k s k)) E.WIlt)
let le_info  =  mk_op_k_info_no_vec (mk_op2 (fun s k -> E.Ole (cmp_of_op_k s k)) E.WIle)
let gt_info  =  mk_op_k_info_no_vec (mk_op2 (fun s k -> E.Ogt (cmp_of_op_k s k)) E.WIgt)
let ge_info  =  mk_op_k_info_no_vec (mk_op2 (fun s k -> E.Oge (cmp_of_op_k s k)) E.WIge)

let op2_of_ty exn op s castop ty (info:E.sop2 op_info) =
  let tok = op_info exn (`Op2 op) s castop ty info.opi_wcmp info.opi_vcmp in
  info.opi_op tok

let ensure_word exn ty = (max_ty ty (P.etw U256) |> oget ~exn)

let op2_of_pop2 exn ty (op : S.peop2) =
  match op with
  | `And    -> E.Oand
  | `Or     -> E.Oor

  | `Add  c -> op2_of_ty exn op None c ty add_info
  | `Sub  c -> op2_of_ty exn op None c ty sub_info
  | `Mul  c -> op2_of_ty exn op None c ty mul_info
  | `Div(s, c) -> op2_of_ty exn op (tt_osign s) c ty div_info
  | `Mod(s, c) -> op2_of_ty exn op (tt_osign s) c ty mod_info

  | `BAnd c -> op2_of_ty exn op None c (ensure_word exn ty) land_info
  | `BOr  c -> op2_of_ty exn op None c (ensure_word exn ty) lor_info
  | `BXOr c -> op2_of_ty exn op None c (ensure_word exn ty) lxor_info
  | `ShR(s, c) -> op2_of_ty exn op (tt_osign s) c ty shr_info
  | `ShL  c -> op2_of_ty exn op None c ty shl_info
  | `ROR  c -> op2_of_ty exn op None c ty ror_info
  | `ROL  c -> op2_of_ty exn op None c ty rol_info

  | `Eq   c -> op2_of_ty exn op None c ty eq_info
  | `Neq  c -> op2_of_ty exn op None c ty neq_info
  | `Lt(s, c) -> op2_of_ty exn op (tt_osign s) c ty lt_info
  | `Le(s, c) -> op2_of_ty exn op (tt_osign s) c ty le_info
  | `Gt(s, c) -> op2_of_ty exn op (tt_osign s) c ty gt_info
  | `Ge(s, c) -> op2_of_ty exn op (tt_osign s) c ty ge_info

let op1_of_pop1 exn ty (op: S.peop1) =
  match op with
  | `Cast _ -> assert false
  | `Not c ->
    if ty = P.etbool then
      if c <> None then raise exn
      else E.Onot
    else
      op1_of_ty exn op c (ensure_word exn ty) lnot_info

  | `Neg c -> op1_of_ty exn op c ty neg_info

(* -------------------------------------------------------------------- *)
let peop2_of_eqop (eqop : S.peqop) =
  match eqop with
  | `Raw    -> None
  | `Add  s -> Some (`Add s)
  | `Sub  s -> Some (`Sub s)
  | `Mul  s -> Some (`Mul s)
  | `Div  s -> Some (`Div s)
  | `Mod  s -> Some (`Mod s)
  | `ShR  s -> Some (`ShR s)
  | `ROR  s -> Some (`ROR s)
  | `ROL  s -> Some (`ROL s)
  | `ShL  s -> Some (`ShL s)
  | `BAnd s -> Some (`BAnd s)
  | `BXOr s -> Some (`BXOr s)
  | `BOr  s -> Some (`BOr s)

(* -------------------------------------------------------------------- *)

let wk_s_ws (s: W.signedness option) (ws: W.wsize) =
  let wk = if s = None then Word else WInt in
  let s = Option.default W.Unsigned s in
  (wk, s, ws)

let op_word_of_int (wk, s, ws) =
  match wk with
  | Word -> E.Oword_of_int ws
  | WInt -> E.Owi1(s, E.WIwint_of_int ws)

let op_int_of_word (wk, s, ws) =
  match wk with
  | Word -> E.Oint_of_word (s, ws)
  | WInt -> E.Owi1(s, E.WIint_of_wint ws)

let cast loc e ety ty =
  match ety, ty with
  | P.ETint, P.ETword(s,ws) ->
    let op = op_word_of_int (wk_s_ws s ws) in
    P.Papp1(op, e)

  | P.ETword(s, ws), P.ETint ->
    (* FIXME do we really want to keep this cast word -> int implicit?
       Since we can use to_uint or to_sint ... *)
    let op = op_int_of_word (wk_s_ws s ws) in
    P.Papp1(op, e)

  | P.ETword(None, w1), P.ETword(None, w2) when W.wsize_cmp w1 w2 <> Datatypes.Lt -> e
  | P.ETword(Some W.Unsigned, w1),  P.ETword(Some W.Unsigned, w2) when W.wsize_cmp w1 w2 <> Datatypes.Lt -> e

  | _, _ when P.epty_equal ety ty -> e
  | P.ETarr _, P.ETarr _ -> e (* we delay typechecking until we know the lengths *)
  | _  ->  rs_tyerror ~loc (InvalidCast(ety,ty))

(*
let cast_word loc ws e ety =
  match ety with
  | P.Bty P.Int   -> P.Papp1 (E.Oword_of_int ws, e), ws
  | P.Bty (P.U ws1) -> e, ws1
  | _             ->  rs_tyerror ~loc (InvalidCast(ety,P.Bty (P.U ws)))
*)

let cast_int loc os e ety =
  match ety with
  | P.ETint -> e
  | P.ETword (s, ws) ->
    let wk, s, ws = wk_s_ws s ws in
    let s =
      match wk, os with
      | _, None ->
       if wk = Word then
          Utils.warning Deprecated (L.i_loc0 loc)
            "Syntax (int)e when e has type %a is deprecated. Use (uint)e of (sint)e instead"
            (fun fmt -> PrintCommon.pp_btype fmt) (P.U ws);
        s
      | Word, Some s -> tt_sign s
      | WInt, Some s' ->
        (* FIXME: Should we do a better error message ? *)
        if tt_sign s' <> s then rs_tyerror ~loc (InvalidCast(ety,P.etint));
        s
    in
    let op = op_int_of_word(wk, s, ws) in
    P.Papp1(op, e)
  | _ -> rs_tyerror ~loc (InvalidCast(ety,P.etint))


(* -------------------------------------------------------------------- *)
let conv_ty : BinNums.positive T.extended_type -> P.epty = function
    | T.ETbool       -> P.etbool
    | T.ETint        -> P.etint
    | T.ETword(s,ws) -> P.ETword(s,ws)
    | T.ETarr p      -> P.ETarr (U8, PE (P.icnst (Conv.int_of_pos p)))

let conv_cty : T.stype -> P.epty = function
    | T.Coq_sbool    -> P.etbool
    | T.Coq_sint     -> P.etint
    | T.Coq_sword ws -> P.etw ws
    | T.Coq_sarr p   -> P.ETarr (U8, PE (P.icnst (Conv.int_of_pos p)))

let type_of_op2 op =
  let (ty1, ty2), tyo = E.etype_of_op2 op in
  conv_ty ty1, conv_ty ty2, conv_ty tyo

let tt_op2 (loc1, (e1, ety1)) (loc2, (e2, ety2))
           { L.pl_desc = pop; L.pl_loc = loc } =

  match pop with
  | `Eq None when ety1 = P.etbool && ety2 = P.etbool ->
     P.Papp2(E.Obeq, e1, e2), P.etbool
  | `Neq None when ety1 = P.etbool && ety1 = P.etbool ->
    P.Papp1 (E.Onot, P.Papp2(E.Obeq, e1, e2)), P.etbool
  | _ ->
    let exn = tyerror ~loc (NoOperator (`Op2 pop, [ety1; ety2])) in
    let ty =
      match pop with
      | `And   | `Or    -> P.etbool
      | `ShR _ | `ShL _ | `ROR _ | `ROL _ -> ety1
      | `Add _ | `Sub _ | `Mul _ | `Div _ | `Mod _
        | `BAnd _ | `BOr _ | `BXOr _
        | `Eq _ | `Neq _ | `Lt _ | `Le _ | `Gt _ | `Ge _ ->
        max_ty ety1 ety2 |> oget ~exn in
    let op = op2_of_pop2 exn ty pop in
    let ty1, ty2, tyo = type_of_op2 op in
    let e1 = cast loc1 e1 ety1 ty1 in
    let e2 = cast loc2 e2 ety2 ty2 in
    P.Papp2(op, e1, e2), tyo

let type_of_op1 op =
  let ty, tyo = E.etype_of_op1 op in
  conv_ty ty, conv_ty tyo

let tt_op1 (loc1, (e1, ety1)) { L.pl_desc = pop; L.pl_loc = loc } =
  let exn = tyerror ~loc (NoOperator (`Op1 pop, [ety1])) in
  let ty = ety1 in
  let op = op1_of_pop1 exn ty pop in
  let ty1, tyo = type_of_op1 op in
  let e1 = cast loc1 e1 ety1 ty1 in
  P.Papp1(op, e1), tyo

(* -------------------------------------------------------------------- *)
let wsize_of_bits ~loc =
  function
  | 8 -> W.U8
  | 16 -> W.U16
  | 32 -> W.U32
  | 64 -> W.U64
  | 128 -> W.U128
  | 256 -> W.U256
  | n -> rs_tyerror ~loc (PackWrongWS n)

let pelem_of_bits ~loc =
  function
  | 1 -> W.PE1
  | 2 -> W.PE2
  | 4 -> W.PE4
  | 8 -> W.PE8
  | 16 -> W.PE16
  | 32 -> W.PE32
  | 64 -> W.PE64
  | 128 -> W.PE128
  | n -> rs_tyerror ~loc (PackWrongPE n)

(* Returns the size of the output word, the size of the elements,
   and the length of the input list *)
let tt_pack ~loc nb es =
  let n1 = S.int_of_vsize nb in
  let n2 = S.bits_of_vesize es in
  wsize_of_bits ~loc (n1 * n2), pelem_of_bits ~loc n2, n1

(* -------------------------------------------------------------------- *)
let combine_flags =
  List.map (fun c -> Printer.string_of_combine_flags c, c)
    [E.CF_LT Signed; E.CF_LT Unsigned;
     E.CF_LE Signed; E.CF_LE Unsigned;
     E.CF_EQ; E.CF_NEQ;
     E.CF_GE Signed; E.CF_GE Unsigned;
     E.CF_GT Signed; E.CF_GT Unsigned]

let is_combine_flags id =
  List.mem_assoc (L.unloc id) combine_flags

(* -------------------------------------------------------------------- *)
let tt_al aa =
  let open Memory_model in
  function
  | None -> (match aa with Warray_.AAdirect -> Unaligned | AAscale -> Aligned)
  | Some `Unaligned -> Unaligned
  | Some `Aligned -> Aligned

let ignore_align ~loc =
  function
  | None -> ()
  | Some _al ->
     warning Always (L.i_loc0 loc) "ignored alignment annotation in array slice"


(* -------------------------------------------------------------------- *)

let tt_mem_wsize dfl (ct : S.swsize L.located option) =
  match ct with
  | None -> dfl
  | Some ct ->
      match L.unloc ct with
      | (_, `WInt _) as a->
        rs_tyerror ~loc:(L.loc ct)
          (StringError ("invalid cast annotation "^(S.string_of_swsize_ty a)))
      | (ws, `Word _) -> ws

(* Precondition e : P.etw ws *)
(*
let wint_of_word ws (cast : W.signedness option) e =
  match cast with
  | None -> e, P.etw ws
  | Some s ->
    let e = P.Papp1 (E.EO.Owint_of_word(s, ws), e) in
    e, P.etwi s ws
*)
(*
let word_of_wint wint_of_word ws (cast : W.signedness option) e =
  match cast with
  | None -> e, P.etw ws
  | Some s ->
    let e = P.Papp1 (E.EO.Owint_of_word(s, ws), e) in
    e, P.etwi s ws
*)

(* -------------------------------------------------------------------- *)
let rec tt_expr pd ?(mode=`AllVar) (env : 'asm Env.env) pe =
  match L.unloc pe with
  | S.PEParens pe ->
    tt_expr ~mode pd env pe

  | S.PEBool b ->
    P.Pbool b, P.etbool

  | S.PEInt i ->
    P.Pconst (S.parse_int i), P.etint

  | S.PEVar x ->
    let x, ty = tt_var_global mode env x in
    P.Pvar x, ty

  | S.PEFetch me ->
    let ct, x, e, al = tt_mem_access ~mode pd env me in
    P.Pload (al, ct, x, e), P.etw ct

  | S.PEGet (al, aa, ws, ({ L.pl_loc = xlc } as x), pi, olen) ->
    let x, ty = tt_var_global mode env x in
    let ty, _ = tt_as_array (xlc, ty) in
    let ws = tt_mem_wsize (P.ws_of_ety ty) ws in
    let ty = P.etw ws in
    let i,ity  = tt_expr ~mode pd env pi in
    let i = cast_int (L.loc pi) (Some `Unsigned) i ity in
    begin match olen with
    | None ->
       let al = tt_al aa al in
       P.Pget (al, aa, ws, x, i), ty
    | Some plen ->
       ignore_align ~loc:(L.loc pe) al;
      let len,ity  = tt_expr ~mode:`OnlyParam pd env plen in
      check_ty_eq ~loc:(L.loc plen) ~from:ity ~to_:P.etint;
      let ty = P.ETarr (ws, P.PE len) in
      P.Psub (aa, ws, P.PE len, x, i), ty
    end

  | S.PEOp1 (op, pe) ->
    let e, ety = tt_expr ~mode pd env pe in

    begin match op with
    | `Cast (`ToInt s) ->
      let e = cast_int (L.loc pe) s e ety in
      e, P.etint

    | `Cast (`ToWord (sz, sg)) ->
       let rty = tt_swsize (sz, sg) in
       (* ensures that the word_kind is the expected *)
       let s, e, ety =
         match sg, ety with
         | `Word s, P.ETword(None, _) ->
            Option.default W.Unsigned (tt_osign s), e, ety
         | `Word s, P.ETword(Some s', ws) ->
            Option.default W.Unsigned (tt_osign s), Papp1(E.Owi1(s', E.WIword_of_wint ws), e), P.etw ws
         | `Word s, P.ETint ->
            Option.default W.Unsigned (tt_osign s), Papp1(E.Oword_of_int sz, e), P.etw sz
         | `WInt s, P.ETword(None, ws) ->
            let s = tt_sign s in
            s, Papp1(E.Owi1 (s, E.WIwint_of_word ws), e), P.etwi s ws
         | `WInt s, P.ETword (Some s', ws) ->
            let s = tt_sign s in
            if s = s' then s, e, ety
            else
              let we = P.Papp1(E.Owi1(s', E.WIword_of_wint ws), e) in
              let wie = P.Papp1(E.Owi1(s, E.WIwint_of_word ws), we) in
              s, wie, P.etwi s ws
         | `WInt s, P.ETint ->
             let s = tt_sign s in
             s, Papp1(E.Owi1(s, E.WIwint_of_int sz), e), P.etwi s sz
         | _ -> rs_tyerror ~loc:(L.loc pe) (InvalidCast(ety,rty))
       in
       (* ensures that the size is the expected *)
       let e =
         match ety with
         | P.ETword(None, ws) when W.wsize_cmp ws sz = Datatypes.Lt ->
           let op = if s = W.Unsigned then E.Ozeroext(sz, ws) else E.Osignext(sz, ws) in
           P.Papp1(op, e)
         | P.ETword(Some W.Unsigned, ws) when W.wsize_cmp ws sz = Datatypes.Lt ->
           P.Papp1(E.Owi1(s, E.WIwint_ext(sz, ws)), e)
         | P.ETword(Some W.Signed, ws) ->
           P.Papp1(E.Owi1(s, E.WIwint_ext(sz, ws)), e)
         | _ -> e
       in
       e, rty
    | _  ->
      let et1 = tt_expr ~mode pd env pe in
      tt_op1 (L.loc pe, et1) (L.mk_loc (L.loc pe) op)
    end

  | S.PEOp2 (pop, (pe1, pe2)) ->
    let et1 = tt_expr ~mode pd env pe1 in
    let et2 = tt_expr ~mode pd env pe2 in
    tt_op2 (L.loc pe1, et1) (L.loc pe2, et2) (L.mk_loc (L.loc pe) pop)

  | S.PECombF(id, args) ->
    begin match List.assoc (L.unloc id) combine_flags with
    | c ->
      let nexp = List.length Expr.tin_combine_flags in
      let nargs = List.length args in
      if nargs <> nexp then
        rs_tyerror ~loc:(L.loc pe) (InvalidArgCount(nargs, nexp));
      let tt_expr pe =
        let e, ety = tt_expr ~mode pd env pe in
        check_ty_eq ~loc:(L.loc pe) ~from:ety ~to_:P.etbool;
        e in
      let args = List.map tt_expr args in
      P.PappN (E.Ocombine_flags c, args), P.etbool
    | exception Not_found -> assert false
    end

  | S.PECall (id, args) when is_combine_flags id ->
    tt_expr ~mode pd env (L.mk_loc (L.loc pe) (S.PECombF(id,args)))

  | S.PECall _ ->
    rs_tyerror ~loc:(L.loc pe) CallNotAllowed

  | S.PEPrim _ ->
    rs_tyerror ~loc:(L.loc pe) PrimNotAllowed

  | S.PEpack ((nb, sg, es), args) ->
    let loc = L.loc pe in
    if sg <> `Unsigned then rs_tyerror ~loc PackSigned;
    let sz, pz, len = tt_pack ~loc nb es in
    let args = List.map (tt_expr ~mode pd env) args in
    let args = List.map (fun (a, ty) -> cast_int loc (Some sg) a ty) args in
    let alen = List.length args in
    if alen <> len then rs_tyerror ~loc (PackWrongLength (len, alen));
    P.PappN (E.Opack (sz, pz), args), P.etw sz

  | S.PEIf (pe1, pe2, pe3) ->
    let e1, ty1 = tt_expr ~mode pd env pe1 in
    let e2, ty2 = tt_expr ~mode pd env pe2 in
    let e3, ty3 = tt_expr ~mode pd env pe3 in

    check_ty_bool ~loc:(L.loc pe1) ty1;
    let ty = max_ty ty2 ty3 |> oget ~exn:(tyerror ~loc:(L.loc pe) (TypeMismatch (ty2, ty3))) in
    P.Pif(P.gty_of_gety ty, e1, e2, e3), ty

and tt_expr_cast pd ?(mode=`AllVar) (env : 'asm Env.env) pe ty =
  let e, ety = tt_expr ~mode pd env pe in
  cast (L.loc pe) e ety ty

and tt_mem_access pd ?(mode=`AllVar) (env : 'asm Env.env)
           (al, ct, ({ L.pl_loc = xlc } as x), e) =
  let x, ty = tt_var `NoParam env x in
  check_ty_ptr pd ~loc:xlc ty;
  let e =
    match e with
    | None -> P.Papp1 (op_word_of_int (Word, W.Unsigned, pd), P.Pconst (Z.zero))
    | Some(k, e) ->
      let e = tt_expr_cast ~mode pd env e (P.etw pd) in
      match k with
      | `Add -> e
      | `Sub -> Papp1(E.Oneg (E.Op_w pd), e) in
  let ct = tt_mem_wsize pd ct in
  let al = tt_al AAdirect al in
  (ct, L.mk_loc xlc x, e, al)

(* -------------------------------------------------------------------- *)
and tt_type pd (env : 'asm Env.env) (pty : S.ptype) : P.epty =
  match L.unloc pty with
  | S.TBool     -> P.etbool
  | S.TInt      -> P.etint
  | S.TWord  ws -> tt_swsize ws
  | S.TArray (ws, e) ->
     let loc, id, ety =
       match ws with
       | TypeWsize ws -> L.loc pty, None, tt_swsize ws
       | TypeSizeAlias id ->
          let ty = Env.TypeAlias.get env id in
          L.loc id, Some (L.mk_loc (L.loc ty) (L.unloc id)), L.unloc ty in
     let ws =
       match ety with
       | P.ETword(None, ws) -> ws (* wint array are not allowed this is require by wint_int *)
       | ty -> rs_tyerror ~loc (InvalidTypeAlias (id,ty))
     in P.ETarr (ws, P.PE (fst (tt_expr ~mode:`OnlyParam pd env e)))
  | S.TAlias id -> L.unloc (Env.TypeAlias.get env id)

(* -------------------------------------------------------------------- *)
let tt_exprs pd (env : 'asm Env.env) es = List.map (tt_expr ~mode:`AllVar pd env) es

(* -------------------------------------------------------------------- *)
let tt_expr_bool pd env pe = tt_expr_cast pd env pe P.etbool
let tt_expr_int  pd env pe = tt_expr_cast pd env pe P.etint

(* -------------------------------------------------------------------- *)

let mk_var x sto xety xlc annot =
  let annot =
    match xety with
    | P.ETword(Some s, ws) ->
      let s = if s = W.Signed then Annotations.sint else Annotations.uint in
      Annotations.add_symbol ~loc:xlc s annot
    | _ -> annot
  in
  P.PV.mk x sto (P.gty_of_gety xety) xlc annot

let tt_vardecl dfl_writable pd (env : 'asm Env.env) ((annot, (sto, xty)), x) =
  let { L.pl_desc = x; L.pl_loc = xlc; } = x in
  let regkind = tt_reg_kind annot in
  let (sto, xety) = (tt_sto regkind (dfl_writable x) sto, tt_type pd env xty) in
  let x = mk_var x sto xety xlc annot in
  if P.is_ptr sto && not (P.is_ty_arr x.v_ty) then
    rs_tyerror ~loc:xlc PtrOnlyForArray;
  L.mk_loc xlc (x, xety)

(* -------------------------------------------------------------------- *)
let tt_vardecls_push dfl_writable pd (env : 'asm Env.env) pxs =
  let xs  = List.map (tt_vardecl dfl_writable pd env) pxs in
  let env =
    List.fold_left (fun env x -> Env.Vars.push_local env (L.unloc x)) env xs in
  (env, xs)

(* -------------------------------------------------------------------- *)
let tt_param pd (env : 'asm Env.env) _loc (pp : S.pparam) : 'asm Env.env =
  let ty = tt_type pd env pp.ppa_ty in
  let pe, ety = tt_expr ~mode:`OnlyParam pd env pp.S.ppa_init in

  check_ty_eq ~loc:(L.loc pp.ppa_init) ~from:ty ~to_:ety;

  let x = mk_var (L.unloc pp.ppa_name) W.Const ty (L.loc pp.ppa_name) [] in
  let env = Env.Vars.push_param env (x,ety, pe) in
  env


(* -------------------------------------------------------------------- *)
let tt_lvalue pd (env : 'asm Env.env) { L.pl_desc = pl; L.pl_loc = loc; } =

  let reject_constant_pointers loc x =
    match x.P.v_kind with
    | Stack (Pointer Constant) | Reg (_, Pointer Constant) ->
       warning PedanticPretyping (L.i_loc0 loc) "Cannot write to the constant pointer %s" x.P.v_name
    | _ -> ()
  in

  match pl with
  | S.PLIgnore ->
    loc, (fun ety -> P.Lnone(loc, P.gty_of_gety ety)) , None

  | S.PLVar x ->
    let x, xty = tt_var `NoParam env x in
    loc, (fun _ -> P.Lvar (L.mk_loc loc x)), Some xty

  | S.PLArray (al, aa, ws, ({ pl_loc = xlc } as x), pi, olen) ->
    let x, xty  = tt_var `NoParam env x in
    reject_constant_pointers xlc x ;
    let ty,_ = tt_as_array (xlc, xty) in
    let ws = tt_mem_wsize (P.ws_of_ety ty) ws in
    let ty = P.etw ws in
    let i,ity  = tt_expr ~mode:`AllVar pd env pi in
    let i = cast_int (L.loc pi) (Some `Unsigned) i ity in
    begin match olen with
    | None ->
      let al = tt_al aa al in
      loc, (fun _ -> P.Laset (al, aa, ws, L.mk_loc xlc x, i)), Some ty
    | Some plen ->
      ignore_align ~loc al;
      let len,ity  = tt_expr ~mode:`OnlyParam pd env plen in
      check_ty_eq ~loc:(L.loc plen) ~from:ity ~to_:P.etint;
      let ty = P.ETarr(ws, P.PE len) in
      loc, (fun _ -> P.Lasub (aa, ws, P.PE len, L.mk_loc xlc x, i)), Some ty
    end

  | S.PLMem me ->
    let ct, x, e, al = tt_mem_access ~mode:`AllVar pd env me in
    loc, (fun _ -> P.Lmem (al, ct, x, e)), Some (P.etw ct)

(* -------------------------------------------------------------------- *)

let prim_sig asmOp p : 'a P.gety list * 'a P.gety list * Sopn.arg_desc list =
  let f t = conv_cty t in
  let o = Sopn.asm_op_instr asmOp p in
  List.map f o.tout,
  List.map f o.tin,
  o.i_out

let extract_size str : string * Sopn.prim_x86_suffix option =
  let get_size =
    let open Sopn in
    function
    | "8"   -> PVp W.U8
    | "16"  -> PVp W.U16
    | "32"  -> PVp W.U32
    | "64"  -> PVp W.U64
    | "128" -> PVp W.U128
    | "256" -> PVp W.U256

    | "u8"   -> PVs (Unsigned, W.U8)
    | "u16"  -> PVs (Unsigned, W.U16)
    | "u32"  -> PVs (Unsigned, W.U32)
    | "u64"  -> PVs (Unsigned, W.U64)
    | "u128" -> PVs (Unsigned, W.U128)
    | "u256" -> PVs (Unsigned, W.U256)

    | "s8"   -> PVs (Signed, W.U8)
    | "s16"  -> PVs (Signed, W.U16)
    | "s32"  -> PVs (Signed, W.U32)
    | "s64"  -> PVs (Signed, W.U64)
    | "s128" -> PVs (Signed, W.U128)
    | "s256" -> PVs (Signed, W.U256)

    | "2u8"   -> PVsv (W.Unsigned, W.VE8,  W.U16)
    | "4u8"   -> PVsv (W.Unsigned, W.VE8,  W.U32)
    | "2u16"  -> PVsv (W.Unsigned, W.VE16, W.U32)
    | "8u8"   -> PVsv (W.Unsigned, W.VE8,  W.U64)
    | "4u16"  -> PVsv (W.Unsigned, W.VE16, W.U64)
    | "2u32"  -> PVsv (W.Unsigned, W.VE32, W.U64)
    | "16u8"  -> PVsv (W.Unsigned, W.VE8,  W.U128)
    | "8u16"  -> PVsv (W.Unsigned, W.VE16, W.U128)
    | "4u32"  -> PVsv (W.Unsigned, W.VE32, W.U128)
    | "2u64"  -> PVsv (W.Unsigned, W.VE64, W.U128)
    | "32u8"  -> PVsv (W.Unsigned, W.VE8,  W.U256)
    | "16u16" -> PVsv (W.Unsigned, W.VE16, W.U256)
    | "8u32"  -> PVsv (W.Unsigned, W.VE32, W.U256)
    | "4u64"  -> PVsv (W.Unsigned, W.VE64, W.U256)

    | "2s8"   -> PVsv (W.Signed, W.VE8,  W.U16)
    | "4s8"   -> PVsv (W.Signed, W.VE8,  W.U32)
    | "2s16"  -> PVsv (W.Signed, W.VE16, W.U32)
    | "8s8"   -> PVsv (W.Signed, W.VE8,  W.U64)
    | "4s16"  -> PVsv (W.Signed, W.VE16, W.U64)
    | "2s32"  -> PVsv (W.Signed, W.VE32, W.U64)
    | "16s8"  -> PVsv (W.Signed, W.VE8,  W.U128)
    | "8s16"  -> PVsv (W.Signed, W.VE16, W.U128)
    | "4s32"  -> PVsv (W.Signed, W.VE32, W.U128)
    | "2s64"  -> PVsv (W.Signed, W.VE64, W.U128)
    | "32s8"  -> PVsv (W.Signed, W.VE8,  W.U256)
    | "16s16" -> PVsv (W.Signed, W.VE16, W.U256)
    | "8s32"  -> PVsv (W.Signed, W.VE32, W.U256)
    | "4s64"  -> PVsv (W.Signed, W.VE64, W.U256)
    | s ->
      let wsize_of_int = function
        | 8   -> W.U8
        | 16  -> W.U16
        | 32  -> W.U32
        | 64  -> W.U64
        | 128 -> W.U128
        | 256 -> W.U256
        | _   -> raise Not_found in
      try
        Scanf.sscanf s "%c%u%c%u%!"
          (fun c0 i c1 j ->
            if not ((c0 = 'u' || c0 = 's') && (c1 = 'u' || c1 = 's')) then raise Not_found;
            PVx(wsize_of_int i, wsize_of_int j))
      with End_of_file | Scanf.Scan_failure _ -> raise Not_found
  in
  try
  match List.rev (String.split_on_char '_' str) with
  | [] -> str, None
  | suf2 :: ((suf1 :: s) as tail) ->
     let sz = get_size suf2 in
     begin try match get_size suf1, sz with
     | PVsv (_, ve1, sz1), PVsv (_, ve2, sz2) -> String.concat "_" (List.rev s), Some (PVvv (ve1, sz1, ve2, sz2))
     | _, _ -> String.concat "_" (List.rev tail), Some sz
     with Not_found -> String.concat "_" (List.rev tail), Some sz
     end
  | suf :: s ->
     let sz = get_size suf in
     String.concat "_" (List.rev s), Some sz
  with Not_found -> str, None

let simplify_suffix ~loc =
  let open Sopn in
  let open PrintCommon in
  function
  | PVsv (_sg, ve, sz) -> Some (PVv (ve, sz), fun x -> x)
  | PVv (ve, sz) -> Some (PVp sz, fun () ->
      warning SimplifyVectorSuffix (L.i_loc0 loc) "vector suffix simplified from %s to %a"
        (string_of_velem Unsigned sz ve) pp_wsize sz)
  | _ -> None

let default_suffix =
  function
  | x :: _ -> x
  | [] -> Sopn.PVp U8

(**
Deprecated intrinsic operators map (old name -> new name)
*)
let deprecated_intrinsic = 
  let m = Ms.empty in 
  let m = Ms.add "VPBLENDVB" "BLENDV" m in
  Ms.add "VPMOVMSKB" "MOVEMASK" m

(**
  Check if intrinsic opperator is deprecated and emit a warning if so.
*)
let check_deprecated_intrinsic (old_name: string) (loc:L.t) =
  match Ms.find_opt old_name deprecated_intrinsic with
  | None -> ()
  | Some new_name ->
    warning Deprecated (L.i_loc0 loc) "Intrinsic operator '%s' is deprecated. Please use '%s' instead." old_name new_name


let tt_prim asmOp id = 
  let { L.pl_loc = loc ; L.pl_desc = s } = id in
  let name, sz = extract_size s in
  check_deprecated_intrinsic name loc;
  let c =
    match List.assoc name asmOp.Sopn.prim_string with
    | PrimX86 (valid_suffixes, preop) ->
      begin match match sz with
          | None -> default_suffix valid_suffixes |> preop
       | Some sfx ->
              let rec loop sfx =
                if List.mem sfx valid_suffixes then preop sfx else
                  begin match simplify_suffix ~loc sfx with
              | Some (sfx, w) -> w (); loop sfx
              | None -> None end
              in loop sfx
        with | Some d -> d
            | None -> rs_tyerror ~loc (PrimWrongSuffix (name, valid_suffixes))
    end
    | PrimARM _ | exception Not_found ->
       let err msg = tyerror ~loc (UnknownPrim(s, msg)) in
       Tt_arm_m4.tt_prim err asmOp.Sopn.prim_string name sz
  in c

let prim_of_op exn loc o =
  (* TODO: use context typing information when the operator is not annotated *)
  let bits_of_swsize : S.castop -> int option =
    function
    | None -> None
    | Some({L.pl_desc = S.CVS _} ) -> raise exn
    | Some({L.pl_desc = S.CSS(sz, `WInt _)}) -> raise exn
    | Some({L.pl_desc = S.CSS(sz, _)}) ->
      Some (Annotations.int_of_ws sz)
  in
  let p =
    let f s n =
      match bits_of_swsize s with
      | None -> n
      | Some b -> F.sprintf "%s_%d" n b
    in
    match o with
    | `Add s -> f s "adc"
    | `Sub s -> f s "sbb"
    | `Mul s -> f s "mulu"
    | _    -> raise exn in
  L.mk_loc loc p

(*  x + y     -> addc x y false
    x + y + c -> addc x y c
    x - y     -> subb x y false
    x - y - c -> subb x y c
    x * y     -> umul *)

let prim_of_pe pe =
  let loc = L.loc pe in
  let exn = tyerror ~loc (Unsupported "can not recognize the primitive") in
  match L.unloc pe with
  | S.PEOp2 (o, (pe1, pe2)) ->
    let desc =
      match o with
      | (`Add _ | `Sub _) as o1 ->
        let check_size op s1 s2 =
          match s1, s2 with
          | None, _ -> Some (op s2)
          | _, None -> Some (op s1)
          | Some s1', Some s2' when s1' = s2' -> Some (op s1)
          | _ -> None in
        let check_op o1 o2 =
          match o1, o2 with
          | `Add s1, `Add s2 -> check_size (fun x -> `Add x) s1 s2
          | `Sub s1, `Sub s2 -> check_size (fun x -> `Sub x) s1 s2
          | _                -> None in

        let o, pe1, pe2, pe3 =
          match L.unloc pe1, L.unloc pe2 with
          | S.PEOp2(o2, (pe1', pe3')), _ ->
            begin match check_op o1 o2 with
            | None -> o, pe1, pe2, L.mk_loc (L.loc pe2) (S.PEBool false)
            | Some o -> o, pe1', pe3', pe2
            end
          | _, S.PEOp2(o2, (pe2', pe3')) ->
            begin match check_op o1 o2 with
            | None -> o, pe1, pe2, L.mk_loc (L.loc pe2) (S.PEBool false)
            | Some o -> o, pe1, pe2', pe3'
            end
          | _, _ -> o, pe1, pe2, L.mk_loc (L.loc pe2) (S.PEBool false)
        in

        S.PEPrim(prim_of_op exn loc o, [pe1; pe2; pe3])

      | _  ->
        S.PEPrim(prim_of_op exn loc o, [pe1; pe2])
    in
    L.mk_loc (L.loc pe) desc
  | _ -> raise exn

let cast_opn ~loc id ws =
  let open Sopn in
  let name fmt = Format.pp_print_string fmt (id.str ()) in
  let invalid () = rs_tyerror ~loc (UnsupportedZeroExtend name) in
  let open Arch_extra in
  function
  | Oasm (BaseOp (None, op)) ->
    begin match List.last id.tout with
      | Coq_sword from ->
          if wsize_le ws from then rs_tyerror ~loc(InvalidZeroExtend (from, ws, name))
          else Oasm (BaseOp (Some ws, op))
      | _ -> invalid ()
  end
  | Oasm (BaseOp (Some _, _)) -> assert false
  | _ -> invalid ()

(* -------------------------------------------------------------------- *)
let pexpr_of_plvalue exn l =
  match L.unloc l with
  | S.PLIgnore      -> raise exn
  | S.PLVar  x      -> L.mk_loc (L.loc l) (S.PEVar x)
  | S.PLArray(al, aa,ws,x,e,len) -> L.mk_loc (L.loc l) (S.PEGet(al, aa,ws,x,e,len))
  | S.PLMem(ty,x,e,al) -> L.mk_loc (L.loc l) (S.PEFetch(ty,x,e,al))


type ('a, 'b, 'c, 'd, 'e, 'f, 'g) arch_info = {
  pd : Wsize.wsize;
  asmOp : ('a, 'b, 'c, 'd, 'e, 'f, 'g) Arch_extra.extended_op Sopn.sopn Sopn.asmOp;
  known_implicits : (CoreIdent.Name.t * string) list;
  flagnames: CoreIdent.Name.t list;
}

let tt_lvalues arch_info env loc (pimp, pls) implicit tys =
  let loc = loc_of_tuples loc (List.map P.L.loc pls) in
  let ignore_ = L.mk_loc loc S.PLIgnore in


  let extend_pls n =
     let nargs = List.length pls in
     if nargs < n then
       let nextra = n - nargs in
       warning IntroduceNone (L.i_loc0 loc) "introduce %d _ lvalues" nextra;
       List.make nextra ignore_ @ pls
     else pls in

  let combines =
        [ "<s" , E.CF_LT Wsize.Signed
        ; "<u" , E.CF_LT Wsize.Unsigned
        ; "<=s", E.CF_LE Wsize.Signed
        ; "<=u", E.CF_LE Wsize.Unsigned
        ; "==" , E.CF_EQ
        ; "!=" , E.CF_NEQ
        ; ">=s", E.CF_GE Wsize.Signed
        ; ">=u", E.CF_GE Wsize.Unsigned
        ; ">s" , E.CF_GT Wsize.Signed
        ; ">u" , E.CF_GT Wsize.Unsigned ] in

  let pls, pimp_c, implicits =
    match pimp, implicit with
    | None, _ -> extend_pls (List.length tys), [], []
    | Some pimp, None -> rs_tyerror ~loc:(L.loc pimp) (string_error "no implicit argument expected");
    | Some pimp, Some implicit ->
      let pimp = L.unloc pimp in
      let nb_explicit =
        let open Sopn in
        List.count_matching (function ADExplicit _ -> true | _ -> false) implicit in
      let pls = extend_pls nb_explicit in
      let arguments =
        (* FIXME this is not generic *)
        let open Sopn in
        List.map
          (function
           | ADExplicit _ -> None
           | ADImplicit v -> Some (Var0.Var.vname v).v_name)
          implicit in

      let iargs = List.pmap (Option.map String.uppercase_ascii) arguments in

      let check (id, _) =
        let loc = L.loc id in
        let nid = L.unloc id in
        let nID = String.uppercase_ascii nid in
        if not (List.mem nID iargs || List.mem_assoc nid combines) then
          rs_tyerror ~loc (string_error "unknown implicit label %s" nid) in
      List.iter check pimp;
      let pimp_c, pimp_f = List.partition (fun (id,_) -> List.mem_assoc (L.unloc id) combines) pimp in

      let implicits = ref [] in
      let get_implicit i =
        let error loc =
          rs_tyerror ~loc (string_error "an ident is expected (default is %s)" i) in
        let mk loc s =
          let s = L.mk_loc loc s in
          implicits := (i, L.mk_loc loc (S.PEVar s)) :: !implicits;
          L.mk_loc loc (S.PLVar s) in
        let a =
          Annot.ensure_uniq1 ~case_sensitive:false i (Annot.on_attribute ~on_empty:(fun loc nid () -> mk loc nid)
                                                   ~on_id:(fun loc _nid s -> mk loc s)
                                                   error) pimp_f in
        match a with
        | None ->
          (try mk loc (List.assoc i (Env.get_known_implicits env))
           with Not_found -> L.mk_loc loc (S.PLIgnore))
        | Some a -> a in

      let rec aux arguments pls =
        match arguments, pls with
        | [], _                      -> pls
        | None :: arguments, x :: pls -> x :: aux arguments pls
        | None :: _, []              -> assert false
        | Some i :: arguments, pls    -> get_implicit i :: aux arguments pls in
      let a = aux arguments pls in
      a, pimp_c, !implicits
  in

  let ls = List.map (tt_lvalue arch_info.pd env) pls in
  let ls = check_sig_lvs loc tys ls in
  let li =
    match pimp_c with
    | [] -> []
    | (id, _) :: _ ->
      let loc = L.loc id in
      let get_implicit i =
        try List.assoc i implicits
        with Not_found ->
          rs_tyerror ~loc (string_error "implicit label %s need to be defined" i) in
      let pargs = List.map get_implicit arch_info.flagnames in
      let args = List.map (tt_expr_bool arch_info.pd env) pargs in
      let doc (c, s) =
        let error loc = rs_tyerror ~loc (string_error " = ident is expected after %s" (L.unloc c)) in
        let a =
         Annot.on_attribute
            ~on_id:(fun loc _nid s -> L.mk_loc loc (S.PLVar (L.mk_loc loc s)))
            error (c,s) in
        let _, flv, vty = tt_lvalue arch_info.pd env a in
        let e, ety = P.PappN (E.Ocombine_flags (List.assoc (L.unloc c) combines), args), P.etbool in
        let e = vty |> Option.map_default (cast (L.loc a) e ety) e in
        let ety =
          match vty with
          | None -> ety
          | Some vty -> vty
        in
        let x = flv ety in
        let tg = E.AT_inline in
        P.{ i_desc = Cassgn (x, tg, P.tbool, e);
            i_loc = L.of_loc c;
            i_info = ();
            i_annot = [] } in
      List.map doc pimp_c in
  ls, li



let tt_exprs_cast pd env loc les tys =
  let loc () = loc_of_tuples loc (List.map L.loc les) in
  let n1 = List.length les in
  let n2 = List.length tys in
  if n1 <> n2 then
    rs_tyerror ~loc:(loc ()) (InvalidArgCount (n1, n2));
  List.map2 (fun le ty ->
    let e, ety = tt_expr ~mode:`AllVar pd env le in
    cast (L.loc le) e ety ty) les tys

let arr_init (xi, ty) =
  let open P in
  match ty with
  | P.ETarr(ws, PE e) as ty ->
    let size = PE (icnst (size_of_ws ws) ** e) in
    Cassgn (Lvar xi, E.AT_inline, P.gty_of_gety ty, P.Parr_init size)
  | _           ->
    rs_tyerror ~loc:(L.loc xi) (InvalidArrayType ty)

let cassgn_for (x: P.plval) (tg: E.assgn_tag) (ty: P.epty) (e: P.pexpr) :
  (unit, 'asm) P.pinstr_r =
  Cassgn (x, tg, P.gty_of_gety ty, e)

let mk_call loc inline lvs f es =
  let open P in
  begin match f.f_cc with
  | Internal -> ()
  | Export _ ->
    if not inline then
      warning Always (L.i_loc0 loc) "export function will be inlined"
  | Subroutine _ when not inline ->
    let check_lval = function
      | Lnone _ | Lvar _ | Lasub _ -> ()
      | Lmem _ | Laset _ -> rs_tyerror ~loc (string_error "memory/array assignment are not allowed here") in
    let rec check_e = function
      | Pvar _ | Psub _ -> ()
      | Pif (_, _, e1, e2) -> check_e e1; check_e e2
      | _ -> warning PedanticPretyping (L.i_loc0 loc)  "only variables and subarray are allowed in arguments of non-inlined function" in
    List.iter check_lval lvs;
    List.iter check_e es
  | Subroutine _ -> ()
  end;

  (* Check writability *)
  let check_ptr_writable x =
     match x.v_kind with
     | Stack (Pointer Writable) | Reg (_, Pointer Writable) -> true
     | _ -> false in
  let check_w x e =
    if check_ptr_writable x then
      let rec aux  = function
        | Pvar y | Psub(_, _, _, y, _) ->
          let y = L.unloc y.gv in
          if not (check_ptr_writable y || y.v_kind = Stack Direct) then
            rs_tyerror ~loc (string_error "argument %a needs to be writable" Printer.pp_pvar y)
        | Pif (_, _, e1, e2) -> aux e1; aux e2
        | _ -> assert false in
      aux e in
  List.iter2 check_w f.f_args es;

  P.Ccall (lvs, f.P.f_name, es)

let assign_from_decl (decl: S.vardecl L.located) =
  let v, e = L.unloc decl in
  Option.map (fun e ->
      let d = L.mk_loc (L.loc decl) (S.PLVar v) in
      (None, [d]), `Raw, e, None
    ) e

let tt_annot_paramdecls dfl_writable pd env (annot, (ty,vs)) =
  let aty = annot, ty in
  let vars = List.map (fun v -> aty, v) vs in
  tt_vardecls_push dfl_writable pd env vars

let rec tt_instr arch_info (env : 'asm Env.env) ((annot,pi) : S.pinstr) : 'asm Env.env * (unit, 'asm) P.pinstr list  =
  let mk_i ?(annot=annot) instr =
    { P.i_desc = instr; P.i_loc = L.of_loc pi; P.i_info = (); P.i_annot = annot} in
  let rec tt_assign env_lhs env_rhs ls eqop pe ocp =
    match ls, eqop, pe, ocp with
    | ls, `Raw, { L.pl_desc = S.PECall (f, args); pl_loc = el }, None when is_combine_flags f ->
      tt_assign env_lhs env_rhs ls `Raw (L.mk_loc el (S.PECombF(f, args))) None

    | ls, `Raw, { L.pl_desc = S.PECall (f, args); pl_loc = el }, None ->
      let (f,fsig) = tt_fun env_rhs f in
      let lvs, is = tt_lvalues arch_info env_lhs (L.loc pi) ls None fsig.fs_tout in
      assert (is = []);
      let es  = tt_exprs_cast arch_info.pd env_rhs (L.loc pi) args fsig.fs_tin in
      let is_inline = P.is_inline annot f.P.f_cc in
      let annot =
        if is_inline || FInfo.is_export f.P.f_cc
        then Annotations.add_symbol ~loc:el "inline" annot
        else annot
      in
      [mk_i ~annot (mk_call (L.loc pi) is_inline lvs f es)]
  | (ls, xs), `Raw, { pl_desc = PEPrim (f, args) }, None
        when L.unloc f = "spill" || L.unloc f = "unspill"  ->
    let op = L.unloc f in
    if ls <> None then rs_tyerror ~loc:(L.loc pi) (string_error "%s expects no implicit result" op);
    if xs <> [] then rs_tyerror ~loc:(L.loc pi) (string_error "%s expects no result" op);
    let es = tt_exprs arch_info.pd env_rhs args in
    let doit (e, _) =
      match e with
      | P.Pvar x when P.is_reg_kind (P.kind_i x.gv) -> e
      | _ ->  rs_tyerror ~loc:(L.loc pi) (string_error "%s expects only reg/reg ptr as arguments" op) in
    let es = List.map doit es in
    let op = if op = "spill" then Pseudo_operator.Spill else Pseudo_operator.Unspill in
    let p = Sopn.Opseudo_op (Ospill(op, [] (* dummy info, will be fixed latter *))) in
    [mk_i ~annot (P.Copn([], AT_keep, p, es))]

  | (ls, xs), `Raw, { pl_desc = PEPrim (f, args) }, None when L.unloc f = "randombytes" ->
      (* FIXME syscall *)
      (* This is dirty but ... *)
      if ls <> None then rs_tyerror ~loc:(L.loc pi) (string_error "randombytes expects no implicit arguments");
      let loc, x, ty =
        match xs with
        | [x] ->
          let loc, x, oty = tt_lvalue arch_info.pd env_lhs x in
          let ty =
            match oty with
            | None -> rs_tyerror ~loc (string_error "_ lvalue not accepted here")
            | Some ty -> ty in
          loc, x ty, ty
        | _ ->
          rs_tyerror ~loc:(L.loc pi)
            (string_error "only a single variable is allowed as destination of randombytes") in
      let _ = tt_as_array (loc, ty) in
      let es = tt_exprs_cast arch_info.pd env_rhs (L.loc pi) args [ty] in
      [mk_i (P.Csyscall([x], Syscall_t.RandomBytes (Conv.pos_of_int 1), es))]

  | (ls, xs), `Raw, { pl_desc = PEPrim (f, args) }, None when L.unloc f = "swap" ->
      if ls <> None then rs_tyerror ~loc:(L.loc pi) (string_error "swap expects no implicit arguments");
      let lvs, ty =
        match xs with
        | [x; y] ->
          let loc, x, oxty = tt_lvalue arch_info.pd env_lhs x in
          let yloc, y, _oytu = tt_lvalue arch_info.pd env_lhs y in
          let ty =
            match oxty with
            | None -> rs_tyerror ~loc (string_error "_ lvalue not accepted here")
            | Some ty -> ty in
          let _ =
             match oxty with
            | None -> rs_tyerror ~loc (string_error "_ lvalue not accepted here")
            | Some yty -> check_ty_eq ~loc:yloc ~from:yty ~to_:ty in
          [x ty; y ty], ty
        | _ ->
          rs_tyerror ~loc:(L.loc pi)
            (string_error "a pair of destination is expected for swap")
      in
      let () = match ty with
        | P.ETarr _ -> ()
        | P.ETword(None, ws) when ws <= U64 -> ()
        | _ ->
          let w = match ty with P.ETword(w, ws) -> w | _ -> None in
          let ty = match P.gty_of_gety ty with P.Bty ty -> ty | _ -> assert false in
            rs_tyerror ~loc:(L.loc pi)
              (string_error "the swap primitive is not available at type %a"
                 (PrintCommon.pp_btype ?w) ty)

      in
      let es = tt_exprs_cast arch_info.pd env_rhs (L.loc pi) args [ty; ty] in
      let p = Sopn.Opseudo_op (Oswap Type.Coq_sbool) in  (* The type is fixed latter *)
      [mk_i (P.Copn(lvs, AT_keep, p, es))]

  | ls, `Raw, { pl_desc = PEPrim (f, args) }, None ->
      let p = tt_prim arch_info.asmOp f in
      let tlvs, tes, arguments = prim_sig arch_info.asmOp p in
      let lvs, einstr = tt_lvalues arch_info env_lhs (L.loc pi) ls (Some arguments) tlvs in
      let es  = tt_exprs_cast arch_info.pd env_rhs (L.loc pi) args tes in
      mk_i (P.Copn(lvs, AT_keep, p, es)) :: einstr

  | ls, `Raw, { pl_desc = PEOp1 (`Cast(`ToWord ct), {pl_desc = PEPrim (f, args) }); pl_loc = loc} , None
      ->
      let ws =
        match ct with
        | (ws, `Word _) -> ws
        | (ws, `WInt _) -> rs_tyerror ~loc (string_error "invalid cast for asm operator")
        in
      let p = tt_prim arch_info.asmOp f in
      let id = Sopn.asm_op_instr arch_info.asmOp p in
      let p = cast_opn ~loc:(L.loc pi) id ws p in
      let tlvs, tes, arguments = prim_sig arch_info.asmOp p in
      let lvs, einstr = tt_lvalues arch_info env_lhs (L.loc pi) ls (Some arguments) tlvs in
      let es  = tt_exprs_cast arch_info.pd env_rhs (L.loc pi) args tes in
      mk_i (P.Copn(lvs, AT_keep, p, es)) :: einstr

  | (None,[lv]), `Raw, pe, None ->
      let _, flv, vty = tt_lvalue arch_info.pd env_lhs lv in
      let e, ety = tt_expr ~mode:`AllVar arch_info.pd env_rhs pe in
      let e = vty |> Option.map_default (cast (L.loc pe) e ety) e in
      let ety =
        match vty with
        | None -> ety
        | Some vty -> vty
      in
      let v = flv ety in
      let tg =
        P.(match v with
            | Lvar v -> (match kind_i v with Inline -> E.AT_inline | _ -> E.AT_none)
            | _ -> AT_none) in
      [mk_i (cassgn_for v tg ety e)]

  | ls, `Raw, pe, None ->
      (* Try to match addc, subc, mulu *)
      let pe = prim_of_pe pe in
      tt_assign env_lhs env_rhs ls `Raw pe None

  | (pimp,ls), eqop, pe, None ->
      let op = oget (peop2_of_eqop eqop) in
      let loc = L.loc pi in
      let exn = tyerror ~loc EqOpWithNoLValue in
      if List.is_empty ls then raise exn;
      let pe1 = pexpr_of_plvalue exn (List.last ls) in
      let pe  = L.mk_loc loc (S.PEOp2(op,(pe1,pe))) in
      tt_assign env_lhs env_rhs (pimp, ls) `Raw pe None

  | ls, eqop, e, Some cp ->
      let loc = L.loc pi in
      let exn = Unsupported "if not allowed here" in
      let i = tt_assign env_lhs env_rhs ls eqop e None in
      let x, ty, e, is =
        match i with
        | { i_desc = P.Cassgn (x, _, ty, e) ; _ } :: is -> x, ty, e, is
        | _ -> rs_tyerror ~loc exn in
      let e' = oget ~exn:(tyerror ~loc exn) (P.expr_of_lval x) in
      let c = tt_expr_bool arch_info.pd env_rhs cp in
      mk_i (P.Cassgn (x, AT_none, ty, Pif (ty, c, e, e'))) :: is
  in
  let tt_annot_decl env (vd: S.vardecl L.located) (aty: A.annotations * S.pstotype) =
    (* remember the environment prior to the declaration:
      it will be used to type-check the right-hand side initializing expression, if any *)
    let env_rhs = env in
    let var = tt_vardecl (fun _ -> true) arch_info.pd env (aty, S.var_decl_id (L.unloc vd)) in
    let env = Env.Vars.push_local env_rhs (L.unloc var) in
    match assign_from_decl vd with
    | None -> env, []
    | Some (ls, eq, op, ocp) -> env, tt_assign env env_rhs ls eq op ocp
  in

  match L.unloc pi with
  | S.PIdecl (ty,vds) ->
    List.fold (fun (env, acc) v ->
        let env, cmd = tt_annot_decl env v (annot, ty) in
        env, acc @ cmd)
      (env, [])
      vds

  | S.PIArrayInit ({ L.pl_loc = lc; } as x) ->
    let x, xty = tt_var `AllVar env x in
    let xi = (L.mk_loc lc x) in
    env, [mk_i (arr_init (xi, xty))]

  | S.PIAssign (ls, eqop, pe, ocp) -> env, tt_assign env env ls eqop pe ocp

  | PIIf (cp, st, sf) ->
      let c  = tt_expr_bool arch_info.pd env cp in
      let st = tt_block arch_info env st in
      let sf = Option.map_default (tt_block arch_info env) [] sf in
      env, [mk_i (P.Cif (c, st, sf))]

  | PIFor ({ pl_loc = lx } as x, (d, i1, i2), s) ->
      let i1   = tt_expr_int arch_info.pd env i1 in
      let i2   = tt_expr_int arch_info.pd env i2 in
      let vx, xty = tt_var `AllVar env x in
      check_ty_eq ~loc:lx ~from:xty ~to_:P.etint;
      let s    = tt_block arch_info env s in
      let d    = match d with `Down -> E.DownTo | `Up -> E.UpTo in
      env, [mk_i (P.Cfor (L.mk_loc lx vx, (d, i1, i2), s))]

  | PIWhile (s1, e, s2) ->
      let c  = tt_expr_bool arch_info.pd env e in
      let s1 = Option.map_default (tt_block arch_info env) [] s1 in
      let s2 = Option.map_default (tt_block arch_info env) [] s2 in
      let a =
        Option.map_default (fun () -> E.Align) E.NoAlign (Annot.ensure_uniq1 "align" Annot.none annot) in
      let annot = Annot.consume "align" annot in
      env, [mk_i ~annot (P.Cwhile (a, s1, c, ((L.of_loc e, []), ()), s2))]

(* -------------------------------------------------------------------- *)
and tt_block arch_info env (pb : S.pblock) =
  snd (tt_cmd arch_info env (L.unloc pb))

and tt_cmd arch_info env c =
  match c with
  | [] -> env, []
  | i::c ->
    let env, i = tt_instr arch_info env i in
    let env, c = tt_cmd arch_info env c in
    env, i @ c

(* -------------------------------------------------------------------- *)
let tt_funbody arch_info env (pb : S.pfunbody) =
  let env, bdy = tt_cmd arch_info env pb.S.pdb_instr in
  let ret_loc = L.loc pb.pdb_ret in
  let ret =
    let for1 x = L.mk_loc (L.loc x) (tt_var `AllVar env x) in
    List.map for1 (Option.default [] (L.unloc pb.pdb_ret)) in
  (bdy, ret_loc, ret)


(* -------------------------------------------------------------------- *)

let tt_call_conv _loc params returns cc =
  match cc with
  | Some `Inline -> FInfo.Internal

  | Some `Export | None ->
    let check s x =
      if not (P.is_reg_kind (L.unloc x).P.v_kind) then
        warning PedanticPretyping (L.i_loc0 (L.loc x))
          "%a has kind %a, only reg or reg ptr are allowed in %s of non inlined function"
            Printer.pp_pvar (L.unloc x)
            PrintCommon.pp_kind (L.unloc x).P.v_kind s in
    List.iter (check "parameter") params;
    List.iter (check "result") returns;
    let returned_params =
      let args = List.map L.unloc params in
      List.map (fun x ->
        let loc = L.loc x in
        let x = L.unloc x in
        match x.P.v_kind with
        | W.Reg(_, Direct) -> None
        | W.Reg(_, Pointer writable) ->
          if writable = Constant then
            warning Always (L.i_loc0 loc) "no need to return a [reg const ptr] %a"
              Printer.pp_pvar x;
          let i = List.index_of x args in
          if i = None then
            rs_tyerror ~loc (string_error "%a should be one of the paramaters"
                               Printer.pp_pvar x);
          i
        | _ -> assert false) returns in
    let is_writable_ptr k =
      match k with
      | W.Reg(_, Pointer Writable) -> true
      | _ -> false in
    let check_writable_param i x =
      let loc = L.loc x in
      let x = L.unloc x in
      if is_writable_ptr x.P.v_kind then
        if not (List.exists ((=) (Some i)) returned_params) then
          rs_tyerror ~loc (string_error "%a is mutable, it should be returned"
                             Printer.pp_pvar x) in
    List.iteri check_writable_param params;
    if cc = None then
      FInfo.Subroutine { returned_params }
    else
      FInfo.Export { returned_params }

(* -------------------------------------------------------------------- *)

let process_f_annot loc funname f_cc annot =
  let open FInfo in

  let mk_ra = Annot.filter_string_list None ["stack", OnStack; "reg", OnReg] in

  let retaddr_kind =
    let kind = Annot.ensure_uniq1 "returnaddress" mk_ra annot in
    if kind <> None && not (FInfo.is_subroutine f_cc) then
      hierror
        ~loc:(Lone loc)
        ~funname
        ~kind:"unexpected annotation"
        "returnaddress only applies to subroutines";
    kind
  in

  let stack_zero_strategy =

    let strategy =
      let mk_szs = Annot.filter_string_list None Glob_options.stack_zero_strategies in
      let strategy = Annot.ensure_uniq1 "stackzero" mk_szs annot in
      if strategy <> None && not (FInfo.is_export f_cc) then
        hierror
          ~loc:(Lone loc)
          ~funname
          ~kind:"unexpected annotation"
          "stackzero only applies to export functions";
      if Option.is_none strategy then
        !Glob_options.stack_zero_strategy
      else
        strategy
    in

    let size =
      let size = Annot.ensure_uniq1 "stackzerosize" (Annot.wsize None) annot in
      if Option.is_none size then
        !Glob_options.stack_zero_size
      else
        size
    in

    match strategy, size with
    | None, None -> None
    | None, Some _ ->
        warning Always
          (L.i_loc0 loc)
          "\"stackzerosize\" is ignored, since you did not specify a strategy with attribute \"stackzero\"";
        None
    | Some szs, _ -> Some (szs, size)
  in

  { retaddr_kind;
    stack_allocation_size = Annot.ensure_uniq1 "stackallocsize" (Annot.pos_int None) annot;
    stack_size            = Annot.ensure_uniq1 "stacksize"      (Annot.pos_int None) annot;
    stack_align           = Annot.ensure_uniq1 "stackalign"     (Annot.wsize None)   annot;
    max_call_depth        = Annot.ensure_uniq1 "calldepth"      (Annot.pos_int None) annot;
    stack_zero_strategy;
    f_user_annot          = annot;
  }


(* -------------------------------------------------------------------- *)
(* Compute the set of declared variables                                *)
let rec add_reserved_i env (_,i) =
  match L.unloc i with
  | S.PIdecl (_, ids) ->
      List.fold_left (fun env id -> Env.add_reserved env (L.unloc (S.var_decl_id (L.unloc id)))) env ids
  | PIArrayInit _ | PIAssign _ -> env
  | PIIf(_, c, oc) -> add_reserved_oc (add_reserved_c' env c) oc
  | PIFor(_, _, c) -> add_reserved_c' env c
  | PIWhile(oc1, _, oc2) -> add_reserved_oc (add_reserved_oc env oc1) oc2

and add_reserved_c env c =
  List.fold_left add_reserved_i env c

and add_reserved_c' env c = add_reserved_c env (L.unloc c)

and add_reserved_oc env =
  function
  | None -> env
  | Some c -> add_reserved_c' env c

(* -------------------------------------------------------------------- *)

let add_known_implicits arch_info env c =
  let env = add_reserved_c env c in
  let create env s =
    if not (Env.is_reserved env s) then s
    else
      let rec aux i =
        let s' = Format.sprintf "%s_%i" s i in
        if not (Env.is_reserved env s') then s'
        else aux (i+1) in
      aux 0 in
  let env, known_implicits =
    List.map_fold (fun env (s1, s2) ->
        let s2 = create env s2 in
        let env = Env.Vars.push_implicit env (mk_var s2 (Reg(Normal, Direct)) P.etbool L._dummy [], P.etbool) in
        env, (s1, s2)) env arch_info.known_implicits in
  Env.set_known_implicits env known_implicits


let warn_unused_variables env f =
  let used = List.fold_left (fun s v -> P.Spv.add (L.unloc v) s) P.Spv.empty f.P.f_ret in
  let used = P.Spv.union used (P.pvars_c f.P.f_body) in
  let pp_var fmt x = F.fprintf fmt "%s.%s" x.P.v_name (CoreIdent.string_of_uid x.P.v_id) in
  Env.Vars.iter_locals (fun x ->
   if not (P.Spv.mem x used) then
     warning UnusedVar (L.i_loc0 x.v_dloc) "unused variable %a" pp_var x)
    env

let tt_fundef arch_info (env0 : 'asm Env.env) loc (pf : S.pfundef) : 'asm Env.env =
  let env = Env.Vars.clear_locals env0 in
  if is_combine_flags pf.pdf_name then
    rs_tyerror ~loc:(L.loc pf.pdf_name) (string_error "invalid function name");
  let inret = Option.map_default (List.map L.unloc) [] (L.unloc pf.pdf_body.pdb_ret) in
  let dfl_mut x = List.mem x inret in

  let envb, args =
    let env, args = List.map_fold (tt_annot_paramdecls dfl_mut arch_info.pd) env pf.pdf_args in
    let env = add_known_implicits arch_info env pf.pdf_body.pdb_instr in
    env, List.flatten args in
  let fs_tout = Option.map_default (List.map (tt_type arch_info.pd env |- snd |- snd)) [] pf.pdf_rty in
  let ret_annot = Option.map_default (List.map fst) [] pf.pdf_rty in
  let body, ret_loc, xret = tt_funbody arch_info envb pf.pdf_body in
  let f_args = List.map (fun x -> L.mk_loc (L.loc x) (fst (L.unloc x))) args in
  let fs_tin = List.map (fun x -> snd (L.unloc x)) args in
  let f_ret = List.map (fun x -> L.mk_loc (L.loc x) (fst (L.unloc x))) xret in
  let f_cc = tt_call_conv loc f_args f_ret pf.pdf_cc in
  let name = L.unloc pf.pdf_name in
  let fdef =
    { P.f_loc   = loc;
      P.f_annot = process_f_annot loc name f_cc pf.pdf_annot;
      P.f_cc    = f_cc;
      P.f_info  = ();
      P.f_name  = P.F.mk name;
      P.f_tyin  = List.map P.gty_of_gety fs_tin;
      P.f_args  = List.map L.unloc f_args;
      P.f_body  = body;
      P.f_tyout = List.map P.gty_of_gety fs_tout;
      P.f_ret_info = { ret_annot; ret_loc };
      P.f_ret   = f_ret; } in

  check_return_statement ~loc fdef.P.f_name fs_tout
    (List.map (fun x -> L.loc x, snd (L.unloc x)) xret);

  warn_unused_variables envb fdef;

  let return_storage = Option.map_default (List.map (fst |- snd)) [] pf.pdf_rty in
  check_return_storage ~loc fdef.P.f_name return_storage f_ret;

  Env.Funs.push env0 fdef {fs_tin; fs_tout}

(* -------------------------------------------------------------------- *)
let tt_global_def pd env (gd:S.gpexpr) =
  let f e =
    let pe,ety = tt_expr ~mode:`AllVar pd env e in
    (L.mk_loc e.pl_loc pe, ety) in
  let array_of_string s =
    L.unloc s |> String.to_list |> List.map @@ fun c ->
    c |> Char.code |> Z.of_int |> fun z ->
    P.(L.mk_loc (L.loc s) (Papp1 (op_word_of_int(Word, W.Unsigned, W.U8), Pconst z)), P.etw U8) in
  match gd with
  | S.GEword e ->
    `Word (f e)
  | S.GEarray es ->
    `Array (List.map f es)
  | S.GEstring e ->
    `Array (array_of_string e)

let tt_global pd (env : 'asm Env.env) _loc (gd: S.pglobal) : 'asm Env.env =

  let open P in
  let mk_pe ws (pe,ety) =
    match ety with
    | P.ETword(wk, ews) when wk = None && Utils0.cmp_le Wsize.wsize_cmp ws ews ->
      L.unloc pe
    | P.ETint -> Papp1 (op_word_of_int(Word, W.Unsigned, ws), L.unloc pe)
    | _ -> rs_tyerror ~loc:(L.loc pe) (TypeMismatch (ety, P.etw ws))
    in

  let ty, d =
    match tt_type pd env gd.S.pgd_type, tt_global_def pd env gd.S.pgd_val with
    | P.ETword(None, ws) as ty, `Word (pe,ety) ->
      let pe = mk_pe ws (pe,ety) in
      ty, P.GEword pe
    | (P.ETint | P.ETbool | P.ETword _), `Array _ ->
      rs_tyerror ~loc:(L.loc gd.S.pgd_type) GlobArrayNotWord
    | P.ETarr(ws, _n) as ty, `Array es ->
      let pes = List.map (mk_pe ws) es in
      ty, P.GEarray pes
    | P.ETarr _, `Word _ ->
      rs_tyerror ~loc:(L.loc gd.S.pgd_type) GlobWordNotArray
    | ty,_ -> rs_tyerror ~loc:(L.loc gd.S.pgd_type) (InvalidTypeForGlobal ty)
  in

  let x = mk_var (L.unloc gd.S.pgd_name) W.Global ty (L.loc gd.S.pgd_name) [] in

  Env.Vars.push_global env (x,ty,d)


let tt_typealias arch_info env id ty =
  let alias = tt_type arch_info.pd env ty in
  Env.TypeAlias.push env id alias

(* -------------------------------------------------------------------- *)
let rec tt_item arch_info (env : 'asm Env.env) pt : 'asm Env.env =
  match L.unloc pt with
  | S.PParam  pp -> tt_param  arch_info.pd env (L.loc pt) pp
  | S.PFundef pf -> tt_fundef arch_info env (L.loc pt) pf
  | S.PGlobal pg -> tt_global arch_info.pd env (L.loc pt) pg
  | S.Pexec   pf ->
    Env.Exec.push (L.loc pt)
      (fst (tt_fun env pf.pex_name)).P.f_name
      (List.map (fun (x, y) -> S.parse_int x, S.parse_int y) pf.pex_mem)
      env
  | S.Prequire (from, fs) ->
    List.fold_left (tt_file_loc arch_info from) env fs
  | S.PNamespace (ns, items) ->
     let env = Env.enter_namespace env ns in
     let env = List.fold_left (tt_item arch_info) env items in
     let env = Env.exit_namespace env in
     env
  | S.PTypeAlias (id,ty) -> tt_typealias arch_info env id ty

and tt_file_loc arch_info from env fname =
  fst (tt_file arch_info env from (Some (L.loc fname)) (L.unloc fname))

and tt_file arch_info env from loc fname =
  match Env.enter_file env from loc fname with
  | None -> env, []
  | Some(env, fname) ->
    let ast   = Parseio.parse_program ~name:fname in
    let ast =
      try BatFile.with_file_in fname ast
      with Sys_error(err) ->
        let loc = Option.map_default (fun l -> Lone l) Lnone loc in
        hierror ~loc ~kind:"typing" "error reading file %S (%s)" fname err
    in
    let env   = List.fold_left (tt_item arch_info) env ast in
    Env.exit_file env, ast

(* -------------------------------------------------------------------- *)
let tt_program arch_info (env : 'asm Env.env) (fname : string) =
  let env, ast = tt_file arch_info env None None fname in
  env, Env.decls env, ast

(* FIXME :
   - Les fonctions exportees doivent pas avoir de tableau en argument,
     rendre au plus un argument (pas un tableau).
   - Verifier les kind dans les applications de fonctions
*)

