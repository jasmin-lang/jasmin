(* -------------------------------------------------------------------- *)
open Utils
module Path = BatPathGen.OfString
module F = Format
module L = Location
module S = Syntax
module E = Expr
module P = Prog
module W = Wsize
module T = Type

(* -------------------------------------------------------------------- *)
let loc_of_tuples default locs =
  List.fold_left L.merge default locs

(* -------------------------------------------------------------------- *)
type typattern = TPBool | TPInt | TPWord | TPArray

type sop = [ `Op2 of S.peop2 | `Op1 of S.peop1]

type tyerror =
  | UnknownVar          of S.symbol
  | UnknownFun          of S.symbol
  | InvalidType         of P.pty * typattern
  | TypeMismatch        of P.pty pair
  | NoOperator          of sop * P.pty list
  | InvalidOperator     of sop
  | NoReturnStatement   of P.funname * int
  | InvalidReturnStatement of P.funname * int * int
  | InvalidArgCount     of int * int
  | InvalidLvalCount    of int * int
  | DuplicateFun        of S.symbol * L.t
  | InvalidCast         of P.pty pair
  | InvalidGlobal       of S.symbol
  | InvalidTypeForGlobal of P.pty
  | NotAPointer         of P.plval
  | GlobArrayNotWord    
  | GlobWordNotArray
  | EqOpWithNoLValue
  | CallNotAllowed
  | PrimNotAllowed
  | Unsupported         of string
  | UnknownPrim         of S.symbol
  | PrimNoSize of S.symbol
  | PrimNotVector of S.symbol
  | PrimIsVector of S.symbol
  | PrimIsVectorVector of S.symbol
  | PrimIsX of S.symbol
  | PrimNotX of S.symbol
  | ReturnLocalStack    of S.symbol
  | PtrOnlyForArray
  | ArgumentNotVar      
  | BadVariableKind     of P.v_kind
  | WriteToConstantPointer of S.symbol
  | PackSigned
  | PackWrongWS of int
  | PackWrongPE of int
  | PackWrongLength of int * int
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
let pp_typat fmt = function
  | TPBool  -> F.fprintf fmt "bool"
  | TPInt   -> F.fprintf fmt "int"
  | TPWord  -> F.fprintf fmt "word (u8, u16, u32, u64)"
  | TPArray -> F.fprintf fmt "array"

let pp_tyerror fmt (code : tyerror) =
  match code with
  | UnknownVar x ->
      F.fprintf fmt "unknown variable: `%s'" x

  | UnknownFun x ->
      F.fprintf fmt "unknown function: `%s'" x

  | InvalidType (ty, p) ->
    F.fprintf fmt "the expression as type %a instead of %a"
       Printer.pp_ptype ty pp_typat p

  | TypeMismatch (t1,t2) ->
    F.fprintf fmt
      "the expression has type %a instead of %a"
      Printer.pp_ptype t1 Printer.pp_ptype t2

  | InvalidCast (t1,t2) ->
    F.fprintf fmt "can not implicitly cast %a into %a"
      Printer.pp_ptype t1 Printer.pp_ptype t2        

  | InvalidGlobal g ->
      F.fprintf fmt "invalid use of a global name: ‘%s’" g

  | InvalidTypeForGlobal ty ->
      F.fprintf fmt "globals should have type word; found: ‘%a’"
        Printer.pp_ptype ty

  | NotAPointer x -> 
    F.fprintf fmt "The variable %a should be a pointer"
      Printer. pp_plval x

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
        (pp_list " * " Printer.pp_ptype) ts

  | NoOperator (`Op1 o, ts) ->
      F.fprintf fmt
        "no operator %s for these type %a"
        (S.string_of_peop1 o)
        (pp_list " * " Printer.pp_ptype) ts

  | NoReturnStatement (name, expected) ->
     F.fprintf fmt "function “%s” has no return statement (but its signature claims that %d values should be returned)" name.P.fn_name expected

  | InvalidReturnStatement (name, given, expected) ->
      F.fprintf fmt "return statement of function %s has %d values instead of %d (as claimed by the signature)" name.P.fn_name given expected

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
  | UnknownPrim s ->
      F.fprintf fmt "unknown primitive: `%s'" s

  | PrimNoSize s ->
      F.fprintf fmt "primitive accepts no size annotation: `%s'" s

  | PrimNotVector s ->
      F.fprintf fmt "primitive does not operate on vectors: `%s'" s

  | PrimNotX s ->
      F.fprintf fmt "primitive does not need  two word sizes annotations: `%s'" s

  | PrimIsVector s ->
     F.fprintf fmt "primitive needs a vector size annotation: `%s'" s

  | PrimIsVectorVector s ->
     F.fprintf fmt "primitive needs two vector size annotations: `%s'" s

  | PrimIsX s ->
      F.fprintf fmt "primitive needs two word sizes annotations: `%s'" s

  | ReturnLocalStack v ->
      F.fprintf fmt "can not return the local stack variable %s" v

  | PtrOnlyForArray -> 
    F.fprintf fmt "Pointer allowed only on array"

  | ArgumentNotVar ->
    F.fprintf fmt "the expression should be a variable"

  | BadVariableKind kind ->
    F.fprintf fmt "the variable should have kind %a"
       Printer.pp_kind kind

  | WriteToConstantPointer v ->
    F.fprintf fmt "Cannot write to the constant pointer %s" v

  | PackSigned ->
    F.fprintf fmt "packs should be unsigned"

  | PackWrongWS n ->
    F.fprintf fmt "wrong word-size (%d) in pack" n

  | PackWrongPE n ->
    F.fprintf fmt "wrong element-size (%d) in pack" n

  | PackWrongLength (e, f) ->
    F.fprintf fmt "wrong length of pack; expected: %d; found: %d" e f
  
  | StringError s ->
    F.fprintf fmt "%s" s

(* -------------------------------------------------------------------- *)
module Env : sig
  type env

  val empty : env

  val decls : env -> unit P.pmod_item list
    
  val add_from : env -> string * string -> env

  val enter_file : env -> S.pident option -> L.t option -> string -> (env * string) option
  val exit_file  : env -> env

  val dependencies : env -> Path.t list

  module Vars : sig
    val push       : env -> P.pvar -> env
    val push_param : env -> (P.pvar * P.pexpr) -> env
    val find       : S.symbol -> env -> P.pvar option
  end

  module Globals : sig
    val push : env -> (P.pvar * P.pexpr P.ggexpr) -> env
    val find : S.symbol -> env -> P.pvar option
  end

  module Funs : sig
    val push : env -> unit P.pfunc -> P.pty list -> env 
    val find : S.symbol -> env -> (unit P.pfunc * P.pty list) option
  end

  module Exec : sig
    val push : P.funname -> (Z.t * Z.t) list -> env -> env
    val get  : env -> (P.funname * (Z.t * Z.t) list) list
  end

end = struct
  type loader = 
    { loaded : Path.t list (* absolute path *)
    ; idir   : Path.t      (* absolute initial path *)
    ; dirs   : Path.t list 
    ; from   : (S.symbol, Path.t) Map.t
    } 

  type env = {
    e_vars    : (S.symbol, P.pvar) Map.t;
    e_globals : (S.symbol, P.pvar) Map.t;
    e_funs    : (S.symbol, unit P.pfunc * P.pty list) Map.t;
    e_decls   : unit P.pmod_item list;
    e_exec    : (P.funname * (Z.t * Z.t) list) list;
    e_loader  : loader;
  }

  let empty : env =
    { e_vars    = Map.empty
    ; e_globals = Map.empty 
    ; e_funs    = Map.empty
    ; e_decls   = []
    ; e_exec    = []
    ; e_loader  = 
        { loaded = []
        ; idir   = Path.of_string (Sys.getcwd ())
        ; dirs   = [[]]
        ; from   = Map.empty
        }
    }


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
            rs_tyerror ~loc:(L.loc name) (string_error "unkown name %s" (L.unloc name)) in 
    let p = 
      if Path.is_absolute p then p
      else Path.concat current_dir p in
    let p = Path.normalize_in_tree p in
    let ap = 
      if Path.is_absolute p then p
      else Path.concat loader.idir p in
    let ap = Path.normalize_in_tree ap in
    if List.mem ap loader.loaded then None
    else
      let e_loader = 
        { loader with
          loaded = ap :: loader.loaded;
          dirs = List.tl p :: loader.dirs } in
      Some({ env with e_loader }, Path.to_string p)

  let exit_file env = 
    { env with 
      e_loader = { env.e_loader with dirs = List.tl env.e_loader.dirs }}
    
  let decls env = env.e_decls 

  let dependencies env = env.e_loader.loaded

  module Vars = struct
    let push (env : env) (v : P.pvar) =
      { env with e_vars = Map.add v.P.v_name v env.e_vars }

    let push_param env (x,_ as d) = 
      let env = push env x in
      { env with e_decls = P.MIparam d :: env.e_decls }

    let find (x : S.symbol) (env : env) =
      Map.Exceptionless.find x env.e_vars
  end

  module Globals = struct

    let push env (v,_ as d) = 
      { env with e_globals = Map.add v.P.v_name v env.e_globals;
                 e_decls = P.MIglobal d :: env.e_decls }

    let find (x : S.symbol) (env : env) =
      Map.Exceptionless.find x env.e_globals
  end

  module Funs = struct
    let find (x : S.symbol) (env : env) =
      Map.Exceptionless.find x env.e_funs

    let push env (v : unit P.pfunc) rty =
      let name = v.P.f_name.P.fn_name in
      match find name env with
      | None -> { env with e_funs = Map.add name (v,rty) env.e_funs;
                           e_decls = P.MIfun v :: env.e_decls }
      | Some (fd,_) -> 
        rs_tyerror ~loc:v.P.f_loc (DuplicateFun(name, fd.P.f_loc))

  end

  module Exec = struct
    let push f m env = { env with e_exec = (f, m) :: env.e_exec }
    let get env = List.rev env.e_exec
  end

end

(* -------------------------------------------------------------------- *)
let tt_ws (ws : S.wsize) =
  match ws with
  | `W8   -> W.U8
  | `W16  -> W.U16
  | `W32  -> W.U32
  | `W64  -> W.U64
  | `W128 -> W.U128
  | `W256 -> W.U256

(* -------------------------------------------------------------------- *)

module Annot = struct
 
  let on_attribute ?on_empty ?on_int ?on_id ?on_string ?on_ws ?on_struct error (id, attribute) =
    let nid = L.unloc id in
    let doit loc o arg = 
      match o with
      | None -> error loc nid 
      | Some f -> f loc nid arg in
    match attribute with
    | None -> doit (L.loc id) on_empty ()
    | Some a ->
      let loc = L.loc a in
      match L.unloc a with
      | S.Aint i    -> doit loc on_int i 
      | S.Aid id    -> doit loc on_id id
      | S.Astring s -> doit loc on_string s 
      | S.Aws ws    -> doit loc on_ws ws 
      | S.Astruct s -> doit loc on_struct s

  let pp_dfl_attribute pp fmt dfl = 
    match dfl with
    | Some a -> Format.fprintf fmt "@ default is “%a”" pp a 
    | None   -> () 

  let error_attribute loc id pp a pp_dfl dfl = 
    rs_tyerror ~loc (string_error "attribute for “%s” should be %a%a"
                       id pp a (pp_dfl_attribute pp_dfl) dfl)

  let on_empty error dfl loc nid () = 
    match dfl with
    | None -> error loc nid
    | Some d -> d

  let filter_string_list dfl l arg = 
    let error loc nid = 
      assert (l<> []);
      let pp fmt l = 
        Format.fprintf fmt "(@[%a@])" (pp_list " |@ " (fun fmt (s,_) -> Format.pp_print_string fmt s)) l in
      error_attribute loc nid pp l Format.pp_print_string dfl in
    let on_string loc nid s =
      try List.assoc s l 
      with Not_found -> error loc nid in
    on_attribute  
      ~on_empty:(fun loc nid () -> on_string loc nid (on_empty error dfl loc nid ()))
      ~on_id:(on_string) 
      ~on_string error arg

  let bool dfl = 
    filter_string_list 
      (Some (if dfl then "yes" else "no"))
      ["yes", true; "no", false]

  let none (id,_ as arg) = 
    on_attribute
      ~on_empty:(fun _loc _nid () -> ())
      (fun loc _nid -> 
        rs_tyerror ~loc 
          (string_error "attribute for “%s” should be empty" (L.unloc id)))
      arg
    
  let int dfl arg = 
    let error loc nid =
       error_attribute loc nid Format.pp_print_string "an integer"
                              Z.pp_print dfl in
    let on_empty loc nid () = 
      match dfl with
      | Some i -> i
      | None -> error loc nid in

    let on_string loc nid s = 
      try Z.of_string s 
      with Invalid_argument _ -> error loc nid in

    on_attribute 
      ~on_empty
      ~on_int:(fun _loc _nid i -> i)
      ~on_string 
      error arg 

  let pos_int dfl (id, _ as arg) = 
    let i = int dfl arg in
    if Z.lt i Z.zero then 
      error_attribute (L.loc id) (L.unloc id) 
        Format.pp_print_string "a positive integer"
        Z.pp_print dfl;
    i
        
  let ws_of_string = 
    let l = List.map (fun ws -> P.string_of_ws ws, ws) 
              [U8;U16;U32;U64;U128;U256] in
    fun s -> List.assoc s l 

  let wsize dfl arg = 
    let error loc nid =
      error_attribute loc nid 
        Format.pp_print_string "a word size"
        (fun fmt ws -> Format.fprintf fmt "%s" (P.string_of_ws ws)) dfl in
    let on_empty loc nid () = 
      match dfl with
      | Some ws -> ws
      | None -> error loc nid in
    let on_string loc nid s = 
      try ws_of_string s with Not_found -> error loc nid in
    let on_ws _loc _nid ws = tt_ws ws in
    on_attribute 
      ~on_empty
      ~on_string 
      ~on_ws 
      error arg 
  
  let filter_attribute ?(case_sensitive=true) name (f: S.annotation -> 'a) (annot:S.annotations) = 
    let test = 
      if case_sensitive then fun id -> L.unloc id = name 
      else 
        let name = String.uppercase_ascii name in
        fun id -> String.uppercase_ascii (L.unloc id) = name in

    List.pmap (fun (id,_ as arg) -> if test id then Some (id, f arg) else None) annot

  let process_annot ?(case_sensitive=true) (filters: (string * (S.annotation -> 'a)) list) annot = 
    List.flatten 
      (List.map (fun (name,f) -> filter_attribute ~case_sensitive name f annot) filters)
    
  let ensure_uniq ?(case_sensitive=true) (filters: (string * (S.annotation -> 'a)) list) annot = 
    match process_annot ~case_sensitive filters annot with
    | [] -> None
    | [_, r] -> Some r
    | (id, _) :: _ as l -> 
      rs_tyerror ~loc:(L.loc id) (string_error "only one of the attribute %a is expected"
                                 (pp_list ", " (fun fmt (id, _) -> Format.fprintf fmt "%s" (L.unloc id))) l)

  let ensure_uniq1 ?(case_sensitive=true) id f annot = 
    ensure_uniq ~case_sensitive [id, f] annot
end 





(* -------------------------------------------------------------------- *)
let tt_pointer dfl_writable (p:S.ptr) : P.pointer = 
  match p with
  | `Pointer (Some `Writable) -> P.Pointer P.Writable
  | `Pointer (Some `Constant) -> P.Pointer P.Constant
  | `Pointer None             -> 
    P.Pointer (if dfl_writable then P.Writable else P.Constant)
  | `Direct  -> P.Direct

let tt_sto dfl_writable (sto : S.pstorage) : P.v_kind =
  match sto with
  | `Inline  -> P.Inline
  | `Reg   p -> P.Reg (tt_pointer dfl_writable p)
  | `Stack p -> P.Stack (tt_pointer dfl_writable p)
  | `Global  -> P.Global

type tt_mode = [
  | `AllVar
  | `OnlyParam
  | `NoParam
  ]

(* -------------------------------------------------------------------- *)
let tt_var (mode:tt_mode) (env : Env.env) { L.pl_desc = x; L.pl_loc = lc; } =
  let v =
    match Env.Vars.find x env with
    | Some v -> v
    | None -> rs_tyerror ~loc:lc (UnknownVar x) in
  begin match mode with
  | `OnlyParam ->
    if v.P.v_kind <> P.Const then
      rs_tyerror ~loc:lc (StringError "only param variable are allowed here")
  | `NoParam -> 
    if v.P.v_kind = P.Const then
      rs_tyerror ~loc:lc (StringError "param variable not allowed here")
  | `AllVar -> ()
  end;
  v

let tt_var_global (mode:tt_mode) (env : Env.env) v = 
  let lc = v.L.pl_loc in
  let x, k = 
    try tt_var mode env v, E.Slocal
    with TyError _ -> 
      let x = v.L.pl_desc in
      if mode = `OnlyParam then rs_tyerror ~loc:lc (UnknownVar x);
      match Env.Globals.find x env with
      | Some v -> v, E.Sglob
      | None -> rs_tyerror ~loc:lc (UnknownVar x) in
  { P.gv = L.mk_loc lc x; P.gs = k }, x.P.v_ty

(* -------------------------------------------------------------------- *)
let tt_fun (env : Env.env) { L.pl_desc = x; L.pl_loc = loc; } =
  Env.Funs.find x env |> oget ~exn:(tyerror ~loc (UnknownFun x))

(* -------------------------------------------------------------------- *)
let check_ty (ety : typattern) (loc, ty) =
  match ety, ty with
  | TPBool , P.Bty P.Bool  -> ()
  | TPInt  , P.Bty P.Int   -> ()
  | TPWord , P.Bty (P.U _) -> ()
  | TPArray, P.Arr _       -> ()

  | _ -> rs_tyerror ~loc (InvalidType (ty, ety))

(* -------------------------------------------------------------------- *)
let warn_arr loc from to_ = 
  warning Always (L.i_loc0 loc) "cannot ensure that the type %a is compatible with %a"
    Printer.pp_ptype from Printer.pp_ptype to_

let check_ty_eq ~loc ~(from : P.pty) ~(to_ : P.pty) =
  if not (P.pty_equal from to_) then
    match from, to_ with
    | P.Arr _, P.Arr _ ->
      warn_arr loc from to_
    | _, _ -> rs_tyerror ~loc (TypeMismatch (from, to_))

let check_ty_u64 ~loc ty =
  check_ty_eq ~loc ~from:ty ~to_:P.u64

let check_ty_bool ~loc ty =
  check_ty_eq ~loc ~from:ty ~to_:P.tbool

(* -------------------------------------------------------------------- *)
let check_return_statement ~loc name (declared : P.pty list) (given : (L.t * P.pty) list) : unit =
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

(* -------------------------------------------------------------------- *)
let check_sig_lvs loc sig_ lvs =
  let loc () = loc_of_tuples loc (List.map (fun (l,_,_) -> l) lvs) in

  let nsig_ = List.length sig_ in
  let nlvs  = List.length lvs  in

  if nlvs <> nsig_ then 
    rs_tyerror ~loc:(loc ()) (InvalidLvalCount(nlvs, nsig_));

  List.iter2
    (fun ty (loc, _, lty) -> lty
      |> oiter (fun lty -> check_ty_eq ~loc ~from:ty ~to_:lty))
     sig_ lvs;

  List.map2 (fun ty (_,flv,_) -> flv ty) sig_ lvs


(* -------------------------------------------------------------------- *)
let tt_sign = function
  | `Signed -> W.Signed
  | `Unsigned -> W.Unsigned
  
(* -------------------------------------------------------------------- *)
let tt_as_bool = check_ty TPBool
let tt_as_int  = check_ty TPInt

(* -------------------------------------------------------------------- *)
let tt_as_array ((loc, ty) : L.t * P.pty) : P.pty * P.pexpr =
  match ty with
  | P.Arr (ws, n) -> P.Bty (P.U ws), n
  | _ -> rs_tyerror ~loc (InvalidType (ty, TPArray))

(* -------------------------------------------------------------------- *)
let tt_as_word ((loc, ty) : L.t * P.pty) : W.wsize =
  match ty with
  | P.Bty (P.U ws) -> ws
  | _ -> rs_tyerror ~loc (InvalidType (ty, TPWord))

(* -------------------------------------------------------------------- *)

type ty_op_kind = 
  | OpKE of E.cmp_kind 
  | OpKV of W.signedness * W.velem * W.wsize 
   
let wsize_le = Utils0.cmp_le W.wsize_cmp
let wsize_min = Utils0.cmp_min W.wsize_cmp
let wsize_max s1 s2 = if wsize_le s1 s2 then s2 else s1

let max_ty ty1 ty2 =
  if P.pty_equal ty1 ty2 then Some ty1 else
  match ty1, ty2 with
  | P.Bty P.Int, P.Bty (P.U _) -> Some ty2
  | P.Bty (P.U _), P.Bty P.Int -> Some ty1
  | P.Bty (P.U w1), P.Bty (P.U w2) -> Some (P.Bty (P.U (Utils0.cmp_min W.wsize_cmp w1 w2)))
  | _    , _     -> None

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

let op_info_dfl exn ty s (intok, (minws, maxws)) = 
  match ty with
  | P.Bty (P.U ws) -> 
    let ws = wsize_max minws ws in
    let ws = wsize_min ws maxws in
    OpKE (E.Cmp_w(s, ws))
  | _          -> 
    if not intok then raise exn;
    OpKE (E.Cmp_int)

let check_op loc op cmp sz = 
  match cmp with
  | None -> rs_tyerror ~loc (InvalidOperator op)
  | Some (min, max) ->
    if not (wsize_le min sz && wsize_le sz max) then
      rs_tyerror ~loc (InvalidOperator op)

let op_info exn op (castop:S.castop) ty ws_cmp vs_cmp =
  match castop with
  | None                -> 
    let s = W.Unsigned in
    op_info_dfl exn ty s ws_cmp

  | Some c -> 
    let loc = L.loc c in
    match L.unloc c with 
    | CSS(None, s) -> 
      let s = tt_sign s in
      op_info_dfl exn ty s ws_cmp

    | CSS(Some sz, s) -> 
      let s = tt_sign s in
      let sz = tt_ws sz in
      check_op loc op (Some (snd ws_cmp)) sz;
      OpKE(E.Cmp_w(s, sz))

    | CVS(vs,s,ve) ->
      let s = tt_sign s in
      let ve, ws = tt_vsize_op loc op vs ve in
      check_op loc op vs_cmp (W.wsize_of_velem ve);
      OpKV(s, ve, ws)

  

(* -------------------------------------------------------------------- *)
let op_kind_of_cmp = function
  | E.Cmp_int     -> E.Op_int
  | E.Cmp_w(_,ws) -> E.Op_w ws  

type 'o op_info = { 
    opi_op   : ty_op_kind -> 'o;
    opi_wcmp : bool * (W.wsize * W.wsize);  
    opi_vcmp : (W.wsize * W.wsize) option;
  }

let cmp_8_64 = (W.U8, W.U64)
let cmp_8_256 = (W.U8, W.U256)

let mk_cmp_kind eop vop = function
  | OpKE c        -> eop c
  | OpKV(s,ve,ws) -> vop s ve ws

let mk_cmp_info eop vop = {
    opi_op   = mk_cmp_kind eop vop;
    opi_wcmp = true, cmp_8_256;
    opi_vcmp = Some cmp_8_64;
  }

let mk_op_of_c op c = op (op_kind_of_cmp c) 

let mk_op_info eop vop = mk_cmp_info (mk_op_of_c eop) vop

let mk_cmp_info_nvec eop = {
    opi_op   = mk_cmp_kind eop (fun _ _ _ -> assert false);
    opi_wcmp = true, cmp_8_256;
    opi_vcmp = None;
  }

let mk_op64_info_nvec eop = mk_cmp_info_nvec (mk_op_of_c eop)

let mk_logic_info eop = 
  let mk = function
    | OpKE (Cmp_int)     -> assert false 
    | OpKE (Cmp_w(_,ws)) -> eop ws
    | OpKV (_s,_ve,ws)   -> eop ws in
  { opi_op = mk;
    opi_wcmp = false, cmp_8_256;
    opi_vcmp = Some (cmp_8_64); }

(* -------------------------------------------------------------------- *)

let op1_of_ty exn op castop ty (info:E.sop1 op_info) = 
  let tok = op_info exn (`Op1 op) castop ty info.opi_wcmp info.opi_vcmp in
  info.opi_op tok

let lnot_info = mk_logic_info (fun s -> E.Olnot s)
let  neg_info = mk_op64_info_nvec (fun s -> E.Oneg s)

(* -------------------------------------------------------------------- *)

let add_info = 
  mk_op_info (fun k -> E.Oadd k) (fun _s ve ws -> E.Ovadd(ve,ws))

let sub_info = 
  mk_op_info (fun k -> E.Osub k) (fun _s ve ws -> E.Ovsub(ve,ws))

let mul_info = 
  mk_op_info (fun k -> E.Omul k) (fun _s ve ws -> E.Ovmul(ve,ws))

let div_info = mk_cmp_info_nvec (fun k -> E.Odiv k) 
let mod_info = mk_cmp_info_nvec (fun k -> E.Omod k) 

let land_info = mk_logic_info (fun k -> E.Oland k)
let lor_info  = mk_logic_info (fun k -> E.Olor  k)
let lxor_info = mk_logic_info (fun k -> E.Olxor k)

let shr_info = 
  let mk = function
    | OpKE (Cmp_int)     -> E.Oasr E.Op_int 
    | OpKE (Cmp_w(s,ws)) -> 
      if s = W.Unsigned then E.Olsr ws else E.Oasr (E.Op_w ws)
    | OpKV (s,ve,ws)   -> 
      if s = W.Unsigned then E.Ovlsr(ve,ws) else E.Ovasr(ve,ws) in
  { opi_op   = mk;
    opi_wcmp = true, cmp_8_256;
    opi_vcmp = Some cmp_8_64;
  }
   
let shl_info = 
  let mk = function
    | OpKE (Cmp_int)      -> E.Olsl E.Op_int
    | OpKE (Cmp_w(_s,ws)) -> E.Olsl (E.Op_w ws)
    | OpKV (_s,ve,ws)     -> E.Ovlsl(ve,ws) in
  { opi_op   = mk;
    opi_wcmp = true, cmp_8_256;
    opi_vcmp = Some cmp_8_64;
  } 

let mk_test_info eop2 = 
  let mk = function
    | OpKE k          -> eop2 k
    | OpKV (s,_ve,ws) -> eop2 (E.Cmp_w(s,ws)) in
  { opi_op = mk;
    opi_wcmp = true, cmp_8_256;
    opi_vcmp = Some (cmp_8_64); }

let eq_info  = mk_test_info (fun c -> E.Oeq (op_kind_of_cmp c))
let neq_info = mk_test_info (fun c -> E.Oneq (op_kind_of_cmp c))
let lt_info  = mk_test_info (fun c -> E.Olt c)
let le_info  = mk_test_info (fun c -> E.Ole c)
let gt_info  = mk_test_info (fun c -> E.Ogt c)
let ge_info  = mk_test_info (fun c -> E.Oge c)

let op2_of_ty exn op castop ty (info:E.sop2 op_info) = 
  let tok = op_info exn (`Op2 op) castop ty info.opi_wcmp info.opi_vcmp in
  info.opi_op tok

let op2_of_pop2 exn ty (op : S.peop2) =
  match op with
  | `And    -> E.Oand
  | `Or     -> E.Oor

  | `Add  c -> op2_of_ty exn op c ty add_info 
  | `Sub  c -> op2_of_ty exn op c ty sub_info 
  | `Mul  c -> op2_of_ty exn op c ty mul_info 
  | `Div  c -> op2_of_ty exn op c ty div_info 
  | `Mod  c -> op2_of_ty exn op c ty mod_info 

  | `BAnd c -> op2_of_ty exn op c (max_ty ty P.u256 |> oget ~exn) land_info
  | `BOr  c -> op2_of_ty exn op c (max_ty ty P.u256 |> oget ~exn) lor_info
  | `BXOr c -> op2_of_ty exn op c (max_ty ty P.u256 |> oget ~exn) lxor_info
  | `ShR  c -> op2_of_ty exn op c ty shr_info
  | `ShL  c -> op2_of_ty exn op c ty shl_info

  | `Eq   c -> op2_of_ty exn op c ty eq_info 
  | `Neq  c -> op2_of_ty exn op c ty neq_info
  | `Lt   c -> op2_of_ty exn op c ty lt_info
  | `Le   c -> op2_of_ty exn op c ty le_info
  | `Gt   c -> op2_of_ty exn op c ty gt_info
  | `Ge   c -> op2_of_ty exn op c ty ge_info

let op1_of_pop1 exn ty (op: S.peop1) = 
  match op with
  | `Cast _ -> assert false 
  | `Not c ->
    if ty = P.tbool then 
      if c <> None then raise exn
      else E.Onot
    else
      op1_of_ty exn op c  (max_ty ty P.u256 |> oget ~exn) lnot_info 

  | `Neg c -> op1_of_ty exn op c ty neg_info

(* -------------------------------------------------------------------- *)
let peop2_of_eqop (eqop : S.peqop) =
  match eqop with
  | `Raw    -> None
  | `Add  s -> Some (`Add s)
  | `Sub  s -> Some (`Sub s)
  | `Mul  s -> Some (`Mul s)
  | `ShR  s -> Some (`ShR s)
  | `ShL  s -> Some (`ShL s)
  | `BAnd s -> Some (`BAnd s)
  | `BXOr s -> Some (`BXOr s)
  | `BOr  s -> Some (`BOr s)

(* -------------------------------------------------------------------- *)
let cast loc e ety ty =
  match ety, ty with
  | P.Bty P.Int , P.Bty (P.U w) -> P.Papp1 (E.Oword_of_int w, e)
  | P.Bty (P.U w), P.Bty P.Int -> P.Papp1 (E.Oint_of_word w, e)
  | P.Bty (P.U w1), P.Bty (P.U w2) when W.wsize_cmp w1 w2 <> Datatypes.Lt -> e
  | _, _ when P.pty_equal ety ty -> e
  | P.Arr _, P.Arr _ ->
    warn_arr loc ety ty; e
  | _  ->  rs_tyerror ~loc (InvalidCast(ety,ty))

let cast_word loc ws e ety =
  match ety with
  | P.Bty P.Int   -> P.Papp1 (Oword_of_int ws, e), ws
  | P.Bty (P.U ws1) -> e, ws1
  | _             ->  rs_tyerror ~loc (InvalidCast(ety,P.Bty (P.U ws)))

let cast_int loc e ety = 
  cast loc e ety P.tint 

(* -------------------------------------------------------------------- *)
let conv_ty = function
    | T.Coq_sbool    -> P.tbool
    | T.Coq_sint     -> P.tint
    | T.Coq_sword ws -> P.Bty (P.U ws)
    | T.Coq_sarr _   -> assert false 

let type_of_op2 op = 
  let (ty1, ty2), tyo = E.type_of_op2 op in
  conv_ty ty1, conv_ty ty2, conv_ty tyo

let tt_op2 (loc1, (e1, ety1)) (loc2, (e2, ety2))
           { L.pl_desc = pop; L.pl_loc = loc } =

  match pop with
  | `Eq None when ety1 = P.tbool && ety2 = P.tbool ->
    P.Papp2(E.Obeq, e1, e2), P.tbool
  | `Neq None when ety1 = P.tbool && ety1 = P.tbool ->
    P.Papp1 (E.Onot, P.Papp2(E.Obeq, e1, e2)), P.tbool
  | _ -> 
    let exn = tyerror ~loc (NoOperator (`Op2 pop, [ety1; ety2])) in
    let ty = 
      match pop with
      | `And   | `Or    -> P.tbool 
      | `ShR _ | `ShL _ -> ety1 
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
  let ty, tyo = E.type_of_op1 op in
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
let rec tt_expr ?(mode=`AllVar) (env : Env.env) pe =
  match L.unloc pe with
  | S.PEParens pe ->
    tt_expr ~mode env pe

  | S.PEBool b ->
    P.Pbool b, P.tbool

  | S.PEInt i ->
    P.Pconst i, P.tint

  | S.PEVar x ->
    let x, ty = tt_var_global mode env x in
    P.Pvar x, ty

  | S.PEFetch me ->
    let ct, x, e = tt_mem_access ~mode env me in
    P.Pload (ct, x, e), P.Bty (P.U ct)

  | S.PEGet (aa, ws, ({ L.pl_loc = xlc } as x), pi, olen) ->
    let x, ty = tt_var_global mode env x in
    let ty, _ = tt_as_array (xlc, ty) in
    let ws = omap_dfl tt_ws (P.ws_of_ty ty) ws in
    let ty = P.tu ws in
    let i,ity  = tt_expr ~mode env pi in
    check_ty_eq ~loc:(L.loc pi) ~from:ity ~to_:P.tint;
    begin match olen with
    | None -> P.Pget (aa, ws, x, i), ty
    | Some plen ->
      let len,ity  = tt_expr ~mode:`OnlyParam env plen in
      check_ty_eq ~loc:(L.loc plen) ~from:ity ~to_:P.tint;
      let ty = P.Arr(ws, len) in
      P.Psub (aa, ws, len, x, i), ty
    end

  | S.PEOp1 (op, pe) ->
    let e, ety = tt_expr ~mode env pe in

    begin match op with
    | `Cast (`ToInt) ->
      let e = cast_int (L.loc pe) e ety in
      e, P.tint 
      
    | `Cast (`ToWord (sz, sg)) ->
      let sz = tt_ws sz in
      let e, ws = cast_word (L.loc pe) sz e ety in
      let e = 
        if W.wsize_cmp ws sz = Datatypes.Lt then 
          let op =
            match sg with
            | `Unsigned -> E.Ozeroext (sz, ws)
            | `Signed   -> E.Osignext (sz, ws)
          in
          P.Papp1(op,e)
        else e in
      e, P.Bty (P.U sz)
    | _  ->
      let et1 = tt_expr ~mode env pe in
      tt_op1 (L.loc pe, et1) (L.mk_loc (L.loc pe) op)
    end

  | S.PEOp2 (pop, (pe1, pe2)) ->
    let et1 = tt_expr ~mode env pe1 in
    let et2 = tt_expr ~mode env pe2 in
    tt_op2 (L.loc pe1, et1) (L.loc pe2, et2) (L.mk_loc (L.loc pe) pop)

  | S.PECombF(id, args) ->
    begin match List.assoc (L.unloc id) combine_flags with
    | c ->
      let nexp = List.length Expr.tin_combine_flags in
      let nargs = List.length args in
      if nargs <> nexp then
        rs_tyerror ~loc:(L.loc pe) (InvalidArgCount(nargs, nexp));
      let tt_expr pe =
        let e, ety = tt_expr ~mode env pe in
        check_ty_eq ~loc:(L.loc pe) ~from:ety ~to_:P.tbool;
        e in
      let args = List.map tt_expr args in
      P.PappN (E.Ocombine_flags c, args), P.tbool
    | exception Not_found -> assert false 
    end

  | S.PECall (id, args) when is_combine_flags id ->
    tt_expr ~mode env (L.mk_loc (L.loc pe) (S.PECombF(id,args)))

  | S.PECall _ ->
    rs_tyerror ~loc:(L.loc pe) CallNotAllowed

  | S.PEPrim _ ->
    rs_tyerror ~loc:(L.loc pe) PrimNotAllowed

  | S.PEpack ((nb, sg, es), args) ->
    let loc = L.loc pe in
    if sg <> `Unsigned then rs_tyerror ~loc PackSigned;
    let sz, pz, len = tt_pack ~loc nb es in
    let args = List.map (tt_expr ~mode env) args in
    let args = List.map (fun (a, ty) -> cast loc a ty (P.Bty P.Int)) args in
    let alen = List.length args in
    if alen <> len then rs_tyerror ~loc (PackWrongLength (len, alen));
    P.PappN (E.Opack (sz, pz), args), P.Bty (P.U sz)

  | S.PEIf (pe1, pe2, pe3) ->
    let e1, ty1 = tt_expr ~mode env pe1 in
    let e2, ty2 = tt_expr ~mode env pe2 in
    let e3, ty3 = tt_expr ~mode env pe3 in

    check_ty_bool ~loc:(L.loc pe1) ty1;
    let ty = max_ty ty2 ty3 |> oget ~exn:(tyerror ~loc:(L.loc pe) (TypeMismatch (ty2, ty3))) in
    P.Pif(ty, e1, e2, e3), ty

and tt_expr_cast ?(mode=`AllVar) (env : Env.env) pe ty = 
  let e, ety = tt_expr ~mode env pe in
  cast (L.loc pe) e ety ty 
  
and tt_mem_access ?(mode=`AllVar) (env : Env.env) 
           (ct, ({ L.pl_loc = xlc } as x), e) = 
  let x = tt_var `NoParam env x in
  check_ty_u64 ~loc:xlc x.P.v_ty;
  let e = 
    match e with
    | None -> P.Papp1 (Oword_of_int U64, P.Pconst (Z.zero)) 
    | Some(k, e) -> 
      let e = tt_expr_cast ~mode env e P.u64 in
      match k with
      | `Add -> e
      | `Sub -> Papp1(E.Oneg (E.Op_w U64), e) in
  let ct = ct |> omap_dfl tt_ws U64 in
  (ct,L.mk_loc xlc x,e)

(* -------------------------------------------------------------------- *)
and tt_type (env : Env.env) (pty : S.ptype) : P.pty =
  match L.unloc pty with
  | S.TBool     -> P.tbool
  | S.TInt      -> P.tint
  | S.TWord  ws -> P.Bty (P.U (tt_ws ws))
  | S.TArray (ws, e) ->
      P.Arr (tt_ws ws, fst (tt_expr ~mode:`OnlyParam env e))

(* -------------------------------------------------------------------- *)
let tt_exprs (env : Env.env) es = List.map (tt_expr ~mode:`AllVar env) es

(* -------------------------------------------------------------------- *)
let tt_expr_bool env pe = tt_expr_cast env pe P.tbool
let tt_expr_int  env pe = tt_expr_cast env pe P.tint

(* -------------------------------------------------------------------- *)
let tt_vardecl dfl_writable (env : Env.env) ((annot, (sto, xty)), x) =
  let { L.pl_desc = x; L.pl_loc = xlc; } = x in
  let (sto, xty) = (tt_sto (dfl_writable x) sto, tt_type env xty) in
  if P.is_ptr sto && not (P.is_ty_arr xty) then
    rs_tyerror ~loc:xlc PtrOnlyForArray;
  L.mk_loc xlc (P.PV.mk x sto xty xlc annot)

(* -------------------------------------------------------------------- *)
let tt_vardecls_push dfl_writable (env : Env.env) pxs =
  let xs  = List.map (tt_vardecl dfl_writable env) pxs in
  let env = 
    List.fold_left (fun env x -> Env.Vars.push env (L.unloc x)) env xs in
  (env, xs)

(* -------------------------------------------------------------------- *)
let tt_vardecl_push dfl_writable (env : Env.env) px =
  snd_map as_seq1 (tt_vardecls_push dfl_writable env [px])

(* -------------------------------------------------------------------- *)
let tt_param (env : Env.env) _loc (pp : S.pparam) : Env.env =
  let ty = tt_type env pp.ppa_ty in
  let pe, ety = tt_expr ~mode:`OnlyParam env pp.S.ppa_init in

  check_ty_eq ~loc:(L.loc pp.ppa_init) ~from:ty ~to_:ety;

  let x = P.PV.mk (L.unloc pp.ppa_name) P.Const ty (L.loc pp.ppa_name) [] in
  let env = Env.Vars.push_param env (x,pe) in
  env


(* -------------------------------------------------------------------- *)
let tt_lvalue (env : Env.env) { L.pl_desc = pl; L.pl_loc = loc; } =

  let reject_constant_pointers loc x =
    match x.P.v_kind with
    | Stack (Pointer Constant) | Reg (Pointer Constant) ->
       rs_tyerror ~loc (WriteToConstantPointer x.P.v_name)
    | _ -> ()
  in

  match pl with
  | S.PLIgnore ->
    loc, (fun ty -> P.Lnone(loc,ty)) , None

  | S.PLVar x ->
    let x = tt_var `NoParam env x in
    reject_constant_pointers loc x ;
    loc, (fun _ -> P.Lvar (L.mk_loc loc x)), Some x.P.v_ty

  | S.PLArray (aa, ws, ({ pl_loc = xlc } as x), pi, olen) ->
    let x  = tt_var `NoParam env x in
    reject_constant_pointers xlc x ;
    let ty,_ = tt_as_array (xlc, x.P.v_ty) in
    let ws = omap_dfl tt_ws (P.ws_of_ty ty) ws in 
    let ty = P.tu ws in
    let i,ity  = tt_expr env ~mode:`AllVar pi in
    check_ty_eq ~loc:(L.loc pi) ~from:ity ~to_:P.tint;
    begin match olen with
    | None -> 
      loc, (fun _ -> P.Laset (aa, ws, L.mk_loc xlc x, i)), Some ty
    | Some plen ->
      let len,ity  = tt_expr ~mode:`OnlyParam env plen in
      check_ty_eq ~loc:(L.loc plen) ~from:ity ~to_:P.tint;
      let ty = P.Arr(ws, len) in
      loc, (fun _ -> P.Lasub (aa, ws, len, L.mk_loc xlc x, i)), Some ty
    end

  | S.PLMem me ->
    let ct, x, e = tt_mem_access ~mode:`AllVar env me in
    loc, (fun _ -> P.Lmem (ct, x, e)), Some (P.Bty (P.U ct))

(* -------------------------------------------------------------------- *)

let f_sig f =
  List.map P.ty_i f.P.f_ret, List.map (fun v -> v.P.v_ty) f.P.f_args

let prim_sig (type a) p : a P.gty list * a P.gty list * Sopn.arg_desc list =
  let f = conv_ty in
  let o = Sopn.get_instr_desc (Arch_extra.asm_opI X86_extra.x86_extra) p in
  List.map f o.tout,
  List.map f o.tin,
  o.i_out

type prim_constructor =
  | PrimP of W.wsize * (W.wsize option -> W.wsize -> X86_extra.x86_extended_op Sopn.sopn)
  | PrimM of (W.wsize option -> X86_extra.x86_extended_op Sopn.sopn)
  | PrimV of (W.wsize option -> W.signedness -> W.velem -> W.wsize -> X86_extra.x86_extended_op Sopn.sopn)
  | PrimX of (W.wsize option -> W.wsize -> W.wsize -> X86_extra.x86_extended_op Sopn.sopn)
  | PrimVV of (W.wsize option -> W.velem -> W.wsize -> W.velem -> W.wsize -> X86_extra.x86_extended_op Sopn.sopn)

let prim_string =
  [ "mulu", PrimP (W.U64, fun _ws sz -> Omulu sz);
    "adc", PrimP (W.U64, fun _ws sz -> Oaddcarry sz);
    "sbb", PrimP (W.U64, fun _ws sz -> Osubcarry sz);
    "set0", PrimP (W.U64, fun _ws sz -> Oasm (ExtOp (Oset0 sz)));
    "concat_2u128", PrimM (fun _ws -> Oasm (ExtOp Oconcat128)) ] @
  List.map (fun (s, prc) ->
      let s = Conv.string_of_string0 s in
      let prc = 
        match prc with
        | Arch_decl.PrimP(x1,x2) -> PrimP(x1, fun ws sz -> Oasm (BaseOp (ws, x2 sz)))
        | Arch_decl.PrimM(x)     -> PrimM(fun ws -> Oasm (BaseOp (ws, x)))
        | Arch_decl.PrimV(x)     -> PrimV(fun ws _ sz sz' -> Oasm (BaseOp (ws, x sz sz')))
        | Arch_decl.PrimSV(x)    -> PrimV(fun ws s sz sz' -> Oasm (BaseOp (ws, x s sz sz')))
        | Arch_decl.PrimX(x)     -> PrimX(fun ws sz sz' -> Oasm (BaseOp (ws, x sz sz')))
        | Arch_decl.PrimVV(x)    -> PrimVV(fun ws ve sz ve' sz' -> Oasm (BaseOp (ws, x ve sz ve' sz'))) in
      (s, prc)) X86_instr_decl.x86_prim_string
            
type size_annotation =
  | SAw of W.wsize
  | SAv of W.signedness * W.velem * W.wsize
  | SAx of W.wsize * W.wsize
  | SAvv of W.velem * W.wsize * W.velem * W.wsize
  | SA

let extract_size str : string * size_annotation =
  let get_size =
    function
    | "8"   -> SAw W.U8
    | "16"  -> SAw W.U16
    | "32"  -> SAw W.U32
    | "64"  -> SAw W.U64
    | "128" -> SAw W.U128
    | "256" -> SAw W.U256

    | "2u8"   -> SAv (W.Unsigned, W.VE8,  W.U16)
    | "4u8"   -> SAv (W.Unsigned, W.VE8,  W.U32)
    | "2u16"  -> SAv (W.Unsigned, W.VE16, W.U32)
    | "8u8"   -> SAv (W.Unsigned, W.VE8,  W.U64)
    | "4u16"  -> SAv (W.Unsigned, W.VE16, W.U64)
    | "2u32"  -> SAv (W.Unsigned, W.VE32, W.U64)
    | "16u8"  -> SAv (W.Unsigned, W.VE8,  W.U128)
    | "8u16"  -> SAv (W.Unsigned, W.VE16, W.U128)
    | "4u32"  -> SAv (W.Unsigned, W.VE32, W.U128)
    | "2u64"  -> SAv (W.Unsigned, W.VE64, W.U128)
    | "32u8"  -> SAv (W.Unsigned, W.VE8,  W.U256)
    | "16u16" -> SAv (W.Unsigned, W.VE16, W.U256)
    | "8u32"  -> SAv (W.Unsigned, W.VE32, W.U256)
    | "4u64"  -> SAv (W.Unsigned, W.VE64, W.U256)

    | "2s8"   -> SAv (W.Signed, W.VE8,  W.U16)
    | "4s8"   -> SAv (W.Signed, W.VE8,  W.U32)
    | "2s16"  -> SAv (W.Signed, W.VE16, W.U32)
    | "8s8"   -> SAv (W.Signed, W.VE8,  W.U64)
    | "4s16"  -> SAv (W.Signed, W.VE16, W.U64)
    | "2s32"  -> SAv (W.Signed, W.VE32, W.U64)
    | "16s8"  -> SAv (W.Signed, W.VE8,  W.U128)
    | "8s16"  -> SAv (W.Signed, W.VE16, W.U128)
    | "4s32"  -> SAv (W.Signed, W.VE32, W.U128)
    | "2s64"  -> SAv (W.Signed, W.VE64, W.U128)
    | "32s8"  -> SAv (W.Signed, W.VE8,  W.U256)
    | "16s16" -> SAv (W.Signed, W.VE16, W.U256)
    | "8s32"  -> SAv (W.Signed, W.VE32, W.U256)
    | "4s64"  -> SAv (W.Signed, W.VE64, W.U256)
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
            SAx(wsize_of_int i, wsize_of_int j))
      with Not_found | End_of_file | Scanf.Scan_failure _ -> SA
  in
  match List.rev (String.split_on_char '_' str) with
  | [] -> str, SA
  | suf2 :: ((suf1 :: s) as tail) ->
     begin match get_size suf1, get_size suf2 with
     | SAv (_, ve1, sz1), SAv (_, ve2, sz2) -> String.concat "_" (List.rev s), SAvv (ve1, sz1, ve2, sz2)
     | _, SA -> str, SA
     | _, sz -> String.concat "_" (List.rev tail), sz
     end
  | suf :: s ->
    match get_size suf with
    | SA -> str, SA
    | sz -> String.concat "_" (List.rev s), sz

let tt_prim ws id =
  let { L.pl_loc = loc ; L.pl_desc = s } = id in
  let name, sz = extract_size s in
  match List.assoc name prim_string with
  | PrimP (d, pr) ->
    pr ws (match sz with
        | SAw sz -> sz 
        | SA -> d 
        | SAv _ | SAvv _ -> rs_tyerror ~loc (PrimNotVector s)
        | SAx _ -> rs_tyerror ~loc (PrimNotX s))
  | PrimM pr -> if sz = SA then pr ws else rs_tyerror ~loc (PrimNoSize s)
  | PrimV pr -> (match sz with SAv (s, ve, sz) -> pr ws s ve sz | _ -> rs_tyerror ~loc (PrimIsVector s))
  | PrimX pr -> (match sz with SAx(sz1, sz2) -> pr ws sz1 sz2 | _ -> rs_tyerror ~loc (PrimIsX s))
  | PrimVV pr -> (match sz with SAvv (ve, sz, ve', sz') -> pr ws ve sz ve' sz' | _ -> rs_tyerror ~loc (PrimIsVectorVector s))
  | exception Not_found -> rs_tyerror ~loc (UnknownPrim s)

let prim_of_op exn loc o =
  (* TODO: use context typing information when the operator is not annotated *)
  let bits_of_swsize : S.castop -> int option =
    function
    | None -> None
    | Some({L.pl_desc = S.CVS _} ) -> raise exn
    | Some({L.pl_desc = S.CSS(None, _)}) -> None
    | Some({L.pl_desc = S.CSS(Some sz, _)}) ->  
      Some (match sz with
      | `W8 -> 8
      | `W16 -> 16
      | `W32 -> 32
      | `W64 -> 64
      | `W128 -> 128
      | `W256 -> 256
        )
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
    x - y     -> addc x y false
    x - y - c -> addc x y c
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


(* -------------------------------------------------------------------- *)
let pexpr_of_plvalue exn l =
  match L.unloc l with
  | S.PLIgnore      -> raise exn
  | S.PLVar  x      -> L.mk_loc (L.loc l) (S.PEVar x)
  | S.PLArray(aa,ws,x,e,len)  -> L.mk_loc (L.loc l) (S.PEGet(aa,ws,x,e,len))
  | S.PLMem(ty,x,e) -> L.mk_loc (L.loc l) (S.PEFetch(ty,x,e))


let tt_lvalues env loc (pimp, pls) implicit tys =
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
          (function ADExplicit _           -> None 
                  | ADImplicit (IArflag f) -> Some (Conv.string_of_string0 (Var0.Var.vname f))
                  | ADImplicit (IAreg r)   -> Some (Conv.string_of_string0 (Var0.Var.vname r)))
          implicit in

      let iargs = List.pmap (omap String.uppercase_ascii) arguments in
    
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
        | None -> L.mk_loc loc (S.PLIgnore)
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

  let ls = List.map (tt_lvalue env) pls in
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
      let pargs = List.map get_implicit ["OF"; "CF"; "SF"; "ZF"] in
      let args = List.map (tt_expr_bool env) pargs in
      let doc (c, s) = 
        let error loc = rs_tyerror ~loc (string_error " = ident is expected after %s" (L.unloc c)) in
        let a = 
         Annot.on_attribute 
            ~on_id:(fun loc _nid s -> L.mk_loc loc (S.PLVar (L.mk_loc loc s)))
            error (c,s) in
        let _, flv, vty = tt_lvalue env a in
        let e, ety = P.PappN (E.Ocombine_flags (List.assoc (L.unloc c) combines), args), P.tbool in
        let e = vty |> omap_dfl (cast (L.loc a) e ety) e in
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

    

let tt_exprs_cast env loc les tys =
  let loc () = loc_of_tuples loc (List.map L.loc les) in
  let n1 = List.length les in
  let n2 = List.length tys in
  if n1 <> n2 then 
    rs_tyerror ~loc:(loc ()) (InvalidArgCount (n1, n2));
  List.map2 (fun le ty ->
    let e, ety = tt_expr ~mode:`AllVar env le in
    cast (L.loc le) e ety ty) les tys

let arr_init xi = 
  let x = L.unloc xi in 
  match x.P.v_ty with
  | P.Arr(ws, e) as ty ->
    let size =  let open P in (icnst (size_of_ws ws) ** e) in
    P.Cassgn (Lvar xi, E.AT_inline, ty, P.Parr_init size)
  | _           -> 
    rs_tyerror ~loc:(L.loc xi) (InvalidType( x.P.v_ty, TPArray))

let cassgn_for (x: P.plval) (tg: E.assgn_tag) (ty: P.pty) (e: P.pexpr) :
  (P.pexpr, unit) P.ginstr_r =
  Cassgn (x, tg, ty, e)

let rec is_constant e = 
  match e with 
  | P.Pconst _ | P.Pbool _ | P.Parr_init _ -> true
  | P.Pvar x  -> P.kind_i x.P.gv = P.Const || P.kind_i x.P.gv = P.Inline
  | P.Pget _ | P.Psub _ | P.Pload _ -> false
  | P.Papp1 (_, e) -> is_constant e
  | P.Papp2 (_, e1, e2) -> is_constant e1 && is_constant e2
  | P.PappN (_, es) -> List.for_all is_constant es
  | P.Pif(_, e1, e2, e3)   -> is_constant e1 && is_constant e2 && is_constant e3


let check_lval_pointer loc x =  
  match x with
  | P.Lvar x when P.is_ptr (L.unloc x).P.v_kind -> () 
  | _ -> rs_tyerror ~loc (NotAPointer x)

let mk_call loc is_inline lvs f es =
  begin match f.P.f_cc with 
  | P.Internal | P.Export -> ()
  | P.Subroutine _ ->
    let check_lval = function
      | P.Lnone _ | Lvar _ | Lasub _ -> ()
      | Lmem _ | Laset _ -> rs_tyerror ~loc (string_error "memory/array assignment are not allowed here") in
    let check_e = function
      | P.Pvar _ | P.Psub _ -> ()
      | _ -> rs_tyerror ~loc (string_error "only variables and subarray are allowed in arguments of non-inlined function") in
    List.iter check_lval lvs;
    List.iter check_e es
  end;
  P.Ccall (is_inline, lvs, f.P.f_name, es)

let tt_annot_vardecls dfl_writable env (annot, (ty,vs)) = 
  let aty = annot, ty in
  let vars = List.map (fun v -> aty, v) vs in
  tt_vardecls_push dfl_writable env vars 
  
let rec tt_instr (env : Env.env) ((annot,pi) : S.pinstr) : Env.env * unit P.pinstr list  =
  let mk_i instr = 
    { P.i_desc = instr; P.i_loc = L.of_loc pi; P.i_info = (); P.i_annot = annot} in
  match L.unloc pi with
  | S.PIdecl tvs -> 
    let env, _ = tt_annot_vardecls (fun _ -> true) env (annot, tvs) in 
    env, []

  | S.PIArrayInit ({ L.pl_loc = lc; } as x) ->
    let x = tt_var `AllVar env x in
    let xi = (L.mk_loc lc x) in
    env, [mk_i (arr_init xi)]
  
  | S.PIAssign (ls, `Raw, { pl_desc = PECall (f, args); pl_loc = el }, None) ->
    if is_combine_flags f then
      let pi = 
        L.mk_loc (L.loc pi) 
          (S.PIAssign (ls, `Raw, L.mk_loc el (S.PECombF(f, args)), None)) in
      tt_instr env (annot, pi) 

    else
      let (f,tlvs) = tt_fun env f in
      let _tlvs, tes = f_sig f in
      let lvs, is = tt_lvalues env (L.loc pi) ls None tlvs in
      assert (is = []);
      let es  = tt_exprs_cast env (L.loc pi) args tes in
      let is_inline = 
        match Annot.ensure_uniq1 "inline" Annot.none annot with
        | Some () -> E.InlineFun
        | None -> 
          match f.P.f_cc with 
          | P.Internal -> E.InlineFun
          | P.Export | P.Subroutine _ -> E.DoNotInline in
      env, [mk_i (mk_call (L.loc pi) is_inline lvs f es)]

  | S.PIAssign ((ls, xs), `Raw, { pl_desc = PEPrim (f, es) }, None) when 
     fst (extract_size (L.unloc f)) = "copy" ->
    if ls <> None then rs_tyerror ~loc:(L.loc pi) (string_error "copy expects no implicit arguments");
    let es = tt_exprs env es in
    let y, yty = 
      match es with
      | [Pvar y, ty] -> y, ty
      | _ -> 
          rs_tyerror ~loc:(L.loc pi) 
            (string_error "only a single variable is allowed as argument of copy")
    in
    let x = 
      match xs with
      | [x] -> 
        let loc, fx, _ = tt_lvalue env x in
        begin match fx yty with
        | Lvar x -> x
        | _ -> 
          rs_tyerror ~loc 
            (string_error "only a single variable is allowed as destination of copy")
        end
      | _ -> 
        rs_tyerror ~loc:(L.loc pi) 
          (string_error "only a single variable is allowed as destination of copy")
    in
    let ws =   
      (* Do not check size of array here, it is done in typing *)
      match snd (extract_size (L.unloc f)) with
      | SAw ws -> ws
      | SAv _ | SAx _ | SAvv _ -> assert false 
      | SA ->
        match (L.unloc x).v_ty with
        | Arr (xws, _) ->
          begin match yty with
          | Arr(yws, _) ->
            if (L.unloc x).v_kind = Reg Direct then xws
            else if (L.unloc y.gv).v_kind = Reg Direct then yws
            else  
              rs_tyerror ~loc:(L.loc pi) 
                (string_error "#copy: the source or the destination should be a reg array")
          | _ -> rs_tyerror ~loc:(L.loc y.gv) (string_error "an array is expected")
          end
        | _ -> rs_tyerror ~loc:(L.loc y.gv) (string_error "an array is expected")
    in
    env, [ mk_i (Copn([Lvar x], AT_none, Sopn.Ocopy(ws, Conv.pos_of_int 1), [Pvar y]))] 

  | S.PIAssign ((ls, xs), `Raw, { pl_desc = PEPrim (f, args) }, None) when L.unloc f = "randombytes" ->
      (* FIXME syscall *)  
      (* It will be good to make this uniform with copy *)
      (* This is durty but ... *)
      if ls <> None then rs_tyerror ~loc:(L.loc pi) (string_error "getrandom expects no implicit arguments");
      let loc, x, ty = 
        match xs with
        | [x] -> 
          let loc, x, oty = tt_lvalue env x in
          let ty = 
            match oty with 
            | None -> rs_tyerror ~loc (string_error "_ lvalue not accepted here")
            | Some ty -> ty in
          loc, x ty, ty  
        | _ ->  
          rs_tyerror ~loc:(L.loc pi) 
            (string_error "only a single variable is allowed as destination of getrandom") in
      let _ = tt_as_array (loc, ty) in
      let es = tt_exprs_cast env (L.loc pi) args [ty] in
      env, [mk_i (P.Csyscall([x], (* Syscall.GetRandom *) (Conv.pos_of_int 1), es))]

  | S.PIAssign (ls, `Raw, { pl_desc = PEPrim (f, args) }, None) ->
      let p = tt_prim None f in
      let tlvs, tes, arguments = prim_sig p in
      let lvs, einstr = tt_lvalues env (L.loc pi) ls (Some arguments) tlvs in
      let es  = tt_exprs_cast env (L.loc pi) args tes in
      env, mk_i (P.Copn(lvs, AT_none, p, es)) :: einstr

  | S.PIAssign (ls, `Raw, { pl_desc = PEOp1 (`Cast(`ToWord ct), {pl_desc = PEPrim (f, args) })} , None)
      ->
      let ws, s = ct in
      let ws = tt_ws ws in
      assert (s = `Unsigned); (* FIXME *)
      let p = tt_prim (Some ws) f in
      let tlvs, tes, arguments = prim_sig p in
      let lvs, einstr = tt_lvalues env (L.loc pi) ls (Some arguments) tlvs in
      let es  = tt_exprs_cast env (L.loc pi) args tes in
      env, mk_i (P.Copn(lvs, AT_none, p, es)) :: einstr

  | PIAssign((None,[lv]), `Raw, pe, None) ->
      let _, flv, vty = tt_lvalue env lv in
      let e, ety = tt_expr ~mode:`AllVar env pe in
      let e = vty |> omap_dfl (cast (L.loc pe) e ety) e in
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
      env, [mk_i (cassgn_for v tg ety e)]
        
  | PIAssign(ls, `Raw, pe, None) ->
      (* Try to match addc, subc, mulu *)
      let pe = prim_of_pe pe in
      let loc = L.loc pi in
      let i = annot, L.mk_loc loc (S.PIAssign(ls, `Raw, pe, None)) in
      tt_instr env i 

  | S.PIAssign((pimp,ls), eqop, pe, None) ->
      let op = oget (peop2_of_eqop eqop) in
      let loc = L.loc pi in
      let exn = tyerror ~loc EqOpWithNoLValue in
      if List.is_empty ls then raise exn;
      let pe1 = pexpr_of_plvalue exn (List.last ls) in
      let pe  = L.mk_loc loc (S.PEOp2(op,(pe1,pe))) in
      let i   = annot, L.mk_loc loc (S.PIAssign((pimp, ls), `Raw, pe, None)) in
      tt_instr env i 

  | PIAssign (ls, eqop, e, Some cp) ->
      let loc = L.loc pi in
      let exn = Unsupported "if not allowed here" in
      if peop2_of_eqop eqop <> None then rs_tyerror ~loc exn;
      let cpi = S.PIAssign (ls, eqop, e, None) in
      let env, i = tt_instr env (annot, L.mk_loc loc cpi) in
      let i, is =
        match i with
        | [] -> assert false
        | i :: is -> i, is in
      let x, _, ty, e = P.destruct_move i in
      let e' = ofdfl (fun _ -> rs_tyerror ~loc exn) (P.expr_of_lval x) in
      let c = tt_expr_bool env cp in
      env, mk_i (P.Cassgn (x, AT_none, ty, Pif (ty, c, e, e'))) :: is

  | PIIf (cp, st, sf) ->
      let c  = tt_expr_bool env cp in
      let st = tt_block env st in
      let sf = odfl [] (omap (tt_block env) sf) in
      env, [mk_i (P.Cif (c, st, sf))]

  | PIFor ({ pl_loc = lx } as x, (d, i1, i2), s) ->
      let i1   = tt_expr_int env i1 in
      let i2   = tt_expr_int env i2 in
      let vx   = tt_var `AllVar env x in
      check_ty_eq ~loc:lx ~from:vx.P.v_ty ~to_:P.tint;
      let s    = tt_block env s in
      let d    = match d with `Down -> E.DownTo | `Up -> E.UpTo in
      env, [mk_i (P.Cfor (L.mk_loc lx vx, (d, i1, i2), s))]

  | PIWhile (s1, c, s2) ->
      let c  = tt_expr_bool env c in
      let s1 = omap_dfl (tt_block env) [] s1 in
      let s2 = omap_dfl (tt_block env) [] s2 in
      let a = 
        omap_dfl (fun () -> E.Align) E.NoAlign (Annot.ensure_uniq1 "align" Annot.none annot) in
      env, [mk_i (P.Cwhile (a, s1, c, s2))]

(* -------------------------------------------------------------------- *)
and tt_block (env : Env.env) (pb : S.pblock) =
  snd (tt_cmd env (L.unloc pb))

and tt_cmd env c = 
  match c with
  | [] -> env, []
  | i::c -> 
    let env, i = tt_instr env i in
    let env, c = tt_cmd env c in
    env, i @ c

(* -------------------------------------------------------------------- *)
let tt_funbody (env : Env.env) (pb : S.pfunbody) =
 (* let vars = List.(pb.pdb_vars |> map (fun (ty, vs) -> map (fun v -> (ty, v)) vs) |> flatten) in 
  let env = fst (tt_vardecls_push (fun _ -> true) env vars) in *)
  let env, bdy = tt_cmd env pb.S.pdb_instr in
  let ret =
    let for1 x = L.mk_loc (L.loc x) (tt_var `AllVar env x) in
    List.map for1 (odfl [] pb.pdb_ret) in
  (bdy, ret)


(* -------------------------------------------------------------------- *)
      
let tt_call_conv loc params returns cc =
  match cc with
  | Some `Inline -> 
    P.Internal

  | Some `Export ->
    let check s x = 
      if (L.unloc x).P.v_kind <> Reg Direct then 
        rs_tyerror ~loc:(L.loc x) 
          (string_error "%a has kind %a, only reg are allowed in %s of export function"
            Printer.pp_pvar (L.unloc x)
            Printer.pp_kind (L.unloc x).P.v_kind s) in
    List.iter (check "parameter") params;
    List.iter (check "result") returns;
    if 2 < List.length returns then
      rs_tyerror ~loc (string_error "export function should return at most two arguments");
    P.Export 

  | None         -> 
    let check s x =
      if not (P.is_reg_kind (L.unloc x).P.v_kind) then 
        rs_tyerror ~loc:(L.loc x) 
          (string_error "%a has kind %a, only reg or reg ptr are allowed in %s of non inlined function"
            Printer.pp_pvar (L.unloc x)
            Printer.pp_kind (L.unloc x).P.v_kind s) in
    List.iter (check "parameter") params;
    List.iter (check "result") returns;
    let returned_params =
      let args = List.map L.unloc params in
      List.map (fun x ->
        let loc = L.loc x in
        let x = L.unloc x in
        match x.P.v_kind with
        | P.Reg Direct -> None
        | P.Reg (Pointer writable) -> 
          if writable = Constant then
            warning Always (L.i_loc0 loc) "no need to return a [reg const ptr] %a"
              Printer.pp_pvar x;
          let i = List.index_of x args in
          if i = None then 
            rs_tyerror ~loc (string_error "%a should be one of the paramaters"
                               Printer.pp_pvar x);
          i
        | _ -> assert false) returns in
    let check_writable_param i x = 
      let loc = L.loc x in
      let x = L.unloc x in
      if x.P.v_kind = Reg (Pointer Writable) then
        if not (List.exists ((=) (Some i)) returned_params) then
          rs_tyerror ~loc (string_error "%a is mutable, it should be returned"
                             Printer.pp_pvar x) in
    List.iteri check_writable_param params;
    P.Subroutine {returned_params}

(* -------------------------------------------------------------------- *)

let process_f_annot annot = 
  let open P in

  let mk_ra = Annot.filter_string_list None ["stack", OnStack; "reg", OnReg] in
 
  { retaddr_kind          = Annot.ensure_uniq1 "returnaddress"  mk_ra                annot;
    stack_allocation_size = Annot.ensure_uniq1 "stackallocsize" (Annot.pos_int None) annot; 
    stack_size            = Annot.ensure_uniq1 "stacksize"      (Annot.pos_int None) annot; 
    stack_align           = Annot.ensure_uniq1 "stackalign"     (Annot.wsize None)   annot}

(* -------------------------------------------------------------------- *)
let tt_fundef (env : Env.env) loc (pf : S.pfundef) : Env.env =
  if is_combine_flags pf.pdf_name then
    rs_tyerror ~loc:(L.loc pf.pdf_name) (string_error "invalid function name");
  let inret = odfl [] (omap (List.map L.unloc) pf.pdf_body.pdb_ret) in
  let dfl_mut x = List.mem x inret in
  let envb, args = 
    let env, args = List.map_fold (tt_annot_vardecls dfl_mut) env pf.pdf_args in
    env, List.flatten args in
  let rty  = odfl [] (omap (List.map (tt_type env |- snd |- snd)) pf.pdf_rty) in
  let oannot = odfl [] (omap (List.map fst) pf.pdf_rty) in
  let body, xret = tt_funbody envb pf.pdf_body in
  let f_cc = tt_call_conv loc args xret pf.pdf_cc in
  let args = List.map L.unloc args in
  let fdef =
    { P.f_loc   = loc;
      P.f_annot = process_f_annot pf.pdf_annot;
      P.f_cc    = f_cc;
      P.f_name  = P.F.mk (L.unloc pf.pdf_name);
      P.f_tyin  = List.map (fun { P.v_ty } -> v_ty) args;
      P.f_args  = args;
      P.f_body  = body;
      P.f_tyout = rty;
      P.f_outannot = oannot;
      P.f_ret   = xret; } in

  check_return_statement ~loc fdef.P.f_name rty
    (List.map (fun x -> (L.loc x, (L.unloc x).P.v_ty)) xret);

  Env.Funs.push env fdef rty

(* -------------------------------------------------------------------- *)
let tt_global_def env (gd:S.gpexpr) = 
  let f e = 
    let pe,ety = tt_expr ~mode:`OnlyParam env e in
    (L.mk_loc e.pl_loc pe, ety) in
  match gd with
  | S.GEword e -> 
    `Word (f e)
  | S.GEarray es ->
    `Array (List.map f es) 

let tt_global (env : Env.env) _loc (gd: S.pglobal) : Env.env =

  let open P in
  let mk_pe ws (pe,ety) = 
    match ety with
    | Bty (U ews) when Utils0.cmp_le Wsize.wsize_cmp ws ews -> L.unloc pe
    | Bty Int -> Papp1 (Oword_of_int ws, L.unloc pe)
    | _ -> rs_tyerror ~loc:(L.loc pe) (TypeMismatch (ety, Bty (U ws)))
    in

  let ty, d = 
    match tt_type env gd.S.pgd_type, tt_global_def env gd.S.pgd_val with
    | (Bty (U ws)) as ty, `Word (pe,ety) -> 
      let pe = mk_pe ws (pe,ety) in
      ty, P.GEword pe
    | Bty _, `Array _ -> 
      rs_tyerror ~loc:(L.loc gd.S.pgd_type) GlobArrayNotWord 
    | Arr(ws, _n) as ty, `Array es ->
      let pes = List.map (mk_pe ws) es in
      ty, P.GEarray pes 
    | Arr _, `Word _ ->
      rs_tyerror ~loc:(L.loc gd.S.pgd_type) GlobWordNotArray
    | ty,_ -> rs_tyerror ~loc:(L.loc gd.S.pgd_type) (InvalidTypeForGlobal ty)
  in

  let x = P.PV.mk (L.unloc gd.S.pgd_name) P.Global ty (L.loc gd.S.pgd_name) [] in

  Env.Globals.push env (x,d)

(* -------------------------------------------------------------------- *)
let rec tt_item (env : Env.env) pt : Env.env =
  match L.unloc pt with
  | S.PParam  pp -> tt_param  env (L.loc pt) pp
  | S.PFundef pf -> tt_fundef env (L.loc pt) pf
  | S.PGlobal pg -> tt_global env (L.loc pt) pg
  | S.Pexec   pf -> 
    Env.Exec.push (fst (tt_fun env pf.pex_name)).P.f_name pf.pex_mem env
  | S.Prequire (from, fs) -> 
    List.fold_left (tt_file_loc from) env fs 

and tt_file_loc from env fname = 
  fst (tt_file env from (Some (L.loc fname)) (L.unloc fname))

and tt_file env from loc fname = 
  match Env.enter_file env from loc fname with
  | None -> env, []
  | Some(env, fname) -> 
    let ast   = Parseio.parse_program ~name:fname in
    let ast   = BatFile.with_file_in fname ast in
    let env   = List.fold_left tt_item env ast in
    Env.exit_file env, ast

(* -------------------------------------------------------------------- *)
let tt_program (env : Env.env) (fname : string) =
  let env, ast = tt_file env None None fname in
  env, Env.decls env, ast

(* FIXME :
   - Les fonctions exportees doivent pas avoir de tableau en argument,
     rendre au plus un argument (pas un tableau).
   - Verifier les kind dans les applications de fonctions
*)

