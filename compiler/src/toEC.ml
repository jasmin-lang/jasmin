open Utils
open Wsize
open Prog
open PrintCommon
module E = Expr

type amodel =
  | ArrayOld
  | WArray
  | BArray

let ws2bytes ws = (int_of_ws ws) / 8

module Scmp = struct
  type t = string
  let compare = compare
end

module Ss = Set.Make(Scmp)
module Ms = Map.Make(Scmp)

(* ------------------------------------------------------------------- *)
(* Array theories in eclib *)

type arraywords = {
  sizew: int; (* in bytes *)
  sizea: int;
}

type subarray = {
  sizes: int;
  sizeb: int;
}

type subarraydirect = {
  sizew: int; (* in bytes *)
  sizes: int;
  sizeb: int;
}

type subarraycast = {
  sizews: int; (* in bytes *)
  sizewb: int; (* in bytes *)
  sizes: int;
  sizeb: int;
}

type arrayaccesscast = {
  sizews: int; (* in bytes *)
  sizewb: int; (* in bytes *)
  sizeb: int;
}

type array_theory =
  | Array of int
  | WArray of int
  | ArrayWords of arraywords
  | SubArray of subarray
  | SubArrayDirect of subarraydirect
  | SubArrayCast of subarraycast
  | ArrayAccessCast of arrayaccesscast
  | ByteArray of int
  | SubByteArray of subarray

module ATcmp = struct
  type t = array_theory
  let compare = compare
end

module Sarraytheory = Set.Make(ATcmp)

(* ------------------------------------------------------------------- *)
(* Easycrypt keywords (and extraction "pseudo-keywords") *)

(* FIXME: generate this list automatically *)
(* Adapted from EasyCrypt source file src/ecLexer.mll *)
let ec_keyword =
 [ "admit"
 ; "admitted"

 ; "forall"
 ; "exists"
 ; "fun"
 ; "glob"
 ; "let"
 ; "in"
 ; "for"
 ; "var"
 ; "proc"
 ; "if"
 ; "is"
 ; "match"
 ; "then"
 ; "else"
 ; "elif"
 ; "match"
 ; "for"
 ; "while"
 ; "assert"
 ; "return"
 ; "res"
 ; "equiv"
 ; "hoare"
 ; "ehoare"
 ; "phoare"
 ; "islossless"
 ; "async"

 ; "try"
 ; "first"
 ; "last"
 ; "do"
 ; "expect"

 (* Lambda tactics *)
 ; "beta"
 ; "iota"
 ; "zeta"
 ; "eta"
 ; "logic"
 ; "delta"
 ; "simplify"
 ; "cbv"
 ; "congr"

 (* Logic tactics *)
 ; "change"
 ; "split"
 ; "left"
 ; "right"
 ; "case"

 ; "pose"
 ; "gen"
 ; "have"
 ; "suff"
 ; "elim"
 ; "exlim"
 ; "ecall"
 ; "clear"
 ; "wlog"

 (* Auto tactics *)
 ; "apply"
 ; "rewrite"
 ; "rwnormal"
 ; "subst"
 ; "progress"
 ; "trivial"
 ; "auto"

 (* Other tactics *)
 ; "idtac"
 ; "move"
 ; "modpath"
 ; "field"
 ; "fieldeq"
 ; "ring"
 ; "ringeq"
 ; "algebra"

 ; "exact"
 ; "assumption"
 ; "smt"
 ; "coq"
 ; "check"
 ; "edit"
 ; "fix"
 ; "by"
 ; "reflexivity"
 ; "done"
 ; "solve"

 (* PHL: tactics *)
 ; "replace"
 ; "transitivity"
 ; "symmetry"
 ; "seq"
 ; "wp"
 ; "sp"
 ; "sim"
 ; "skip"
 ; "call"
 ; "rcondt"
 ; "rcondf"
 ; "swap"
 ; "cfold"
 ; "rnd"
 ; "rndsem"
 ; "pr_bounded"
 ; "bypr"
 ; "byphoare"
 ; "byehoare"
 ; "byequiv"
 ; "byupto"
 ; "fel"

 ; "conseq"
 ; "exfalso"
 ; "inline"
 ; "outline"
 ; "interleave"
 ; "alias"
 ; "weakmem"
 ; "fission"
 ; "fusion"
 ; "unroll"
 ; "splitwhile"
 ; "kill"
 ; "eager"

 ; "axiom"
 ; "axiomatized"
 ; "lemma"
 ; "realize"
 ; "proof"
 ; "qed"
 ; "abort"
 ; "goal"
 ; "end"
 ; "from"
 ; "import"
 ; "export"
 ; "include"
 ; "local"
 ; "declare"
 ; "hint"
 ; "module"
 ; "of"
 ; "const"
 ; "op"
 ; "pred"
 ; "inductive"
 ; "notation"
 ; "abbrev"
 ; "require"
 ; "theory"
 ; "abstract"
 ; "section"
 ; "subtype"
 ; "type"
 ; "class"
 ; "instance"
 ; "print"
 ; "search"
 ; "locate"
 ; "as"
 ; "Pr"
 ; "clone"
 ; "with"
 ; "rename"
 ; "prover"
 ; "timeout"
 ; "why3"
 ; "dump"
 ; "remove"
 ; "exit"

 ; "fail"
 ; "time"
 ; "undo"
 ; "debug"
 ; "pragma"

 ; "Top"
 ; "Self" ]

let syscall_mod_arg = "SC"
let syscall_mod_sig = "Syscall_t"
let syscall_mod     = "Syscall"
let internal_keyword =
  [ "safe"; "leakages"; syscall_mod_arg; syscall_mod_sig; syscall_mod ]

let keywords =
  Ss.union (Ss.of_list ec_keyword) (Ss.of_list internal_keyword)

(* ------------------------------------------------------------------- *)
(* Easycrypt very simplified (and incomplete) AST. *)
type ec_op2 =
    | ArrayGet
    | Plus
    | Infix of string

type ec_op3 =
    | Ternary
    | If
    | InORange

type ec_ident = string list

type ec_expr =
    | Econst of Z.t (* int. literal *)
    | Ebool of bool (* bool literal *)
    | Eident of ec_ident (* variable *)
    | Eapp of ec_expr * ec_expr list (* op. application *)
    | Efun1 of string * ec_expr (* fun s => expr *)
    | Eop2 of ec_op2 * ec_expr * ec_expr (* binary operator *)
    | Eop3 of ec_op3 * ec_expr * ec_expr * ec_expr (* ternary operator *)
    | Elist of ec_expr list (* list litteral *)
    | Etuple of ec_expr list (* tuple litteral *)

type ec_lvalue =
    | LvIdent of ec_ident
    | LvArrItem of ec_ident * ec_expr

type ec_lvalues = ec_lvalue list

type ec_instr =
    | ESasgn of ec_lvalues * ec_expr
    | EScall of ec_lvalues * ec_ident * ec_expr list
    | ESsample of ec_lvalues * ec_expr
    | ESif of ec_expr * ec_stmt * ec_stmt
    | ESwhile of ec_expr * ec_stmt
    | ESreturn of ec_expr
    | EScomment of string (* comment line *)

and ec_stmt = ec_instr list

type ec_ty = string

type ec_var = string * ec_ty

type ec_fun_decl = {
    fname: string;
    args: (string * ec_ty) list;
    rtys: ec_ty list;
}
type ec_fun = {
    decl: ec_fun_decl;
    locals: (string * ec_ty) list;
    stmt: ec_stmt;
}

type ec_modty = string

type ec_module_type = {
    name: ec_modty;
    funs: ec_fun_decl list;
}

type ec_module = {
    name: string;
    params: (string * ec_modty) list;
    ty: ec_modty option;
    vars: (string * string) list;
    funs: ec_fun list;
}

type ec_item =
    | IrequireImport of string list
    | Iimport of string list
    | IfromImport of string * (string list)
    | IfromRequireImport of string * (string list)
    | Iabbrev of string * ec_expr
    | ImoduleType of ec_module_type
    | Imodule of ec_module

type ec_prog = ec_item list


(* ------------------------------------------------------------------- *)
(* env: state of extraction *)

module type EnvT = sig
  type t
  val vars: t -> string Mv.t
  val pd: t -> Wsize.wsize
  val arch: t -> architecture
  val randombytes: t -> int list
  val set_fun: t -> ('a, 'b) func -> t
  val add_Array: t -> int -> unit
  val add_WArray: t -> int -> unit
  val add_ArrayWords: t -> int -> int -> unit
  val add_BArray: t -> int -> unit
  val add_SBArray: t -> subarray -> unit
  val add_SubArray: t -> int -> int -> unit
  val add_SubArrayDirect: t -> int -> int -> int -> unit
  val add_SubArrayCast: t -> int -> int -> int -> int -> unit
  val add_ArrayAccessCast: t -> int -> int -> int -> unit
  val add_randombytes: t -> int -> unit
  val add_ty: t -> int gty -> unit
  val add_jarray: t -> Wsize.wsize -> int -> unit
  val empty: architecture -> Wsize.wsize -> Sarraytheory.t ref -> t
  val create_name: t -> string -> string
  val array_theories: t -> Sarraytheory.t
  val get_funtype: t -> funname -> (ty list * ty list)
  val get_funname: t -> funname -> string
  val create_aux: t -> string -> ec_ty -> string
  val reuse_aux: t -> string -> ec_ty -> string
  val new_aux_range: t -> t
  val new_fun: t -> t
  val set_var: t -> var -> t
  val aux_vars: t -> (string * string) list
end


module Env: EnvT = struct
  module PTcmp = struct
    type t = string * ec_ty
    let compare = compare
  end

  module Mpty = Map.Make (PTcmp)

  type t = {
      arch: architecture;
      pd: Wsize.wsize;
      (* All names: functions, global variables, arguments, local variables, aux variables *)
      alls: Ss.t ref;
      (* All variables, excluding aux: global, argument, local variables *)
      vars: string Mv.t;
      glob: (string * ty) Ms.t;
      funs: (string * (ty list * ty list)) Mf.t;
      array_theories: Sarraytheory.t ref;
      (* aux variables: intermediate variables introduced by extraction.
        aux variables have a prefix in their name that identifies their use
        (such as jasmin assignments, for loop bounds, intermediate leakage variables).
        - auxv: for each (prefix, type), the list of all aux (used for variable declaration).
        - count: number of currently live aux variables for each (prefix, type).
        *)
      auxv: string BatVect.t Mpty.t ref;
      mutable count: int Mpty.t;
      randombytes: Sint.t ref;
    }

  let vars env = env.vars

  let pd env = env.pd

  let arch env = env.arch

  let randombytes env = Sint.elements !(env.randombytes)

  let array_theories env = !(env.array_theories)

  let add_Array env n =
    env.array_theories := Sarraytheory.add (Array n) !(env.array_theories)

  let add_BArray env size =
    env.array_theories := Sarraytheory.add (ByteArray size) !(env.array_theories)

  let add_SBArray env (s:subarray) =
    add_BArray env s.sizeb;
    add_BArray env s.sizes;
    env.array_theories := Sarraytheory.add (SubByteArray s) !(env.array_theories)

  let add_WArray env n =
    env.array_theories := Sarraytheory.add (WArray n) !(env.array_theories)

  let add_ArrayWords env sizew sizea =
    add_Array env sizea;
    add_WArray env (sizew*sizea);
    env.array_theories := Sarraytheory.add (ArrayWords {sizew; sizea}) !(env.array_theories)

  let add_SubArray env sizes sizeb =
    add_Array env sizes;
    add_Array env sizeb;
    env.array_theories := Sarraytheory.add (SubArray {sizes; sizeb}) !(env.array_theories)

  let add_SubArrayDirect env sizew sizes sizeb =
    add_ArrayWords env sizew sizes;
    add_ArrayWords env sizew sizeb;
    env.array_theories := Sarraytheory.add (SubArrayDirect {sizew; sizes; sizeb}) !(env.array_theories)

  let add_SubArrayCast env sizews sizewb sizes sizeb =
    add_ArrayWords env sizews sizes;
    add_ArrayWords env sizewb sizeb;
    env.array_theories := Sarraytheory.add (SubArrayCast {sizews; sizewb; sizes; sizeb}) !(env.array_theories)

  let add_ArrayAccessCast env sizews sizewb sizeb =
    add_ArrayWords env sizewb sizeb;
    env.array_theories := Sarraytheory.add (ArrayAccessCast {sizews; sizewb; sizeb}) !(env.array_theories)

  let add_randombytes env n = env.randombytes := Sint.add n !(env.randombytes)

  let add_jarray env ws n =
    let ats = Sarraytheory.add (Array n) !(env.array_theories) in
    env.array_theories := Sarraytheory.add (WArray (arr_size ws n)) ats

  let create_name env s =
    if not (Ss.mem s !(env.alls)) then s
    else
      let rec aux i =
        let s = Format.sprintf "%s_%i" s i in
        if Ss.mem s !(env.alls) then aux (i+1)
        else s in
      aux 0

  let mkname env n =
    n |> String.uncapitalize_ascii |> escape |> create_name env

  let set_var env x =
    let s = mkname env x.v_name in
    { env with
      alls = ref (Ss.add s !(env.alls));
      vars = Mv.add x s env.vars }

  let add_ty env = function
      | Bty _ -> ()
      | Arr (_ws, n) -> add_Array env n

  let empty arch pd array_theories =
    {
      arch;
      pd;
      alls = ref keywords;
      vars = Mv.empty;
      glob = Ms.empty;
      funs = Mf.empty;
      array_theories;
      auxv  = ref Mpty.empty;
      count = Mpty.empty;
      randombytes = ref Sint.empty;
    }

  let set_fun env fd =
    let s = mkname env fd.f_name.fn_name in
    let funs =
      Mf.add fd.f_name (s, (fd.f_tyout, fd.f_tyin)) env.funs in
    { env with funs; alls = ref (Ss.add s !(env.alls)) }

  let get_funtype env f = snd (Mf.find f env.funs)

  let get_funname env f = fst (Mf.find f env.funs)

  (*
    Auxiliary variables created by "create_aux" have the given prefix and their
    name, and are declared with the given type. Each created variable is
    guaranteed to be unique for all create_aux calls with **the same env**
    and (recursively) with **envs further derived by new_aux_range**.
    However, aux var may be resued across other env (e.g. in two sibling
    envs created by two calls to new_aux_range on the same env).

    This is implemented by keeping a per-env count of created (prefix, ty) auxs
    (env.count), while env.auxv tracks the complete list of created aux in the
    whole function (for re-used and initial declaration).
    new_aux_range copies env.count, ensuring that we don't reuse variables
    already created for this env, but that different calls to new_aux_range do
    not share the same env.count (hence may use the same auxs).
  *)
  let create_aux env prefix ty =
    let i = try Mpty.find (prefix, ty) env.count with Not_found -> 0 in
    let l = try Mpty.find (prefix, ty) !(env.auxv) with Not_found -> BatVect.empty in
    env.count <- Mpty.add (prefix,ty) (i+1) env.count;
    if i < BatVect.length l then begin
      BatVect.get l i
    end else begin
      let aux = create_name env prefix in
      env.auxv := Mpty.add (prefix, ty) (BatVect.append aux l) !(env.auxv);
      env.alls := Ss.add aux !(env.alls);
      aux
    end

  (* Return the last created aux for (prefix, ty) in this env. *)
  let reuse_aux env prefix ty =
    let i = Mpty.find (prefix, ty) env.count in
    let l = Mpty.find (prefix, ty) !(env.auxv) in
    BatVect.get l (i-1)

  let new_aux_range env = { env with count = env.count }

  let new_fun env = { env with count = Mpty.empty; auxv = ref Mpty.empty}

  let aux_vars env  =
    let unpack_vars ((_, ty), vars) = List.map (fun v -> (v, ty)) (BatVect.to_list vars) in
    List.flatten (List.map unpack_vars (Mpty.bindings !(env.auxv)))
end

let check_array env x =
  match (L.unloc x).v_ty with
  | Arr(ws, n) ->
      Sarraytheory.mem (Array n) (Env.array_theories env) &&
      Sarraytheory.mem (WArray (arr_size ws n)) (Env.array_theories env)
  | _ -> true

(* ------------------------------------------------------------------- *)
(* Formatting to string helpers *)

let fmt_array_theory at = match at with
  | Array n -> Format.sprintf "Array%i" n
  | WArray n -> Format.sprintf "WArray%i" n
  | ArrayWords aw -> Format.sprintf "ArrayWords%iW%i" aw.sizea (8*aw.sizew)
  | SubArray x -> Format.sprintf "SubArray%i_%i" x.sizes x.sizeb
  | SubArrayDirect x -> Format.sprintf "SubArrayDirect%i_%iW%i" x.sizes x.sizeb (8*x.sizew)
  | SubArrayCast x -> Format.sprintf "SubArrayDirect%iW%i_%iW%i" x.sizes (8*x.sizews) x.sizeb (8*x.sizewb)
  | ArrayAccessCast x -> Format.sprintf "ArrayAccessCastW%i_%iW%i" (8*x.sizews) x.sizeb (8*x.sizewb)
  | ByteArray n -> Format.sprintf "BArray%i" n
  | SubByteArray x -> Format.sprintf "SBArray%i_%i" x.sizeb x.sizes

let fmt_Wsz sz = Format.asprintf "W%i" (int_of_ws sz)

let fmt_op2 fmt op =
  let fmt_signed fmt ws is = function
    | E.Cmp_w (Signed, _)   -> Format.fprintf fmt "\\s%s" ws
    | E.Cmp_w (Unsigned, _) -> Format.fprintf fmt "\\u%s" ws
    | _                     -> Format.fprintf fmt "%s" is
  in
  let fmt_div fmt ws uints sints sg k =
    match sg, k with
    | Signed, E.Op_w _   -> Format.fprintf fmt "\\s%s" ws
    | Unsigned, E.Op_w _ -> Format.fprintf fmt "\\u%s" ws
    | Signed, E.Op_int   -> Format.fprintf fmt "%s" sints
    | Unsigned, E.Op_int -> Format.fprintf fmt "%s" uints
  in

  let fmt_vop2 fmt (s,ve,ws) =
    Format.fprintf fmt "\\v%s%iu%i" s (int_of_velem ve) (int_of_ws ws)
  in

  match op with
  | E.Obeq   -> Format.fprintf fmt "="
  | E.Oand   -> Format.fprintf fmt "/\\"
  | E.Oor    -> Format.fprintf fmt "\\/"
  | E.Oadd _ -> Format.fprintf fmt "+"
  | E.Omul _ -> Format.fprintf fmt "*"
  | E.Odiv(sg, k) -> fmt_div fmt "div" "%/" "\\zquot" sg k
  | E.Omod(sg, k) -> fmt_div fmt "mod" "%%" "\\zrem"  sg k

  | E.Osub  _ -> Format.fprintf fmt "-"

  | E.Oland _ -> Format.fprintf fmt "`&`"
  | E.Olor  _ -> Format.fprintf fmt "`|`"
  | E.Olxor _ -> Format.fprintf fmt "`^`"
  | E.Olsr  _ -> Format.fprintf fmt "`>>`"
  | E.Olsl  _ -> Format.fprintf fmt "`<<`"
  | E.Oasr  _ -> Format.fprintf fmt "`|>>`"
  | E.Orol _ -> Format.fprintf fmt "`|<<|`"
  | E.Oror _ -> Format.fprintf fmt "`|>>|`"

  | E.Oeq   _ -> Format.fprintf fmt "="
  | E.Oneq  _ -> Format.fprintf fmt "<>"
  | E.Olt s| E.Ogt s -> fmt_signed fmt "lt" "<" s
  | E.Ole s | E.Oge s -> fmt_signed fmt "le" "<=" s

  | Ovadd(ve,ws) -> fmt_vop2 fmt ("add", ve, ws)
  | Ovsub(ve,ws) -> fmt_vop2 fmt ("sub", ve, ws)
  | Ovmul(ve,ws) -> fmt_vop2 fmt ("mul", ve, ws)
  | Ovlsr(ve,ws) -> fmt_vop2 fmt ("shr", ve, ws)
  | Ovlsl(ve,ws) -> fmt_vop2 fmt ("shl", ve, ws)
  | Ovasr(ve,ws) -> fmt_vop2 fmt ("sar", ve, ws)
  | Owi2 _ -> assert false (* wint should have been removed by wint_int or wint_word *)

let fmt_access aa = if aa = Warray_.AAdirect then "_direct" else ""

(* ------------------------------------------------------------------- *)
(* Easycrypt AST pretty-printing *)

let pp_ec_ident fmt ident = Format.fprintf fmt "@[%a@]" (pp_list "." pp_string) ident

let rec pp_ec_ast_expr fmt e = match e with
    | Econst z ->
        if Z.leq Z.zero z then Format.fprintf fmt "%a" Z.pp_print z
        else Format.fprintf fmt "(%a)" Z.pp_print z
    | Ebool b -> pp_bool fmt b
    | Eident s -> pp_ec_ident fmt s
    | Eapp (f, ops) ->
            Format.fprintf fmt "@[(@,%a@,)@]"
            (Format.(pp_print_list ~pp_sep:(fun fmt () -> fprintf fmt "@ ")) pp_ec_ast_expr)
            (f::ops)
    | Efun1 (var, e) ->
            Format.fprintf fmt "@[(fun %s => %a)@]" var pp_ec_ast_expr e
    | Eop2 (op, e1, e2) -> pp_ec_op2 fmt (op, e1, e2)
    | Eop3 (op, e1, e2, e3) -> pp_ec_op3 fmt (op, e1, e2, e3)
    | Elist es -> Format.fprintf fmt "@[[%a]@]" (pp_list ";@ " pp_ec_ast_expr) es
    | Etuple es -> Format.fprintf fmt "@[(%a)@]" (pp_list ",@ " pp_ec_ast_expr) es

and pp_ec_op2 fmt (op2, e1, e2) =
    let f fmt = match op2 with
    | ArrayGet -> Format.fprintf fmt "@[%a.[%a]@]"
    | Plus -> Format.fprintf fmt "@[(%a +@ %a)@]"
    | Infix s -> (fun pp1 e1 -> Format.fprintf fmt "@[(%a %s@ %a)@]" pp1 e1 s)
    in
    (f fmt) pp_ec_ast_expr e1 pp_ec_ast_expr e2

and pp_ec_op3 fmt (op, e1, e2, e3) =
    let f fmt = match op with
    | Ternary -> Format.fprintf fmt "@[(%a ? %a : %a)@]"
    | If -> Format.fprintf fmt "@[(if %a then %a else %a)@]"
    | InORange -> Format.fprintf fmt "@[(%a <= %a < %a)@]"
    in
    (f fmt) pp_ec_ast_expr e1 pp_ec_ast_expr e2 pp_ec_ast_expr e3

let pp_ec_lvalue fmt (lval: ec_lvalue) =
    match lval with
    | LvIdent ident -> pp_ec_ident fmt ident
    | LvArrItem (ident, e) -> pp_ec_op2 fmt (ArrayGet, Eident ident, e)

let pp_ec_lvalues fmt (lvalues: ec_lvalues) =
    match lvalues with
    | [] -> assert false
    | [lv] -> pp_ec_lvalue fmt lv
    | _ -> Format.fprintf fmt "@[(%a)@]" (pp_list ",@ " pp_ec_lvalue) lvalues

let rec pp_ec_ast_stmt fmt stmt =
    Format.fprintf fmt "@[<v>%a@]" (pp_list "@ " pp_ec_ast_instr) stmt

and pp_ec_ast_instr fmt instr =
    match instr with
    | ESasgn (lv, e) -> Format.fprintf fmt "@[%a <-@ %a;@]" pp_ec_lvalues lv pp_ec_ast_expr e
    | EScall (lvs, f, args) ->
            let pp_res fmt lvs =
                if lvs = [] then
                    Format.fprintf fmt ""
                else
                    Format.fprintf fmt "%a <%@ " pp_ec_lvalues lvs
            in
            Format.fprintf fmt "@[%a%a (%a);@]"
                pp_res lvs
                pp_ec_ast_expr (Eident f)
                (pp_list ",@ " pp_ec_ast_expr) args
    | ESsample (lv, e) -> Format.fprintf fmt "@[%a <$@ %a;@]" pp_ec_lvalues lv pp_ec_ast_expr e
    | ESif (e, c1, c2) ->
            Format.fprintf fmt "@[<v>if (%a) {@   %a@ } else {@   %a@ }@]"
            pp_ec_ast_expr e pp_ec_ast_stmt c1 pp_ec_ast_stmt c2
    | ESwhile (e, c) ->
            Format.fprintf fmt "@[<v>while (%a) {@   %a@ }@]"
            pp_ec_ast_expr e pp_ec_ast_stmt c
    | ESreturn e -> Format.fprintf fmt "@[return %a;@]" pp_ec_ast_expr e
    | EScomment s -> Format.fprintf fmt "@[(* %s *)@]" s

let pp_ec_vdecl fmt (x, ty) = Format.fprintf fmt "%s:%a" x pp_string ty

let pp_ec_fun_decl fmt fdecl =
    let pp_ec_rty fmt rtys =
        if rtys = [] then Format.fprintf fmt "unit"
        else Format.fprintf fmt "@[%a@]" (pp_list " *@ " pp_string) rtys
    in
    Format.fprintf fmt
        "@[proc %s (@[%a@]) : @[%a@]@]"
        fdecl.fname
        (pp_list ",@ " pp_ec_vdecl) fdecl.args
        pp_ec_rty fdecl.rtys

let pp_ec_fun fmt f =
    let pp_decl_s fmt v = Format.fprintf fmt "var %a;" pp_ec_vdecl v in
    Format.fprintf fmt
        "@[<v>@[%a = {@]@   @[<v>%a@ %a@]@ }@]"
        pp_ec_fun_decl f.decl
        (pp_list "@ " pp_decl_s) f.locals
        pp_ec_ast_stmt  f.stmt

let pp_ec_item fmt it =
  let pp_option pp fmt = function
    | Some x -> pp fmt x
    | None -> ()
  in
  let pp_list_paren sep pp fmt xs =
    if xs = [] then ()
    else pp_paren (pp_list sep pp) fmt xs
  in
  match it with
  | IrequireImport is ->
    Format.fprintf fmt "@[require import@ @[%a@].@]" (pp_list "@ " pp_string) is
  | Iimport is ->
    Format.fprintf fmt "@[import@ @[%a@].@]" (pp_list "@ " pp_string) is
  | IfromImport (m, is) ->
    Format.fprintf fmt "@[from %s import@ @[%a@].@]" m (pp_list "@ " pp_string) is
  | IfromRequireImport (m, is) ->
    Format.fprintf fmt "@[from %s require import@ @[%a@].@]" m (pp_list "@ " pp_string) is
  | Iabbrev (a, e) ->
    Format.fprintf fmt "@[abbrev %s =@ @[%a@].@]" a pp_ec_ast_expr e
  | ImoduleType mt ->
    Format.fprintf fmt "@[<v>@[module type %s = {@]@   @[<v>%a@]@ }.@]"
      mt.name (pp_list "@ " pp_ec_fun_decl) mt.funs
  | Imodule m ->
    let pp_mp fmt (m, mt) = Format.fprintf fmt "%s:%s" m mt in
    Format.fprintf fmt "@[<v>@[module %s@[%a@]%a = {@]@   @[<v>%a%a%a@]@ }.@]"
      m.name
      (pp_list_paren ",@ " pp_mp) m.params
      (pp_option (fun fmt s -> Format.fprintf fmt " : %s" s)) m.ty
      (pp_list "@ " (fun fmt (v, t) -> Format.fprintf fmt "@[var %s : %s@]" v t)) m.vars
      (fun fmt _ -> if m.vars = [] then (Format.fprintf fmt "") else (Format.fprintf fmt "@ ")) ()
      (pp_list "@ " pp_ec_fun) m.funs

let pp_ec_prog fmt prog = Format.fprintf fmt "@[<v>%a@]" (pp_list "@ @ " pp_ec_item) prog

(* ------------------------------------------------------------------- *)
(* Array theory cloning *)

let fmt_array_decl fmt i =
  Format.fprintf fmt "@[<v>from Jasmin require import JArray.@ @ ";
  Format.fprintf fmt "clone export PolyArray as Array%i  with op size <- %i.@]@." i i

let fmt_warray_decl fmt i =
  Format.fprintf fmt "@[<v>from Jasmin require import JWord_array.@ @ ";
  Format.fprintf fmt "clone export WArray as WArray%i  with op size <- %i.@]@." i i

let fmt_op fmt (op_name, v) = Format.fprintf fmt "op %s <- %i" op_name v

let fmt_the fmt (th, v) = Format.fprintf fmt "theory %s <- %s" th v

let fmt_th fmt (th, v) = Format.fprintf fmt "theory %s <= %s" th v

let fmt_arraywords_decl fmt (aw: arraywords) =
  let arrayn = Format.sprintf "Array%i" aw.sizea in
  let warrayn = Format.sprintf "WArray%i" (aw.sizew*aw.sizea) in
  let fmt_insts fmt (aw: arraywords) =
    Format.fprintf fmt "%a,@ %a,@ %a,@ %a,@ %a"
    fmt_op ("sizeW", aw.sizew)
    fmt_op ("sizeA", aw.sizea)
    fmt_th ("Word", Format.sprintf "W%i" (8*aw.sizew))
    fmt_th ("ArrayN", arrayn)
    fmt_th ("WArrayN", warrayn)
  in
  Format.fprintf fmt "@[<v>from Jasmin require import JWord JWord_array.@ @ ";
  Format.fprintf fmt "@[<v>require import %s %s.@ @ " arrayn warrayn;
  Format.fprintf fmt "clone export ArrayWords as %s  with @[%a@].@]@."
    (fmt_array_theory (ArrayWords aw))
    fmt_insts aw

let fmt_subarray_decl fmt (s: subarray) =
  let arrays = Format.sprintf "Array%i" s.sizes in
  let arrayb = Format.sprintf "Array%i" s.sizeb in
  let fmt_insts fmt (s: subarray) =
    Format.fprintf fmt "%a,@ %a,@ %a,@ %a"
    fmt_op ("sizeS", s.sizes)
    fmt_op ("sizeB", s.sizeb)
    fmt_th ("ArrayS", arrays)
    fmt_th ("ArrayB", arrayb)
  in
  Format.fprintf fmt "@[<v>from Jasmin require import JArray.@ @ ";
  Format.fprintf fmt "@[<v>require import %s %s.@ @ " arrays arrayb;
  Format.fprintf fmt "clone export SubArray as %s  with @[%a@].@]@."
    (fmt_array_theory (SubArray s))
    fmt_insts s

let fmt_subarraydirect_decl fmt (s: subarraydirect) =
  let arrayws = fmt_array_theory (ArrayWords {sizew=s.sizew; sizea=s.sizes}) in
  let arraywb = fmt_array_theory (ArrayWords {sizew=s.sizew; sizea=s.sizeb}) in
  let fmt_insts fmt (s: subarraydirect) =
    Format.fprintf fmt "%a,@ %a,@ %a,@ %a,@ %a,@ %a"
    fmt_op ("sizeW", s.sizew)
    fmt_op ("sizeS", s.sizes)
    fmt_op ("sizeB", s.sizeb)
    fmt_the ("Word", Format.sprintf "W%i" (8*s.sizew))
    fmt_th ("ArrayWordsS", arrayws)
    fmt_th ("ArrayWordsB", arraywb)
  in
  Format.fprintf fmt "@[<v>from Jasmin require import JWord JWord_array.@ @ ";
  Format.fprintf fmt "@[<v>require import %s %s.@ @ " arrayws arraywb;
  Format.fprintf fmt "clone export SubArrayDirect as %s  with @[%a@].@]@."
    (fmt_array_theory (SubArrayDirect s))
    fmt_insts s

let fmt_subarraycast_decl fmt (s: subarraycast) =
  let arrayws = fmt_array_theory (ArrayWords {sizew=s.sizews; sizea=s.sizes}) in
  let arraywb = fmt_array_theory (ArrayWords {sizew=s.sizewb; sizea=s.sizeb}) in
  let fmt_insts fmt (s: subarraycast) =
    Format.fprintf fmt "%a,@ %a,@ %a,@ %a,@ %a,@ %a,@ %a,@ %a"
    fmt_op ("sizeWS", s.sizews)
    fmt_op ("sizeWB", s.sizewb)
    fmt_op ("sizeS", s.sizes)
    fmt_op ("sizeB", s.sizeb)
    fmt_the ("WordS", Format.sprintf "W%i" (8*s.sizews))
    fmt_the ("WordB", Format.sprintf "W%i" (8*s.sizewb))
    fmt_th ("ArrayWordsS", arrayws)
    fmt_th ("ArrayWordsB", arraywb)
  in
  Format.fprintf fmt "@[<v>from Jasmin require import JWord JWord_array.@ @ ";
  Format.fprintf fmt "@[<v>require import %s %s.@ @ " arrayws arraywb;
  Format.fprintf fmt "clone export SubArrayCast as %s  with @[%a@].@]@."
    (fmt_array_theory (SubArrayCast s))
    fmt_insts s

let fmt_arrayaccesscast_decl fmt (s: arrayaccesscast) =
  let arraywb = fmt_array_theory (ArrayWords {sizew=s.sizewb; sizea=s.sizeb}) in
  let fmt_insts fmt (s: arrayaccesscast) =
    Format.fprintf fmt "%a,@ %a,@ %a,@ %a,@ %a,@ %a"
    fmt_op ("sizeWS", s.sizews)
    fmt_op ("sizeWB", s.sizewb)
    fmt_op ("sizeB", s.sizeb)
    fmt_the ("WordS", Format.sprintf "W%i" (8*s.sizews))
    fmt_the ("WordB", Format.sprintf "W%i" (8*s.sizewb))
    fmt_th ("ArrayWordsB", arraywb)
  in
  Format.fprintf fmt "@[<v>from Jasmin require import JWord JWord_array.@ @ ";
  Format.fprintf fmt "@[<v>require import %s.@ @ " arraywb;
  Format.fprintf fmt "clone export ArrayAccessCast as %s  with @[%a@].@]@."
    (fmt_array_theory (ArrayAccessCast s))
    fmt_insts s

let fmt_bytearray_decl fmt n =
  Format.fprintf fmt "@[<v>from Jasmin require import JByte_array.@ @ ";
  Format.fprintf fmt "clone include ByteArray with op size <= %i.@]@." n

let fmt_subbytearray_decl fmt (s:subarray) =
  let arrays = fmt_array_theory (ByteArray s.sizes) in
  let arrayb = fmt_array_theory (ByteArray s.sizeb) in
  let fmt_insts fmt (s: subarray) =
    Format.fprintf fmt "%a,@ %a"
    fmt_th ("Asmall", arrays)
    fmt_th ("Abig", arrayb)
  in
  Format.fprintf fmt "@[<v>from Jasmin require import JByte_array.@ @ ";
  Format.fprintf fmt "@[<v>require import %s %s.@ @ " arrays arrayb;
  Format.fprintf fmt "clone SubByteArray as %s  with @[%a@].@]@."
    (fmt_array_theory (SubByteArray s))
    fmt_insts s

let save_array_theory ~prefix at =
  let fname = Format.sprintf "%s.ec" (fmt_array_theory at) in
  let path = Filename.concat prefix fname in
  let out = open_out path in
  let fmt = Format.formatter_of_out_channel out in
  match at with
    | Array n -> fmt_array_decl fmt n
    | WArray n -> fmt_warray_decl fmt n
    | ArrayWords aw -> fmt_arraywords_decl fmt aw
    | SubArray sa -> fmt_subarray_decl fmt sa
    | SubArrayDirect sad -> fmt_subarraydirect_decl fmt sad
    | SubArrayCast sac -> fmt_subarraycast_decl fmt sac
    | ArrayAccessCast asc -> fmt_arrayaccesscast_decl fmt asc
    | ByteArray n -> fmt_bytearray_decl fmt n
    | SubByteArray sa -> fmt_subbytearray_decl fmt sa
    ;
  close_out out

(* ------------------------------------------------------------------- *)
(* Easycrypt AST construction helpers *)

let add_ptr pd x e =
  (Prog.tu pd, Papp2 (E.Oadd ( E.Op_w pd), Pvar x, e))

let ec_ident s = Eident [s]
let ec_aget a i = Eop2 (ArrayGet, a, i)
let ec_int x = Econst (Z.of_int x)

let ec_vars (env: Env.t) (x: var) = Mv.find x (Env.vars env)
let ec_vari env (x:var) = Eident [ec_vars env x]

let glob_mem = ["Glob"; "mem"]
let glob_memi = Eident glob_mem

let ec_pd env = Eident [Format.sprintf "W%d" (int_of_ws (Env.pd env)); "to_uint"]

let ec_apps1 s e = Eapp (ec_ident s, [e])

let ec_zeroext_sz (szo, szi) e =
  let io, ii = int_of_ws szo, int_of_ws szi in
  if ii < io then ec_apps1 (Format.sprintf "zeroextu%i" io) e
  else if ii = io then e
  else (* io < ii *) ec_apps1 (Format.sprintf "truncateu%i" io) e

let ec_zeroext (t_o, t_i) e =
  if t_o = t_i then e else ec_zeroext_sz (ws_of_ty t_o, ws_of_ty t_i) e

let ec_Array env n = Env.add_Array env n; Format.sprintf "Array%i" n

let ec_WArray env n = Env.add_WArray env n; Format.sprintf "WArray%i" n

let ec_BArray env n = Env.add_BArray env n; Format.sprintf "BArray%i" n

let ec_SBArray env (s:subarray) =
  Env.add_SBArray env s;
  Format.sprintf "SBArray%i_%i" s.sizeb s.sizes

let toec_ty onarray env ty = match ty with
    | Bty Bool -> "bool"
    | Bty Int  -> "int"
    | Bty (U ws) -> Format.sprintf "%s.t" (fmt_Wsz ws)
    | Arr(ws,n) -> onarray env ws n

let onarray_ty_dfl env ws n =
  Format.sprintf "%s.t %s.t" (fmt_Wsz ws) (ec_Array env n)

let of_list_dfl env _ws n =
  Eapp (Eident [ec_Array env n; "of_list"], [ec_ident "witness"])

(* ------------------------------------------------------------------- *)
(* Extraction of array operations *)

module type EcArray = sig
  val ec_darray8: Env.t -> int -> ec_expr
  val ec_cast_array: Env.t -> wsize * int -> wsize * int -> ec_expr -> ec_expr
  val toec_pget: Env.t -> Memory_model.aligned * Warray_.arr_access * wsize * int gvar * ec_expr -> ec_expr
  val toec_psub: Env.t -> Warray_.arr_access * wsize * int * int ggvar * ec_expr -> ec_expr
  val toec_laset: Env.t -> Warray_.arr_access * wsize * int gvar * ec_expr -> ec_expr -> ec_instr
  val toec_lasub: Env.t -> Warray_.arr_access * wsize * int * int gvar L.located * ec_expr -> ec_expr -> ec_expr

  val onarray_ty: Env.t -> wsize -> int -> string
  val add_arr: Env.t -> wsize -> int -> unit
  val add_jarray: Env.t -> wsize -> int -> unit
  val of_list:  Env.t -> wsize -> int -> ec_expr

end


module EcArrayOld : EcArray = struct
  let ec_WArray_init env ws n =
        Eident [ec_WArray env (arr_size ws n); Format.sprintf "init%i" (int_of_ws ws)]

  let ec_WArray_initf env ws n f =
    let i = Env.create_name env "i" in
    Eapp (ec_WArray_init env ws n, [Efun1 (i, f i)])

  let ec_Array_init env len = Eident [ec_Array env len; "init"]

  let ec_initi env (x, n, ws) =
    let f i = ec_aget x (ec_ident i) in
    ec_WArray_initf env ws n f

  let ec_initi_var env (x, n, ws) = ec_initi env (ec_vari env x, n, ws)

  let ec_darray8 env n =
    let wa = ec_WArray env n in
    let eto = Efun1 ("a", Eapp (Eident [ec_Array env n; "init"], [
      Efun1 ("i", Eapp (Eident [wa; "get8"], [ec_ident "a"; ec_ident "i"]))
      ])) in
    Eapp (
            ec_ident "dmap",
            [Eident [ec_WArray env n; "darray"]; eto]
          )

  let ec_cast_array env (ws, n) (wse, ne) e =
    let i = Env.create_name env "i" in
    let geti = ec_ident (Format.sprintf "get%i" (int_of_ws ws)) in
    let init_fun = Efun1 (i, Eapp (geti, [ec_initi env (e, ne, wse); ec_ident i])) in
    Eapp (ec_Array_init env n, [init_fun])

  let toec_pget env (a, aa, ws, x, e) =
    let (xws, n) = array_kind x.v_ty in
    if ws = xws && aa = Warray_.AAscale then
       ec_aget (ec_vari env x) e
    else
      Eapp (
        (ec_ident (Format.sprintf "get%i%s" (int_of_ws ws) (fmt_access aa))),
        [ec_initi_var env (x, n, xws); e]
       )

  let toec_psub env (aa, ws, len, x, e) =
    assert (check_array env x.gv);
    let i = Env.create_name env "i" in
    let x = L.unloc x.gv in
    let (xws,n) = array_kind x.v_ty in
    if ws = xws && aa = Warray_.AAscale then
        Eapp (
            ec_Array_init env len,
            [
                Efun1 (i, ec_aget (ec_vari env x)  (Eop2 (Plus, e, ec_ident i)))
        ])
    else
        Eapp (
            ec_Array_init env len,
            [
                Efun1 (i,
                Eapp (ec_ident (Format.sprintf "get%i%s" (int_of_ws ws) (fmt_access aa)), [
                    ec_initi_var env (x, n, xws); Eop2 (Plus, e, ec_ident i)
            ])
                )
        ])

  let toec_laset env (aa, ws, x, e1) e =
    let (xws,n) = array_kind x.v_ty in
    if ws = xws && aa = Warray_.AAscale then
      ESasgn ([LvArrItem ([ec_vars env x], e1)], e)
    else
      let eset =
        let nws = n * int_of_ws xws in
        let warray = ec_WArray env (nws / 8) in
        let waget = Eident [warray; Format.sprintf "get%i" (int_of_ws xws)] in
        let wsi = int_of_ws ws in
        let waset = Eident [warray; Format.sprintf "set%i%s" wsi (fmt_access aa)] in
        let updwa = Eapp (waset, [ec_initi_var env (x, n, xws); e1; e]) in
        Eapp (ec_Array_init env n, [Eapp (waget, [updwa])]) in
      ESasgn ([LvIdent [ec_vars env x]], eset)

  let toec_lasub env (aa, ws, len, x, e1) e =
    assert (check_array env x);
    let x = L.unloc x in
    let (xws, n) = array_kind x.v_ty in
    if ws = xws && aa = Warray_.AAscale then
        let i = Env.create_name env "i" in
        let range_ub = Eop2 (Plus, e1, ec_int len) in
        Eapp (ec_Array_init env n, [
            Efun1 (i, Eop3 (
                If,
                Eop3 (InORange, e1, ec_ident i, range_ub),
                ec_aget e (Eop2 (Infix "-", ec_ident i, e1)),
                ec_aget (ec_vari env x) (ec_ident i)
                ))
        ])
    else
      let nws = n * int_of_ws xws in
      let nws8 = nws / 8 in
      let start =
        if aa = Warray_.AAscale then
          Eop2 (Infix "*", ec_int (int_of_ws ws / 8), e1)
        else
          e1
      in
      let len8 = len * int_of_ws ws / 8 in
      let i = Env.create_name env "i" in
      let in_range = Eop3 (InORange, start, ec_ident i, Eop2 (Plus, start, ec_int len8)) in
      let ainit = Eident [ec_WArray env nws8; "init8"] in
      let aw_get8 len = Eident [ec_WArray env len; "get8"] in
      let at = Eapp (aw_get8 len8, [ec_initi env (e, len, ws); Eop2 (Infix "-", ec_ident i, start)]) in
      let ae = Eapp (aw_get8 nws8, [ec_initi_var env (x, n, xws); ec_ident i]) in
      let a = Eapp (ainit, [Efun1 (i, Eop3 (If, in_range, at, ae))]) in
      let wag = Eident [ec_WArray env nws8; Format.sprintf "get%i" (int_of_ws xws)] in
      Eapp (ec_Array_init env n, [Eapp (wag, [a])])

  let onarray_ty = onarray_ty_dfl

  let add_arr env _ws n = Env.add_Array env n
  let add_jarray env ws n = Env.add_jarray env ws n

  let of_list =  of_list_dfl
end

module EcWArray: EcArray = struct
  let ec_darray8 env n =
    Env.add_ArrayWords env 1 n;
    let aw = fmt_array_theory (ArrayWords { sizew=1; sizea=n }) in
    let eto = Eident [aw; "to_word_array"] in
    Eapp (
            ec_ident "dmap",
            [Eident [ec_WArray env n; "darray"]; eto]
          )

  let ec_cast_array env (ws, n) (wse, ne) e =
    let sizews = ws2bytes ws in
    let sizewb = ws2bytes wse in
    Env.add_SubArrayCast env sizews sizewb n ne;
    let sa = fmt_array_theory (SubArrayCast { sizews; sizewb; sizes = n; sizeb = ne }) in
    Eapp (Eident [sa; "get_sub"], [e; ec_int 0])

  let toec_pget env (a, aa, ws, x, e) =
    let (xws,n) = array_kind x.v_ty in
    if ws = xws && aa = Warray_.AAscale then
       ec_aget (ec_vari env x) e
    else
      let sizews = ws2bytes ws in
      let sizewb = ws2bytes xws in
      Env.add_ArrayAccessCast env sizews sizewb n;
      let arrayaccesscast = fmt_array_theory (ArrayAccessCast { sizews; sizewb; sizeb = n }) in
      let getf = Format.sprintf "get_cast%s" (fmt_access aa) in
      Eapp (Eident [arrayaccesscast; getf], [ec_vari env x; e])

  let toec_psub env (aa, ws, len, x, e) =
    assert (check_array env x.gv);
    let x = L.unloc x.gv in
    let (xws,n) = array_kind x.v_ty in
    let subf =
      if ws = xws then
        if aa = Warray_.AAscale then begin
          (* Sub-array access aligned *)
          Env.add_SubArray env len n;
          let subarray = fmt_array_theory (SubArray { sizes = len; sizeb = n }) in
          Eident [subarray; "get_sub"]
        end else begin
          (* Sub-array access unaligned *)
          let sizew = ws2bytes ws in
          Env.add_SubArrayDirect env sizew len n;
          let sa = fmt_array_theory (SubArrayDirect { sizew; sizes = len; sizeb = n }) in
          Eident [sa; "get_sub_direct"]
        end
      else begin
        (* Sub-array access typecast (direct or not) *)
        let get_sub = if aa = Warray_.AAscale then "get_sub" else "get_sub_direct" in
        let sizews = ws2bytes ws in
        let sizewb = ws2bytes xws in
        Env.add_SubArrayCast env sizews sizewb len n;
        let sa = fmt_array_theory (SubArrayCast { sizews; sizewb; sizes = len; sizeb = n }) in
        Eident [sa; get_sub]
      end
    in
    Eapp (subf, [ec_vari env x; e])

  let toec_laset env (aa, ws, x, e1) e =
    let (xws,n) = array_kind x.v_ty in
    if ws = xws && aa = Warray_.AAscale then
      ESasgn ([LvArrItem ([ec_vars env x], e1)], e)
    else
      let eset =
        let sizews = ws2bytes ws in
        let sizewb = ws2bytes xws in
        Env.add_ArrayAccessCast env sizews sizewb n;
        let arrayaccesscast = fmt_array_theory (ArrayAccessCast { sizews; sizewb; sizeb = n }) in
        let setf = Format.sprintf "set_cast%s" (fmt_access aa) in
        let subf = Eident [arrayaccesscast; setf] in
        Eapp (subf, [ec_vari env x; e1; e]) in
      ESasgn ([LvIdent [ec_vars env x]], eset)

  let toec_lasub env (aa, ws, len, x, e1) e =
    assert (check_array env x);
    let x = L.unloc x in
    let (xws, n) = array_kind x.v_ty in
    let subf =
      if ws = xws then
        if aa = Warray_.AAscale then begin
          (* Sub-array update aligned *)
          Env.add_SubArray env len n;
          let subarray = fmt_array_theory (SubArray { sizes = len; sizeb = n }) in
          Eident [subarray; "set_sub"]
        end else begin
          (* Sub-array update unaligned *)
          let sizew = ws2bytes ws in
          Env.add_SubArrayDirect env sizew len n;
          let sa = fmt_array_theory (SubArrayDirect { sizew; sizes = len; sizeb = n }) in
          Eident [sa; "set_sub_direct"]
        end
      else begin
        (* Sub-array update typecast (direct or not) *)
        let set_sub = if aa = Warray_.AAscale then "set_sub" else "set_sub_direct" in
        let sizews = ws2bytes ws in
        let sizewb = ws2bytes xws in
        Env.add_SubArrayCast env sizews sizewb len n;
        let sa = fmt_array_theory (SubArrayCast { sizews; sizewb; sizes = len; sizeb = n }) in
        Eident [sa; set_sub]
      end
    in
    Eapp (subf, [ec_vari env x; e1; e])

  let onarray_ty = onarray_ty_dfl

  let add_arr env _ws n = Env.add_Array env n

  let add_jarray env ws n = Env.add_jarray env ws n

  let of_list =  of_list_dfl
end

module EcBArray : EcArray = struct
  let ec_darray8 (env: Env.t) (sz:int) =
    Eident [ec_BArray env sz; "darray"]

  let ec_cast_array (env:Env.t) (ws1, sz1) (ws2, sz2) e =
    assert (Prog.arr_size ws1 sz1 = Prog.arr_size ws2 sz2);
    e

  let direct aa =
    match aa with
    | Warray_.AAdirect -> "d"
    | Warray_.AAscale -> ""

  let scale aa ws =
    match aa with
    | Warray_.AAdirect -> ""
    | Warray_.AAscale -> Format.sprintf "%i" (int_of_ws ws)

  let toec_pget (env:Env.t) (a, aa, ws, x, ei) =
    let (xws, n) = array_kind x.v_ty in
    let sz = arr_size xws n in
    Eapp (Eident [ec_BArray env sz; Format.sprintf "get%i%s" (int_of_ws ws) (direct aa)],
          [ec_vari env x; ei])

  let toec_laset (env:Env.t) (aa, ws, x, ei) e =
    let (xws,n) = array_kind x.v_ty in
    let sz = arr_size xws n in
    let eset =
      Eapp (Eident [ec_BArray env sz; Format.sprintf "set%i%s" (int_of_ws ws) (direct aa)],
            [ec_vari env x; ei; e]) in
    ESasgn ([LvIdent [ec_vars env x]], eset)

  let toec_psub (env:Env.t) (aa, ws, len, x, ei) =
    let x = L.unloc x.gv in
    let (xws,n) = array_kind x.v_ty in
    let sizes = arr_size ws len in
    let sizeb = arr_size xws n in
    let s = { sizes; sizeb } in
    Eapp(Eident [ec_SBArray env s; Format.sprintf "get_sub%s" (scale aa ws)],
         [ec_vari env x; ei])

  let toec_lasub (env:Env.t) (aa, ws, len, x, ei) e =
    let x = L.unloc x in
    let (xws,n) = array_kind x.v_ty in
    let sizes = arr_size ws len in
    let sizeb = arr_size xws n in
    let s = { sizes; sizeb } in
    Eapp(Eident [ec_SBArray env s; Format.sprintf "set_sub%s" (scale aa ws)],
         [ec_vari env x; ei; e])

  let onarray_ty env ws n =
    Format.sprintf "%s.t" (ec_BArray env (arr_size ws n))

  let add_arr env ws n = Env.add_BArray env (arr_size ws n)

  let add_jarray = add_arr

  let of_list env ws n =
    Eident [ec_BArray env (arr_size ws n); Format.sprintf "of_list%i" (int_of_ws ws)]

end

(* ------------------------------------------------------------------- *)
(* Jasmin AST transformation and helpers *)

let base_op = function
  | Sopn.Oasm (Arch_extra.BaseOp (_, o)) -> Sopn.Oasm (Arch_extra.BaseOp(None,o))
  | o -> o

let ty_expr = function
  | Pconst _       -> tint
  | Pbool _        -> tbool
  | Parr_init len  -> Arr (U8, len)
  | Pvar x         -> x.gv.L.pl_desc.v_ty
  | Pload (_, sz,_,_) -> tu sz
  | Pget  (_,_, sz,_,_) -> tu sz
  | Psub (_,ws, len, _, _) -> Arr(ws, len)
  | Papp1 (op,_)   -> Conv.ty_of_cty (snd (E.type_of_op1 op))
  | Papp2 (op,_,_) -> Conv.ty_of_cty (snd (E.type_of_op2 op))
  | PappN (op, _)  -> Conv.ty_of_cty (snd (E.type_of_opN op))
  | Pif (ty,_,_,_) -> ty

let ty_sopn pd asmOp op es =
  match op with
  (* Do a special case for copy since the Coq type loose information  *)
  | Sopn.Opseudo_op (Pseudo_operator.Ocopy(ws, p)) ->
    let l = [Arr(ws, Conv.int_of_pos p)] in
    l, l
  | Sopn.Opseudo_op (Pseudo_operator.Oswap _) ->
    let l = List.map ty_expr es in
    l, l
  | _ ->
    List.map Conv.ty_of_cty (Sopn.sopn_tout pd asmOp op),
    List.map Conv.ty_of_cty (Sopn.sopn_tin pd asmOp op)

(* This code replaces for loop that modify the loop counter by while loop,
   it would be nice to prove in Coq the validity of the transformation *)

let is_write_lv x = function
  | Lnone _ | Lmem _ -> false
  | Lvar x' | Laset(_, _, _, x', _) | Lasub (_, _, _, x', _) ->
    V.equal x x'.L.pl_desc

let is_write_lvs x = List.exists (is_write_lv x)

let rec is_write_i x i =
  match i.i_desc with
  | Cassgn (lv,_,_,_) ->
    is_write_lv x lv
  | Copn(lvs,_,_,_) | Ccall(lvs, _, _) | Csyscall(lvs,_,_) ->
    is_write_lvs x lvs
  | Cif(_, c1, c2) | Cwhile(_, c1, _, _, c2) ->
    is_write_c x c1 || is_write_c x c2
  | Cfor(x',_,c) ->
    V.equal x x'.L.pl_desc || is_write_c x c

and is_write_c x c = List.exists (is_write_i x) c

let rec remove_for_i i =
  let i_desc =
    match i.i_desc with
    | Cassgn _ | Copn _ | Ccall _ | Csyscall _ -> i.i_desc
    | Cif(e, c1, c2) -> Cif(e, remove_for c1, remove_for c2)
    | Cwhile(a, c1, e, loc, c2) -> Cwhile(a, remove_for c1, e, loc, remove_for c2)
    | Cfor(j,r,c) ->
      let jd = j.pl_desc in
      if not (is_write_c jd c) then Cfor(j, r, remove_for c)
      else
        let jd' = V.clone jd in
        let j' = { j with pl_desc = jd' } in
        let ii' = Cassgn (Lvar j, E.AT_inline, jd.v_ty, Pvar (gkvar j')) in
        let ii' = { i with i_desc = ii' } in
        Cfor (j', r, ii' :: remove_for c)
  in
  { i with i_desc }
and remove_for c = List.map remove_for_i c

let ty_lval = function
  | Lnone (_, ty) -> ty
  | Lvar x -> (L.unloc x).v_ty
  | Lmem (_, ws,_,_) | Laset(_, _, ws, _, _) -> Bty (U ws)
  | Lasub (_,ws, len, _, _) -> Arr(ws, len)

module type EcExpression = sig
  val ec_cast: Env.t -> int gty * int gty -> ec_expr -> ec_expr
  val toec_cast: Env.t -> int gty * expr -> ec_expr
  val toec_expr: Env.t -> expr -> ec_expr
end
(* ------------------------------------------------------------------- *)
(* Jasmin AST -> Easycrypt AST *)
module EcExpression(EA: EcArray): EcExpression = struct
  (* ------------------------------------------------------------------- *)
  (* Extraction of expressions *)

  let ec_cast env (ty, ety) e =
      if ety = ty then e
      else
          match ty with
          | Bty _ -> ec_zeroext (ty, ety) e
          | Arr(ws, n) ->
              let wse, ne = array_kind ety in
              EA.ec_cast_array env (ws, n) (wse, ne) e

  let ec_op1 op e = match op with
    | E.Oword_of_int sz ->
      ec_apps1 (Format.sprintf "%s.of_int" (fmt_Wsz sz)) e
    | E.Oint_of_word(s, sz) ->
      ec_apps1 (Format.sprintf "%s.to_%sint" (fmt_Wsz sz) (string_of_signess s)) e
    | E.Osignext(szo,_szi) ->
      ec_apps1 (Format.sprintf "sigextu%i" (int_of_ws szo)) e
    | E.Ozeroext(szo,szi) -> ec_zeroext_sz (szo, szi) e
    | E.Onot     -> ec_apps1 "!" e
    | E.Olnot _  -> ec_apps1 "invw" e
    | E.Oneg _   -> ec_apps1 "-" e
    | E.Owi1 _ -> assert false (* wint should have been removed by wint_int or wint_word *)

  let rec toec_expr env (e: expr) =
      match e with
      | Pconst z -> Econst z
      | Pbool b -> Ebool b
      | Parr_init _n -> ec_ident "witness"
      | Pvar x -> ec_vari env (L.unloc x.gv)
      | Pget (a, aa, ws, y, e) ->
          EA.toec_pget env (a, aa, ws, L.unloc y.gv, toec_expr env e)
      | Psub (aa, ws, len, x, e) -> EA.toec_psub env (aa, ws, len, x, toec_expr env e)
      | Pload (_, sz, x, e) ->
          let load = ec_ident (Format.sprintf "loadW%i" (int_of_ws sz)) in
          Eapp (load, [
              glob_memi;
              Eapp (ec_pd env, [toec_cast env (add_ptr (Env.pd env) (gkvar x) e)])
          ])
      | Papp1 (op1, e) ->
            ec_op1 op1 (toec_cast env (Conv.ty_of_cty (fst (E.type_of_op1 op1)), e))
      | Papp2 (op2, e1, e2) ->
          let t1, t2 = fst (E.type_of_op2 op2) in
          let te1 = (Conv.ty_of_cty t1, e1) in
          let te2 = (Conv.ty_of_cty t2, e2) in
          let te1, te2 = match op2 with
            | E.Ogt _ | E.Oge _ -> te2, te1
            | _ -> te1, te2
          in
          let op = Infix (Format.asprintf "%a" fmt_op2 op2) in
          Eop2 (op, (toec_cast env te1), (toec_cast env te2))
      | PappN (op, es) ->
          begin match op with
          | Opack (ws, we) ->
              let i = int_of_pe we in
              let rec aux es =
                  match es with
                  | [] -> assert false
                  | [e] -> toec_expr env e
                  | e::es ->
                          let exp2i = Eop2 (Infix "^", Econst (Z.of_int 2), Econst (Z.of_int i)) in
                          Eop2 (
                              Infix "+",
                              Eop2 (Infix "%%", toec_expr env e, exp2i),
                              Eop2 (Infix "*", exp2i, aux es)
                              )
              in
              ec_apps1 (Format.sprintf "W%i.of_int" (int_of_ws ws)) (aux (List.rev es))
          | Ocombine_flags c ->
              Eapp (
                  ec_ident (Printer.string_of_combine_flags c),
                  List.map (toec_expr env) es
              )
          end
      | Pif(_,e1,et,ef) ->
          let ty = ty_expr e in
          Eop3 (
              Ternary,
              toec_expr env e1,
              toec_cast env (ty, et),
              toec_cast env (ty, ef)
          )

  and toec_cast env (ty, e) = ec_cast env (ty, ty_expr e) (toec_expr env e)
end

module type EcLeakage = sig
  val ec_leaks_es: Env.t -> exprs -> ec_instr list
  val ec_leaks_opn: Env.t -> exprs -> ec_instr list
  val ec_leaking_if: Env.t -> expr -> (Env.t -> ec_stmt) -> (Env.t -> ec_stmt) -> ec_stmt
  val ec_leaking_while: Env.t -> (Env.t -> ec_stmt) -> expr -> (Env.t -> ec_stmt) -> ec_stmt
  val ec_leaking_for: Env.t -> (Env.t -> ec_stmt) -> expr -> expr -> ec_stmt -> ec_expr -> ec_stmt -> ec_stmt
  val ec_leaks_lvs: Env.t -> int glval list -> ec_stmt
  val global_leakage_vars: Env.t -> (ec_modty * ec_modty) list
  val leakage_imports: Env.t -> ec_item list
  val ec_fun_leak_init: Env.t -> ec_stmt
  val ec_leak_ret: Env.t -> ec_expr list -> ec_expr list
  val ec_leak_rty: Env.t -> ec_ty list -> ec_ty list
  val ec_leak_call_lvs: Env.t -> ec_lvalues
  val ec_leak_call_acc: Env.t -> ec_stmt
end

module EcLeakNormal(EE: EcExpression): EcLeakage = struct
  let ec_leaks_es env es = []
  let ec_leaks_opn env es = []
  let ec_leaking_if env e c1 c2 = [ESif (EE.toec_expr env e, c1 env, c2 env)]
  let ec_leaking_while env c1 e c2 =
    c1 env @ [ESwhile (EE.toec_expr env e, (c2 env @ c1 env))]
  let ec_leaking_for env c e1 e2 init cond i_upd = init @ [ESwhile (cond, c env @ i_upd)]
  let ec_leaks_lvs env lvs = []
  let global_leakage_vars env = []
  let leakage_imports env = []
  let ec_fun_leak_init env = []
  let ec_leak_ret env ret = ret
  let ec_leak_rty env rtys = rtys
  let ec_leak_call_lvs env = []
  let ec_leak_call_acc env = []
end

module EcLeakConstantTimeGlobal(EE: EcExpression): EcLeakage = struct
  open EE

  let int_of_word ws e = Papp1 (E.Oint_of_word(Unsigned, ws), e)

  let rec leaks_e_rec pd leaks e =
    match e with
    | Pconst _ | Pbool _ | Parr_init _ |Pvar _ -> leaks
    | Pload (_,_,x,e) -> leaks_e_rec pd (int_of_word pd (snd (add_ptr pd (gkvar x) e)) :: leaks) e
    | Pget (_,_,_,_, e) | Psub (_,_,_,_,e) -> leaks_e_rec pd (e::leaks) e
    | Papp1 (_, e) -> leaks_e_rec pd leaks e
    | Papp2 (_, e1, e2) -> leaks_e_rec pd (leaks_e_rec pd leaks e1) e2
    | PappN (_, es) -> leaks_es_rec pd leaks es
    | Pif  (_, e1, e2, e3) -> leaks_e_rec pd (leaks_e_rec pd (leaks_e_rec pd leaks e1) e2) e3
  and leaks_es_rec pd leaks es = List.fold_left (leaks_e_rec pd) leaks es

  let leaks_e pd e = leaks_e_rec pd [] e
  let leaks_es pd es = leaks_es_rec pd [] es

  let ece_leaks_e env e = List.map (toec_expr env) (leaks_e (Env.pd env) e)

  let ec_newleaks leaks =
      let add_leak lacc l = Eop2 (Infix "::", l, lacc) in
      List.fold_left add_leak (ec_ident "leakages") leaks

  let ec_addleaks leaks = [ESasgn ([LvIdent ["leakages"]], ec_newleaks leaks)]

  let ec_leaks = function
    | [] -> []
    | es -> ec_addleaks [Eapp (ec_ident "LeakAddr", [Elist es])]

  let ec_leaks_es env es = ec_leaks (List.map (toec_expr env) (leaks_es (Env.pd env) es))

  let ec_leaks_opn env es =  ec_leaks_es env es

  let leak_cond env e = ec_addleaks [
    Eapp (ec_ident "LeakAddr", [Elist (ece_leaks_e env e)]);
    Eapp (ec_ident "LeakCond", [toec_expr env e])
  ]

  let ec_leaking_if env e c1 c2 =
    leak_cond env e @ [ESif (EE.toec_expr env e, c1 env, c2 env)]

  let ec_leaking_while env c1 e c2 =
    let le = leak_cond env e in
    c1 env @ le @ [ESwhile (EE.toec_expr env e, (c2 env @ c1 env @ le))]

  let ec_leaking_for env c e1 e2 init cond i_upd =
    let leaks = List.map (toec_expr env) (leaks_es (Env.pd env) [e1;e2]) in
    ec_addleaks [
        Eapp (ec_ident "LeakAddr", [Elist leaks]);
        Eapp (ec_ident "LeakFor", [Etuple [toec_expr env e1; toec_expr env e2]])
        ] @
    init @
    [ESwhile (cond, c env @ i_upd)]

  let leaks_lval pd = function
    | Lnone _ | Lvar _ -> []
    | Laset (_,_,_,_, e) | Lasub (_,_,_,_,e) -> leaks_e_rec pd [e] e
    | Lmem (_, _, x,e) -> leaks_e_rec pd [int_of_word pd (snd (add_ptr pd (gkvar x) e))] e

  let ec_leaks_lv env lv = ec_leaks (List.map (toec_expr env) (leaks_lval (Env.pd env) lv))

  let ec_leaks_lvs env lvs = List.concat_map (ec_leaks_lv env) lvs

  let global_leakage_vars env = [("leakages", "leakages_glob_t")]

  let leakage_imports env = [IfromRequireImport ("Jasmin", ["JLeakage"])]

  let ec_fun_leak_init env = []

  let ec_leak_ret env ret = ret

  let ec_leak_rty env rtys = rtys

  let ec_leak_call_lvs env = []

  let ec_leak_call_acc env = []
end

module EcLeakConstantTime(EE: EcExpression): EcLeakage = struct
  open EE

  let asgn s e = ESasgn ([LvIdent [s]], e)

  let int_of_word ws e = Papp1 (E.Oint_of_word(Unsigned, ws), e)

  let leak_addr e = Eapp (ec_ident "Leak_int", [e])

  let leak_val env e =
    let sty = match ty_expr e with
    | Bty Bool -> "bool"
    | Bty Int  -> "int"
    | Bty (U ws) -> fmt_Wsz ws
    | Arr(ws, n) -> assert false
    in
    let leakf = ec_ident (Format.sprintf "Leak_%s" sty) in
    [Eapp (leakf, [toec_expr env e])]


  let leak_addr_mem env x e =
    let addr = int_of_word (Env.pd env) (snd (add_ptr (Env.pd env) (gkvar x) e)) in
    [leak_addr (toec_expr env (addr))]

  let rec leaks_e_rec env leaks e =
    match e with
    | Pconst _ | Pbool _ | Parr_init _ | Pvar _ -> leaks
    | Pload (_,_,x,e) -> leaks_e_rec env ((leak_addr_mem env x e) @ leaks) e
    | Pget (_,_,_,_, e) | Psub (_,_,_,_,e) -> leaks_e_rec env ([leak_addr (toec_expr env e)] @ leaks) e
    | Papp1 (_, e) -> leaks_e_rec env leaks e
    | Papp2 (_, e1, e2) -> leaks_es_rec env leaks [e1; e2]
    | PappN (_, es) -> leaks_es_rec env leaks es
    | Pif  (_, e1, e2, e3) -> leaks_es_rec env leaks [e1; e2; e3]

  and leaks_es_rec env leaks es = List.fold_left (leaks_e_rec env) leaks es

  let leaks_e env e = leaks_e_rec env [] e

  let leaks_es env es = leaks_es_rec env [] es

  let leaklist leaks = Eapp (Eident ["LeakList"], [Elist leaks])

  let leaklistv leakv = Eapp (Eident ["LeakList"], [Eident [leakv]])

  let reset_leak vleak = [asgn vleak (Elist [])]

  let leakv_ty = "JLeakage.leakages"
  let leakacc_prefix = "leak"

  let start_leakacc env = reset_leak (Env.create_aux env leakacc_prefix leakv_ty)

  let leakacc env = Env.reuse_aux env leakacc_prefix leakv_ty

  let push_leak leakv leak =
    [asgn leakv (Eop2 (Infix "++", Eident [leakv], Elist [leak]))]

  let leak_block env c acc =
    let env_block = Env.new_aux_range env in
    let leak_reset = start_leakacc env_block in
    leak_reset @ (c env_block) @ (push_leak acc (leaklistv (leakacc env_block)))

  let ec_addleaks env leaks = match leaks with
    | [] -> []
    | _ -> push_leak (leakacc env) (leaklist leaks)

  let ec_leaks_es env es = ec_addleaks env (leaks_es env es)

  let leaks_lval env = function
    | Lnone _ | Lvar _ -> []
    | Laset (_,_,_,_, e) | Lasub (_,_,_,_,e) -> leaks_e_rec env [leak_addr (toec_expr env e)] e
    | Lmem (_, _, x,e) -> leaks_e_rec env (leak_addr_mem env x e) e

  let ec_leaks_lv env lv = ec_addleaks env (leaks_lval env lv)

  let ec_leaks_lvs env lvs = List.concat_map (ec_leaks_lv env) lvs

  let ec_leaks_opn env es = ec_addleaks env (leaks_es env es)

  let leak_cond env e = (leaks_e env e) @ (leak_val env e)

  let ec_leaking_if env e c1 c2 =
    let acc = leakacc env in
    ec_addleaks env (leak_cond env e) @
    [ESif (toec_expr env e, leak_block env c1 acc, leak_block env c2 acc)]

  let ec_leaking_while env c1 e c2 =
    let env = Env.new_aux_range env in
    let vleak_cond = Env.create_aux env "leak_cond" leakv_ty in
    (* We don't use leak_block since we need to check if c1 is empty. *)
    let env_c1 = Env.new_aux_range env in
    let c1 = c1 env_c1 in
    let (leaking_c1, reset_c1_leak, c1_leaklist) = if c1 = [] then
      ([], [], [])
    else
      let leak_c1 = Env.create_aux env "leak_b1" leakv_ty in
      let leak_start_c1 = start_leakacc env_c1 in
      (
        leak_start_c1 @ c1 @ push_leak leak_c1 (leaklistv (leakacc env_c1)),
        reset_leak leak_c1,
        [leaklistv leak_c1]
      )
    in
    let leak_c2 = Env.create_aux env (if c1 = [] then "_b" else "_b2") leakv_ty in
    let leaking_c2 = leak_block env c2 leak_c2 in
    let reset_c2_leak = reset_leak leak_c2 in
    reset_leak vleak_cond @ reset_c1_leak @ reset_c2_leak @
    leaking_c1 @
    push_leak vleak_cond (leaklist (leak_cond env e)) @
    [ESwhile (
      toec_expr env e,
      leaking_c2 @ leaking_c1 @ push_leak vleak_cond (leaklist (leak_cond env e))
    )] @
    push_leak (leakacc env) (leaklist (c1_leaklist @ [leaklistv vleak_cond; leaklistv leak_c2]))

  let leak_for_bounds env e1 e2 =
    leaks_es env [e1; e2] @ leak_val env e1 @ leak_val env e2

  let ec_leaking_for env c e1 e2 init cond i_upd =
    let leak_c = Env.create_aux env "leak_b" leakv_ty in
    reset_leak leak_c @
    ec_addleaks env (leak_for_bounds env e1 e2) @
    init @
    [ESwhile (cond, leak_block env c leak_c @ i_upd)] @
    push_leak (leakacc env) (leaklistv leak_c)

  let global_leakage_vars env = []

  let leakage_imports env = [IfromRequireImport ("Jasmin", ["JLeakage"])]

  let ec_fun_leak_init env = start_leakacc env

  let ec_leak_ret env ret =
    (env |> leakacc |> leaklistv) :: ret

  let leak_ret_ty = "JLeakage.leakage"
  let leak_ret_prefix = "leak_c"

  let ec_leak_rty env rtys = leak_ret_ty :: rtys

  let ec_leak_call_lvs env = [LvIdent [Env.create_aux env leak_ret_prefix leak_ret_ty]]

  let ec_leak_call_acc env =
    push_leak (leakacc env) (ec_ident (Env.reuse_aux env leak_ret_prefix leak_ret_ty))
end


module Extraction
  (EA: EcArray)
  (EL: EcLeakage) =
struct
  open EcExpression(EA)
  open EL
  (* ------------------------------------------------------------------- *)
  (* Extraction of lvals *)

  let ec_lvals env xs =
    let ec_lval env = function
      | Lnone _ | Lmem _ | Laset _ | Lasub _ -> assert false
      | Lvar x  -> LvIdent [ec_vars env (L.unloc x)]
    in
    List.map (ec_lval env) xs

  let toec_lval1 env lv e =
      match lv with
      | Lnone _ -> assert false
      | Lmem(_, ws, x, e1) ->
        let storewi = ec_ident (Format.sprintf "storeW%i" (int_of_ws ws)) in
        let addr = Eapp (ec_pd env, [toec_cast env (add_ptr (Env.pd env) (gkvar x) e1)]) in
        ESasgn ([LvIdent glob_mem], Eapp (storewi, [glob_memi; addr; e]))
      | Lvar x  ->
        let lvid = [ec_vars env (L.unloc x)] in
        ESasgn ([LvIdent lvid], e)
      | Laset (_, aa, ws, x, e1) ->
        let e1 = toec_expr env e1 in
        EA.toec_laset env (aa, ws, L.unloc x, e1) e
      | Lasub (aa, ws, len, x, e1) ->
        ESasgn (
          [LvIdent [ec_vars env (L.unloc x)]],
          EA.toec_lasub env (aa, ws, len, x, toec_expr env e1) e
          )

  let lvals_are_vars lvs = List.for_all (function Lvar _ -> true | _ -> false) lvs

  (* ------------------------------------------------------------------- *)
  (* Instruction extraction *)

  let toec_ty = toec_ty EA.onarray_ty

  let add_ty env = function
    | Bty _ -> ()
    | Arr (ws, n) -> EA.add_arr env ws n


  let ec_assgn env lv (etyo, etyi) e =
      let e = e |> ec_zeroext (etyo, etyi) |> ec_cast env (ty_lval lv, etyo) in
      toec_lval1 env lv e

  let ec_assgn_f env lvs etyso etysi f =
    let stmt = if lvals_are_vars lvs && (List.map ty_lval lvs) = etyso && etyso = etysi then
      [f (ec_lvals env lvs)]
      else
      let ec_typs = (List.map (toec_ty env) etysi) in
      let env = Env.new_aux_range env in
      let auxs = List.map (Env.create_aux env "aux") ec_typs in
      let s2lv s = LvIdent [s] in
      let call = f (List.map s2lv auxs) in
      let ec_auxs = List.map ec_ident auxs in
      let assgn lv (ets, e) = ec_assgn env lv ets e in
      let tyauxs = List.combine (List.combine etyso etysi) ec_auxs in
      let assgn_auxs = List.map2 assgn lvs tyauxs in
      call :: assgn_auxs
    in
    (ec_leaks_lvs env lvs) @ stmt

  let ec_pcall env lvs leak_lvs otys f args =
    if lvals_are_vars lvs && (List.map ty_lval lvs) = otys then
      (ec_leaks_lvs env lvs) @ [EScall (leak_lvs @ ec_lvals env lvs, f, args)]
    else
      ec_assgn_f env lvs otys otys (fun lvals -> EScall (leak_lvs @ lvals, f, args))

  let ec_expr_assgn env lvs etyso etysi e =
    if lvals_are_vars lvs && (List.map ty_lval lvs) = etyso && etyso = etysi then
      (ec_leaks_lvs env lvs) @ [ESasgn (ec_lvals env lvs, e)]
    else if List.length lvs = 1 then
      (ec_leaks_lvs env lvs) @ [ec_assgn env (List.hd lvs) (List.hd etyso, List.hd etysi) e]
    else
      ec_assgn_f env lvs etyso etysi (fun lvals -> ESasgn (lvals, e))

  let ec_syscall env o =
    match o with
    | Syscall_t.RandomBytes p ->
      let n = (Conv.int_of_pos p) in
      Env.add_randombytes env n;
      Format.sprintf "%s.randombytes_%i" syscall_mod_arg n

  let ec_opn pd asmOp o =
    let s = Format.asprintf "%a" (pp_opn pd asmOp) o in
    if Ss.mem s keywords then s^"_" else s

  let rec toec_cmd asmOp env c = List.flatten (List.map (toec_instr asmOp env) c)

  and toec_instr asmOp env i =
      match i.i_desc with
      | Cassgn (lv, _, _, (Parr_init _ as e)) ->
          (ec_leaks_es env [e]) @
          [toec_lval1 env lv (ec_ident "witness")]
      | Cassgn (lv, _, _, e) ->
          let tys = [ty_expr e] in
          (ec_leaks_es env [e]) @
          ec_expr_assgn env [lv] tys tys (toec_expr env e)
      | Copn ([], _, op, es) ->
          (ec_leaks_opn env es) @
          [EScomment (Format.sprintf "Erased call to %s" (ec_opn (Env.pd env) asmOp op))]
      | Copn (lvs, _, op, es) ->
          let op' = base_op op in
          (* Since we do not have merge for the moment only the output type can change *)
          let otys,itys = ty_sopn (Env.pd env) asmOp op es in
          let otys', _ = ty_sopn (Env.pd env) asmOp op' es in
          let ec_op op = ec_ident (ec_opn (Env.pd env) asmOp op) in
          let ec_e op = Eapp (ec_op op, List.map (toec_cast env) (List.combine itys es)) in
          (ec_leaks_opn env es) @
          (ec_expr_assgn env lvs otys otys' (ec_e op'))
      | Ccall (lvs, f, es) ->
          let env = Env.new_aux_range env in
          let otys, itys = Env.get_funtype env f in
          let args = List.map (toec_cast env) (List.combine itys es) in
          let leak_lvs = ec_leak_call_lvs env in
          (ec_leaks_es env es) @
          (ec_pcall env lvs leak_lvs otys [Env.get_funname env f] args) @
          (ec_leak_call_acc env)
      | Csyscall (lvs, o, es) ->
          let s = Syscall.syscall_sig_u o in
          let otys = List.map Conv.ty_of_cty s.scs_tout in
          let itys =  List.map Conv.ty_of_cty s.scs_tin in
          let args = List.map (toec_cast env) (List.combine itys es) in
          (ec_leaks_es env es) @
          (ec_pcall env lvs [] otys [ec_syscall env o] args)
      | Cif (e, c1, c2) ->
          let c1 env = toec_cmd asmOp env c1 in
          let c2 env = toec_cmd asmOp env c2 in
          ec_leaking_if env e c1 c2
      | Cwhile (_, c1, e, _, c2) ->
          let c1 env = toec_cmd asmOp env c1 in
          let c2 env = toec_cmd asmOp env c2 in
          ec_leaking_while env c1 e c2
      | Cfor (i, (d,e1,e2), c) ->
          let env = Env.new_aux_range env in
          (* decreasing for loops have bounds swaped *)
          let e1, e2 = if d = UpTo then e1, e2 else e2, e1 in
          let init, ec_e2 =
              match e2 with
              (* Can be generalized to the case where e2 is not modified by c and i *)
              | Pconst _ -> ([], toec_expr env e2)
              | _ ->
                  let aux = Env.create_aux env "inc" "int" in
                  let init = ESasgn ([LvIdent [aux]], toec_expr env e2) in
                  let ec_e2 = ec_ident aux in
                  [init], ec_e2 in
          let ec_i = [ec_vars env (L.unloc i)] in
          let lv_i = [LvIdent ec_i] in
          let init  = init @ [ESasgn (lv_i, toec_expr env e1)] in
          let ec_i1, ec_i2 =
              if d = UpTo then Eident ec_i , ec_e2
              else ec_e2, Eident ec_i in
          let i_upd_op = Infix (if d = UpTo then "+" else "-") in
          let i_upd = [ESasgn (lv_i, Eop2 (i_upd_op, Eident ec_i, Econst (Z.of_int 1)))] in
          let c env = toec_cmd asmOp env c in
          let cond = Eop2 (Infix "<", ec_i1, ec_i2) in
          ec_leaking_for env c e1 e2 init cond i_upd

  (* ------------------------------------------------------------------- *)
  (* Function extraction *)

  let var2ec_var env x = (List.hd [ec_vars env x], toec_ty env x.v_ty)

  let toec_fun asmOp env f =
      let f = { f with f_body = remove_for f.f_body } in
      let locals = Sv.elements (locals f) in
      let env = List.fold_left Env.set_var env (f.f_args @ locals) in
      (* Limit the scope of changes for aux variables to the current function. *)
      let env = Env.new_fun env in
      let init = ec_fun_leak_init env in
      let stmts = init @ (toec_cmd asmOp env f.f_body) in
      let ec_locals = (Env.aux_vars env) @ (List.map (var2ec_var env) locals) in
      let aux_locals_init = locals
          |> List.filter (fun x -> match x.v_ty with Arr _ -> true | _ -> false)
          |> List.sort (fun x1 x2 -> compare x1.v_name x2.v_name)
          |> List.map (fun x -> ESasgn ([LvIdent [ec_vars env x]], ec_ident "witness"))
      in
      let ret =
          let ec_var x = ec_vari env (L.unloc x) in
          match ec_leak_ret env (List.map ec_var f.f_ret) with
          | [x] -> ESreturn x
          | xs -> ESreturn (Etuple xs)
      in
      List.iter (Env.add_ty env) f.f_tyout;
      List.iter (fun x -> Env.add_ty env x.v_ty) (f.f_args @ locals);
      {
          decl = {
              fname = (Env.get_funname env f.f_name);
              args = List.map (var2ec_var env) f.f_args;
              rtys = ec_leak_rty env (List.map (toec_ty env) f.f_tyout);
          };
          locals = ec_locals;
          stmt = aux_locals_init @ stmts @ [ret];
      }

  (* ------------------------------------------------------------------- *)
  (* Program extraction *)

  let add_glob_arrsz env (x,d) =
    match d with
    | Global.Gword _ -> ()
    | Global.Garr(p,t) ->
      let ws, t = Conv.to_array x.v_ty p t in
      let n = Array.length t in
      Env.add_jarray env ws n

  let jmodel env = match Env.arch env with
    | X86_64 -> "JModel_x86"
    | ARM_M4 -> "JModel_m4"
    | RISCV  -> "JModel_riscv"

  let lib_slh env = match Env.arch env with
    | X86_64 -> "SLH64"
    | ARM_M4 -> "SLH32"
    | RISCV  -> "SLH32"

  let ec_glob_decl env (x,d) =
    let w_of_z ws z = Eapp (Eident [fmt_Wsz ws; "of_int"], [Econst z]) in
    let mk_abbrev e = Iabbrev (ec_vars env x, e) in
    match d with
    | Global.Gword(ws, w) -> mk_abbrev (w_of_z ws (Conv.z_of_word ws w))
    | Global.Garr(p,t) ->
      let ws, t = Conv.to_array x.v_ty p t in
      mk_abbrev (Eapp (EA.of_list env ws (Array.length t),
                       [Elist (List.map (w_of_z ws) (Array.to_list t))]))

  let ec_randombytes env =
      let randombytes_decl a n =
          let arr_ty = toec_ty env (Arr (U8, n)) in
          {
              fname = Format.sprintf "randombytes_%i" n;
              args = [(a, arr_ty)];
              rtys = [arr_ty];
          }
      in
      let randombytes_f n =
        let dmap = EA.ec_darray8 env n in
        { decl = randombytes_decl "a" n
        ; locals = []
        ; stmt = [ESsample ([LvIdent ["a"]], dmap); ESreturn (ec_ident "a")]
        }
      in
      let randombytes = Env.randombytes env in
      if List.is_empty randombytes then
        []
      else
        [
          ImoduleType {
            name = syscall_mod_sig;
              funs = List.map (randombytes_decl "_") randombytes;
          };
          Imodule {
            name = syscall_mod;
              params = [];
              ty = Some syscall_mod_sig;
              vars = [];
              funs = List.map randombytes_f randombytes;
          }
        ]

  let toec_prog env asmOp globs funcs =
      let add_glob_env env (x, d) =
        add_glob_arrsz env (x, d);
        Env.set_var env x
      in
      let add_arrsz env f =
        let add env x =
          match x.v_ty with
          | Arr(ws, n) -> EA.add_jarray env ws n
          | _ -> ()
        in
        let vars = vars_fc f in
        Sv.iter (add env) vars
      in
      let env = List.fold_left Env.set_fun env funcs in
      let env = List.fold_left add_glob_env env globs in
      List.iter (add_arrsz env) funcs;

      let funs = List.map (toec_fun asmOp env) funcs in

      let pp_array_theories ats = match Sarraytheory.elements ats with
          | [] -> []
          | l -> [IrequireImport (List.map fmt_array_theory l)]
      in
      let mod_arg =
          if List.is_empty (Env.randombytes env) then []
          else [(syscall_mod_arg, syscall_mod_sig)]
      in
      let glob_imports = [
          IrequireImport ["AllCore"; "IntDiv"; "CoreMap"; "List"; "Distr"];
          IfromRequireImport ("Jasmin", [jmodel env]);
          Iimport [lib_slh env];
      ] in
      let top_mod = Imodule {
          name = "M";
          params = mod_arg;
          ty = None;
          vars = global_leakage_vars env;
          funs;
      } in
      glob_imports @
      (leakage_imports env) @
      pp_array_theories (Env.array_theories env) @
      (List.map (fun glob -> ec_glob_decl env glob) globs) @
      (ec_randombytes env) @
      [top_mod]

  let pp_prog env asmOp fmt globs funcs =
    Format.fprintf fmt "%a@." pp_ec_prog (toec_prog env asmOp globs funcs)

end

(* ------------------------------------------------------------------- *)
(* Program extraction: find used functions and setup env data. *)

let rec used_func f =
  used_func_c Ss.empty f.f_body

and used_func_c used c =
  List.fold_left used_func_i used c

and used_func_i used i =
  match i.i_desc with
  | Cassgn _ | Copn _ | Csyscall _ -> used
  | Cif (_,c1,c2)     -> used_func_c (used_func_c used c1) c2
  | Cfor(_,_,c)       -> used_func_c used c
  | Cwhile(_, c1, _, _, c2) -> used_func_c (used_func_c used c1) c2
  | Ccall (_,f,_)   -> Ss.add f.fn_name used

let extract ((globs,funcs):('info, 'asm) prog) arch pd asmOp (model: model) amodel fnames array_dir fmt =
  let save_array_theories array_theories =
    match array_dir with
    | Some prefix ->
        begin
          Sarraytheory.iter (save_array_theory ~prefix) array_theories
    end
    | None -> ()
  in
  let fnames =
    match fnames with
    | [] -> List.map (fun { f_name ; _ } -> f_name.fn_name) funcs
    | fnames -> fnames
  in
  let funcs = List.map Regalloc.fill_in_missing_names funcs in
  let tokeep = ref (Ss.of_list fnames) in
  let dofun f =
    if Ss.mem f.f_name.fn_name !tokeep then
      (tokeep := Ss.union (used_func f) !tokeep; true)
    else false in
  let funcs = List.rev (List.filter dofun funcs) in
  let array_theories = ref Sarraytheory.empty in
  let env = Env.empty arch pd array_theories in
  let module EA: EcArray = (val match amodel with
    | ArrayOld -> (module EcArrayOld: EcArray)
    | WArray   -> (module EcWArray  : EcArray)
    | BArray   -> (module EcBArray  : EcArray)
  ) in
  let module EE = EcExpression(EA) in
  let module EL: EcLeakage = (val match model with
    | Normal -> (module EcLeakNormal(EE): EcLeakage)
    | ConstantTime -> (module EcLeakConstantTime(EE): EcLeakage)
    | ConstantTimeGlobal ->
        warning Deprecated Location.i_dummy
          "EasyCrypt extraction for constant-time in CTG mode is deprecated. Use the CT mode instead.";
        (module EcLeakConstantTimeGlobal(EE): EcLeakage)
  ) in
  let module E = Extraction(EA)(EL) in
  let prog = E.pp_prog env asmOp fmt globs funcs in
  save_array_theories (Env.array_theories env);
  prog
