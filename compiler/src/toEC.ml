open Utils
open Annotations
open Wsize
open Operators
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

type quantif =
  | Lforall
  | Lexists
  | Llambda

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
    | Equant  of quantif * string list * ec_expr
    | Eproj  of ec_expr * int  (* projection of a tuple *)
    | EHoare of ec_ident * ec_expr * ec_expr

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

type ec_ty =
  | Base of string
  | Tuple of ec_ty list

type ec_var = string * ec_ty

type ec_fun_decl = {
    fname: string;
    args: (string * ec_ty) list;
    rtys: ec_ty;
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
    vars: (string * ec_ty) list;
    funs: ec_fun list;
}

type ec_proposition =  string * string list * ec_expr

type ec_tactic_args =
  | Conti of ec_tactic
  | Seq of ec_tactic
  | Param of ec_tactic_args list
  | Form of ec_proposition
  | Ident of ec_ident
  | Pattern of string
  | Prop of string
  | DProp of ec_expr
  | Comment of string

and ec_tactic =
  { tname : string;
    targs : ec_tactic_args list;
    (* subgoals : ec_tactic list *)
  }

type ec_proof = ec_tactic list

type ec_item =
    | IrequireImport of string list
    | Iimport of string list
    | IfromImport of string * (string list)
    | IfromRequireImport of string * (string list)
    | Iabbrev of bool * string * ec_expr
    | ImoduleType of ec_module_type
    | Imodule of ec_module
    | Icomment of string
    | Axiom of  ec_proposition
    | Lemma of ec_proposition * ec_proof

type ec_prog = ec_item list


(* ------------------------------------------------------------------- *)
(* env: state of extraction *)

module type EnvT = sig
  type t
  val vars: t -> string Mv.t
  val pd: t -> Wsize.wsize
  val arch: t -> architecture
  val randombytes: t -> int list
  val set_fun: t -> (int, 'a, 'b) gfunc -> t
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
  val empty: architecture -> Wsize.wsize -> Sarraytheory.t ref -> bool -> t
  val create_name: t -> string -> string
  val array_theories: t -> Sarraytheory.t
  val get_funtype: t -> funname -> (ty list * ty list)
  val get_funname: t -> funname -> string
  val create_aux: t -> string -> ec_ty -> string
  val reuse_aux: t -> string -> ec_ty -> string
  val new_aux_range: t -> t
  val new_fun: t -> t
  val set_var: t -> var -> t
  val set_var_prefix : t -> var -> string -> t
  val set_var_prefix_u : t -> var -> string -> t
  val set_name_prefix: t -> string -> string * t
  val mk_var_prefix : t -> string -> int gty -> t * int gvar
  val aux_vars: t -> (string * ec_ty) list
  val get_args: t -> funname -> Ss.elt list
  val add_args: t -> funname -> ec_modty list -> unit

  (*old get get out if the environement*)
  val get_old: t -> funname -> Ss.elt list
  val add_old: t -> ec_modty list -> funname -> unit

  val get_proofv: t -> funname -> Ss.elt
  val add_proofv: t -> funname -> Ss.elt -> unit
  val get_tmplvs: t -> funname -> (Prog.var * ec_ty) list
  val add_tmplvs: t -> funname -> (Prog.var * ec_ty) list -> unit
  val get_all_tmplvs: t -> (Prog.var * ec_ty) list
  val get_ttmplvs: t -> funname -> (Ss.elt * ec_ty)
  val add_ttmplvs: t -> funname -> (Ss.elt * ec_ty) -> unit
  val get_all_ttmplvs: t -> (Ss.elt * ec_ty) list
  val get_contra: t -> funname -> (int Prog.gfcontract option)
  val add_contra: t -> (int, 'a, 'b) gfunc -> t
  val add_func: t -> funname -> t
  val get_func: t -> funname
  val add_sign: t -> bool -> t
  val get_sign: t -> bool
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
      tmplvs : ((Prog.var * ec_ty) list) Mf.t ref;
      ttmplvs : ((Ss.elt * ec_ty)) Mf.t ref;
      old : (Ss.elt list) Mf.t ref;
      args : (Ss.elt list) Mf.t ref;
      contra : (int Prog.gfcontract option) Mf.t;
      proofv : Ss.elt Mf.t ref;
      func : funname option;
      sign : bool
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

  let set_var_prefix env x s =
    let s = mkname env s in
    { env with
      alls = ref (Ss.add s !(env.alls));
      vars = Mv.add x s env.vars }

  let normalize_name n =
    n |> String.uncapitalize_ascii |> escape

  let set_var_prefix_u env x s =
    let s = String.uncapitalize_ascii s in
    { env with vars = Mv.add x s env.vars }

  let set_name_prefix env s =
    let s = normalize_name s in
    s , {env with alls = ref (Ss.add s !(env.alls))}

  let mk_var_prefix env s ty =
    let s = mkname env s in
    let v = CoreIdent.GV.mk s (Wsize.Stack Direct) ty L._dummy [] in
    let env = { env with
                alls = ref (Ss.add s !(env.alls));
                vars = Mv.add v s env.vars
              }
    in
    env , v

  let add_ty env = function
      | Bty _ -> ()
      | Arr (_ws, n) -> add_Array env n

  let empty arch pd array_theories sign =
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
      tmplvs = ref Mf.empty;
      ttmplvs = ref Mf.empty;
      old = ref Mf.empty;
      args = ref Mf.empty;
      contra = Mf.empty;
      proofv = ref Mf.empty;
      func = None;
      sign
    }

  let set_fun env fd =
    let s = mkname env fd.f_name.fn_name in
    let funs =
      Mf.add fd.f_name (s, (fd.f_tyout, fd.f_tyin)) env.funs in
    { env with funs; alls = ref (Ss.add s !(env.alls)) }

  let add_contra env fd =
      let contra = Mf.add fd.f_name fd.f_contra env.contra in
      { env with contra }

  

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

  let get_proofv env f =
    Mf.find f !(env.proofv)

  let add_proofv env f s =
    let p,env = set_name_prefix env s in
    env.proofv := Mf.add f p !(env.proofv)

  let get_tmplvs env f =
    Mf.find f !(env.tmplvs)

  let get_all_tmplvs env =
    Mf.fold (fun _ a acc -> a @ acc ) !(env.tmplvs) []

  let add_tmplvs env f tmps =
    env.tmplvs := Mf.add f tmps !(env.tmplvs)

  let get_ttmplvs env f =
    Mf.find f !(env.ttmplvs)

  let get_all_ttmplvs env =
    Mf.fold (fun _ a acc -> a :: acc ) !(env.ttmplvs) []

  let add_ttmplvs env f (s,typ) =
    let tmp,env = set_name_prefix env s in
    env.ttmplvs := Mf.add f (tmp,typ) !(env.ttmplvs)

  let get_contra env f =
    Mf.find f env.contra

  let get_args env f =
    Mf.find f !(env.args)

  let add_args env f args =
    env.args := Mf.add f args !(env.args)

  let get_old env f =
    Mf.find f !(env.old)

  let add_old env old f =
    env.old := Mf.add f old !(env.old)

  let get_func env =
    Option.get env.func

  let add_func env f =
    { env with func = Some f}

  let add_sign env b =
    {env with sign = b}

  let get_sign env =
    env.sign

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
    | Cmp_w (Signed, _)   -> Format.fprintf fmt "\\s%s" ws
    | Cmp_w (Unsigned, _) -> Format.fprintf fmt "\\u%s" ws
    | _                     -> Format.fprintf fmt "%s" is
  in
  let fmt_vop2 fmt (s,ve,ws) =
    Format.fprintf fmt "\\v%s%iu%i" s (int_of_velem ve) (int_of_ws ws)
  in
  match op with
  | Obeq   -> Format.fprintf fmt "="
  | Oand   -> Format.fprintf fmt "/\\"
  | Oor    -> Format.fprintf fmt "\\/"
  | Oadd _ -> Format.fprintf fmt "+"
  | Omul _ -> Format.fprintf fmt "*"
  | Odiv s -> fmt_signed fmt "div" "%/" s
  | Omod s -> fmt_signed fmt "mod" "%%" s

  | Osub  _ -> Format.fprintf fmt "-"

  | Oland _ -> Format.fprintf fmt "`&`"
  | Olor  _ -> Format.fprintf fmt "`|`"
  | Olxor _ -> Format.fprintf fmt "`^`"
  | Olsr  _ -> Format.fprintf fmt "`>>`"
  | Olsl  _ -> Format.fprintf fmt "`<<`"
  | Oasr  _ -> Format.fprintf fmt "`|>>`"
  | Orol _ -> Format.fprintf fmt "`|<<|`"
  | Oror _ -> Format.fprintf fmt "`|>>|`"

  | Oeq   _ -> Format.fprintf fmt "="
  | Oneq  _ -> Format.fprintf fmt "<>"
  | Olt s| Ogt s -> fmt_signed fmt "lt" "<" s
  | Ole s | Oge s -> fmt_signed fmt "le" "<=" s

  | Ovadd(ve,ws) -> fmt_vop2 fmt ("add", ve, ws)
  | Ovsub(ve,ws) -> fmt_vop2 fmt ("sub", ve, ws)
  | Ovmul(ve,ws) -> fmt_vop2 fmt ("mul", ve, ws)
  | Ovlsr(ve,ws) -> fmt_vop2 fmt ("shr", ve, ws)
  | Ovlsl(ve,ws) -> fmt_vop2 fmt ("shl", ve, ws)
  | Ovasr(ve,ws) -> fmt_vop2 fmt ("sar", ve, ws)

let fmt_access aa = if aa = Warray_.AAdirect then "_direct" else ""

let string_of_quant = function
  | Lforall -> "forall"
  | Lexists -> "exists"
  | Llambda -> "fun"

let rec pp_ec_ty fmt ty =
  match ty with
  | Base t -> Format.fprintf fmt "%s" t
  | Tuple tl ->
    if tl = [] then Format.fprintf fmt "unit"
    else Format.fprintf fmt "@[(%a)@]" (pp_list " *@ " pp_ec_ty) tl

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
    | Equant (q, i, f) ->
      begin
        match q with
        | Llambda ->
          Format.fprintf fmt "@[(%s %a =>@ %a)@]"
            (string_of_quant q) (pp_list " " pp_string) i pp_ec_ast_expr f
        | _ ->
          Format.fprintf fmt "@[%s %a,@ %a@]"
            (string_of_quant q) (pp_list " " pp_string) i pp_ec_ast_expr f
      end
    | Eproj (e,i) -> Format.fprintf fmt "@[%a.`%i@]" pp_ec_ast_expr e i
    | EHoare (i,fpre,fpost) ->
      Format.fprintf fmt "@[hoare [%a :@ @[%a ==>@ %a@]]@]"
        pp_ec_ident i
        (pp_ec_ast_expr) fpre
        (pp_ec_ast_expr) fpost

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

let pp_ec_vdecl fmt (x, ty) = Format.fprintf fmt "%s:%a" x pp_ec_ty ty

let pp_ec_fun_decl fmt fdecl =
    Format.fprintf fmt
        "@[proc %s (@[%a@]) : @[%a@]@]"
        fdecl.fname
        (pp_list ",@ " pp_ec_vdecl) fdecl.args
        pp_ec_ty fdecl.rtys

let pp_ec_fun fmt f =
    let pp_decl_s fmt v = Format.fprintf fmt "var %a;" pp_ec_vdecl v in
    Format.fprintf fmt
        "@[<v>@[%a = {@]@   @[<v>%a@ %a@]@ }@]"
        pp_ec_fun_decl f.decl
        (pp_list "@ " pp_decl_s) f.locals
        pp_ec_ast_stmt  f.stmt

let pp_ec_propostion fmt (n, b, e) =
  Format.fprintf fmt "@[%s @[%a@] :@ @[%a@]@]"
    n
    (pp_list " " pp_string) b
    pp_ec_ast_expr e

let rec pp_ec_tatic_args fmt args =
  match args with
  | Conti t -> Format.fprintf fmt "@[%a@]" pp_ec_rtactic t
  | Seq t -> Format.fprintf fmt "@[; %a@]" pp_ec_rtactic t
  | Param a -> Format.fprintf fmt "(@[%a@])" (pp_list " " pp_ec_tatic_args) a
  | Form f -> Format.fprintf fmt "@[%a@]" pp_ec_propostion f
  | Ident i -> Format.fprintf fmt "@[%a@]" pp_ec_ident i
  | Pattern s -> Format.fprintf fmt "@[%s@]" s
  | Prop s -> Format.fprintf fmt "@[%s@]" s
  | DProp e -> Format.fprintf fmt "@[%a@]" pp_ec_ast_expr e
  | Comment s -> Format.fprintf fmt "@[(* %s *)@]" s

and pp_ec_rtactic fmt t =
  Format.fprintf fmt "@[%s @[%a@]@]" t.tname (pp_list " " pp_ec_tatic_args) t.targs

let pp_ec_tactic fmt t =
  Format.fprintf fmt "@[%a@]." pp_ec_rtactic t

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
  | Iabbrev (p, a, e) ->
    let printing = if p then "[-printing]" else "" in
    Format.fprintf fmt "@[abbrev %s %s =@ @[%a@].@]" printing a pp_ec_ast_expr e
  | ImoduleType mt ->
    Format.fprintf fmt "@[<v>@[module type %s = {@]@   @[<v>%a@]@ }.@]"
      mt.name (pp_list "@ " pp_ec_fun_decl) mt.funs
  | Imodule m ->
    let pp_mp fmt (m, mt) = Format.fprintf fmt "%s:%s" m mt in
    Format.fprintf fmt "@[<v>@[module %s@[%a@]%a = {@]@   @[<v>%a%a%a@]@ }.@]"
      m.name
      (pp_list_paren ",@ " pp_mp) m.params
      (pp_option (fun fmt s -> Format.fprintf fmt " : %s" s)) m.ty
      (pp_list "@ " (fun fmt (v, t) -> Format.fprintf fmt "@[var %s : %a@]" v pp_ec_ty t)) m.vars
      (fun fmt _ -> if m.vars = [] then (Format.fprintf fmt "") else (Format.fprintf fmt "@ ")) ()
      (pp_list "@ " pp_ec_fun) m.funs
  | Icomment s -> Format.fprintf fmt "@[(* %s *)@]" s
  | Axiom p ->
    Format.fprintf fmt "@[axiom @[%a@].@]" pp_ec_propostion p
  | Lemma (p, t) ->
    Format.fprintf fmt "@[lemma @[%a@].@]@ @[proof.@]@ @[<v>%a@]"
      pp_ec_propostion p
      (pp_list "@ "pp_ec_tactic) t

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
  (Prog.tu pd, Papp2 (Oadd ( Op_w pd), Pvar x, e))

let ec_ident s = Eident [s]
let ec_aget a i = Eop2 (ArrayGet, a, i)
let ec_int x = Econst (Z.of_int x)

let ec_vars (env: Env.t) (x: var) =
  match Mv.find x (Env.vars env) with
  | e -> e
  | exception _ ->
    Format.printf "Notfound %s" x.v_name;
    assert false

let ec_vari env (x:var) = Eident [ec_vars env x]

let ec_lvals env xs =
  let ec_lval env = function
    | Lnone _ | Lmem _ | Laset _ | Lasub _ -> assert false
    | Lvar x  -> LvIdent [ec_vars env (L.unloc x)]
  in
  List.map (ec_lval env) xs

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
    | Bty Abstract s -> Format.sprintf "%s" s

let onarray_ty_dfl env ws n =
  Format.sprintf "%s.t %s.t" (fmt_Wsz ws) (ec_Array env n)

let of_list_dfl env _ws n =
  Eapp (Eident [ec_Array env n; "of_list"], [ec_ident "witness"])

let lvals_are_vars lvs = List.for_all (function Lvar _ -> true | _ -> false) lvs

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
  | Parr_init_elem (_,len)  -> Arr (U8, len)
  | Pvar x         -> x.gv.L.pl_desc.v_ty
  | Pload (_, sz,_,_) -> tu sz
  | Pget  (_,_, sz,_,_) -> tu sz
  | Psub (_,ws, len, _, _) -> Arr(ws, len)
  | Papp1 (op,_)   -> Conv.ty_of_cty (snd (E.type_of_op1 op))
  | Papp2 (op,_,_) -> Conv.ty_of_cty (snd (E.type_of_op2 op))
  | PappN (op, _)  -> Conv.ty_of_cty (snd (E.type_of_opNA op))
  | Pif (ty,_,_,_) -> ty
  | Pbig (_,_,_,_,_,_) -> assert false
  | Pis_var_init _ 
  | Pis_arr_init _
  | Pis_barr_init _
  | Pis_mem_init _ -> tbool

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
  | Cassert _ -> false
  | Cif(_, c1, c2) | Cwhile(_, c1, _, _, c2) ->
    is_write_c x c1 || is_write_c x c2
  | Cfor(x',_,c) ->
    V.equal x x'.L.pl_desc || is_write_c x c

and is_write_c x c = List.exists (is_write_i x) c

let rec remove_for_i i =
  let i_desc =
    match i.i_desc with
    | Cassgn _ | Copn _ | Ccall _ | Csyscall _ | Cassert _ -> i.i_desc
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
  val toec_lval1: Env.t -> int glval -> ec_expr -> ec_instr
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
    | Oword_of_int sz ->
      ec_apps1 (Format.sprintf "%s.of_int" (fmt_Wsz sz)) e
    | Oint_of_word sz ->
      ec_apps1 (Format.sprintf "%s.to_uint" (fmt_Wsz sz)) e
    | Osignext(szo,_szi) ->
      ec_apps1 (Format.sprintf "sigextu%i" (int_of_ws szo)) e
    | Ozeroext(szo,szi) -> ec_zeroext_sz (szo, szi) e
    | Onot     -> ec_apps1 "!" e
    | Olnot _  -> ec_apps1 "invw" e
    | Oneg _   -> ec_apps1 "-" e

  let rec toec_expr env (e: expr) =
      match e with
      | Pconst z -> Econst z
      | Pbool b -> Ebool b
      | Parr_init n -> ec_ident "witness"
      | Parr_init_elem (e,l) -> Eapp (Eident [ec_BArray env l; "init_arr"],[toec_expr env e; Econst (Z.of_int l)] )
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
            | Ogt _ | Oge _ -> te2, te1
            | _ -> te1, te2
          in
          let op = Infix (Format.asprintf "%a" fmt_op2 op2) in
          Eop2 (op, (toec_cast env te1), (toec_cast env te2))
      | PappN (OopN op, es) ->
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
      | PappN (Oabstract op, es) ->
              Eapp (ec_ident (op.pa_name), List.map (toec_expr env) es)

      | Pif(_,e1,et,ef) ->
          let ty = ty_expr e in
          Eop3 (
              Ternary,
              toec_expr env e1,
              toec_cast env (ty, et),
              toec_cast env (ty, ef)
            )
      | Pbig (e, Oand, v, a, b, Pbool true) ->
        let v = L.unloc v in
        let env = Env.set_var env v in
        let a = toec_expr env a in
        let b = toec_expr env b in
        let e = toec_expr env e in
        let f = toec_expr env (Pbool true) in
        let lambda1 = Equant (Llambda, ["_"], f) in
        let lambda2 = Equant(Llambda, [ec_vars env v],e) in
        let iota = Eapp (ec_ident "iota_", [a; b]) in
        Eapp (ec_ident "BBAnd.big", [lambda1;lambda2;iota])
      | Pbig (e, Oor, v, a, b, Pbool false) ->
        let v = L.unloc v in
        let env = Env.set_var env v in
        let a = toec_expr env a in
        let b = toec_expr env b in
        let e = toec_expr env e in
        let f = toec_expr env (Pbool true) in
        let lambda1 = Equant (Llambda, ["_"], f) in
        let lambda2 = Equant(Llambda, [ec_vars env v],e) in
        let iota = Eapp (ec_ident "iota_", [a; b]) in
        Eapp (ec_ident "BBOr.big", [lambda1;lambda2;iota])
      | Pbig (e, op, v, a, b, i) ->
        let v = L.unloc v in
        let env = Env.set_var env v in
        let op = Infix (Format.asprintf "%a" fmt_op2 op) in
        let acc = "acc" and x = "x" in
        let expr = Eop2 (op, Eident [x], Eident [acc]) in
        let lambda1 = Equant (Llambda, [acc], expr) in
        let lambda1 = Equant (Llambda, [x], lambda1) in
        let i = toec_expr env i in
        let a = toec_expr env a in
        let b = toec_expr env b in
        let e = toec_expr env e in
        let lambda2 = Equant(Llambda, [ec_vars env v],e) in
        let iota = Eapp (ec_ident "iota_", [a; b]) in
        let map = Eapp (ec_ident "map", [lambda2;iota]) in
        Eapp (ec_ident "foldr", [lambda1;i; map])
      | Pis_var_init _ 
      | Pis_arr_init _ -> assert false
      | Pis_barr_init (x,e1,e2) -> Eapp (ec_ident "is_init",[ec_vari env (L.unloc x); toec_expr env e1;toec_expr env e2] )
      | Pis_mem_init (e1,e2) -> Eapp (ec_ident "is_valid", [Eapp (ec_pd env, [toec_expr env e1]) ; toec_expr env e2])

  and toec_cast env (ty, e) = ec_cast env (ty, ty_expr e) (toec_expr env e)

  (* ------------------------------------------------------------------- *)
  (* Extraction of lvals *)

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

end

module type EcLeakage = sig
  val ec_leaks_es: Env.t -> exprs -> ec_instr list
  val ec_leaks_opn: Env.t -> exprs -> ec_instr list
  val ec_leaking_if: Env.t -> expr -> (Env.t -> ec_stmt) -> (Env.t -> ec_stmt) -> ec_stmt
  val ec_leaking_while: Env.t -> (Env.t -> ec_stmt) -> expr -> (Env.t -> ec_stmt) -> ec_stmt
  val ec_leaking_for: Env.t -> (Env.t -> ec_stmt) -> expr -> expr -> ec_stmt -> ec_expr -> ec_stmt -> ec_stmt
  val ec_leaks_lvs: Env.t -> int glval list -> ec_stmt
  val global_leakage_vars: Env.t -> (ec_modty * ec_ty) list
  val leakage_imports: Env.t -> ec_item list
  val ec_fun_leak_init: Env.t -> ec_stmt
  val ec_leak_ret: Env.t -> ec_expr list -> ec_expr list
  val ec_leak_rty: Env.t -> ec_ty list -> ec_ty list
  val ec_leak_call_lvs: Env.t -> ec_lvalues
  val ec_leak_call_acc: Env.t -> ec_stmt
end

module EcLeakConstantTimeGlobal(EE: EcExpression): EcLeakage = struct
  open EE

  let int_of_word ws e = Papp1 (Oint_of_word ws, e)

  let rec leaks_e_rec pd leaks e =
    match e with
    | Pconst _ | Pbool _ | Parr_init _ | Pvar _ | Pis_var_init _ -> leaks
    | Pload (_,_,x,e) -> leaks_e_rec pd (int_of_word pd (snd (add_ptr pd (gkvar x) e)) :: leaks) e
    | Pget (_,_,_,_, e) | Psub (_,_,_,_,e) -> leaks_e_rec pd (e::leaks) e
    | Parr_init_elem (e,_) | Papp1 (_, e) -> leaks_e_rec pd leaks e
    | Papp2 (_, e1, e2) -> leaks_e_rec pd (leaks_e_rec pd leaks e1) e2
    | PappN (_, es) -> leaks_es_rec pd leaks es
    | Pif  (_, e1, e2, e3) -> leaks_e_rec pd (leaks_e_rec pd (leaks_e_rec pd leaks e1) e2) e3
    | Pbig _ -> assert false
    | Pis_arr_init(_,e1,e2)
    | Pis_barr_init(_,e1,e2) -> leaks_e_rec pd (leaks_e_rec pd leaks e1) e2
    | Pis_mem_init(e1,e2) -> leaks_e_rec pd (leaks_e_rec pd leaks e1) e2
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

  let global_leakage_vars env = [("leakages", Base "leakages_glob_t")]

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

  let int_of_word ws e = Papp1 (Oint_of_word ws, e)

  let leak_addr e = Eapp (ec_ident "Leak_int", [e])

  let leak_val env e =
    let sty = match ty_expr e with
    | Bty Bool -> "bool"
    | Bty Int  -> "int"
    | Bty (U ws) -> fmt_Wsz ws
    | Arr(ws, n) -> assert false
    | Bty Abstract _ -> assert false
    in
    let leakf = ec_ident (Format.sprintf "Leak_%s" sty) in
    [Eapp (leakf, [toec_expr env e])]


  let leak_addr_mem env x e =
    let addr = int_of_word (Env.pd env) (snd (add_ptr (Env.pd env) (gkvar x) e)) in
    [leak_addr (toec_expr env (addr))]

  let rec leaks_e_rec env leaks e =
    match e with
    | Pconst _ | Pbool _ | Parr_init _ |Pvar _ | Pis_var_init _ -> leaks
    | Pload (_,_,x,e) -> leaks_e_rec env ((leak_addr_mem env x e) @ leaks) e
    | Pget (_,_,_,_, e) | Psub (_,_,_,_,e) -> leaks_e_rec env ([leak_addr (toec_expr env e)] @ leaks) e
    | Parr_init_elem (e,_) | Papp1 (_, e) -> leaks_e_rec env leaks e
    | Papp2 (_, e1, e2) -> leaks_es_rec env leaks [e1; e2]
    | PappN (_, es) -> leaks_es_rec env leaks es
    | Pif  (_, e1, e2, e3) -> leaks_es_rec env leaks [e1; e2; e3]
    | Pbig (_, _, _, _, _, _) -> assert false
    | Pis_arr_init(_,e1,e2)
    | Pis_barr_init(_,e1,e2) -> leaks_es_rec env leaks [e1; e2]
    | Pis_mem_init(e1,e2) -> leaks_es_rec env leaks [e1; e2]

  and leaks_es_rec env leaks es = List.fold_left (leaks_e_rec env) leaks es

  let leaks_e env e = leaks_e_rec env [] e

  let leaks_es env es = leaks_es_rec env [] es

  let leaklist leaks = Eapp (Eident ["LeakList"], [Elist leaks])

  let leaklistv leakv = Eapp (Eident ["LeakList"], [Eident [leakv]])

  let reset_leak vleak = [asgn vleak (Elist [])]

  let leakv_ty = Base "JLeakage.leakages"
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

  let leak_ret_ty = Base "JLeakage.leakage"
  let leak_ret_prefix = "leak_c"

  let ec_leak_rty env rtys = leak_ret_ty :: rtys

  let ec_leak_call_lvs env = [LvIdent [Env.create_aux env leak_ret_prefix leak_ret_ty]]

  let ec_leak_call_acc env =
    push_leak (leakacc env) (ec_ident (Env.reuse_aux env leak_ret_prefix leak_ret_ty))
end

module type Model = sig

  module EA : EcArray

  val toec_ty:  Env.t -> int gty -> ec_ty
  val toec_expr_assign: Env.t -> lval -> expr -> ec_stmt
  val toec_copn_era: Env.t -> expr list -> ec_stmt
  val toec_copn :
    Env.t -> lval list ->
    ('a, 'b, 'c, 'd, 'e, 'f, 'g) Arch_extra.extended_op Sopn.asmOp ->
    ('a, 'b, 'c, 'd, 'e, 'f, 'g) Arch_extra.extended_op Sopn.sopn ->
    exprs -> ec_stmt
  val toec_call: Env.t -> int glval list -> funname -> exprs -> ec_instr list
  val toec_syscall:
    Env.t ->
    int glval list ->
    BinNums.positive Syscall_t.syscall_t -> exprs -> ec_instr list
  val toec_assert: Env.t -> E.annotation_kind -> expr -> ec_instr list
  val toec_if: Env.t -> expr -> (Env.t -> ec_stmt) -> (Env.t -> ec_stmt) -> ec_stmt
  val toec_while: Env.t -> (Env.t -> ec_stmt) -> expr -> (Env.t -> ec_stmt) -> ec_stmt
  val toec_for: Env.t ->
    var L.located ->
    E.dir * expr * expr -> (Env.t -> ec_stmt) -> ec_stmt
  val fun_init: Env.t -> (int, 'a, 'b) gfunc -> ec_stmt * ec_stmt * (ec_modty * ec_ty) list * Env.t
  val fun_ret: Env.t -> funname -> ec_expr list -> ec_expr list
  val fun_rty: Env.t -> ec_ty list -> ec_ty list
  val global_vars: Env.t -> (ec_modty * ec_ty) list
  val import: Env.t -> ec_item list
  val init_env: Env.t -> ((int, 'a, 'b) gfunc) list -> Env.t
  val final: Env.t -> ((int, 'a, 'b) gfunc) list  -> ec_item list

end

module Normal (EA: EcArray):Model = struct
  open EcExpression(EA)

  module EA = EA

  let toec_ty env ty = Base (toec_ty EA.onarray_ty env ty)

  let ec_assgn env lv (etyo, etyi) e =
    let e = e |> ec_zeroext (etyo, etyi) |> ec_cast env (ty_lval lv, etyo) in
    toec_lval1 env lv e

  let ec_assgn_f env lvs etyso etysi f =
    if lvals_are_vars lvs && (List.map ty_lval lvs) = etyso && etyso = etysi then
      [f (ec_lvals env lvs)]
    else
      let ec_typs = (List.map (fun ty -> toec_ty env ty) etysi) in
      let env = Env.new_aux_range env in
      let auxs = List.map (Env.create_aux env "aux") ec_typs in
      let s2lv s = LvIdent [s] in
      let call = f (List.map s2lv auxs) in
      let ec_auxs = List.map ec_ident auxs in
      let assgn lv (ets, e) = ec_assgn env lv ets e in
      let tyauxs = List.combine (List.combine etyso etysi) ec_auxs in
      let assgn_auxs = List.map2 assgn lvs tyauxs in
      call :: assgn_auxs

  let ec_expr_assgn env lvs etyso etysi e =
    if lvals_are_vars lvs && (List.map ty_lval lvs) = etyso && etyso = etysi then
      [ESasgn (ec_lvals env lvs, e)]
    else if List.length lvs = 1 then
      [ec_assgn env (List.hd lvs) (List.hd etyso, List.hd etysi) e]
    else
      ec_assgn_f env lvs etyso etysi (fun lvals -> ESasgn (lvals, e))

  let toec_expr_assign env lv e =
    match e with
    | Parr_init _ ->
      [toec_lval1 env lv (ec_ident "witness")]
    | _ ->
      let tys = [ty_expr e] in
      ec_expr_assgn env [lv] tys tys (toec_expr env e)

  let toec_copn_era env eq = []

  let ec_opn pd asmOp o =
    let s = Format.asprintf "%a" (pp_opn pd asmOp) o in
    if Ss.mem s keywords then s^"_" else s

  let toec_copn env lvs asmOp op es =
    let op' = base_op op in
    (* Since we do not have merge for the moment only the output type can change *)
    let otys,itys = ty_sopn (Env.pd env) asmOp op es in
    let otys', _ = ty_sopn (Env.pd env) asmOp op' es in
    let ec_op op = ec_ident (ec_opn (Env.pd env) asmOp op) in
    let ec_e op = Eapp (ec_op op, List.map (toec_cast env) (List.combine itys es)) in
    (ec_expr_assgn env lvs otys otys' (ec_e op'))

  let ec_pcall env lvs otys f args =
    if (List.map ty_lval lvs) = otys then
      [EScall (ec_lvals env lvs, f, args)]
    else
      ec_assgn_f env lvs otys otys (fun lvals -> EScall (lvals, f, args))

  let toec_call env lvs f es =
    let env = Env.new_aux_range env in
    let otys, itys = Env.get_funtype env f in
    let args = List.map (toec_cast env) (List.combine itys es) in
    (ec_pcall env lvs otys [Env.get_funname env f] args)

  let ec_syscall env o =
    match o with
    | Syscall_t.RandomBytes p ->
      let n = (Conv.int_of_pos p) in
      Env.add_randombytes env n;
      Format.sprintf "%s.randombytes_%i" syscall_mod_arg n

  let toec_syscall env lvs o es =
    let s = Syscall.syscall_sig_u o in
    let otys = List.map Conv.ty_of_cty s.scs_tout in
    let itys =  List.map Conv.ty_of_cty s.scs_tin in
    let args = List.map (toec_cast env) (List.combine itys es) in
    (ec_pcall env lvs otys [ec_syscall env o] args)

  let toec_assert env k e = []

  let toec_if env e c1 c2 = [ESif (toec_expr env e, c1 env, c2 env)]

  let toec_while env c1 e c2 =
    c1 env @ [ESwhile (toec_expr env e, (c2 env @ c1 env))]

  let toec_for env i (d,e1,e2) c =
    let env = Env.new_aux_range env in
    (* decreasing for loops have bounds swaped *)
    let e1, e2 = if d = Expr.UpTo then e1, e2 else e2, e1 in
    let init, ec_e2 =
      match e2 with
      (* Can be generalized to the case where e2 is not modified by c and i *)
      | Pconst _ -> ([], toec_expr env e2)
      | _ ->
        let aux = Env.create_aux env "inc" (Base "int") in
        let init = ESasgn ([LvIdent [aux]], toec_expr env e2) in
        let ec_e2 = ec_ident aux in
        [init], ec_e2 in
    let ec_i = [ec_vars env (L.unloc i)] in
    let lv_i = [LvIdent ec_i] in
    let init  = init @ [ESasgn (lv_i, toec_expr env e1)] in
    let ec_i1, ec_i2 =
      if d = Expr.UpTo then Eident ec_i , ec_e2
      else ec_e2, Eident ec_i in
    let i_upd_op = Infix (if d = Expr.UpTo then "+" else "-") in
    let i_upd = [ESasgn (lv_i, Eop2 (i_upd_op, Eident ec_i, Econst (Z.of_int 1)))] in
    let cond = Eop2 (Infix "<", ec_i1, ec_i2) in
    init @ [ESwhile (cond, c env @ i_upd)]

  let fun_init env f = [],[],[],env
  let fun_ret env _ ret = ret
  let fun_rty env rtys = rtys
  let global_vars env = []
  let import env = []
  let init_env env funcs = env
  let final env funcs = []
end

module Annotations (EA: EcArray) : Model =
struct
  module EC = EcExpression(EA)
  include Normal(EA)

  let fand a b = Eop2 (Infix "/\\", a, b)

  let fun_ret env name ret = 
    let trace = Env.get_proofv env name in
    Etuple(ret) :: [Eident [trace]]

  let fun_rty env rtyps = Tuple(rtyps) :: [Base "trace"]
  
  let ec_kind = function
  | Expr.Assume -> ["Assume"]
  | Assert -> ["Assert"]
  | _ -> assert false

  let ec_trace env k e =
    let k = ec_kind k in
    let f =  Env.get_func env in
    let p = Env.get_proofv env f in
    let e = EC.toec_expr env e in
    let e1 = Eop2 (Infix "++", Eident [p], Elist [Etuple [Eident k;e]]) in
    let i = ESasgn ([LvIdent ([p])],e1) in
    [i]

  let toec_assert env k e =
    ec_trace env k e 

  let sub_contra args params =
    let aux f =
      List.map (fun (prover,clause) -> prover, f clause)
    in
    let check v vi=
      (L.unloc v.gv).v_name = vi.v_name && (L.unloc v.gv).v_id = vi.v_id
    in
    let aux1 v =
      match List.findi (fun _ vi -> check v vi) args with
      | i,_ ->
        let _,e = List.findi (fun ii _ -> ii = i) params in
        e
      | exception _ ->  Pvar v
    in
    aux (Subst.gsubst_e (fun ?loc:_ x -> x) aux1)

  let get_pre = function
    | None -> []
    | Some f -> f.f_pre

  let get_post = function
    | None -> []
    | Some f -> f.f_post

  let get_iparams = function
    | None -> []
    | Some f -> f.f_iparams

  let get_ires = function
    | None -> []
    | Some f -> f.f_ires

  let contrat env c =
    let c = List.map (fun (_,x) -> x) c in
    if List.is_empty c then
      Ebool true
    else
      let c = List.map (EC.toec_expr env) c in
      List.fold_left (fun acc a -> Eop2 (Infix "/\\", a, acc) ) (List.hd c) (List.tl c)

  let var_eq vars1 vars2 =
    if List.length vars1 = 0 then
      Ebool true
    else
      let vars = List.map2 (fun a b -> (a,b)) vars1 vars2 in
      let eq (var1,var2) =
        Eop2 (Infix "=", ec_ident var1, ec_ident var2)
      in
      List.fold_left
        (fun acc a -> Eop2 (Infix "/\\", eq a, acc))
        (eq (List.hd vars))
        (List.tl vars)

  let mk_old_param env params iparams =
    if List.length iparams = 0 then env, []
    else
      List.fold_left2 (fun (env,acc) v iv ->
          let s = String.uncapitalize_ascii v.v_name in
          let s = "_" ^ s in
          let env = Env.set_var_prefix env iv s in
          env, s :: acc
        ) (env,[]) (List.rev params) (List.rev iparams)


  let update_res_env env f ires =
    List.fold_lefti
      (fun env i res ->
         let s = "res.`1" in
         let s =
           if List.length f.f_tyout > 1 then
             s ^ ".`" ^ string_of_int (i+1)
           else s
         in
         Env.set_var_prefix_u env res s)
      env ires

  let res = Eident ["res"]

  let pp_valid_post env f =
    let fname = Env.get_funname env f.f_name in

    let iparams = get_iparams f.f_contra in
    let iparams = List.map L.unloc iparams in
    let env,vars = mk_old_param env f.f_args iparams in

    let ires = get_ires f.f_contra in
    let ires = List.map L.unloc ires in
    let env1 = update_res_env env f ires in

    let args = Env.get_args env f.f_name in
    let pre = var_eq vars args in

    let post = get_post f.f_contra in

    let wp_step = List.length post in
    let wp_step = if wp_step <= 0 then -1 else (-1 * wp_step) in
    let wp_step = string_of_int wp_step in

    let post = contrat env1 post in

    let rec aux acc = function
      | Equant (_ , _ , e) -> aux acc e
      | Eident i -> i :: acc
      | Eapp (e, el) -> List.fold_left aux (aux acc e) el
      | Eop2 (_, e1, e2) -> aux (aux acc e1) e2
      | Eop3 (_, e1, e2, e3) -> aux (aux (aux acc e1) e2) e3
      | Elist el -> List.fold_left aux acc el
      | Etuple el -> List.fold_left aux acc el
      | Eproj (e, _) -> aux acc e
      | EHoare (_ ,e1, e2) -> aux (aux acc e1) e2
      | _ -> acc
    in
    let acc = aux [] post in
    let filter  = function
      | s :: _ ->
        if String.count_string s "res" > 0 then true else false
      | _ -> false
    in
    let acc = List.filter filter acc in
    let eq a b =
      match a, b with
      | s1 :: _ , s2 :: _ -> String.equal s1 s2
      | _ -> false
    in
    let acc = List.unique ~eq acc in

    let trace = Eapp(Eident ["trace"],[res]) in
    let valid_trace = Eapp(Eident ["valid"], [trace]) in
    let post = Eop2 (Infix "=>", valid_trace, post) in

    let name = Format.asprintf "%s_valid_post" fname in

    let form = EHoare (["M";fname], pre, post) in
    let prop = (name, vars, form) in

    let tactic = {
      tname = "proc";
      targs = []
    }
    in

    let tactic1 = {
      tname = "wp";
      targs = [Pattern wp_step; Pattern "=>"; Pattern "/="]
    }
    in

    let old = Env.get_old env f.f_name in
    let e = var_eq vars (List.rev old) in

    let tactic2 = {
      tname = "conseq";
      targs = [Param [Pattern ":"; Pattern " _"; Pattern "==>"; DProp e]]
    }
    in

    let i = 1 + List.length acc  in
    let p = string_of_int i ^ "?" in

    let tactic3 =
      {
        tname = "move";
        targs = [Pattern "=>"; Pattern "?"; Pattern "_"; Pattern "/>"; Pattern p]
      }
    in

    let tactic4 =
      {
        tname = "rewrite";
        targs = [Prop "/trace"; Pattern "/="; Prop "!valid_cat";
                 Prop "/valid"; Pattern "//="]
      }
    in

    let i = List.length f.f_args in
    let i = string_of_int i in
    let tactic5 =
      {
        tname = "seq";
        targs = [Pattern i; Pattern ":"; Param [DProp e]]
      }
    in
    let tactic6 =
      {
        tname = "auto";
        targs = []
      }
    in

    let tactic7 =
      {
        tname = "by";
        targs = [Conti tactic6]
      }
    in
    let tactic8 =
      {
        tname = "conseq";
        targs = []
      }
    in
    let tactic9 =
      {
        tname = "by";
        targs = [Conti tactic8; Pattern "/>"]
      }
    in
    let tactic10 = {
      tname ="qed";
      targs = []
    }
    in

    if List.is_empty (get_post f.f_contra) then
      Lemma (prop, [tactic;tactic6;tactic10])
    else
      Lemma (prop, [tactic; tactic1; tactic2; tactic3; tactic4;
                  tactic5; tactic7; tactic9; tactic10])

  let pp_valid_assume_ env f =
    let fname = Env.get_funname env f.f_name in

    let iparams = get_iparams f.f_contra in
    let iparams = List.map L.unloc iparams in
    let env,vars = mk_old_param env f.f_args iparams in

    let args = Env.get_args env f.f_name in
    let pre = var_eq vars args in

    let p = contrat env (get_pre f.f_contra) in

    let trace = Eapp(Eident ["trace"],[res]) in
    let valid_assume_trace = Eapp(Eident ["validk"], [Eident ["Assume"]; trace]) in
    let post = Eop2 (Infix "=>", p, valid_assume_trace) in

    let name = Format.asprintf "%s_assume_" fname in

    let form = EHoare (["M";fname], pre, post) in
    let prop = (name, vars, form) in

    let tactic = {
      tname = "admitted";
      targs = [Comment "TODO"];
    }
    in

    Lemma (prop, [tactic])

  let pp_valid_assume env f =
    let fname = Env.get_funname env f.f_name in

    let iparams = get_iparams f.f_contra in
    let iparams = List.map L.unloc iparams in
    let env,vars = mk_old_param env f.f_args iparams in

    let ires = get_ires f.f_contra in
    let ires = List.map L.unloc ires in
    let env1 = update_res_env env f ires in

    let args = Env.get_args env f.f_name in
    let pre = var_eq vars args in
    let p = contrat env (get_pre f.f_contra) in

    let post = contrat env1 (get_post f.f_contra) in
    let trace = Eapp(Eident ["trace"],[res]) in
    let valid_trace = Eapp(Eident ["valid"], [trace]) in
    let post1 = Eop2 (Infix "=>", valid_trace, post) in

    let valid_assume_trace = Eapp(Eident ["validk"], [Eident ["Assume"]; trace]) in
    let post2 = Eop2 (Infix "=>", p, valid_assume_trace) in

    let post = Eop2 (Infix "/\\", post1, post2) in

    let name = Format.asprintf "%s_assume" fname in

    let form = EHoare (["M";fname], pre, post) in
    let prop = (name, vars, form) in

    let name1 = Format.asprintf "%s_assume_" fname in
    let vars = List.map (fun x -> Ident [x]) vars in
    let param1 = Prop name1 :: vars in
    let name2 = Format.asprintf "%s_valid_post" fname in
    let param2 = Prop name2 :: vars in


    let tactic1 = {
      tname ="conseq";
      targs = [Param (param1); Param (param2) ; Pattern "=>"; Pattern "/>"]
    }
    in

    let tactic2 = {
      tname ="qed";
      targs = []
    }
    in

    Lemma (prop, [tactic1; tactic2])

  let pp_valid_assert env f =
    let fname = Env.get_funname env f.f_name in

    let iparams = get_iparams f.f_contra in
    let iparams = List.map L.unloc iparams in
    let env,vars = mk_old_param env f.f_args iparams in

    let args = Env.get_args env f.f_name in
    let f1 = var_eq vars args in
    let f2 = contrat env (get_pre f.f_contra) in
    let pre = fand f1 f2 in

    let trace = Eapp(Eident ["trace"],[res]) in
    let post = Eapp(Eident ["validk"], [Eident ["Assert"]; trace]) in

    let name = Format.asprintf "%s_assert" fname in

    let form = EHoare (["M";fname], pre, post) in
    let prop = (name, vars, form) in

    let tactic = {
      tname = "admitted";
      targs = [Comment "Proven by Cryptoline"];
    }
    in

    Lemma (prop, [tactic])

  let pp_spec env f =
    let fname = Env.get_funname env f.f_name in

    let iparams = get_iparams f.f_contra in
    let iparams = List.map L.unloc iparams in
    let env,vars = mk_old_param env f.f_args iparams in

    let ires = get_ires f.f_contra in
    let ires = List.map L.unloc ires in
    let env1 = update_res_env env f ires in

    let args = Env.get_args env f.f_name in
    let f1 = var_eq vars args in
    let f2 = contrat env (get_pre f.f_contra) in
    let pre = fand f1 f2 in

    let post = contrat env1 (get_post f.f_contra) in

    let name = Format.asprintf "%s_spec" fname in

    let form = EHoare (["M";fname], pre, post) in
    let prop = (name, vars, form) in


    let name1 = Format.asprintf "%s_assume" fname in
    let vars = List.map (fun x -> Ident [x]) vars in
    let param1 = Prop name1 :: vars in
    let name2 = Format.asprintf "%s_assert" fname in
    let param2 = Prop name2 :: vars in


    let tactic1 = {
      tname ="conseq";
      targs = [Param (param1); Param (param2) ; Pattern "=>"; Pattern "/>"]
    }
    in

    let tactic2 ={
      tname = "smt";
      targs = [Param [Prop "all_validk_valid"]]
    }
    in

    let tactic3 = {
      tname ="qed";
      targs = []
    }
    in

    if post == (Ebool true) then 
      Lemma (prop, [tactic1; tactic3])
    else
      Lemma (prop, [tactic1;tactic2;tactic3])

  let final env funcs =
    let aux f =
      FInfo.is_export f.f_cc || FInfo.is_subroutine f.f_cc
    in
    let funcs = List.filter aux funcs in
    let p1 = List.map (pp_valid_post env) funcs in
    let p2 =
      List.map
        (fun f ->
          let p1 = pp_valid_assume_ env f in
          let p2 = pp_valid_assume env f in
          [p1; p2]
        )
        funcs
    in
    let p2 = List.flatten p2 in
    let p3 = List.map (pp_valid_assert env) funcs in
    let p4 = List.map (pp_spec env) funcs in
    let c1 = Icomment "The post is in the trace." in
    let c2 = Icomment "The post is in the trace and all assumes are valid." in
    let c3 = Icomment "All assert are valid." in
    let c4 = Icomment "Final specification for the functions." in
    (c1 :: p1) @ (c2 :: p2) @ (c3 :: p3) @ (c4 :: p4)

  let init_trace env f =
    let fname = Env.get_funname env f.f_name in

    let proofv = ("trace_" ^ fname) in
    Env.add_proofv env f.f_name proofv;
    let env = Env.add_func env f.f_name in
    let trace_ = Env.get_proofv env f.f_name in
    let vars =
      [trace_, Base "trace"]
    in
    env, vars

  let proof_var_init env f =
    let proofv = Env.get_proofv env f.f_name in
    [ESasgn ([LvIdent [proofv]], Elist [])]

  let check_vars env f =
    let proofv = Env.get_proofv env f.f_name in
    Eident [proofv]

  let trans annot =
    let l =
      ["t", true ; "f", false]
    in
    let mk_trans = Annot.filter_string_list None l in
    let atran annot =
      match Annot.ensure_uniq1 "signed" mk_trans annot with
      | None -> false
      | Some s -> s
    in
    atran annot

  let sign env f =
    let sign = trans f.f_annot.f_user_annot in
    Env.add_sign env sign

  let ec_tmp_lvs env f =
    let fn = f.f_name in
    let otys, itys = Env.get_funtype env fn in
    let env,tmps =
      List.fold_left_map
        (fun env ty ->
           let name = "tmp__" ^ fn.fn_name in
           Env.mk_var_prefix env name ty
        )
        env otys
    in
    let tmps = List.map (fun x -> x, toec_ty env x.v_ty) tmps in
    Env.add_tmplvs env fn tmps;
    let name = "tmp__data_" ^ fn.fn_name in
    let tmps = (name, Tuple(List.map (fun x -> toec_ty env x) f.f_tyout)) in
    Env.add_ttmplvs env fn tmps;
    env

  let init_env env funcs =
    let env = List.fold_left Env.add_contra env funcs in
    List.fold_left ec_tmp_lvs env funcs

  let var2ec_var env x = (List.hd [ec_vars env x], toec_ty env x.v_ty)

  let fun_init env f =

    let args = List.map (ec_vars env)  f.f_args in
    let fn = f.f_name in
    Env.add_args env fn args;

    let old = List.fold
        (fun acc a-> (a, V.clone a) :: acc)
            [] f.f_args
    in

    let env,init =
      List.fold_left_map
      (fun env (x, o) ->
         let lvar = Lvar (L.mk_loc L._dummy o) in
         let e = Pvar (gkvar (L.mk_loc L._dummy x)) in
         let name = "old_" ^ o.v_name in
         let env = Env.set_var_prefix env o name in
         env, toec_expr_assign env lvar e
      ) env old
    in
    let init = List.flatten init in
    let old_vars = List.map (fun (_,o) -> o) old in

    let vars = Env.vars env in
    let old_v = List.map (fun x -> Mv.find x vars) old_vars in
    Env.add_old env old_v f.f_name;
    let old = List.map (var2ec_var env) old_vars in

    let clone x =
      let aux v = L.mk_loc L._dummy (V.clone v) in
      List.map aux f.f_args
    in
    let contra = match f.f_contra with
      | None ->
        {f_iparams = clone f.f_args;
         f_ires = clone (List.map L.unloc f.f_ret);
         f_pre = [];
         f_post = [];
        }
      | Some c -> c
    in
    let es = List.map (fun x -> Pvar (gkvar (L.mk_loc L._dummy x))) f.f_args in
    let iparam = List.map L.unloc contra.f_iparams in
    let assume = sub_contra iparam es contra.f_pre in

    let env,proofv = init_trace env f in
    let proofv_init = proof_var_init env f in

    let assume = List.map
        (fun (prover,exp) -> ec_trace env Assume exp)
        assume
    in
    let assume = List.flatten assume in
    let es = List.map (fun x -> Pvar (gkvar (L.mk_loc L._dummy x))) (List.rev old_vars) in
    let assert_ = sub_contra iparam es contra.f_post in
    let es = List.map (fun x -> Pvar (gkvar x)) f.f_ret in
    let ires = List.map L.unloc contra.f_ires in
    let assert_ = sub_contra ires es assert_ in
    let assert_ = List.map
        (fun (prover,exp) -> ec_trace env Assert exp)
        assert_
    in
    let assert_ = List.flatten assert_ in

    init@proofv_init@assume,assert_,old@proofv,env

  let toec_call env lvs f es =
    let otys, itys = Env.get_funtype env f in
    let args = List.map (EC.toec_cast env) (List.combine itys es) in

    let tmps = Env.get_tmplvs env f in
    let ttmpt,_ = Env.get_ttmplvs env f in

    let contr = Env.get_contra env f in

    let lvs2 = List.map (fun (v,_) -> Lvar (L.mk_loc L._dummy v)) tmps in

    let elvs2 =
      List.map (fun (v,_) ->
          Pvar({gv = L.mk_loc L._dummy v; gs = Expr.Slocal})
        ) tmps
    in

    let iparams = List.map L.unloc (get_iparams contr) in
    let pre = sub_contra iparams es (get_pre contr) in
    let pre = List.map (fun (_,e) -> e) pre in

    let post = sub_contra iparams es (get_post contr) in
    let ires = List.map L.unloc (get_ires contr) in
    let tmps =
      List.map
        (fun (x,_)-> Pvar {gv=L.mk_loc L._dummy x; gs=E.Slocal})
        tmps
    in
    let post = sub_contra ires tmps post in
    let post = List.map (fun (_,e) -> e) post in

    let i = List.fold (fun acc pre -> ec_trace env Assert pre @ acc ) [] pre in

    let i = i @
      [EScall ([LvIdent [ttmpt] ; LvIdent ["tmp__trace"]], [Env.get_funname env f], args)]
    in
    let i = i @ [ESasgn(ec_lvals env lvs2, Eident [ttmpt])] in
    let f = Env.get_func env in
    let p = Env.get_proofv env f in
    let e1 =
      Eop2 (Infix "++", Eident [p], Eident["tmp__trace"])
    in
    let i = i @ [ESasgn ([LvIdent ([p])],e1)] in
    let i = List.fold_left (fun acc post -> acc @ ec_trace env Assume post ) i post in
    List.fold_left2
      (fun acc lv e ->
         let ec_e = EC.toec_expr env e in
         let e = EC.ec_cast env (ty_lval lv, ty_expr e) ec_e in
         acc @ [EC.toec_lval1 env lv e])
      i lvs elvs2

  let import env = [IfromRequireImport ("Jasmin",["Jcheck"])]

  let global_vars env =
    let tmp = Env.get_all_tmplvs env in
    let tmp = List.map (fun (v,typ) -> v.v_name,typ) tmp in
    [("tmp__trace",Base "trace")] @ tmp @ Env.get_all_ttmplvs env
end


module SafetyAnnotations (EA: EcArray) : Model =
struct
  module EC = EcExpression(EA)
  include Normal(EA)

  let fand a b = Eop2 (Infix "/\\", a, b)

  let fun_ret env name ret = 
    let trace = Env.get_proofv env name in
    Etuple(ret) :: [Eident [trace]]

  let fun_rty env rtyps = Tuple(rtyps) :: [Base "trace"]
  
  let ec_kind = function
  | Expr.Assume -> ["Assume"]
  | Assert -> ["Assert"]
  | _ -> assert false

  let ec_trace env k e =
    let k = ec_kind k in
    let f =  Env.get_func env in
    let p = Env.get_proofv env f in
    let e = EC.toec_expr env e in
    let e1 = Eop2 (Infix "++", Eident [p], Elist [Etuple [Eident k;e]]) in
    let i = ESasgn ([LvIdent ([p])],e1) in
    [i]

  let toec_assert env k e =
    ec_trace env k e 

  let sub_contra args params =
    let aux f =
      List.map (fun (prover,clause) -> prover, f clause)
    in
    let check v vi=
      (L.unloc v.gv).v_name = vi.v_name && (L.unloc v.gv).v_id = vi.v_id
    in
    let aux1 v =
      match List.findi (fun _ vi -> check v vi) args with
      | i,_ ->
        let _,e = List.findi (fun ii _ -> ii = i) params in
        e
      | exception _ ->  Pvar v
    in
    aux (Subst.gsubst_e (fun ?loc:_ x -> x) aux1)

  let get_pre = function
    | None -> []
    | Some f -> f.f_pre

  let get_post = function
    | None -> []
    | Some f -> f.f_post

  let get_iparams = function
    | None -> []
    | Some f -> f.f_iparams

  let get_ires = function
    | None -> []
    | Some f -> f.f_ires

  let contrat env c =
    let c = List.map (fun (_,x) -> x) c in
    if List.is_empty c then
      Ebool true
    else
      let c = List.map (EC.toec_expr env) c in
      List.fold_left (fun acc a -> Eop2 (Infix "/\\", a, acc) ) (List.hd c) (List.tl c)

  let var_eq vars1 vars2 =
    if List.length vars1 = 0 then
      Ebool true
    else
      let vars = List.map2 (fun a b -> (a,b)) vars1 vars2 in
      let eq (var1,var2) =
        Eop2 (Infix "=", ec_ident var1, ec_ident var2)
      in
      List.fold_left
        (fun acc a -> Eop2 (Infix "/\\", eq a, acc))
        (eq (List.hd vars))
        (List.tl vars)

  let mk_old_param env params iparams =
    if List.length iparams = 0 then
      List.fold_left2 (fun (env,acc) v iv ->
        let s = String.uncapitalize_ascii v.v_name in
        let s = "_" ^ s in
        let env = Env.set_var_prefix env iv s in
        env, s :: acc
      ) (env,[]) (List.rev params) (List.rev params)
    else
      List.fold_left2 (fun (env,acc) v iv ->
          let s = String.uncapitalize_ascii v.v_name in
          let s = "_" ^ s in
          let env = Env.set_var_prefix env iv s in
          env, s :: acc
        ) (env,[]) (List.rev params) (List.rev iparams)


  let update_res_env env f ires =
    List.fold_lefti
      (fun env i res ->
         let s = "res.`1" in
         let s =
           if List.length f.f_tyout > 1 then
             s ^ ".`" ^ string_of_int (i+1)
           else s
         in
         Env.set_var_prefix_u env res s)
      env ires

  let res = Eident ["res"]
  let get_smt_lemmas (annot:annotations): string list option =
    match (get "smt" annot) with
    | Some (Some x )-> 
      let x = L.unloc x in
      begin match x with
      | Astring x -> Some (String.split_on_char ',' x)
      | _ -> None
      end
    | _ -> None


  let get_smt_tactic (annot:annotations): ec_tactic =
    let smt_lemmas = match get_smt_lemmas annot with
      | Some s -> List.map (fun l -> Prop l) s
      | None -> [ Prop "all_cat"]
    in
    {
      tname = "smt";
      targs = [Param smt_lemmas]
    }

  let get_invariant env c =
    match c with
     | {i_desc = Cassert (_, Safety, e)}:: t -> 
       let e = EC.toec_expr env e in
       Pattern "/\\ " :: [DProp e], t
     | c -> [Pattern "/\\ ..."], c
  

  let rec pp_valid_trace_instrs env f p instrs: ec_tactic list =
    let auto_tactic = {
      tname = "auto";
      targs = []
    } in
    let rewrite_tactic =
      {
        tname = "rewrite";
        targs = [Prop "/trace"; Prop "/is_init"; Prop "/valid"; Pattern "/="]
      }
    in
    let smt_tactic = get_smt_tactic f.f_annot.f_user_annot in
    let fn = Env.get_funname env f.f_name in
    let proofv = "trace_" ^ fn in
    let valid_trace = DProp(Eapp(Eident ["valid"], [Eident [proofv]])) in
    match instrs with
    | [] -> p
    | i::t -> begin match i.i_desc with
      | Cassert (_, Safety, e) -> 
        let pre = pp_valid_trace_instrs env f [auto_tactic] t in
        let pre = if (List.last pre).tname = "auto" then
            pre @ [rewrite_tactic;smt_tactic]
        else pre in
        let e = EC.toec_expr env e in
        [{tname = "seq"; targs = [Pattern "x"; Pattern ":"; Param [valid_trace;Pattern "/\\ ";DProp e]]}] @ pre @ p
      | Cfor (_,_,c) ->
        let invariant,c = get_invariant env c in 
        let c = pp_valid_trace_instrs env f []  (List.rev c) in
        let default = [auto_tactic;rewrite_tactic;smt_tactic] in
        let c1 = 
          if c == [] then
            default
          else
              if (List.last c).tname = "auto" then
                auto_tactic :: c @ [rewrite_tactic;smt_tactic]
              else
                auto_tactic :: c
        in
        let p = p @ [{tname = "while"; targs = [Param (valid_trace::invariant)]}] @ c1 @ [auto_tactic] in
        pp_valid_trace_instrs env f p t
      | Cwhile(_,c1,_,_,c2) -> 
        let invariant,c2 = get_invariant env c2 in 
        let c1 = pp_valid_trace_instrs env f [] (List.rev c1) in
        let c2 = pp_valid_trace_instrs env f []  (List.rev c2) in
        let default = [auto_tactic;rewrite_tactic;smt_tactic] in
        let c3 = 
          if c1 == [] && c2 == [] then
            default
          else
            let c = c2 @ c1 in 
            if (List.last c).tname = "auto" then
              auto_tactic :: c @ [rewrite_tactic; smt_tactic]
            else
              auto_tactic :: c
        in
        let p = p @ [{tname = "while"; targs = [Param (valid_trace::invariant)]}] @ c3 @ [auto_tactic] @ c1 in
        pp_valid_trace_instrs env f p t 
      | Ccall(lvs,fn,es) -> 
        let otys, itys = Env.get_funtype env fn in
        let args = List.map (EC.toec_cast env) (List.combine itys es) in
        let params = List.map (fun e -> DProp e) args in
        let lemma_name = Prop (Format.asprintf "%s_trace" (Env.get_funname env fn)) in
        let p = p @ [{tname = "ecall"; targs = [Param (lemma_name::params)]};auto_tactic] in
        pp_valid_trace_instrs env f p t
      | Cif (e, c1, c2) ->
        let c1 = pp_valid_trace_instrs env f [] (List.rev c1) in
        let c2 = pp_valid_trace_instrs env f [] (List.rev c2) in
        let first_not_assert_safety t =
          match t with
          | {i_desc = Cassert (_, Safety, _)}::_ -> true
          | _ -> false in
        if (c1 == [] && c2 == []) || (first_not_assert_safety t)then
          pp_valid_trace_instrs env f p t
        else
          let c1 = p @ c1 in
          let c2 = p @ c2 in
          let c1 = if c1==[] then [auto_tactic;rewrite_tactic;smt_tactic]
                   else if (List.last c1).tname == "auto" then c1@[rewrite_tactic;smt_tactic] else c1 in
          let c2 = if c2==[] then [auto_tactic;rewrite_tactic;smt_tactic]
                   else if (List.last c2).tname == "auto" then c2@[rewrite_tactic;smt_tactic] else c2 in
          let c1 = if List.first c1 == auto_tactic then c1 else auto_tactic::c1 in
          let c2 = if List.first c2 == auto_tactic then c2 else auto_tactic::c2 in
          let p = [{tname = "if"; targs = []}] @ c1 @ c2 in
          pp_valid_trace_instrs env f p t
      | _ -> pp_valid_trace_instrs env f p t
      end
   
  let pp_valid_trace_t_t = 
    let tactic1 =
      {
        tname = "proc; inline *; auto";
        targs = []
      } in
      let tactic2 =
      {
        tname = "qed";
        targs = []
      } in
      [tactic1;tactic2]

  let pp_valid_trace env f =
    let fname = Env.get_funname env f.f_name in

    let iparams = get_iparams f.f_contra in
    let iparams = List.map L.unloc iparams in
    let env,vars = mk_old_param env f.f_args iparams in

    let args = Env.get_args env f.f_name in
    let f1 = var_eq vars args in
    let f2 = contrat env (get_pre f.f_contra) in
    let pre = fand f1 f2 in

    let ires = get_ires f.f_contra in
    let ires = List.map L.unloc ires in
    let env1 = update_res_env env f ires in

    let post = contrat env1 (get_post f.f_contra) in
    let trace = Eapp(Eident ["trace"],[res]) in
    let valid_trace = Eapp(Eident ["valid"], [trace]) in

    let post' = fand post valid_trace in

    let name = Format.asprintf "%s_trace" fname in
    let module_name =
      if List.is_empty (Env.randombytes env) then "M"
      else "M("^syscall_mod^")"
    in
    let form = EHoare ([module_name;fname], pre, post') in
    let prop = (name, vars, form) in
    let locals = Sv.elements (locals f) in
    let env = List.fold_left Env.set_var env (f.f_args @ locals) in
    let env = Env.new_fun env in
    let init,final,ilocals,env = fun_init env f in
    let smt_tactic = get_smt_tactic f.f_annot.f_user_annot in
    let tactics = 
      if f.f_contra == None then 
        pp_valid_trace_t_t
      else
        let tactic1 = {
          tname = "proc; auto";
          targs = []
        } in
        let tactic2 = pp_valid_trace_instrs env f [] (List.rev f.f_body) in
        let tactic2 = 
          if (tactic2 == [] ) then 
            [{tname = "rewrite /is_init /trace /valid /="; targs = []}; smt_tactic]
          else 
            let last_tactic = List.last tactic2 in
            if last_tactic.tname = "auto" then
              tactic2 @ [{tname = "rewrite /is_init /trace /valid /="; targs = []};smt_tactic]
            else
              tactic2
        in    
        let tactic3 =
          {
            tname = "qed";
            targs = []
        } in
        tactic1 ::  tactic2 @ [tactic3]
      in
    Lemma (prop, tactics)


  let final env funcs =
    let p1 = List.map (pp_valid_trace env) funcs in

    let c1 = Icomment "The post and trace are valid." in
    (c1 :: p1)

  let init_trace env f =
    let fname = Env.get_funname env f.f_name in

    let proofv = ("trace_" ^ fname) in
    Env.add_proofv env f.f_name proofv;
    let env = Env.add_func env f.f_name in
    let trace_ = Env.get_proofv env f.f_name in
    let vars =
      [trace_, Base "trace"]
    in
    env, vars

  let proof_var_init env f =
    let proofv = Env.get_proofv env f.f_name in
    [ESasgn ([LvIdent [proofv]], Elist [])]

  let check_vars env f =
    let proofv = Env.get_proofv env f.f_name in
    Eident [proofv]

  let trans annot =
    let l =
      ["t", true ; "f", false]
    in
    let mk_trans = Annot.filter_string_list None l in
    let atran annot =
      match Annot.ensure_uniq1 "signed" mk_trans annot with
      | None -> false
      | Some s -> s
    in
    atran annot

  let sign env f =
    let sign = trans f.f_annot.f_user_annot in
    Env.add_sign env sign

  let ec_tmp_lvs env f =
    let fn = f.f_name in
    let otys, itys = Env.get_funtype env fn in
    let env,tmps =
      List.fold_left_map
        (fun env ty ->
           let name = "tmp__" ^ fn.fn_name in
           Env.mk_var_prefix env name ty
        )
        env otys
    in
    let tmps = List.map (fun x -> x, toec_ty env x.v_ty) tmps in
    Env.add_tmplvs env fn tmps;
    let name = "tmp__data_" ^ fn.fn_name in
    let tmps = (name, Tuple(List.map (fun x -> toec_ty env x) f.f_tyout)) in
    Env.add_ttmplvs env fn tmps;
    env

  let init_env env funcs =
    let env = List.fold_left Env.add_contra env funcs in
    List.fold_left ec_tmp_lvs env funcs

  let var2ec_var env x = (List.hd [ec_vars env x], toec_ty env x.v_ty)

  let fun_init env f =

    let args = List.map (ec_vars env)  f.f_args in
    let fn = f.f_name in
    Env.add_args env fn args;

    let old = List.fold
        (fun acc a-> (a, V.clone a) :: acc)
            [] f.f_args
    in

    let env,init =
      List.fold_left_map
      (fun env (x, o) ->
         let lvar = Lvar (L.mk_loc L._dummy o) in
         let e = Pvar (gkvar (L.mk_loc L._dummy x)) in
         let name = "old_" ^ o.v_name in
         let env = Env.set_var_prefix env o name in
         env, toec_expr_assign env lvar e
      ) env old
    in
    let init = List.flatten init in
    let old_vars = List.map (fun (_,o) -> o) old in

    let vars = Env.vars env in
    let old_v = List.map (fun x -> Mv.find x vars) old_vars in
    Env.add_old env old_v f.f_name;
    let old = List.map (var2ec_var env) old_vars in
    let env,proofv = init_trace env f in
    let proofv_init = proof_var_init env f in
    init@proofv_init@[],[],old@proofv,env

  let toec_call env lvs f es =
    let otys, itys = Env.get_funtype env f in
    let args = List.map (EC.toec_cast env) (List.combine itys es) in

    let tmps = Env.get_tmplvs env f in
    let ttmpt,_ = Env.get_ttmplvs env f in

    let lvs2 = List.map (fun (v,_) -> Lvar (L.mk_loc L._dummy v)) tmps in

    let elvs2 =
      List.map (fun (v,_) ->
          Pvar({gv = L.mk_loc L._dummy v; gs = Expr.Slocal})
        ) tmps
    in


    let i = [EScall ([LvIdent [ttmpt] ; LvIdent ["tmp__trace"]], [Env.get_funname env f], args)]
    in
    let i = if lvs2 == [] then i else i @ [ESasgn(ec_lvals env lvs2, Eident [ttmpt])] in
    let f = Env.get_func env in
    let p = Env.get_proofv env f in
    let e1 =
      Eop2 (Infix "++", Eident [p], Eident["tmp__trace"])
    in
    let i = i @ [ESasgn ([LvIdent ([p])],e1)] in
    List.fold_left2
      (fun acc lv e ->
         let ec_e = EC.toec_expr env e in
         let e = EC.ec_cast env (ty_lval lv, ty_expr e) ec_e in
         acc @ [EC.toec_lval1 env lv e])
      i lvs elvs2

  let import env = [IfromRequireImport ("Jasmin",["Jcheck"; "JSafety"])]

  let global_vars env =
    let tmp = Env.get_all_tmplvs env in
    let tmp = List.map (fun (v,typ) -> v.v_name,typ) tmp in
    [("tmp__trace",Base "trace")] @ tmp @ Env.get_all_ttmplvs env
end

module Model_EcLeak (EA: EcArray) (EL:EcLeakage) : Model =
struct
  open EcExpression(EA)
  open EL

  module EA = EA

  let toec_ty env ty = Base (toec_ty EA.onarray_ty env ty)

  let ec_assgn env lv (etyo, etyi) e =
    let e = e |> ec_zeroext (etyo, etyi) |> ec_cast env (ty_lval lv, etyo) in
    toec_lval1 env lv e

  let ec_assgn_f env lvs etyso etysi f =
    let stmt = if lvals_are_vars lvs && (List.map ty_lval lvs) = etyso && etyso = etysi then
      [f (ec_lvals env lvs)]
      else
      let ec_typs = (List.map (fun ty -> toec_ty env ty) etysi) in
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

  let ec_expr_assgn env lvs etyso etysi e =
    if lvals_are_vars lvs && (List.map ty_lval lvs) = etyso && etyso = etysi then
      (ec_leaks_lvs env lvs) @ [ESasgn (ec_lvals env lvs, e)]
    else if List.length lvs = 1 then
      (ec_leaks_lvs env lvs) @ [ec_assgn env (List.hd lvs) (List.hd etyso, List.hd etysi) e]
    else
      ec_assgn_f env lvs etyso etysi (fun lvals -> ESasgn (lvals, e))

  let toec_expr_assign env lv e =
    match e with
    | Parr_init _ ->
      (ec_leaks_es env [e]) @
      [toec_lval1 env lv (ec_ident "witness")]
    | _ ->
      let tys = [ty_expr e] in
      (ec_leaks_es env [e]) @
      ec_expr_assgn env [lv] tys tys (toec_expr env e)

  let toec_copn_era env es = ec_leaks_opn env es

  let ec_opn pd asmOp o =
    let s = Format.asprintf "%a" (pp_opn pd asmOp) o in
    if Ss.mem s keywords then s^"_" else s

  let toec_copn env lvs asmOp op es =
    let op' = base_op op in
    (* Since we do not have merge for the moment only the output type can change *)
    let otys,itys = ty_sopn (Env.pd env) asmOp op es in
    let otys', _ = ty_sopn (Env.pd env) asmOp op' es in
    let ec_op op = ec_ident (ec_opn (Env.pd env) asmOp op) in
    let ec_e op = Eapp (ec_op op, List.map (toec_cast env) (List.combine itys es)) in
    (ec_leaks_opn env es) @
    (ec_expr_assgn env lvs otys otys' (ec_e op'))

  let ec_pcall env lvs leak_lvs otys f args =
    if lvals_are_vars lvs && (List.map ty_lval lvs) = otys then
      (ec_leaks_lvs env lvs) @ [EScall (leak_lvs @ ec_lvals env lvs, f, args)]
    else
      ec_assgn_f env lvs otys otys (fun lvals -> EScall (leak_lvs @ lvals, f, args))

  let toec_call env lvs f es =
    let env = Env.new_aux_range env in
    let otys, itys = Env.get_funtype env f in
    let args = List.map (toec_cast env) (List.combine itys es) in
    let leak_lvs = ec_leak_call_lvs env in
    (ec_leaks_es env es) @
    (ec_pcall env lvs leak_lvs otys [Env.get_funname env f] args) @
    (ec_leak_call_acc env)

  let ec_syscall env o =
    match o with
    | Syscall_t.RandomBytes p ->
      let n = (Conv.int_of_pos p) in
      Env.add_randombytes env n;
      Format.sprintf "%s.randombytes_%i" syscall_mod_arg n

  let toec_syscall env lvs o es =
    let s = Syscall.syscall_sig_u o in
    let otys = List.map Conv.ty_of_cty s.scs_tout in
    let itys =  List.map Conv.ty_of_cty s.scs_tin in
    let args = List.map (toec_cast env) (List.combine itys es) in
    (ec_leaks_es env es) @
    (ec_pcall env lvs [] otys [ec_syscall env o] args)

  let toec_assert k e = assert false

  let toec_if env e c1 c2 =
    ec_leaking_if env e c1 c2

  let toec_while env c1 e c2 =
    ec_leaking_while env c1 e c2

  let toec_for env i (d,e1,e2) c =
    let env = Env.new_aux_range env in
    (* decreasing for loops have bounds swaped *)
    let e1, e2 = if d = Expr.UpTo then e1, e2 else e2, e1 in
    let init, ec_e2 =
      match e2 with
      (* Can be generalized to the case where e2 is not modified by c and i *)
      | Pconst _ -> ([], toec_expr env e2)
      | _ ->
        let aux = Env.create_aux env "inc" (Base "int") in
        let init = ESasgn ([LvIdent [aux]], toec_expr env e2) in
        let ec_e2 = ec_ident aux in
        [init], ec_e2 in
    let ec_i = [ec_vars env (L.unloc i)] in
    let lv_i = [LvIdent ec_i] in
    let init  = init @ [ESasgn (lv_i, toec_expr env e1)] in
    let ec_i1, ec_i2 =
      if d = Expr.UpTo then Eident ec_i , ec_e2
      else ec_e2, Eident ec_i in
    let i_upd_op = Infix (if d = Expr.UpTo then "+" else "-") in
    let i_upd = [ESasgn (lv_i, Eop2 (i_upd_op, Eident ec_i, Econst (Z.of_int 1)))] in
    let cond = Eop2 (Infix "<", ec_i1, ec_i2) in
    ec_leaking_for env c e1 e2 init cond i_upd

  let fun_init env f = ec_fun_leak_init env,[],[],env
  let fun_ret env _ = ec_leak_ret env
  let fun_rty = ec_leak_rty
  let global_vars = global_leakage_vars
  let import = leakage_imports
  let init_env env funcs = env
  let final env funcs = []
end

module Extraction (M: Model) =
struct

  (* ------------------------------------------------------------------- *)
  (* Instruction extraction *)

  let ec_opn pd asmOp o =
    let s = Format.asprintf "%a" (pp_opn pd asmOp) o in
    if Ss.mem s keywords then s^"_" else s

  let rec toec_cmd asmOp env c = List.flatten (List.map (toec_instr asmOp env) c)

  and toec_instr asmOp env i =
      match i.i_desc with
      | Cassgn (lv, _, _, e) ->
          M.toec_expr_assign env lv e
      | Copn ([], _, op, es) ->
          M.toec_copn_era env es @
          [EScomment (Format.sprintf "Erased call to %s" (ec_opn (Env.pd env) asmOp op))]
      | Copn (lvs, _, op, es) ->
          M.toec_copn env lvs asmOp op es
      | Ccall (lvs, f, es) ->
          M.toec_call env lvs f es
      | Csyscall (lvs, o, es) ->
          M.toec_syscall env lvs o es
      | Cassert (k,_,e) ->
          M.toec_assert env k e
      | Cif (e, c1, c2) ->
          let c1 env = toec_cmd asmOp env c1 in
          let c2 env = toec_cmd asmOp env c2 in
          M.toec_if env e c1 c2
      | Cwhile (_, c1, e, _, c2) ->
          let c1 env = toec_cmd asmOp env c1 in
          let c2 env = toec_cmd asmOp env c2 in
          M.toec_while env c1 e c2
      | Cfor (i, (d,e1,e2), c) ->
          let c env = toec_cmd asmOp env c in
          M.toec_for env i (d,e1,e2) c

  (* ------------------------------------------------------------------- *)
  (* Function extraction *)

  let var2ec_var env x = (List.hd [ec_vars env x], M.toec_ty env x.v_ty)

  let toec_fun asmOp env f =
      let f = { f with f_body = remove_for f.f_body } in
      let locals = Sv.elements (locals f) in
      let env = List.fold_left Env.set_var env (f.f_args @ locals) in
      (* Limit the scope of changes for aux variables to the current function. *)
      let env = Env.new_fun env in
      let init,final,ilocals,env = M.fun_init env f in
      let stmts = init @ (toec_cmd asmOp env f.f_body) @ final in
      let ec_locals = (Env.aux_vars env) @ (List.map (var2ec_var env) locals) in
      let ec_locals = ec_locals @ ilocals in
      let aux_locals_init = locals
          |> List.filter (fun x -> match x.v_ty with Arr _ -> true | _ -> false)
          |> List.sort (fun x1 x2 -> compare x1.v_name x2.v_name)
          |> List.map (fun x -> ESasgn ([LvIdent [ec_vars env x]], ec_ident "witness"))
      in
      let ret =
          let ec_var x = ec_vari env (L.unloc x) in
          match M.fun_ret env f.f_name (List.map ec_var f.f_ret) with
          | [x] -> ESreturn x
          | xs -> ESreturn (Etuple xs)
      in
      List.iter (Env.add_ty env) f.f_tyout;
      List.iter (fun x -> Env.add_ty env x.v_ty) (f.f_args @ locals);
      {
          decl = {
              fname = (Env.get_funname env f.f_name);
              args = List.map (var2ec_var env) f.f_args;
              rtys = Tuple (M.fun_rty env (List.map (M.toec_ty env) f.f_tyout));
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
    let mk_abbrev p e = Iabbrev (p,ec_vars env x, e) in
    match d with
    | Global.Gword(ws, w) -> mk_abbrev true (w_of_z ws (Conv.z_of_word ws w))
    | Global.Garr(p,t) ->
      let ws, t = Conv.to_array x.v_ty p t in
      mk_abbrev false (Eapp (M.EA.of_list env ws (Array.length t),
                       [Elist (List.map (w_of_z ws) (Array.to_list t))]))

  let ec_randombytes env =
      let randombytes_decl a n =
          let arr_ty = M.toec_ty env (Arr (U8, n)) in
          {
              fname = Format.sprintf "randombytes_%i" n;
              args = [(a, arr_ty)];
              rtys = Tuple [arr_ty];
          }
      in
      let randombytes_f n =
        let dmap =M. EA.ec_darray8 env n in
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
          | Arr(ws, n) -> M.EA.add_jarray env ws n
          | _ -> ()
        in
        let vars = vars_fc f in
        Sv.iter (add env) vars
      in
      let env = List.fold_left Env.set_fun env funcs in

      let env = M.init_env env funcs in

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
          IrequireImport ["AllCore"; "IntDiv"; "CoreMap"; "List"; "Distr"; "StdBigop"];
          IfromRequireImport ("Jasmin", [jmodel env]);
          Iimport [lib_slh env; "Bigbool"];
      ] in
      let top_mod = Imodule {
          name = "M";
          params = mod_arg;
          ty = None;
          vars = M.global_vars env;
          funs;
      } in
      glob_imports @
      (M.import env) @
      pp_array_theories (Env.array_theories env) @
      (List.map (fun glob -> ec_glob_decl env glob) globs) @
      (ec_randombytes env) @
      [top_mod] @
      M.final env funcs

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
  | Cassgn _ | Copn _ | Csyscall _ | Cassert _ -> used
  | Cif (_,c1,c2)     -> used_func_c (used_func_c used c1) c2
  | Cfor(_,_,c)       -> used_func_c used c
  | Cwhile(_, c1, _, _, c2) -> used_func_c (used_func_c used c1) c2
  | Ccall (_,f,_)   -> Ss.add f.fn_name used

let extract ((globs,_,funcs):('info, 'asm) prog) arch pd asmOp (model: model) amodel fnames array_dir fmt =
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
  let env = Env.empty arch pd array_theories false in
  let module EA: EcArray = (val match amodel with
    | ArrayOld -> (module EcArrayOld: EcArray)
    | WArray   -> (module EcWArray  : EcArray)
    | BArray   -> (module EcBArray  : EcArray)
  ) in

  let module EE = EcExpression(EA) in

  let module M: Model = (val match model with
      | Normal -> (module Normal(EA) : Model)
      | ConstantTime ->
        let module EL = EcLeakConstantTime(EE) in
        (module Model_EcLeak(EA)(EL) : Model)
      | ConstantTimeGlobal ->
        warning Deprecated Location.i_dummy
          "EasyCrypt extraction for constant-time in CTG mode is deprecated. Use the CT mode instead.";
        let module EL = EcLeakConstantTimeGlobal(EE) in
        (module Model_EcLeak(EA)(EL) : Model)
      | Annotations ->  (module Annotations(EA):Model)
      | SafetyAnnotations ->  (module SafetyAnnotations(EA):Model)
    ) in

  let module E = Extraction(M) in
  let prog = E.pp_prog env asmOp fmt globs funcs in
  save_array_theories (Env.array_theories env);
  prog
