open Utils
open Wsize
open Prog
open Operators
open PrintCommon

let ws2bytes ws = (int_of_ws ws) / 8

module Ws = struct
  type t = wsize
  let compare = compare
end

module WsInt = Set.Make2(Ws)(BatInt)
module Swi = WsInt.Product

module Scmp = struct
  type t = string
  let compare = compare
end

module Ss = Set.Make(Scmp)
module Ms = Map.Make(Scmp)

(* ------------------------------------------------------------------- *)
(* Array theories in eclib *)

type 'len arraywords = {
  sizew: 'len; (* in bytes *)
  sizea: 'len;
}

type 'len subarray = {
  sizes: 'len;
  sizeb: 'len;
}

type 'len subarraydirect = {
  sizew: 'len; (* in bytes *)
  sizes: 'len;
  sizeb: 'len;
}

type 'len subarraycast = {
  sizews: 'len; (* in bytes *)
  sizewb: 'len; (* in bytes *)
  sizes: 'len;
  sizeb: 'len;
}

type 'len arrayaccesscast = {
  sizews: 'len; (* in bytes *)
  sizewb: 'len; (* in bytes *)
  sizeb: 'len;
}

type 'len array_theory =
  | Array of 'len
  | WArray of 'len
  | ArrayWords of 'len arraywords
  | SubArray of 'len subarray
  | SubArrayDirect of 'len subarraydirect
  | SubArrayCast of 'len subarraycast
  | ArrayAccessCast of 'len arrayaccesscast
  | ByteArray of 'len
  | SubByteArray of 'len subarray

module ATcmp = struct
  type t = int array_theory
  let compare = compare
end

module Sarraytheory = Set.Make(ATcmp)


module AbsATcmp = struct
  type t = pexpr_ array_theory
  let map_at f = function
    | Array n -> Array (f n)
    | WArray n -> WArray (f n)
    | ByteArray n -> ByteArray (f n)
    | ArrayWords a -> ArrayWords { sizew = f a.sizew; sizea = f a.sizea }
    | SubArray a -> SubArray { sizes = f a.sizes; sizeb = f a.sizeb }
    | SubByteArray a -> SubByteArray { sizes = f a.sizes; sizeb = f a.sizeb }
    | SubArrayDirect a -> SubArrayDirect { sizew = f a.sizew; sizes = f a.sizes; sizeb = f a.sizeb }
    | SubArrayCast a -> SubArrayCast { sizews = f a.sizews; sizewb = f a.sizewb; sizes = f a.sizes; sizeb = f a.sizeb }
    | ArrayAccessCast a -> ArrayAccessCast { sizews = f a.sizews; sizewb = f a.sizewb; sizeb = f a.sizeb }
  let compare a1 a2 =
  match a1, a2 with
  | Array e1, Array e2 -> if Prog.pexpr__equal e1 e2 then 0 else compare e1 e2
  | WArray e1, WArray e2 -> if Prog.pexpr__equal e1 e2 then 0 else compare e1 e2
  | ByteArray e1, ByteArray e2 -> if Prog.pexpr__equal e1 e2 then 0 else compare e1 e2
  | ArrayWords aw1, ArrayWords aw2 -> 
    if Prog.pexpr__equal aw1.sizew aw2.sizew && Prog.pexpr__equal aw1.sizea aw2.sizea then 0 else compare a1 a2
  | SubByteArray s1, SubByteArray s2
  | SubArray s1, SubArray s2 ->
    if Prog.pexpr__equal s1.sizes s2.sizes && Prog.pexpr__equal s1.sizeb s2.sizeb then 0 else compare a1 a2
  | SubArrayDirect s1, SubArrayDirect s2 ->
    if Prog.pexpr__equal s1.sizes s2.sizes && Prog.pexpr__equal s1.sizeb s2.sizeb && Prog.pexpr__equal s1.sizew s2.sizew
    then 0 else compare a1 a2
  | SubArrayCast s1, SubArrayCast s2 ->
    if Prog.pexpr__equal s1.sizes s2.sizes && Prog.pexpr__equal s1.sizeb s2.sizeb && 
       Prog.pexpr__equal s1.sizews s2.sizews && Prog.pexpr__equal s1.sizewb s2.sizewb
    then 0 else compare a1 a2
  | ArrayAccessCast s1, ArrayAccessCast s2 ->
    if Prog.pexpr__equal s1.sizewb s2.sizewb && Prog.pexpr__equal s1.sizeb s2.sizeb && Prog.pexpr__equal s1.sizews s2.sizews
    then 0 else compare a1 a2
  | _ , _ -> compare a1 a2
end
module Aarraytheory = Map.Make(AbsATcmp)


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
 ; "raise"
 ; "assert" (* No longer a keyword since 2026.03 *)
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
 ; "extens"

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

 ; "idassign"

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

 ; "array"
 ; "bind"
 ; "circuit"
 ; "bitstring"
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
 ; "global"
 ; "declare"
 ; "hint"
 ; "module"
 ; "of"
 ; "const"
 ; "op"
 ; "exception"
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
 ; "class" (* No longer a keyword since 2026.02 *)
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

  let int_of_op1 =
  function
  | Oneg Op_int -> Z.neg
  | _ -> raise (Failure (Printf.sprintf "unary operator %s not supported in array sizes" ("")))

let shift_left (x: Z.t) (y: Z.t) : Z.t =
  let y = Z.to_int y in
  if y < 0 then Z.shift_right x (-y) else Z.shift_left x y

let shift_right (x: Z.t) (y: Z.t) : Z.t =
  let y = Z.to_int y in
  if y < 0 then Z.shift_left x (-y) else Z.shift_right x y

let zremu (x : Z.t) (y : Z.t) = Z.(of_int (sign y) * erem (of_int (sign y) * x) y)

let int_of_op2 o =
  match o with
  | Oadd Op_int -> Z.add
  | Omul Op_int -> Z.mul
  | Osub Op_int -> Z.sub
  | Odiv(sg, Op_int) -> if sg = Unsigned then Z.fdiv else Z.div
  | Omod(sg, Op_int) -> if sg = Unsigned then zremu else Z.rem
  | Olsl Op_int -> shift_left
  | Oasr Op_int -> shift_right
  | _     -> raise (Failure (Printf.sprintf "binary operator %s not supported in array sizes" ("")))

let rec int_of_expr e =
  match e with
  | Pconst i -> Some i
  | Papp1 (o, e1) ->
    begin match int_of_expr e1 with
    | None -> None
    | Some z -> Some (int_of_op1 o z)
    end
  | Papp2 (o, e1, e2) ->
      let op = int_of_op2 o in
      begin match (int_of_expr e1),(int_of_expr e2) with
      | Some z1, Some z2 -> Some (op z1 z2)
      | _ -> None
      end
  | Pbool _ | Parr_init _ | Pvar _
  | Pget _ | Psub _ | Pload _ | PappN _ | Pif _ -> None

let get_int (PE e) =
  match int_of_expr e with
    | None -> None
    | Some z ->
        try Some (Z.to_int z)
        with Z.Overflow -> None

let pexpr_of_pexpr_ (PE e) = e

let arr_size_pexpr_ ws n =   Papp2 (Omul Op_int, pexpr_of_pexpr_ n , icnst (size_of_ws ws))

let fmt_abstract_array_theory at i = match at with
  | Array _ -> "PolyArray", Format.sprintf "ArrayS%i" i
  | WArray _ -> "WArray", Format.sprintf "WArrayS%i" i
  | ArrayWords _ -> "ArrayWords", Format.sprintf "ArrayWordsWS%i" i
  | SubArray _ -> "SubArray", Format.sprintf "SubArrayS%i" i
  | SubArrayDirect _ -> "SubArrayDirect", Format.sprintf "SubArrayDirectS%i" i
  | SubArrayCast _ -> "SubArrayCast", Format.sprintf "SubArrayDirectWS%i" i
  | ArrayAccessCast _ -> "ArrayAccessCast", Format.sprintf "ArrayAccessCastWS%i" i
  | ByteArray _ -> "ByteArray", Format.sprintf "BArrayS%i" i
  | SubByteArray _ -> "SubByteArray", Format.sprintf "SBArrayS%i" i
(* we print negative lengths with a "m"-prefix to create valid module names *)
let pp_length fmt i =
  if i < 0 then
    Format.fprintf fmt "m%d" (-i)
  else
    Format.fprintf fmt "%d" i

let fmt_array_theory at = match at with
  | Array n -> Format.asprintf "Array%a" pp_length n
  | WArray n -> Format.asprintf "WArray%a" pp_length n
  | ArrayWords aw -> Format.asprintf "ArrayWords%aW%i" pp_length aw.sizea (8*aw.sizew)
  | SubArray x -> Format.asprintf "SubArray%a_%a" pp_length x.sizes pp_length x.sizeb
  | SubArrayDirect x -> Format.asprintf "SubArrayDirect%a_%aW%i" pp_length x.sizes pp_length x.sizeb (8*x.sizew)
  | SubArrayCast x -> Format.asprintf "SubArrayDirect%aW%i_%aW%i" pp_length x.sizes (8*x.sizews) pp_length x.sizeb (8*x.sizewb)
  | ArrayAccessCast x -> Format.asprintf "ArrayAccessCastW%i_%aW%i" (8*x.sizews) pp_length x.sizeb (8*x.sizewb)
  | ByteArray n -> Format.asprintf "BArray%a" pp_length n
  | SubByteArray x -> Format.asprintf "SBArray%a_%a" pp_length x.sizeb pp_length x.sizes

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
    args: ec_var list;
    rtys: ec_ty list;
}
type ec_fun = {
    decl: ec_fun_decl;
    locals: ec_var list;
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
    | IfromRequireImport of string * (string list)
    | Iabbrev of string * ec_expr
    | Iop of string * string * ec_expr
    | ImoduleTypeEq of string * string * (string * string) list 
    | ImoduleEq of string * string
    | ImoduleType of ec_module_type
    | Imodule of ec_module
    | Itheory of bool * string
    | IendTheory of string
    | IopA of string * ec_modty
    | Iclone of bool * string * string * ((string * ec_expr) list) * ((string * string) list)
type ec_prog = ec_item list

module type EnvT = sig
  type t
  val pd: t -> Wsize.wsize
  val msfsz: t -> Wsize.wsize
  val arch: t -> architecture
  val randombytes: t -> (wsize * int) list
  val set_fun: t -> ('a, 'b) pfunc -> t
  val add_Array: t -> int -> unit
  val add_AArray: t -> pexpr_ -> unit
  val add_WArray: t -> int -> unit
  val add_AWArray: t -> pexpr_ -> unit
  val add_ArrayWords: t -> int -> pexpr_ -> unit
  val add_BArray: t -> int -> unit
  val add_ABArray: t -> pexpr_ -> unit
  val add_SBArray: t -> int subarray -> unit
  val add_ASBArray: t -> pexpr_ subarray -> unit
  val add_SubArray: t -> pexpr_ -> pexpr_ -> string
  val add_SubArrayDirect: t -> int -> pexpr_ -> pexpr_ -> string
  val add_SubArrayCast: t -> int -> int -> pexpr_ -> pexpr_ -> string
  val add_ArrayAccessCast: t -> int -> int -> pexpr_ -> string
  val add_randombytes: t -> wsize -> int -> unit
  val add_jarray: t -> Wsize.wsize -> int -> unit
  val empty: architecture -> Wsize.wsize -> Wsize.wsize -> Sarraytheory.t ref ->  int Aarraytheory.t ref -> t
  val create_name: t -> string -> string
  val array_theories: t -> Sarraytheory.t
  val abstract_array_theories: t -> int Aarraytheory.t
  val set_abstract_array_theories: t -> int Aarraytheory.t -> unit
  val array_alias: t -> string Aarraytheory.t
  val set_array_alias: t -> string Aarraytheory.t -> unit
  val get_alias: t -> pexpr_ array_theory -> string option
  val add_alias: t -> pexpr_ array_theory -> string -> unit
  val abstract_name: t -> pexpr_ array_theory -> string
  val get_funtype: t -> funname -> (pty list * pty list)
  val get_funname: t -> funname -> string
  val fun_names: t -> (string * string) list
  val create_aux: t -> string -> ec_ty -> string
  val reuse_aux: t -> string -> ec_ty -> string
  val new_aux_range: t -> t
  val new_fun: t -> t
  val set_var: t -> pvar -> t
  val get_varname: t -> pvar -> string
  val set_module: t -> string -> string list -> t * string
  val get_module: t -> string -> string list * string
  val exit_module: t -> string -> t
  val get_module_funcs: t -> string -> funname list
  val get_module_vars: t -> string -> pvar list
  val get_module_modules: t -> string -> string list
  val get_module_arrays: t -> string -> (pexpr_ array_theory * string) list
  val add_module_fun: t -> string -> funname -> t
  val add_module_var: t -> string -> pvar -> t
  val add_module_module: t -> string -> string -> t
  val set_fun_mod: t -> funname -> funname -> string -> t
  val set_var_mod: t -> pvar -> pvar -> string -> t
  val set_mod_mod: t -> string -> string -> string -> t
  val set_fun_fsig: t -> string -> Mprog.funsig -> t
  val rename_fun: t -> Mprog.funsig -> string -> t
  val aux_vars: t -> (string * string) list
end


module Env: EnvT = struct
  module PTcmp = struct
    type t = ec_var
    let compare = compare
  end

  module Mpty = Map.Make (PTcmp)

  module Ms = Map.Make (String)

  type module_info = {
    name: string;
    args: string list;
    funs: funname list;
    vars: pvar list;
    modules: string list;
    arrays: (pexpr_ array_theory * string) list;
  } 

  type t = {
      arch: architecture;
      pd: Wsize.wsize;
      msfsz: Wsize.wsize;
      (* All names: functions, global variables, arguments, local variables, aux variables *)
      alls: Ss.t ref;
      (* All variables, excluding aux: global, argument, local variables *)
      vars: string Mpv.t;
      funs: (string * (pty list * pty list)) Mf.t;
      modules: module_info Ms.t;
      array_theories: Sarraytheory.t ref;
      abstract_array_theories: int Aarraytheory.t ref;
      array_alias: string Aarraytheory.t ref;
      (* aux variables: intermediate variables introduced by extraction.
        aux variables have a prefix in their name that identifies their use
        (such as jasmin assignments, for loop bounds, intermediate leakage variables).
        - auxv: for each (prefix, type), the list of all aux (used for variable declaration).
        - count: number of currently live aux variables for each (prefix, type).
        *)
      auxv: string BatVect.t Mpty.t ref;
      mutable count: int Mpty.t;
      randombytes: Swi.t ref;
    }


  let pd env = env.pd

  let msfsz env = env.msfsz

  let arch env = env.arch

  let randombytes env = Swi.elements !(env.randombytes)

  let array_theories env = !(env.array_theories)
  let abstract_array_theories env = !(env.abstract_array_theories)
  let set_abstract_array_theories env abs_theories =
    env.abstract_array_theories := abs_theories
  let array_alias env = !(env.array_alias)
  let set_array_alias env alias = env.array_alias := alias
  let get_alias env a = Aarraytheory.find_opt a !(env.array_alias)
  let add_alias env a name = env.array_alias := Aarraytheory.add a name !(env.array_alias)

  let register env a =
    if not (Aarraytheory.mem a !(env.abstract_array_theories)) && not (Aarraytheory.mem a !(env.array_alias)) then
      let used = List.map snd (Aarraytheory.to_list !(env.abstract_array_theories)) in
      let aliases = List.map (fun (_, n) -> List.last (String.split_on_char '.' n)) (Aarraytheory.to_list !(env.array_alias)) in
      let rec next i = if List.mem i used || List.mem (snd (fmt_abstract_array_theory a i)) aliases then next (i + 1) else i in
      env.abstract_array_theories := Aarraytheory.add a (next 0) !(env.abstract_array_theories)

  let abstract_name env a =
    match Aarraytheory.find_opt a !(env.array_alias) with
    | Some name -> name
    | None -> snd (fmt_abstract_array_theory a (Aarraytheory.find a !(env.abstract_array_theories)))

  let add_Array env n =
    env.array_theories := Sarraytheory.add (Array n) !(env.array_theories)
  
  let add_AArray env n = register env (Array n)


  let add_BArray env size =
    env.array_theories := Sarraytheory.add (ByteArray size) !(env.array_theories)

  let add_ABArray env size = register env (ByteArray size)

  let add_SBArray env (s:int subarray) =
    add_BArray env s.sizeb;
    add_BArray env s.sizes;
    env.array_theories := Sarraytheory.add (SubByteArray s) !(env.array_theories)
  
  let add_ASBArray env (s:pexpr_ subarray) =
    add_ABArray env s.sizeb;
    add_ABArray env s.sizes;
    register env (SubByteArray s)

  let add_WArray env n =
    env.array_theories := Sarraytheory.add (WArray n) !(env.array_theories)

  let add_AWArray env size = register env (WArray size)

  let add_ArrayWords env sizew sizea =
    match get_int sizea with
    | Some sizea ->
      add_Array env sizea;
      add_WArray env (sizew*sizea);
      env.array_theories := Sarraytheory.add (ArrayWords {sizew; sizea}) !(env.array_theories)
    | _ ->
      let size = Papp2 (Omul Op_int ,icnst sizew , pexpr_of_pexpr_ sizea) in
      add_AWArray env (PE size);
      add_AArray env sizea;
      register env (ArrayWords {sizew = PE (icnst sizew); sizea})

  let add_SubArray env sizes sizeb =
    let addSubArrayA sizes sizeb =
      add_AArray env sizes;
      add_AArray env sizeb;
      register env (SubArray {sizes;sizeb});
      abstract_name env (SubArray {sizes;sizeb})
    in
    match get_int sizes, get_int sizeb with
    | Some sizes, Some sizeb ->
      add_Array env sizes;
      add_Array env sizeb;
      env.array_theories := Sarraytheory.add (SubArray {sizes; sizeb}) !(env.array_theories);
      fmt_array_theory (SubArray {sizes; sizeb})
    | _,_ -> addSubArrayA sizes sizeb

  let add_SubArrayDirect env sizew sizes sizeb =
    add_ArrayWords env sizew sizes;
    add_ArrayWords env sizew sizeb;
    match get_int sizes, get_int sizeb with
    | Some sizes, Some sizeb ->
      env.array_theories := Sarraytheory.add (SubArrayDirect {sizew; sizes; sizeb}) !(env.array_theories);
      fmt_array_theory (SubArrayDirect {sizew; sizes; sizeb})
    | _,_ -> 
      let theory = SubArrayDirect {sizew = PE (icnst sizew); sizes; sizeb} in
      register env theory;
      abstract_name env theory

  let add_SubArrayCast env sizews sizewb sizes sizeb =
    add_ArrayWords env sizews sizes;
    add_ArrayWords env sizewb sizeb;
    match get_int sizes, get_int sizeb with
    | Some sizes, Some sizeb ->
      let theory = SubArrayCast {sizews; sizewb; sizes; sizeb} in
      env.array_theories := Sarraytheory.add (theory) !(env.array_theories);
      fmt_array_theory (theory)
    | _,_ ->
      let theory = SubArrayCast {sizews = PE (icnst sizews); sizewb = PE (icnst sizewb); sizes; sizeb} in
      register env theory;
      abstract_name env theory

  let add_ArrayAccessCast env sizews sizewb sizeb =
    add_ArrayWords env sizewb sizeb;
    match get_int sizeb with
    | Some sizeb ->
      let theory = ArrayAccessCast {sizews; sizewb; sizeb} in
      env.array_theories := Sarraytheory.add (theory) !(env.array_theories);
      fmt_array_theory (theory)
    | None ->
      let theory = ArrayAccessCast {sizews = PE (icnst sizews); sizewb = PE (icnst sizewb); sizeb} in
      register env theory;
      abstract_name env theory

  let add_randombytes env ws n = env.randombytes := Swi.add (ws, n) !(env.randombytes)

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
    n |> String.split_on_string ~by:"::"  |> List.last |> String.uncapitalize_ascii |> escape |> create_name env
  
  let mkname_mod n =
    n |> String.split_on_string ~by:"::"  |> List.last |> String.capitalize_ascii |> escape 

  let set_var env x =
    let s = mkname env x.v_name in
    { env with
      alls = ref (Ss.add s !(env.alls));
      vars = Mpv.add x s env.vars }

  let get_varname env v = 
    try Mpv.find v env.vars 
     with Not_found -> 
      Mpv.filter (fun v' _ -> v'.v_name = v.v_name) env.vars |> Mpv.choose |> snd
  let empty arch pd msfsz array_theories abstract_array_theories =
    {
      arch;
      pd;
      msfsz;
      alls = ref keywords;
      vars = Mpv.empty;
      funs = Mf.empty;
      modules = Ms.empty;
      array_theories;
      abstract_array_theories;
      array_alias = ref Aarraytheory.empty;
      auxv  = ref Mpty.empty;
      count = Mpty.empty;
      randombytes = ref Swi.empty;
    }

  let set_fun env fd =
    let s = mkname env fd.f_name.fn_name in
    let funs =
      Mf.add fd.f_name (s, (fd.f_tyout, fd.f_tyin)) env.funs in
    { env with funs; alls = ref (Ss.add s !(env.alls)) }



  let get_fun env f = 
    try Mf.find f env.funs 
    with Not_found -> 
      Mf.filter (fun k _ -> k.fn_name = f.fn_name) env.funs |> Mf.choose |> snd

  let get_funtype env f = snd (get_fun env f)

  let fun_names env = List.map (fun (f, (s, _)) -> f.fn_name, s) (Mf.bindings env.funs)

  let get_funname env f = fst (get_fun env f)


    let set_fun_fsig env m (fsig: Mprog.funsig) =
    let s = mkname env fsig.name.fn_name in
    let s = if m = "" then s else m ^ "." ^ s in
    let funs =
      Mf.add fsig.name (s, (fsig.fs_tyout, fsig.fs_tyin)) env.funs in
    { env with funs; alls = ref (Ss.add s !(env.alls)) }
  
  let rename_fun env (fsig: Mprog.funsig) new_name =
    let funs =
      Mf.add fsig.name (new_name, (fsig.fs_tyout, fsig.fs_tyin)) env.funs in
    { env with funs; alls = ref (Ss.add new_name !(env.alls)) }

  let get_module_info env m = 
    Ms.find m env.modules
  
  let update_module_info env m minfo = 
    { env with modules = Ms.add m minfo env.modules }

  let get_module env m = 
    let minfo = get_module_info env m in
    (minfo.args, minfo.name)
  let get_module_funcs env m = 
    (get_module_info env m).funs

  let get_module_vars env m = 
    (get_module_info env m).vars
  
  let get_module_modules env m = 
    (get_module_info env m).modules

  let get_module_arrays env m = 
    (get_module_info env m).arrays


  let add_module_fun env m f =
    let mod_info = get_module_info env m in
    let funs = f :: mod_info.funs in
    update_module_info env m {mod_info with funs}

  let add_module_var env m v =
    let mod_info = get_module_info env m in
    let vars = v :: mod_info.vars in
    update_module_info env m {mod_info with vars}

  let add_module_module env m sm =
    let mod_info = get_module_info env m in
    let modules = sm :: mod_info.modules in
    update_module_info env m {mod_info with modules}

  let set_module env m args = 
    let name = mkname_mod m in
    let minfo = {
      name;
      args;
      funs = [];
      vars = [];
      modules = [];
      arrays = [];
    } in
    { env with modules = Ms.add m minfo env.modules }, name
  
  let exit_module env m =
    let array_theories = List.map (fun (a, i) -> a, snd (fmt_abstract_array_theory a i)) (Aarraytheory.to_list !(env.abstract_array_theories)) in
    let array_theories = array_theories @ Aarraytheory.to_list !(env.array_alias) in
    let minfo = get_module_info env m in
    let modules = Ms.add m {minfo with arrays = array_theories} env.modules in
    let env = { env with modules } in
    env.abstract_array_theories := Aarraytheory.empty;
    env.array_alias := Aarraytheory.empty;
    let mname = minfo.name in
    let env = List.fold_left (fun env f ->
      let fname = get_funname env f in
      let ftype = get_funtype env f in
      let funs = Mf.add f (mname^"."^fname, ftype) env.funs in
      {env with funs}
    ) env minfo.funs in
    let env = List.fold_left (fun env mm ->
      let minfo = get_module_info env mm in
      let modules = Ms.add mm {minfo with name = mname^"."^minfo.name} env.modules in
      {env with modules}
    ) env minfo.modules in
    List.fold_left (fun env v ->
      let vname = get_varname env v in
      let vars = Mpv.add v  (mname^"."^vname) env.vars in
      {env with vars}
    ) env minfo.vars


  let set_fun_mod env f old_f m =
    let mod_f = get_funname env old_f in
    let ftype = get_funtype env old_f in
    let fsplit = String.split_on_char '.' mod_f in
    let mname = get_module env m |> snd in
    let fsplit = String.concat "." (List.modify_at 0 (fun _ -> mname) fsplit) in
    let funs = Mf.add f (fsplit, ftype) env.funs in
    {env with funs;}

  let set_var_mod env v old_v m =
    let mod_v = get_varname env old_v in
    let vsplit = String.split_on_char '.' mod_v in
    let mname = get_module env m |> snd in
    let vsplit = String.concat "." (List.modify_at 0 (fun _ -> mname) vsplit) in
    let vars = Mpv.add v vsplit env.vars in
    {env with vars;}

  let set_mod_mod env mm old_mm m =
    let minfo = get_module_info env old_mm in
    let msplit = String.split_on_char '.' minfo.name in
    let mname = get_module env m |> snd in
    let name = String.concat "." (List.modify_at 0 (fun _ -> mname) msplit) in
    let modules = Ms.add mm {minfo with name } env.modules in
    {env with modules}

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
      begin match get_int n with
      | None -> 
        let mem a = Aarraytheory.mem a (Env.abstract_array_theories env) || Env.get_alias env a <> None in
        mem (Array n) && mem (WArray ((PE (arr_size_pexpr_ ws n))))
      | Some n ->
        Sarraytheory.mem (Array n) (Env.array_theories env) &&
        Sarraytheory.mem (WArray (arr_size ws n)) (Env.array_theories env)
      end
  | _ -> true

(* ------------------------------------------------------------------- *)
(* Formatting to string helpers *)

let fmt_Wsz sz = Format.asprintf "W%i" (int_of_ws sz)

let fmt_op2 fmt op =
  let fmt_signed fmt ws is = function
    | Cmp_w (Signed, _)   -> Format.fprintf fmt "\\s%s" ws
    | Cmp_w (Unsigned, _) -> Format.fprintf fmt "\\u%s" ws
    | _                     -> Format.fprintf fmt "%s" is
  in
  let fmt_div fmt ws uints sints sg k =
    match sg, k with
    | Signed, Op_w _   -> Format.fprintf fmt "\\s%s" ws
    | Unsigned, Op_w _ -> Format.fprintf fmt "\\u%s" ws
    | Signed, Op_int   -> Format.fprintf fmt "%s" sints
    | Unsigned, Op_int -> Format.fprintf fmt "%s" uints
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
  | Odiv(sg, k) -> fmt_div fmt "div" "%/" "\\zquot" sg k
  | Omod(sg, k) -> fmt_div fmt "mod" "%%" "\\zrem"  sg k

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
  | IfromRequireImport (m, is) ->
    Format.fprintf fmt "@[from %s require import@ @[%a@].@]" m (pp_list "@ " pp_string) is
  | Iabbrev (a, e) ->
    Format.fprintf fmt "@[abbrev %s =@ @[%a@].@]" a pp_ec_ast_expr e
  | Iop (a, opts, e) ->
    let pp_opts fmt = function
      | "" -> ()
      | opts -> Format.fprintf fmt " [%s]" opts
    in
    Format.fprintf fmt "@[op%a %s =@ @[%a@].@]" pp_opts opts a pp_ec_ast_expr e
  | ImoduleType mt ->
    Format.fprintf fmt "@[<v>@[module type %s = {@]@   @[<v>%a@]@ }.@]"
      mt.name (pp_list "@ " pp_ec_fun_decl) mt.funs
  | ImoduleTypeEq (m, ty, funs) ->
    let pp_fun_eq fmt (f1,f2) = Format.fprintf fmt "proc %s = %s" f1 f2 in
    Format.fprintf fmt "@[<v>@[module %s : %s = {@]@   @[<v>%a@]@ }.@]" m ty (pp_list "@ " pp_fun_eq) funs;
  | ImoduleEq (m,ma) ->
     Format.fprintf fmt "@[<v>@[module %s = %s.@]" m ma;
  | Imodule m ->
    let pp_mp fmt (m, mt) = Format.fprintf fmt "%s:%s" m mt in
    Format.fprintf fmt "@[<v>@[module %s@[%a@]%a = {@]@   @[<v>%a%a%a@]@ }.@]"
      m.name
      (pp_list_paren ",@ " pp_mp) m.params
      (pp_option (fun fmt s -> Format.fprintf fmt " : %s" s)) m.ty
      (pp_list "@ " (fun fmt (v, t) -> Format.fprintf fmt "@[var %s : %s@]" v t)) m.vars
      (fun fmt _ -> if m.vars = [] then (Format.fprintf fmt "") else (Format.fprintf fmt "@ ")) ()
      (pp_list "@ " pp_ec_fun) m.funs
  | Itheory (b,th) ->
    Format.fprintf fmt "@[%stheory %s.@]" (if b then "abstract " else "") th
  | IendTheory th ->
    Format.fprintf fmt "@[end %s.@]" th
    | IopA (op, mt) ->
    Format.fprintf fmt "@[op %s : %s.@]" op mt
  | Iclone (import, mold, mnew, args,theories) ->
    if args = [] && theories = [] then 
      Format.fprintf fmt "@[clone %s as %s.@]" mold mnew
    else
      Format.fprintf fmt "@[clone%s %s as %s with %a%s%a.@]"
        (if import then " import" else "") mold mnew
        (pp_list ",@ " (fun fmt (s, e) -> Format.fprintf fmt "op %s <= %a" s pp_ec_ast_expr e)) args
        (if args <> [] && theories <> [] then ",\n " else "")
        (pp_list ",@ " (fun fmt (s, e) -> Format.fprintf fmt "theory %s <= %s" s e)) theories

let pp_ec_prog fmt (prog:ec_prog) = Format.fprintf fmt "@[<v>%a@]" (pp_list "@ @ " pp_ec_item) prog

(* ------------------------------------------------------------------- *)
(* Array theory cloning *)


(* For negative lengths, we need to import Int. We import it systematically. *)
let pp_import_Int fmt () =
  Format.fprintf fmt "require import Int.@ @ "

let fmt_array_decl fmt i =
  Format.fprintf fmt "@[<v>";
  pp_import_Int fmt ();
  Format.fprintf fmt "from Jasmin require import JArray.@ @ ";
  Format.fprintf fmt "clone export PolyArray as Array%a  with op size <= %i.@]@." pp_length i i

let fmt_warray_decl fmt i =
  Format.fprintf fmt "@[<v>";
  pp_import_Int fmt ();
  Format.fprintf fmt "from Jasmin require import JWord_array.@ @ ";
  Format.fprintf fmt "clone export WArray as WArray%a  with op size <= %i.@]@." pp_length i i

let fmt_op fmt (op_name, v) = Format.fprintf fmt "op %s <= %i" op_name v

let fmt_the fmt (th, v) = Format.fprintf fmt "theory %s <= %s" th v

let fmt_th fmt (th, v) = Format.fprintf fmt "theory %s <= %s" th v

let fmt_arraywords_decl fmt (aw: int arraywords) =
  let arrayn = Format.asprintf "Array%a" pp_length aw.sizea in
  let warrayn = Format.asprintf "WArray%a" pp_length (aw.sizew*aw.sizea) in
  let fmt_insts fmt (aw: int arraywords) =
    Format.fprintf fmt "%a,@ %a,@ %a,@ %a,@ %a"
    fmt_op ("sizeW", aw.sizew)
    fmt_op ("sizeA", aw.sizea)
    fmt_th ("Word", Format.sprintf "W%i" (8*aw.sizew))
    fmt_th ("ArrayN", arrayn)
    fmt_th ("WArrayN", warrayn)
  in
  Format.fprintf fmt "@[<v>";
  pp_import_Int fmt ();
  Format.fprintf fmt "from Jasmin require import JWord JWord_array.@ @ ";
  Format.fprintf fmt "require import %s %s.@ @ " arrayn warrayn;
  Format.fprintf fmt "clone export ArrayWords as %s  with @[%a@].@]@."
    (fmt_array_theory (ArrayWords aw))
    fmt_insts aw

let fmt_subarray_decl fmt (s: int subarray) =
  let arrays = Format.asprintf "Array%a" pp_length s.sizes in
  let arrayb = Format.asprintf "Array%a" pp_length s.sizeb in
  let fmt_insts fmt (s: int subarray) =
    Format.fprintf fmt "%a,@ %a,@ %a,@ %a"
    fmt_op ("sizeS", s.sizes)
    fmt_op ("sizeB", s.sizeb)
    fmt_th ("ArrayS", arrays)
    fmt_th ("ArrayB", arrayb)
  in
  Format.fprintf fmt "@[<v>";
  pp_import_Int fmt ();
  Format.fprintf fmt "from Jasmin require import JArray.@ @ ";
  Format.fprintf fmt "require import %s %s.@ @ " arrays arrayb;
  Format.fprintf fmt "clone export SubArray as %s  with @[%a@].@]@."
    (fmt_array_theory (SubArray s))
    fmt_insts s

let fmt_subarraydirect_decl fmt (s: int subarraydirect) =
  let arrayws = fmt_array_theory (ArrayWords {sizew=s.sizew; sizea=s.sizes}) in
  let arraywb = fmt_array_theory (ArrayWords {sizew=s.sizew; sizea=s.sizeb}) in
  let fmt_insts fmt (s: int subarraydirect) =
    Format.fprintf fmt "%a,@ %a,@ %a,@ %a,@ %a,@ %a"
    fmt_op ("sizeW", s.sizew)
    fmt_op ("sizeS", s.sizes)
    fmt_op ("sizeB", s.sizeb)
    fmt_the ("Word", Format.sprintf "W%i" (8*s.sizew))
    fmt_th ("ArrayWordsS", arrayws)
    fmt_th ("ArrayWordsB", arraywb)
  in
  Format.fprintf fmt "@[<v>";
  pp_import_Int fmt ();
  Format.fprintf fmt "from Jasmin require import JWord JWord_array.@ @ ";
  Format.fprintf fmt "require import %s %s.@ @ " arrayws arraywb;
  Format.fprintf fmt "clone export SubArrayDirect as %s  with @[%a@].@]@."
    (fmt_array_theory (SubArrayDirect s))
    fmt_insts s

let fmt_subarraycast_decl fmt (s: int subarraycast) =
  let arrayws = fmt_array_theory (ArrayWords {sizew=s.sizews; sizea=s.sizes}) in
  let arraywb = fmt_array_theory (ArrayWords {sizew=s.sizewb; sizea=s.sizeb}) in
  let fmt_insts fmt (s: int subarraycast) =
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
  Format.fprintf fmt "@[<v>";
  pp_import_Int fmt ();
  Format.fprintf fmt "from Jasmin require import JWord JWord_array.@ @ ";
  Format.fprintf fmt "require import %s %s.@ @ " arrayws arraywb;
  Format.fprintf fmt "clone export SubArrayCast as %s  with @[%a@].@]@."
    (fmt_array_theory (SubArrayCast s))
    fmt_insts s

let fmt_arrayaccesscast_decl fmt (s: int arrayaccesscast) =
  let arraywb = fmt_array_theory (ArrayWords {sizew=s.sizewb; sizea=s.sizeb}) in
  let fmt_insts fmt (s: int arrayaccesscast) =
    Format.fprintf fmt "%a,@ %a,@ %a,@ %a,@ %a,@ %a"
    fmt_op ("sizeWS", s.sizews)
    fmt_op ("sizeWB", s.sizewb)
    fmt_op ("sizeB", s.sizeb)
    fmt_the ("WordS", Format.sprintf "W%i" (8*s.sizews))
    fmt_the ("WordB", Format.sprintf "W%i" (8*s.sizewb))
    fmt_th ("ArrayWordsB", arraywb)
  in
  Format.fprintf fmt "@[<v>";
  pp_import_Int fmt ();
  Format.fprintf fmt "from Jasmin require import JWord JWord_array.@ @ ";
  Format.fprintf fmt "require import %s.@ @ " arraywb;
  Format.fprintf fmt "clone export ArrayAccessCast as %s  with @[%a@].@]@."
    (fmt_array_theory (ArrayAccessCast s))
    fmt_insts s

let fmt_bytearray_decl fmt n =
  Format.fprintf fmt "@[<v>";
  pp_import_Int fmt ();
  Format.fprintf fmt "from Jasmin require import JByte_array.@ @ ";
  Format.fprintf fmt "clone include ByteArray with op size <= %i.@]@." n

let fmt_subbytearray_decl fmt (s:int subarray) =
  let arrays = fmt_array_theory (ByteArray s.sizes) in
  let arrayb = fmt_array_theory (ByteArray s.sizeb) in
  let fmt_insts fmt =
    Format.fprintf fmt "%a,@ %a"
    fmt_th ("Asmall", arrays)
    fmt_th ("Abig", arrayb)
  in
  Format.fprintf fmt "@[<v>";
  pp_import_Int fmt ();
  Format.fprintf fmt "from Jasmin require import JByte_array.@ @ ";
  Format.fprintf fmt "require import %s %s.@ @ " arrays arrayb;
  Format.fprintf fmt "clone SubByteArray as %s  with @[%t@].@]@."
    (fmt_array_theory (SubByteArray s))
    fmt_insts

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

let ec_ident s = Eident [s]
let ec_aget a i = Eop2 (ArrayGet, a, i)
let ec_int x = Econst (Z.of_int x)

let ec_vars (env: Env.t) (x: pvar) = Env.get_varname env x
let ec_vari env (x:pvar) = Eident [ec_vars env x]

let glob_mem = ["Glob"; "mem"]
let glob_memi = Eident glob_mem

let ec_apps1 s e = Eapp (ec_ident s, [e])

let ec_zeroext_sz (szo, szi) e =
  let io, ii = int_of_ws szo, int_of_ws szi in
  if ii < io then ec_apps1 (Format.sprintf "zeroextu%i" io) e
  else if ii = io then e
  else (* io < ii *) ec_apps1 (Format.sprintf "truncateu%i" io) e

let ec_zeroext (t_o, t_i) e =
  if t_o = t_i then e else ec_zeroext_sz (ws_of_ty t_o, ws_of_ty t_i) e

let ec_Array env n = Env.add_Array env n; Format.asprintf "Array%a" pp_length n
let ec_PArray env n =
  Env.add_AArray env n;
  Env.abstract_name env (Array n)

let ec_WArray env n = Env.add_WArray env n; Format.asprintf "WArray%a" pp_length n
let ec_PWArray env n =
  Env.add_AWArray env n;
  Env.abstract_name env (WArray n)
let ec_BArray env n = Env.add_BArray env n; Format.asprintf "BArray%a" pp_length n

let ec_PBArray env size =
  Env.add_ABArray env size;
  Env.abstract_name env (ByteArray size)
  

let ec_SBArray env s =
  Env.add_SBArray env s;
  Format.asprintf "SBArray%a_%a" pp_length s.sizeb pp_length s.sizes

let ec_PSBArray env s = 
  Env.add_ASBArray env s;
  Env.abstract_name env (SubByteArray s)


let toec_ty onarray env ty = match ty with
    | Bty Bool -> "bool"
    | Bty Int  -> "int"
    | Bty (U ws) -> Format.sprintf "%s.t" (fmt_Wsz ws)
    | Arr(ws,n) -> onarray env ws n

let onarray_ty_dfl env ws n =
  match get_int n with
  | Some n ->
    Format.sprintf "%s.t %s.t" (fmt_Wsz ws) (ec_Array env n)
  | None ->
    Format.sprintf "%s.t %s.t" (fmt_Wsz ws) (ec_PArray env n)
  

let of_list_dfl env ws n =
  let witness = Format.asprintf "witness<:%s.t>" (fmt_Wsz ws) in
  Eapp (Eident [ec_Array env n; "of_list"], [ec_ident witness])

let randombytes_suffix_dfl ws n =
  if ws = U8 then
    (* in the U8 case, we just print the length for backward compatibility *)
    Format.asprintf "%a" pp_length n
  else
    Format.asprintf "%a%s" pp_length n (fmt_Wsz ws)

(* ------------------------------------------------------------------- *)
(* Extraction of array operations *)

module type EcArray = sig
  val ec_darray8: Env.t -> wsize -> int -> ec_expr
  val ec_cast_array: Env.t -> wsize * pexpr_ -> wsize * pexpr_ -> ec_expr -> ec_expr
  val toec_pget: Env.t -> Memory_model.aligned * Warray_.arr_access * wsize * pvar * ec_expr -> ec_expr
  val toec_psub: Env.t -> Warray_.arr_access * wsize * pexpr_ * pexpr_ ggvar * ec_expr -> ec_expr
  val toec_laset: Env.t -> Warray_.arr_access * wsize * pvar * ec_expr -> ec_expr -> ec_instr
  val toec_lasub: Env.t -> (Env.t -> pexpr -> ec_expr) -> Warray_.arr_access * wsize * pexpr_ * pvar L.located * ec_expr -> ec_expr -> ec_expr

  val onarray_ty: Env.t -> wsize -> pexpr_ -> string
  val add_arr: Env.t -> wsize -> int -> unit
  val add_jarray: Env.t -> wsize -> int -> unit
  val add_abstract_array: Env.t -> wsize -> pexpr_ -> unit
  val randombytes_suffix: wsize -> int -> string
  val of_byte_list: (Env.t -> wsize -> pexpr_ -> ec_expr) option
  val of_list:  Env.t -> wsize -> int -> ec_expr

end


module EcArrayOld : EcArray = struct
  let ec_WArray_init env ws n =
    match get_int n with
    | Some n -> 
        Eident [ec_WArray env (arr_size ws n); Format.sprintf "init%i" (int_of_ws ws)]
    | None ->
      
      Eident [ec_PWArray env (PE (arr_size_pexpr_ ws n)); Format.sprintf "init%i" (int_of_ws ws)]

  let ec_WArray_initf env ws n f =
    let i = Env.create_name env "i" in
    Eapp (ec_WArray_init env ws n, [Efun1 (i, f i)])

  let ec_Array_init env len = 
    match get_int len with
    | Some len -> Eident [ec_Array env len; "init"]
    | None -> Eident [ec_PArray env len; "init"]

  let ec_initi env (x, n, ws) =
    let f i = ec_aget x (ec_ident i) in
    ec_WArray_initf env ws n f

  let ec_initi_var env (x, n, ws) = ec_initi env (ec_vari env x, n, ws)

  let ec_darray8 env ws n =
    let wa = ec_WArray env (arr_size ws n) in
    let geti = Format.sprintf "get%i" (int_of_ws ws) in
    let eto = Efun1 ("a", Eapp (Eident [ec_Array env n; "init"], [
      Efun1 ("i", Eapp (Eident [wa; geti], [ec_ident "a"; ec_ident "i"]))
      ])) in
    Eapp (
            ec_ident "dmap",
            [Eident [wa; "darray"]; eto]
          )

  let ec_cast_array env (ws, n) (wse, ne) e =
    let i = Env.create_name env "i" in
    let geti = ec_ident (Format.sprintf "get%i" (int_of_ws ws)) in
    let init_fun = Efun1 (i, Eapp (geti, [ec_initi env (e, ne, wse); ec_ident i])) in
    Eapp (ec_Array_init env n, [init_fun])

  let toec_pget env (_a, aa, ws, x, e) =
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
        let warray =
          match get_int n with
          | Some n -> 
            let nws = n * int_of_ws xws in
            ec_WArray env (nws / 8) 
          | None ->
            ec_PWArray env (PE (arr_size_pexpr_ xws n))
        in
        let waget = Eident [warray; Format.sprintf "get%i" (int_of_ws xws)] in
        let wsi = int_of_ws ws in
        let waset = Eident [warray; Format.sprintf "set%i%s" wsi (fmt_access aa)] in
        let updwa = Eapp (waset, [ec_initi_var env (x, n, xws); e1; e]) in
        Eapp (ec_Array_init env n, [Eapp (waget, [updwa])]) in
      ESasgn ([LvIdent [ec_vars env x]], eset)

  let toec_lasub env toec_expr (aa, ws, len, x, e1) e =
    assert (check_array env x);
    let x = L.unloc x in
    let (xws, n) = array_kind x.v_ty in
    if ws = xws && aa = Warray_.AAscale then
        let i = Env.create_name env "i" in
        let range_ub = 
          match get_int len with
          | Some len -> Eop2 (Plus, e1, ec_int len)
          | None -> 
            let len = toec_expr env (pexpr_of_pexpr_ len) in
            Eop2 (Plus, e1, len)
        in
        Eapp (ec_Array_init env n, [
            Efun1 (i, Eop3 (
                If,
                Eop3 (InORange, e1, ec_ident i, range_ub),
                ec_aget e (Eop2 (Infix "-", ec_ident i, e1)),
                ec_aget (ec_vari env x) (ec_ident i)
                ))
        ])
    else
     let start =
        if aa = Warray_.AAscale then
          Eop2 (Infix "*", ec_int (int_of_ws ws / 8), e1)
        else
          e1
      in
      let i = Env.create_name env "i" in
      let aw_get len = 
        match get_int len with
        | Some len -> ec_WArray env (len* int_of_ws ws / 8 )
        | None -> 
          let size = Papp2 (Omul Op_int, pexpr_of_pexpr_ len , icnst (int_of_ws ws /8)) in
          ec_PWArray env (PE size)
      in
      let at = Eapp (Eident[aw_get len; "get8"], [ec_initi env (e, len, ws); Eop2 (Infix "-", ec_ident i, start)]) in
      let ae = Eapp (Eident[aw_get n; "get8"], [ec_initi_var env (x, n, xws); ec_ident i]) in
      let len8 =
        match get_int len with
        | Some len ->ec_int (len * int_of_ws ws / 8)
        | None -> 
          toec_expr env (arr_size_pexpr_ ws len)
      in
      let in_range = Eop3 (InORange, start, ec_ident i, Eop2 (Plus, start, len8)) in
      let ainit = Eident [aw_get n; "init8"] in
      let a = Eapp (ainit, [Efun1 (i, Eop3 (If, in_range, at, ae))]) in
      let wag = Eident [aw_get n; Format.sprintf "get%i" (int_of_ws xws)] in
      Eapp (ec_Array_init env n, [Eapp (wag, [a])])

  let onarray_ty = onarray_ty_dfl

  let add_arr env _ws n = Env.add_Array env n
  let add_jarray env ws n = Env.add_jarray env ws n
  let add_abstract_array env ws n = 
    let size = PE (arr_size_pexpr_ ws n) in
    Env.add_AArray env n;
    Env.add_AWArray env size

  let randombytes_suffix = randombytes_suffix_dfl
  let of_byte_list = None

  let of_list =  of_list_dfl
end


module EcWArray : EcArray  = struct
  let ec_darray8 env ws n =
    Env.add_ArrayWords env (ws2bytes ws) (PE (icnst n));
    let aw = fmt_array_theory (ArrayWords { sizew=ws2bytes ws; sizea=n }) in
    let eto = Eident [aw; "to_word_array"] in
    Eapp (
            ec_ident "dmap",
            [Eident [ec_WArray env (arr_size ws n); "darray"]; eto]
          )

  let ec_cast_array env (ws, n) (wse, ne) e =
    let sizews = ws2bytes ws in
    let sizewb = ws2bytes wse in
    let sa = Env.add_SubArrayCast env sizews sizewb n ne in
    Eapp (Eident [sa; "get_sub"], [e; ec_int 0])

  let toec_pget env (_a, aa, ws, x, e) =
    let (xws,n) = array_kind x.v_ty in
    if ws = xws && aa = Warray_.AAscale then
       ec_aget (ec_vari env x) e
    else
      let sizews = ws2bytes ws in
      let sizewb = ws2bytes xws in
      let arrayaccesscast = Env.add_ArrayAccessCast env sizews sizewb n in
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
          let subarray = Env.add_SubArray env len n in
          Eident [subarray; "get_sub"]
        end else begin
          (* Sub-array access unaligned *)
          let sizew = ws2bytes ws in
          let sa = Env.add_SubArrayDirect env sizew len n in
          Eident [sa; "get_sub_direct"]
        end
      else begin
        (* Sub-array access typecast (direct or not) *)
        let get_sub = if aa = Warray_.AAscale then "get_sub" else "get_sub_direct" in
        let sizews = ws2bytes ws in
        let sizewb = ws2bytes xws in
        let sa = Env.add_SubArrayCast env sizews sizewb len n in
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
        let arrayaccesscast = Env.add_ArrayAccessCast env sizews sizewb n in
        let setf = Format.sprintf "set_cast%s" (fmt_access aa) in
        let subf = Eident [arrayaccesscast; setf] in
        Eapp (subf, [ec_vari env x; e1; e]) in
      ESasgn ([LvIdent [ec_vars env x]], eset)

  let toec_lasub env _ (aa, ws, len, x, e1) e =
    assert (check_array env x);
    let x = L.unloc x in
    let (xws, n) = array_kind x.v_ty in
    let subf =
      if ws = xws then
        if aa = Warray_.AAscale then begin
          (* Sub-array update aligned *)
          let subarray = Env.add_SubArray env len n in
          Eident [subarray; "set_sub"]
        end else begin
          (* Sub-array update unaligned *)
          let sizew = ws2bytes ws in
          let sa = Env.add_SubArrayDirect env sizew len n in
          Eident [sa; "set_sub_direct"]
        end
      else begin
        (* Sub-array update typecast (direct or not) *)
        let set_sub = if aa = Warray_.AAscale then "set_sub" else "set_sub_direct" in
        let sizews = ws2bytes ws in
        let sizewb = ws2bytes xws in
        let sa = Env.add_SubArrayCast env sizews sizewb len n in
        Eident [sa; set_sub]
      end
    in
    Eapp (subf, [ec_vari env x; e1; e])

  let onarray_ty = onarray_ty_dfl

  let add_arr env _ws n = Env.add_Array env n

  let add_jarray env ws n = Env.add_jarray env ws n

  let add_abstract_array env ws n = 
    let size = PE (arr_size_pexpr_ ws n) in
    Env.add_AArray env n;
    Env.add_AWArray env size

  let randombytes_suffix = randombytes_suffix_dfl
  let of_byte_list = None
  let of_list =  of_list_dfl
end

module EcBArray : EcArray = struct
  let arr_size_pexpr_ ws n = Pretyping.canon_expr (arr_size_pexpr_ ws n)

  let ec_darray8 (env: Env.t) ws (n:int) =
    Eident [ec_BArray env (arr_size ws n); "darray"]

  let ec_cast_array (_env:Env.t) (ws1, sz1) (ws2, sz2) e =
    match get_int sz1, get_int sz2 with
    | Some sz1, Some sz2 ->
      assert (Prog.arr_size ws1 sz1 = Prog.arr_size ws2 sz2);
      e
    | _ -> e (* assume it was type checked before*)

  let direct aa =
    match aa with
    | Warray_.AAdirect -> "d"
    | Warray_.AAscale -> ""

  let scale aa ws =
    match aa with
    | Warray_.AAdirect -> ""
    | Warray_.AAscale -> Format.sprintf "%i" (int_of_ws ws)

  let toec_pget (env:Env.t) (_a, aa, ws, x, ei) =
    let (xws, n) = array_kind x.v_ty in
    match get_int n with
    | Some n -> 
      let sz = arr_size xws n in
      Eapp (Eident [ec_BArray env sz; Format.sprintf "get%i%s" (int_of_ws ws) (direct aa)],[ec_vari env x; ei])
    | None -> 
      let sz = PE (arr_size_pexpr_ xws n)in
      Eapp (Eident [ec_PBArray env sz; Format.sprintf "get%i%s" (int_of_ws ws) (direct aa)],[ec_vari env x;ei])

  let toec_laset (env:Env.t) (aa, ws, x, ei) e =
    let (xws,n) = array_kind x.v_ty in
    match get_int n with
    | Some n -> 
      let sz = arr_size xws n in
      let eset =
        Eapp (Eident [ec_BArray env sz; Format.sprintf "set%i%s" (int_of_ws ws) (direct aa)],
            [ec_vari env x; ei; e]) in
      ESasgn ([LvIdent [ec_vars env x]], eset)
    | None -> 
      let sz = PE (arr_size_pexpr_ xws n) in
      let eset =
        Eapp (Eident [ec_PBArray env sz; Format.sprintf "set%i%s" (int_of_ws ws) (direct aa)],
            [ec_vari env x; ei; e]) in
      ESasgn ([LvIdent [ec_vars env x]], eset)


  let toec_psub (env:Env.t) (aa, ws, len, x, ei) =
    let x = L.unloc x.gv in
    let (xws,n) = array_kind x.v_ty in
    match get_int n, get_int len with
    | Some n, Some len ->
        let sizes = arr_size ws len in
        let sizeb = arr_size xws n in
        let s = { sizes; sizeb } in
        Eapp(Eident [ec_SBArray env s; Format.sprintf "get_sub%s" (scale aa ws)], [ec_vari env x; ei])
    | _ -> 
      let sizes = PE (arr_size_pexpr_ ws len) in
      let sizeb = PE (arr_size_pexpr_ xws n) in
      let s = { sizes; sizeb } in
      Eapp(Eident [ec_PSBArray env s; Format.sprintf "get_sub%s" (scale aa ws)], [ec_vari env x; ei])

  let toec_lasub (env:Env.t) _ (aa, ws, len, x, ei) e =
    let x = L.unloc x in
    let (xws,n) = array_kind x.v_ty in
    match get_int n, get_int len with
    | Some n, Some len ->
      let sizes = arr_size ws len in
      let sizeb = arr_size xws n in
      let s = { sizes; sizeb } in
      Eapp(Eident [ec_SBArray env s; Format.sprintf "set_sub%s" (scale aa ws)],
           [ec_vari env x; ei; e])
    | _ ->
      let sizes = PE (arr_size_pexpr_ ws len) in
      let sizeb = PE (arr_size_pexpr_ xws n) in
      let s = { sizes; sizeb } in
       Eapp(Eident [ec_PSBArray env s; Format.sprintf "set_sub%s" (scale aa ws)],
           [ec_vari env x; ei; e])

  let onarray_ty env ws n =
    match get_int n with
    | Some n ->
      Format.sprintf "%s.t" (ec_BArray env (arr_size ws n))
    | None ->
       Format.sprintf "%s.t" (ec_PBArray env (PE (arr_size_pexpr_ ws n)))

  let add_arr env ws n = Env.add_BArray env (arr_size ws n)

  let add_jarray = add_arr

  let add_abstract_array env ws n = 
    let size = PE (arr_size_pexpr_ ws n) in
    Env.add_ABArray env size

  let randombytes_suffix ws n =
    Format.asprintf "%i" (arr_size ws n)

  let of_byte_list = Some (fun env ws n ->
    match get_int n with
    | Some n -> Eident [ec_BArray env (arr_size ws n); "of_list"]
    | None -> Eident [ec_PBArray env (PE (arr_size_pexpr_ ws n)); "of_list"])

  let of_list env ws n =
    Eident [ec_BArray env (arr_size ws n); Format.sprintf "of_list%i" (int_of_ws ws)]

end


(* ------------------------------------------------------------------- *)
(* Jasmin AST transformation and helpers *)

let base_op = function
  | Sopn.Oasm (Arch_extra.BaseOp (_, o)) -> Sopn.Oasm (Arch_extra.BaseOp(None,o))
  | o -> o

let ty_expr (e: pexpr) = 
  match e with
  | Pconst _       -> tint
  | Pbool _        -> tbool
  | Parr_init (ws, len) -> Arr (ws, len)
  | Pvar x         -> x.gv.L.pl_desc.v_ty
  | Pload (_, sz,_) -> tu sz
  | Pget  (_,_, sz,_,_) -> tu sz
  | Psub (_,ws, len, _, _) -> Arr(ws, len)
  | Papp1 (op,_)   -> Conv.pty_of_cty (snd (Operators.type_of_op1 op))
  | Papp2 (op,_,_) -> Conv.pty_of_cty (snd (Operators.type_of_op2 op))
  | PappN (op, _)  -> Conv.pty_of_cty (snd (Operators.type_of_opN op))
  | Pif (ty,_,_,_) -> ty

let ty_sopn pd msfsz asmOp op (es: pexpr list) =
  match op with
  (* Do a special case for copy since the Coq type loose information  *)
  | Sopn.Opseudo_op (Pseudo_operator.Ocopy _) ->
    let l = List.map ty_expr es in
    l, l
  | Sopn.Opseudo_op (Pseudo_operator.Oswap _) ->
    let l = List.map ty_expr es in
    l, l
  | _ ->
    List.map Conv.pty_of_cty (Sopn.sopn_tout pd msfsz asmOp op),
    List.map Conv.pty_of_cty (Sopn.sopn_tin pd msfsz asmOp op)

(* This code replaces for loop that modify the loop counter by while loop,
   it would be nice to prove in Coq the validity of the transformation *)

let is_write_lv x = function
  | Lnone _ | Lmem _ -> false
  | Lvar x' | Laset(_, _, _, x', _) | Lasub (_, _, _, x', _) ->
    PV.equal x x'.L.pl_desc

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
    PV.equal x x'.L.pl_desc || is_write_c x c

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
        let jd' = GV.clone jd in
        let j' = { j with pl_desc = jd' } in
        let ii' = Cassgn (Lvar j, E.AT_inline, jd.v_ty, Pvar (gkvar j')) in
        let ii' = { i with i_desc = ii' } in
        Cfor (j', r, ii' :: remove_for c)
  in
  { i with i_desc }
and remove_for c = List.map remove_for_i c

let rec toec_while_i i =
  match i.i_desc with
  | Cassgn _ | Copn _ | Csyscall _ | Cassert _ | Ccall _ -> [i]
  | Cif (e, c1, c2) -> [{ i with i_desc = Cif (e, toec_while c1, toec_while c2) }]
  | Cfor (x, r, c) -> [{ i with i_desc = Cfor (x, r, toec_while c) }]
  | Cwhile (a, c1, e, ii, c2) ->
    let c1 = toec_while c1 in
    let c2 = toec_while c2 in
    c1 @ [{ i with i_desc = Cwhile (a, [], e, ii, c2 @ c1) }]
and toec_while c = List.concat_map toec_while_i c

let wi2i_op2 = function
  | Owi2 (s, _, op) ->
    begin match op with
    | WIadd -> Oadd Op_int
    | WImul -> Omul Op_int
    | WIsub -> Osub Op_int
    | WIdiv -> Odiv (s, Op_int)
    | WImod -> Omod (s, Op_int)
    | WIshl -> Olsl Op_int
    | WIshr -> Oasr Op_int
    | WIeq  -> Oeq Op_int
    | WIneq -> Oneq Op_int
    | WIlt  -> Olt Cmp_int
    | WIle  -> Ole Cmp_int
    | WIgt  -> Ogt Cmp_int
    | WIge  -> Oge Cmp_int
    end
  | o -> o

let wi2i_op1_e o e =
  match o with
  | Owi1 (s, o) ->
    begin match o with
    | WIwint_of_int _ | WIint_of_wint _ -> e
    | WIword_of_wint ws -> Papp1 (Owi1 (s, WIwint_of_int ws), e)
    | WIwint_of_word ws -> Papp1 (Oint_of_word (s, ws), e)
    | WIwint_ext (szo, szi) ->
      if int_of_ws szi <= int_of_ws szo then e
      else
        let ext = if s = Signed then Osignext (szo, szi) else Ozeroext (szo, szi) in
        Papp1 (Oint_of_word (s, szo), Papp1 (ext, Papp1 (Oword_of_int szi, e)))
    | WIneg _ -> Papp1 (Oneg Op_int, e)
    end
  | o -> Papp1 (o, e)

let wi2i_fun (f: ('info, 'asm) pfunc) : ('info, 'asm) pfunc =
  let m = Spv.fold (fun x m ->
      match x.v_ty, Annotations.has_wint x.v_annot with
      | Bty (U _), Some sg ->
        Mpv.add x (sg, PV.mk x.v_name x.v_kind (Bty Int) x.v_dloc (Annotations.remove_wint x.v_annot)) m
      | _ -> m) (pvars_fc f) Mpv.empty in
  if Mpv.is_empty m then f else
  let sign_v x = Option.map fst (Mpv.find_opt (L.unloc x) m) in
  let rec sign_e = function
    | Pvar x -> sign_v x.gv
    | Papp1 (Owi1 (s, (WIwint_of_int _ | WIwint_of_word _ | WIwint_ext _ | WIneg _)), _) -> Some s
    | Papp2 (Owi2 (s, _, (WIadd | WImul | WIsub | WIdiv | WImod | WIshl | WIshr)), _, _) -> Some s
    | Pif (_, _, e, _) -> sign_e e
    | _ -> None in
  let wi2i_type sg ty = if sg = None then ty else Bty Int in
  let rec wi2i_e = function
    | (Pconst _ | Pbool _ | Parr_init _ | Pvar _) as e -> e
    | Pget (al, aa, ws, x, e) -> Pget (al, aa, ws, x, wi2i_e e)
    | Psub (aa, ws, len, x, e) -> Psub (aa, ws, len, x, wi2i_e e)
    | Pload (al, ws, e) -> Pload (al, ws, wi2i_e e)
    | Papp1 (o, e) -> wi2i_op1_e o (wi2i_e e)
    | Papp2 (o, e1, e2) -> Papp2 (wi2i_op2 o, wi2i_e e1, wi2i_e e2)
    | PappN (o, es) -> PappN (o, List.map wi2i_e es)
    | Pif (ty, e1, e2, e3) -> Pif (wi2i_type (sign_e e2) ty, wi2i_e e1, wi2i_e e2, wi2i_e e3) in
  let wi2i_lv sg = function
    | Lnone (l, ty) -> Lnone (l, wi2i_type sg ty)
    | Lvar _ as lv -> lv
    | Lmem (al, ws, l, e) -> Lmem (al, ws, l, wi2i_e e)
    | Laset (al, aa, ws, x, e) -> Laset (al, aa, ws, x, wi2i_e e)
    | Lasub (aa, ws, len, x, e) -> Lasub (aa, ws, len, x, wi2i_e e) in
  let wi2i_lvs = List.map (wi2i_lv None) in
  let wi2i_es = List.map wi2i_e in
  let patch_op o es =
    let sg e = sign_e e in
    match o with
    | Sopn.Opseudo_op (Pseudo_operator.Ospill (k, tys)) when List.length tys = List.length es ->
      Sopn.Opseudo_op (Pseudo_operator.Ospill (k, List.map2 (fun ty e -> if sg e = None then ty else Type.Coq_aint) tys es))
    | Sopn.Opseudo_op (Pseudo_operator.Oswap ty) ->
      Sopn.Opseudo_op (Pseudo_operator.Oswap (if sg (List.hd es) = None then ty else Type.Coq_aint))
    | Sopn.Opseudo_op (Pseudo_operator.Odeclassify ty) ->
      Sopn.Opseudo_op (Pseudo_operator.Odeclassify (if sg (List.hd es) = None then ty else Type.Coq_aint))
    | o -> o in
  let rec wi2i_i i =
    let i_desc =
      match i.i_desc with
      | Cassgn (x, tag, ty, e) ->
        let sg = sign_e e in
        Cassgn (wi2i_lv sg x, tag, wi2i_type sg ty, wi2i_e e)
      | Copn (xs, t, o, es) -> Copn (wi2i_lvs xs, t, patch_op o es, wi2i_es es)
      | Csyscall (xs, o, es) -> Csyscall (wi2i_lvs xs, o, wi2i_es es)
      | Cassert _ as c -> c
      | Cif (b, c1, c2) -> Cif (wi2i_e b, wi2i_c c1, wi2i_c c2)
      | Cfor (x, (d, e1, e2), c) -> Cfor (x, (d, wi2i_e e1, wi2i_e e2), wi2i_c c)
      | Cwhile (a, c, e, ii, c') -> Cwhile (a, wi2i_c c, wi2i_e e, ii, wi2i_c c')
      | Ccall (xs, fn, es) -> Ccall (wi2i_lvs xs, fn, wi2i_es es)
    in
    { i with i_desc }
  and wi2i_c c = List.map wi2i_i c in
  let mk xs tys = List.map2 (fun x ty -> wi2i_type (sign_v x) ty) xs tys in
  let f = { f with
            f_tyin = mk (List.map (fun x -> L.mk_loc L._dummy x) f.f_args) f.f_tyin;
            f_tyout = mk f.f_ret f.f_tyout;
            f_body = wi2i_c f.f_body } in
  let subst v =
    match Mpv.find_opt (L.unloc v.gv) m with
    | Some (_, x') -> Pvar { v with gv = L.mk_loc (L.loc v.gv) x' }
    | None -> Pvar v in
  Subst.gsubst_func (fun ?loc:_ l -> l) subst f

let fill_in_missing_names (f: ('info, 'asm) pfunc) : ('info, 'asm) pfunc =
  let fresh_name : L.t -> pty -> pvar_i =
    let count = ref 0 in
    fun loc ty ->
      let n = Printf.sprintf " _%d" !count in
      incr count;
      L.mk_loc loc (PV.mk n (Reg(Normal, Direct)) ty L._dummy [])
  in
  let fill_lv =
    function
    | Lnone(p, ty) -> Lvar (fresh_name p ty)
    | x -> x in
  let fill_lvs lvs = List.map fill_lv lvs in
  let rec fill_instr_r =
    function
    | Cassgn (lv, tg, ty, e) -> Cassgn (fill_lv lv, tg, ty, e)
    | Copn (lvs, tg, op, es) -> Copn (fill_lvs lvs, tg, op, es)
    | Csyscall (lvs, op, es) -> Csyscall(fill_lvs lvs, op, es)
    | Cassert (msg, e) -> Cassert (msg, e)
    | Cif (e, s1, s2) -> Cif (e, fill_stmt s1, fill_stmt s2)
    | Cfor (i, r, s) -> Cfor (i, r, fill_stmt s)
    | Cwhile (a, s, e, loc, s') -> Cwhile (a, fill_stmt s, e, loc, fill_stmt s')
    | Ccall (lvs, f, es) -> Ccall (fill_lvs lvs, f, es)
  and fill_instr i = { i with i_desc = fill_instr_r i.i_desc }
  and fill_stmt s = List.map fill_instr s in
  let f_body = fill_stmt f.f_body in
  { f with f_body }

let rec is_const_bound = function
  | Pconst _ -> true
  | Pvar x -> let x = L.unloc x.gv in x.v_kind = Const && x.v_ty = Bty Int
  | Papp1 (_, e) -> is_const_bound e
  | Papp2 (_, e1, e2) -> is_const_bound e1 && is_const_bound e2
  | _ -> false

let ty_lval = function
  | Lnone (_, ty) -> ty
  | Lvar x -> (L.unloc x).v_ty
  | Lmem (_, ws,_,_) | Laset(_, _, ws, _, _) -> Bty (U ws)
  | Lasub (_,ws, len, _, _) -> Arr(ws, len)

let is_array_copy (x:plval) (e:pexpr) =
  match x, e with
  | Lvar x, Pvar y ->
    let x = L.unloc x in
    let y = L.unloc y.gv in
    begin match x.v_ty, y.v_ty with
    | Arr (xws, xn), Arr (yws, yn) ->
      begin match get_int xn, get_int yn with
      | Some xn', Some yn' when arr_size yws yn' < arr_size xws xn' -> None
      | _ ->
        if x.v_kind = Reg(Normal, Direct) then Some xws
        else if y.v_kind = Reg(Normal, Direct) then Some yws
        else None
      end
    | _ -> None
    end
  | _ -> None

let rec insert_copy_and_fix_length_i i =
  let i_desc =
    match i.i_desc with
    | Cassgn (x, t, _, e) ->
      begin match is_array_copy x e with
      | None -> i.i_desc
      | Some ws -> Copn([x], t, Sopn.Opseudo_op (Pseudo_operator.Ocopy(ws, Conv.cz_of_int 1)), [e])
      end
    | Csyscall ([x], Syscall_t.RandomBytes _, es) ->
      begin match ty_lval x with
      | Arr (ws, n) when get_int n <> None ->
        Csyscall ([x], Syscall_t.RandomBytes (ws, Conv.cz_of_int (Option.get (get_int n))), es)
      | _ -> i.i_desc
      end
    | Cif (b, th, el) -> Cif (b, insert_copy_and_fix_length th, insert_copy_and_fix_length el)
    | Cfor (x, r, c) -> Cfor (x, r, insert_copy_and_fix_length c)
    | Cwhile (a, c1, e, info, c2) -> Cwhile (a, insert_copy_and_fix_length c1, e, info, insert_copy_and_fix_length c2)
    | Copn _ | Csyscall _ | Cassert _ | Ccall _ -> i.i_desc
  in
  { i with i_desc }
and insert_copy_and_fix_length c = List.map insert_copy_and_fix_length_i c

module type EcExpression = sig
  val ec_cast: Env.t -> pty * pty -> ec_expr -> ec_expr
  val toec_cast: Env.t -> pty * pexpr -> ec_expr
  val toec_expr: Env.t -> pexpr -> ec_expr
end

let int_of_word ws e = Papp1 (Oint_of_word(Unsigned, ws), e)

let int_of_ptr pd e =
   match e with
   | Papp1(Owi1(_, WIwint_of_int ws), e) when ws = pd -> e
   | _ -> int_of_word pd e

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

  let rec ec_op1 op e = match op with
    | Oword_of_int sz ->
      ec_apps1 (Format.sprintf "%s.of_int" (fmt_Wsz sz)) e
    | Oint_of_word(s, sz) ->
      ec_apps1 (Format.sprintf "%s.to_%sint" (fmt_Wsz sz) (string_of_signess s)) e
    | Osignext(szo,_szi) ->
      ec_apps1 (Format.sprintf "sigextu%i" (int_of_ws szo)) e
    | Ozeroext(szo,szi) -> ec_zeroext_sz (szo, szi) e
    | Onot     -> ec_apps1 "!" e
    | Olnot _  -> ec_apps1 "invw" e
    | Oneg _   -> ec_apps1 "-" e
    | Owi1 (_, WIwint_of_int sz) -> ec_op1 (Oword_of_int sz) e
    | Owi1 _ -> assert false (* other wint operator should have been removed by wint_int or wint_word *)

  let rec toec_expr env (e: pexpr) =
      match e with
      | Pconst z -> Econst z
      | Pbool b -> Ebool b
      | Parr_init (_ws, _n) -> ec_ident "witness"
      | Pvar x -> ec_vari env (L.unloc x.gv)
      | Pget (a, aa, ws, y, e) ->
          EA.toec_pget env (a, aa, ws, L.unloc y.gv, toec_expr env e)
      | Psub (aa, ws, len, x, e) -> EA.toec_psub env (aa, ws, len, x, toec_expr env e)
      | Pload (_, sz, e) ->
          let load = ec_ident (Format.sprintf "loadW%i" (int_of_ws sz)) in
          Eapp (load, [
              glob_memi; toec_expr env (int_of_ptr (Env.pd env) e)
          ])
      | Papp1 (op1, e) ->
            ec_op1 op1 (toec_cast env (Conv.pty_of_cty (fst (Operators.type_of_op1 op1)), e))
      | Papp2 (op2, e1, e2) ->
          let t1, t2 = fst (Operators.type_of_op2 op2) in
          let te1 = (Conv.pty_of_cty t1, e1) in
          let te2 = (Conv.pty_of_cty t2, e2) in
          let te1, te2 = match op2 with
            | Ogt _ | Oge _ -> te2, te1
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
          | Oarray len ->
              Eapp (
                  EA.of_list env U8 (Conv.int_of_cz len),
                  [Elist (List.map (toec_expr env) es)]
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
  val ec_leaks_es: Env.t -> pexprs -> ec_instr list
  val ec_leaks_opn: Env.t -> pexprs -> ec_instr list
  val ec_leaking_if: Env.t -> pexpr -> (Env.t -> ec_stmt) -> (Env.t -> ec_stmt) -> ec_stmt
  val ec_leaking_while: Env.t -> pexpr -> (Env.t -> ec_stmt) -> ec_stmt
  val ec_leaking_for: Env.t -> (Env.t -> ec_stmt) -> pexpr -> pexpr -> ec_stmt -> ec_expr -> ec_stmt -> ec_stmt
  val ec_leaks_lvs: Env.t -> plvals -> ec_stmt
  val global_leakage_vars: Env.t -> (ec_modty * ec_modty) list
  val leakage_imports: Env.t -> ec_item list
  val ec_fun_leak_init: Env.t -> ec_stmt
  val ec_leak_ret: Env.t -> ec_expr list -> ec_expr list
  val ec_leak_rty: Env.t -> ec_ty list -> ec_ty list
  val ec_leak_call_lvs: Env.t -> ec_lvalues
  val ec_leak_call_acc: Env.t -> ec_stmt
end

module EcLeakNormal(EE: EcExpression): EcLeakage = struct
  let ec_leaks_es _env _es = []
  let ec_leaks_opn _env _es = []
  let ec_leaking_if env e c1 c2 = [ESif (EE.toec_expr env e, c1 env, c2 env)]
  let ec_leaking_while env e c =
    [ESwhile (EE.toec_expr env e, c env)]
  let ec_leaking_for env c _e1 _e2 init cond i_upd = init @ [ESwhile (cond, c env @ i_upd)]
  let ec_leaks_lvs _env _lvs = []
  let global_leakage_vars _env = []
  let leakage_imports _env = []
  let ec_fun_leak_init _env = []
  let ec_leak_ret _env ret = ret
  let ec_leak_rty _env rtys = rtys
  let ec_leak_call_lvs _env = []
  let ec_leak_call_acc _env = []
end

module EcLeakConstantTimeGlobal(EE: EcExpression): EcLeakage = struct
  open EE

  let rec leaks_e_rec pd leaks e =
    match e with
    | Pconst _ | Pbool _ | Parr_init _ |Pvar _ -> leaks
    | Pload (_,_,e) -> leaks_e_rec pd (int_of_ptr pd e :: leaks) e
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

  let ec_leaking_while env e c =
    let le = leak_cond env e in
    le @ [ESwhile (EE.toec_expr env e, (c env @ le))]

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
    | Lmem (_, _, _,e) -> leaks_e_rec pd [int_of_ptr pd e] e

  let ec_leaks_lv env lv = ec_leaks (List.map (toec_expr env) (leaks_lval (Env.pd env) lv))

  let ec_leaks_lvs env lvs = List.concat_map (ec_leaks_lv env) lvs

  let global_leakage_vars _env = [("leakages", "leakages_glob_t")]

  let leakage_imports _env = [IfromRequireImport ("Jasmin", ["JLeakage"])]

  let ec_fun_leak_init _env = []

  let ec_leak_ret _env ret = ret

  let ec_leak_rty _env rtys = rtys

  let ec_leak_call_lvs _env = []

  let ec_leak_call_acc _env = []
end

module EcLeakConstantTime(EE: EcExpression): EcLeakage = struct
  open EE

  let asgn s e = ESasgn ([LvIdent [s]], e)

  let leak_addr e = Eapp (ec_ident "Leak_int", [e])

  let leak_val env e =
    let sty = match ty_expr e with
    | Bty Bool -> "bool"
    | Bty Int  -> "int"
    | Bty (U ws) -> fmt_Wsz ws
    | Arr(_ws, _n) -> assert false
    in
    let leakf = ec_ident (Format.sprintf "Leak_%s" sty) in
    [Eapp (leakf, [toec_expr env e])]


  let leak_addr_mem env e =
    let addr = int_of_ptr (Env.pd env) e in
    [leak_addr (toec_expr env addr)]

  let rec leaks_e_rec env leaks e =
    match e with
    | Pconst _ | Pbool _ | Parr_init _ | Pvar _ -> leaks
    | Pload (_,_,e) -> leaks_e_rec env ((leak_addr_mem env e) @ leaks) e
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
    | Lmem (_, _, _,e) -> leaks_e_rec env (leak_addr_mem env e) e

  let ec_leaks_lv env lv = ec_addleaks env (leaks_lval env lv)

  let ec_leaks_lvs env lvs = List.concat_map (ec_leaks_lv env) lvs

  let ec_leaks_opn env es = ec_addleaks env (leaks_es env es)

  let leak_cond env e = (leaks_e env e) @ (leak_val env e)

  let ec_leaking_if env e c1 c2 =
    let acc = leakacc env in
    ec_addleaks env (leak_cond env e) @
    [ESif (toec_expr env e, leak_block env c1 acc, leak_block env c2 acc)]

  let ec_leaking_while env e c =
    let env = Env.new_aux_range env in
    let vleak_cond = Env.create_aux env "leak_cond" leakv_ty in
    let leak_c = Env.create_aux env "_b" leakv_ty in
    let leaking_c = leak_block env c leak_c in
    let reset_c_leak = reset_leak leak_c in
    reset_leak vleak_cond @ reset_c_leak @
    push_leak vleak_cond (leaklist (leak_cond env e)) @
    [ESwhile (
      toec_expr env e,
      leaking_c @ push_leak vleak_cond (leaklist (leak_cond env e))
    )] @
    push_leak (leakacc env) (leaklist ([leaklistv vleak_cond; leaklistv leak_c]))

  let leak_for_bounds env e1 e2 =
    leaks_es env [e1; e2] @ leak_val env e1 @ leak_val env e2

  let ec_leaking_for env c e1 e2 init cond i_upd =
    let leak_c = Env.create_aux env "leak_b" leakv_ty in
    reset_leak leak_c @
    ec_addleaks env (leak_for_bounds env e1 e2) @
    init @
    [ESwhile (cond, leak_block env c leak_c @ i_upd)] @
    push_leak (leakacc env) (leaklistv leak_c)

  let global_leakage_vars _env = []

  let leakage_imports _env = [IfromRequireImport ("Jasmin", ["JLeakage"])]

  let ec_fun_leak_init env = start_leakacc env

  let ec_leak_ret env ret =
    (env |> leakacc |> leaklistv) :: ret

  let leak_ret_ty = "JLeakage.leakage"
  let leak_ret_prefix = "leak_c"

  let ec_leak_rty _env rtys = leak_ret_ty :: rtys

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
      | Lmem(_, ws, _, e1) ->
        let storewi = ec_ident (Format.sprintf "storeW%i" (int_of_ws ws)) in
        let addr = toec_expr env (int_of_ptr (Env.pd env) e1) in
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
          EA.toec_lasub env toec_expr (aa, ws, len, x, toec_expr env e1) e
          )

  let lvals_are_vars lvs = List.for_all (function Lvar _ -> true | _ -> false) lvs

  (* ------------------------------------------------------------------- *)
  (* Instruction extraction *)

  let toec_ty = toec_ty EA.onarray_ty

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
    | Syscall_t.RandomBytes (ws, n) ->
      let n = Conv.int_of_cz n in
      Env.add_randombytes env ws n;
      Format.asprintf "%s.randombytes_%s" syscall_mod_arg (EA.randombytes_suffix ws n)

  let ec_opn pd msfsz asmOp o =
    let s = Format.asprintf "%a" (pp_opn pd msfsz asmOp) o in
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
          [EScomment (Format.sprintf "Erased call to %s" (ec_opn (Env.pd env) (Env.msfsz env) asmOp op))]
      | Copn (lvs, _, op, es) ->
          let op' = base_op op in
          (* Since we do not have merge for the moment only the output type can change *)
          let otys,itys = ty_sopn (Env.pd env) (Env.msfsz env) asmOp op es in
          let otys', _ = ty_sopn (Env.pd env) (Env.msfsz env) asmOp op' es in
          let ec_op op = ec_ident (ec_opn (Env.pd env) (Env.msfsz env) asmOp op) in
          let ec_e op = Eapp (ec_op op, List.map (toec_cast env) (List.combine itys es)) in
          (ec_leaks_opn env es) @
          (ec_expr_assgn env lvs otys otys' (ec_e op'))
      | Ccall (lvs, f, es) ->
          let env = Env.new_aux_range env in
          let otys, itys = Env.get_funtype env f in
          let concrete ty ty' = match ty, ty' with
            | Arr (_, n), Arr (_, n') when get_int n = None || get_int n' = None -> ty'
            | _ -> ty in
          let otys = List.map2 concrete otys (List.map ty_lval lvs) in
          let itys = List.map2 concrete itys (List.map ty_expr es) in
          let args = List.map (toec_cast env) (List.combine itys es) in
          let leak_lvs = ec_leak_call_lvs env in
          (ec_leaks_es env es) @
          (ec_pcall env lvs leak_lvs otys [Env.get_funname env f] args) @
          (ec_leak_call_acc env)
      | Csyscall ([x], Syscall_t.RandomBytes _, es) when EA.of_byte_list <> None ->
          let ws, n = match ty_lval x with Arr (ws, n) -> ws, n | _ -> assert false in
          let len = match get_int n with
            | Some n -> ec_int (arr_size ws n)
            | None -> toec_expr env (Pretyping.canon_expr (arr_size_pexpr_ ws n)) in
          let l = Env.create_aux env "bytes" "W8.t list" in
          (ec_leaks_es env es) @ (ec_leaks_lvs env [x]) @
          [EScall ([LvIdent [l]], [syscall_mod_arg ^ ".randombytes"], [len]);
           toec_lval1 env x (Eapp (Option.get EA.of_byte_list env ws n, [ec_ident l]))]
      | Csyscall (lvs, o, es) ->
          let s = Syscall.syscall_sig_u o in
          let otys = List.map Conv.pty_of_cty s.scs_tout in
          let itys =  List.map Conv.pty_of_cty s.scs_tin in
          let args = List.map (toec_cast env) (List.combine itys es) in
          (ec_leaks_es env es) @
          (ec_pcall env lvs [] otys [ec_syscall env o] args)
      | Cassert _a -> [(* TODO *)]
      | Cif (e, c1, c2) ->
          let c1 env = toec_cmd asmOp env c1 in
          let c2 env = toec_cmd asmOp env c2 in
          ec_leaking_if env e c1 c2
      | Cwhile (_, c1, e, _, c) ->
          assert (List.is_empty c1); (* c1 is empty after toec_while. *)
          let c env = toec_cmd asmOp env c in
          ec_leaking_while env e c
      | Cfor (i, (d,e1,e2), c) ->
          let env = Env.new_aux_range env in
          (* decreasing for loops have bounds swaped *)
          let e1, e2 = if d = UpTo then e1, e2 else e2, e1 in
          let init, ec_e2 =
              match e2 with
              (* Can be generalized to the case where e2 is not modified by c and i *)
              | _ when is_const_bound e2 -> ([], toec_expr env e2)
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
      let locals = Spv.elements (plocals f) in
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
          let ret = List.map (fun x -> Pvar (gkvar x)) f.f_ret in
          let ret = List.map (toec_cast env) (List.combine f.f_tyout ret) in
          match ec_leak_ret env ret with
          | [x] -> ESreturn x
          | xs -> ESreturn (Etuple xs)
      in
      {
          decl = {
              fname = (Env.get_funname env f.f_name);
              args = List.map (var2ec_var env) f.f_args;
              rtys = ec_leak_rty env (List.map (toec_ty env) f.f_tyout);
          };
          locals = ec_locals;
          stmt = aux_locals_init @ stmts @ [ret];
      }

  let toec_funsig env name fsig =
    let dummy_args = List.map (fun ty -> ("_", toec_ty env ty)) fsig.Mprog.fs_tyin in
    let rtys = ec_leak_rty env (List.map (toec_ty env) fsig.Mprog.fs_tyout) in
    {
      fname = name;
      args = dummy_args;
      rtys
    }
  (* ------------------------------------------------------------------- *)
  (* Program extraction *)

  let jmodel env = match Env.arch env with
    | X86_64 -> "JModel_x86"
    | ARM_M4 -> "JModel_m4"
    | ARMv8A -> "JModel_armv8a"
    | RISCV  -> "JModel_riscv"

  let lib_slh env = match Env.arch env with
    | X86_64 -> "SLH64"
    | ARM_M4 -> "SLH32"
    | ARMv8A -> "SLH64"
    | RISCV  -> "SLH32"

  let ec_randombytes env =
      let randombytes_decl a (ws, n) =
          let arr_ty = toec_ty env (Arr (ws, PE (Pconst (Z.of_int n)))) in
          {
              fname = Format.asprintf "randombytes_%s" (EA.randombytes_suffix ws n);
              args = [(a, arr_ty)];
              rtys = [arr_ty];
          }
      in
      let randombytes_list_decl n = { fname = "randombytes"; args = [(n, "int")]; rtys = ["W8.t list"] } in
      let randombytes_f (ws, n) =
        let dmap = EA.ec_darray8 env ws n in
        { decl = randombytes_decl "a" (ws, n)
        ; locals = []
        ; stmt = [ESsample ([LvIdent ["a"]], dmap); ESreturn (ec_ident "a")]
        }
      in
      let randombytes =
        Env.randombytes env
        |> List.sort_uniq (fun (ws1, n1) (ws2, n2) -> compare (EA.randombytes_suffix ws1 n1) (EA.randombytes_suffix ws2 n2))
      in
      if List.is_empty randombytes then
        []
      else if EA.of_byte_list <> None then
        [
          IrequireImport ["DList"];
          ImoduleType {
            name = syscall_mod_sig;
              funs = [randombytes_list_decl "_"];
          };
          Imodule {
            name = syscall_mod;
              params = [];
              ty = Some syscall_mod_sig;
              vars = [];
              funs = [{ decl = randombytes_list_decl "n"; locals = [("l", "W8.t list")];
                        stmt = [ESsample ([LvIdent ["l"]], Eapp (ec_ident "dlist", [ec_ident "W8.dword"; ec_ident "n"])); ESreturn (ec_ident "l")] }];
          }
        ]
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

  let toec_paramdecl env p =
      match p with
      | Mprog.Param v
      | Glob v -> 
        let name = Env.get_varname env v in
        env, IopA(name,(toec_ty env v.v_ty))
      | Fun _ -> assert false
    
  let toec_modulearg env arg arg_name =
      match arg with
      | Mprog.MaParam e  -> [(arg_name, toec_expr env e)]
      | MaGlob v -> [(arg_name, toec_expr env (Pvar{gs=E.Sglob; gv = v}))]
      | MaFun _ -> []


   let init_args_modapp env ma_args =
    let funs = List.map (fun (param, arg) ->
      let old_fun = Env.get_funname env arg.f_name in
      (param,old_fun)
    ) ma_args in
    funs

  let get_array_params env = 
    function
    | Array n -> ["size",toec_expr env (pexpr_of_pexpr_ n)],[]
    | WArray n -> ["size",toec_expr env (pexpr_of_pexpr_ n)],[]
    | ByteArray n -> ["size",toec_expr env (pexpr_of_pexpr_ n)],[] 
    | SubByteArray s ->
      Env.add_ASBArray env s;
      [],["Asmall", ec_PBArray env s.sizes ; "Abig", ec_PBArray env s.sizeb]
    | SubArray s ->
      let _ = Env.add_SubArray env s.sizes s.sizeb in
      [("sizeS",  toec_expr env (pexpr_of_pexpr_ s.sizes)); 
       ("sizeB", toec_expr env (pexpr_of_pexpr_ s.sizeb))],
      [("ArrayS",  ec_PArray env s.sizes) ; ("ArrayB", ec_PArray env s.sizeb)]
    | ArrayWords s ->
      begin match get_int s.sizew with
      | Some sizew ->
        let _ = Env.add_ArrayWords env sizew s.sizea in
        let size = Papp2 (Omul Op_int, icnst sizew, pexpr_of_pexpr_ s.sizea ) in
        [("sizeW",  toec_expr env (pexpr_of_pexpr_ s.sizew)); 
       ("sizeA", toec_expr env (pexpr_of_pexpr_ s.sizea))],
        [
          "Word", Format.sprintf "W%i" (8*sizew);
          "ArrayN", ec_PArray env s.sizea;
          "WArrayN", ec_PWArray env (PE size)
        ]
      | None -> assert false
      end
    | SubArrayDirect s ->
      begin match get_int s.sizew with
      | Some sizew ->
        let _ = Env.add_SubArrayDirect env sizew s.sizes s.sizeb in
        let aw size = begin match get_int size with
        | Some sizea -> fmt_array_theory (ArrayWords{sizew; sizea})
        | None -> 
          let aw = ArrayWords{sizew=s.sizew; sizea = size} in
          Env.abstract_name env aw
        end in
        [("sizeW",  toec_expr env (pexpr_of_pexpr_ s.sizew)); 
        ("sizeS", toec_expr env (pexpr_of_pexpr_ s.sizes));
        ("sizeB", toec_expr env (pexpr_of_pexpr_ s.sizeb))],
        [
          "Word", Format.sprintf "W%i" (8*sizew);
          "ArrayWordsS", aw s.sizes;
          "ArrayWordsB", aw s.sizeb
        ]
      | None -> assert false
      end
    | SubArrayCast s ->
      begin match get_int s.sizews, get_int s.sizewb with
      | Some sizews, Some sizewb ->
        let _ = Env.add_SubArrayCast env sizews sizewb s.sizes s.sizeb in
        let aw size sizew = begin match get_int size with
        | Some sizea -> fmt_array_theory (ArrayWords{sizew; sizea})
        | None -> 
          let aw = ArrayWords{sizew= (PE (icnst sizew)); sizea = size} in
          Env.abstract_name env aw
        end in
      [("sizeWS",  toec_expr env (pexpr_of_pexpr_ s.sizews));
       ("sizeWB", toec_expr env (pexpr_of_pexpr_ s.sizewb));
       ("sizeS", toec_expr env (pexpr_of_pexpr_ s.sizes));
       ("sizeB", toec_expr env (pexpr_of_pexpr_ s.sizeb))],
        [
          "WordS", Format.sprintf "W%i" (8*sizews);
          "WordB", Format.sprintf "W%i" (8*sizewb);
          "ArrayWordsS", aw s.sizes sizews;
          "ArrayWordsB", aw s.sizeb sizewb
        ]
      | _ -> assert false
      end
    | ArrayAccessCast s -> 
      begin match get_int s.sizews, get_int s.sizewb with
      | Some sizews, Some sizewb ->
        let _ = Env.add_ArrayAccessCast env sizews sizewb s.sizeb in
        let aw size sizew = begin match get_int size with
        | Some sizea -> fmt_array_theory (ArrayWords{sizew; sizea})
        | None -> 
          let aw = ArrayWords{sizew= (PE (icnst sizew)); sizea = size} in
          Env.abstract_name env aw
        end in
      [("sizeWS",  toec_expr env (pexpr_of_pexpr_ s.sizews));
       ("sizeWB", toec_expr env (pexpr_of_pexpr_ s.sizewb));
       ("sizeB", toec_expr env (pexpr_of_pexpr_ s.sizeb))],
        [
          "WordS", Format.sprintf "W%i" (8*sizews);
          "WordB", Format.sprintf "W%i" (8*sizewb);
          "ArrayWordsB", aw s.sizeb sizewb
        ]
      | _ -> assert false
      end

  let rec subst_expr_arr env (v_arg:string) (v_exp:pexpr) (e:pexpr) = 
    match e with
    | Pvar v -> 
      let v = Env.get_varname env (L.unloc v.gv) in
      if String.equal v_arg v then v_exp else e
    | Papp1 (op, e) -> Papp1 (op, subst_expr_arr env v_arg v_exp e)
    | Papp2 (op, e1, e2) -> Papp2 (op, subst_expr_arr env v_arg v_exp e1, subst_expr_arr env v_arg v_exp e2)
    | PappN (op, es) -> PappN (op, List.map (subst_expr_arr env v_arg v_exp) es)
    | Parr_init _  | Pget _  | Psub _  | Pload _ | Pif _-> assert false
    | _ -> e

  let subst_var_ma env ma (v:string) e =
    let subst_pexpr e' = Pretyping.canon_expr (subst_expr_arr env v e e') in
    let subst_pexpr_ s = PE(subst_pexpr(pexpr_of_pexpr_ s )) in
    let subst_bytes e' =
      match subst_expr_arr env v e e' with
      | Papp2 (Omul Op_int, a, (Pconst _ as k)) -> Papp2 (Omul Op_int, Pretyping.canon_expr a, k)
      | Papp2 (Omul Op_int, (Pconst _ as k), a) -> Papp2 (Omul Op_int, k, Pretyping.canon_expr a)
      | e' -> Pretyping.canon_expr e' in
    match ma with
    | Array (PE n) -> Array (PE(subst_pexpr n))
    | WArray (PE n) -> WArray(PE(subst_bytes n))
    | ByteArray (PE n) -> ByteArray(PE(subst_pexpr n))
    | SubByteArray s -> 
      let sizes = subst_pexpr_ s.sizes in
      let sizeb = subst_pexpr_ s.sizeb in
      SubByteArray {sizes;sizeb}
    | SubArray s ->
      let sizes = subst_pexpr_ s.sizes in
      let sizeb = subst_pexpr_ s.sizeb in
      SubArray {sizes;sizeb}
    | ArrayWords s ->
      let sizew = subst_pexpr_ s.sizew in
      let sizea = subst_pexpr_ s.sizea in
      ArrayWords {sizew;sizea}
    | SubArrayDirect s ->
      let sizew = subst_pexpr_ s.sizew in
      let sizes = subst_pexpr_ s.sizes in
      let sizeb = subst_pexpr_ s.sizeb in
      SubArrayDirect {sizew; sizes; sizeb}
    | SubArrayCast s ->
      let sizews = subst_pexpr_ s.sizews in
      let sizewb = subst_pexpr_ s.sizewb in
      let sizes = subst_pexpr_ s.sizes in
      let sizeb = subst_pexpr_ s.sizeb in
      SubArrayCast {sizews; sizewb; sizes; sizeb}
    | ArrayAccessCast s ->
      let sizews = subst_pexpr_ s.sizews in
      let sizewb = subst_pexpr_ s.sizewb in
      let sizeb = subst_pexpr_ s.sizeb in
      ArrayAccessCast {sizews; sizewb; sizeb}

  let ma_pexpr_to_string env =
    function
    | Array n -> 
      begin match get_int n with
      | Some n -> ec_Array env n
      | None -> 
        Env.add_AArray env n;
        ec_PArray env n
      end
    | WArray n -> 
      begin match get_int n with
      | Some n -> ec_WArray env n
      | None -> 
        Env.add_AWArray env n;
        ec_PWArray env n
      end
    | ByteArray n -> 
      begin match get_int n with
      | Some n -> ec_BArray env n
      | None -> 
        Env.add_ABArray env n;
        ec_PBArray env n
      end
    | SubByteArray s ->
      begin match get_int s.sizes, get_int s.sizeb with
      | Some sizes, Some sizeb -> ec_SBArray env {sizes; sizeb}
      | _ ->
        Env.add_ASBArray env s;
        ec_PSBArray env s
      end
    | SubArray s -> Env.add_SubArray env s.sizes s.sizeb
    | ArrayWords s ->
      begin match get_int s.sizew, get_int s.sizea with
      | Some sizew, Some sizea -> 
        Env.add_ArrayWords env sizew s.sizea;
        fmt_array_theory (ArrayWords{sizew; sizea})
      | Some sw, None -> 
        Env.add_ArrayWords env sw s.sizea;
        Env.abstract_name env (ArrayWords s)
      | _ -> assert false
      end
    | SubArrayDirect s ->
      begin match get_int s.sizew with
      | Some sw ->
        Env.add_SubArrayDirect env sw s.sizes s.sizeb;
      | _ -> assert false
      end
    | SubArrayCast s ->
      begin match get_int s.sizews, get_int s.sizewb with
      | Some sws, Some swb ->
        Env.add_SubArrayCast env sws swb s.sizes s.sizeb;
      | _ -> assert false
      end
    | ArrayAccessCast s -> 
      begin match get_int s.sizews, get_int s.sizewb with
      | Some sws, Some swb ->
        Env.add_ArrayAccessCast env sws swb s.sizeb;
      | _ -> assert false
      end      

    let modapp_f env m mapp mod_arg = 
      let sc_app = if mod_arg = [] then "" else "(" ^ syscall_mod_arg ^ ")" in
      let sc_param = if mod_arg = [] then "" else Format.sprintf "(%s:%s)" syscall_mod_arg syscall_mod_sig in
      let ma_params, ma_func = Env.get_module env mapp.Mprog.ma_func in
      let ma_func_funcs = Env.get_module_funcs env mapp.Mprog.ma_func in
      let ma_args_funcs = List.concat (List.map2 (fun param arg ->
          match arg with
          | Mprog.MaFun f -> [(param,f)]
          | _ -> []
          ) ma_params mapp.Mprog.ma_args ) in

      let env, new_fs = List.fold_left ( fun (env,new_fs) f ->
        let new_funname = F.mk (String.replace ~str:f.fn_name ~sub:mapp.ma_func ~by:mapp.ma_name |> snd) in
        let env = Env.add_module_fun env mapp.ma_name new_funname in
        let env = Env.add_module_fun env m.Mprog.name new_funname in
        Env.set_fun_mod env new_funname f mapp.ma_name , new_funname :: new_fs
      ) (env,[]) ma_func_funcs in

      if ma_args_funcs <> []
      then 
        let _, ma_name = Env.get_module env mapp.ma_name in
        let init_args = init_args_modapp env ma_args_funcs in
        let m_args = ma_name ^ "_args" in
        let ma_args = ma_func ^ "_args" in
        let env, init_funs = List.fold_left ( fun (env,init_funs) f ->
          let f_modname = f.fn_name |> String.split_on_string ~by:"::"  |> List.last |> String.capitalize_ascii|>  escape in
          let fname = Env.get_funname env f in
          let fs_tyout,fs_tyin = Env.get_funtype env f in
          let f = { name = f; Mprog.fs_tyin; fs_tyout} in
          let new_fmodname = ma_name^"__"^f_modname in
          let _,new_fname = String.replace ~str:fname ~sub:ma_args ~by:(m_args ^ sc_app) in
          let fname, new_fname = 
            match List.rev (String.split_on_char '.' new_fname) with
            | [] -> "", ""
            | f :: m -> f, String.concat "." (List.rev m)  
          in
          let env = Env.rename_fun env f (new_fmodname ^ sc_app ^ "." ^ fname) in
          env, ImoduleEq(new_fmodname ^ sc_param,new_fname)::init_funs
        ) (env,[]) new_fs
        in
        env, ImoduleTypeEq(m_args ^ sc_param,ma_name^"."^ma_args,init_args) :: init_funs
      else env, [] 

    let add_arrsz env f =
        let add env x =
          match x.v_ty with
          | Arr(ws, n) -> 
            begin match get_int n with
            | Some n ->
              EA.add_jarray env ws n
            | _ ->
              EA.add_abstract_array env ws n
            end
          | _ -> ()
        in
        let vars = pvars_fc f in
        Spv.iter (add env) vars
    
    let set_module_params env params =
      let set_param env p = match p with
        | Mprog.Param v | Glob v -> 
          let env = Env.set_var env v in
          env, Some (Env.get_varname env v), None
        | Fun f -> 
          let env = Env.set_fun_fsig env "" f in
          env, Some (Env.get_funname env f.name), Some f
      in
      List.fold_left (fun (e, params_acc, pfuns_acc) p ->
        let e, param, f = set_param e p in
        match param, f with
        | Some param, None -> (e, param :: params_acc, pfuns_acc)
        | Some fname, Some f -> (e, fname :: params_acc, f :: pfuns_acc)
        | _ -> assert false
      ) (env, [], []) (List.rev params)

    let setup_theory env m name pfuns =
      if m.Mprog.params <> [] then
        let theory  = Itheory(List.length (m.params) <> List.length pfuns,name) in
        let env, params = List.fold_left (fun acc p ->
          let env,params = acc in
          match p with
          | Mprog.Fun _ -> env, params
          | _ ->
            let env,param = toec_paramdecl env p in
            (env,param :: params)
        ) (env,[]) m.params  in
        
        let env, items, arg_name = 
          if pfuns = [] then env, [], ""
          else
            let mname = name ^ "_args" in
            let env, fun_sigs = List.fold_left (fun (env,fsigs) (f: Mprog.funsig) -> 
              let fname = Env.get_funname env f.name in
              let fsig = toec_funsig env fname f in
              Env.rename_fun env f (mname^"."^fname), fsigs @ [fsig]
              ) (env,[]) pfuns in
            env, [ImoduleType{name = mname; funs = fun_sigs}], "("^mname^")" 
        in
        env, (theory :: (List.rev params)) @ items, [IendTheory(name)], arg_name
      else env, [Itheory(false,name)], [IendTheory(name)], ""
    
    let subst_ma env mapp ma_params ma =
      List.fold_left2 (fun ma arg param ->
          match arg,param with
          | Mprog.MaParam e, v -> subst_var_ma env ma v e
          | _ -> ma
        ) ma mapp.Mprog.ma_args ma_params

    let add_modapp_alias env mapp =
      let ma_params, _ = Env.get_module env mapp.Mprog.ma_func in
      let _, ma_name' = Env.set_module env mapp.ma_name [] in
      let is_abstract ma =
        let abs = ref false in
        ignore (AbsATcmp.map_at (fun n -> if get_int n = None then abs := true; n) ma);
        !abs in
      List.iter (fun (ma, arr) ->
          match subst_ma env mapp ma_params ma with
          | ma when is_abstract ma
                    && Env.get_alias env ma = None
                    && not (Aarraytheory.mem ma (Env.abstract_array_theories env)) ->
            Env.add_alias env ma (ma_name' ^ "." ^ arr)
          | _ -> ()
        ) (Env.get_module_arrays env mapp.ma_func)

    let toec_modapp env m mapp mod_arg =
      let ma_params, ma_func' = Env.get_module env mapp.Mprog.ma_func in
      let env, ma_name' = Env.set_module env mapp.ma_name [] in
      let env = List.fold_left ( fun env v ->
          let new_name = String.replace ~str:v.v_name ~sub:mapp.ma_func ~by:mapp.ma_name |> snd in
          let new_var = PV.mk new_name v.v_kind v.v_ty v.v_dloc v.v_annot in
          let env = Env.add_module_var env m.Mprog.name new_var in
          let env = Env.add_module_var env mapp.ma_name new_var in
          Env.set_var_mod env new_var v mapp.ma_name
      ) env (Env.get_module_vars env mapp.Mprog.ma_func) in
      let env = List.fold_left ( fun env mm ->
          let new_name = String.replace ~str:mm ~sub:mapp.ma_func ~by:mapp.ma_name |> snd in
          let env = Env.add_module_module env m.name new_name in
          let env = Env.add_module_module env mapp.ma_name new_name in
          Env.set_mod_mod env new_name mm mapp.ma_name 
      ) env (Env.get_module_modules env mapp.Mprog.ma_func) in
      let theories = List.filter_map( fun (ma, arr) ->
           let ma = subst_ma env mapp ma_params ma in
           if Env.get_alias env ma = Some (ma_name' ^ "." ^ arr) then None
           else Some (arr, ma_pexpr_to_string env ma)
      ) (Env.get_module_arrays env mapp.Mprog.ma_func) in
      let env, modappf = modapp_f env m mapp mod_arg in
      let abstract_ops = List.concat (List.map2 (toec_modulearg env) mapp.ma_args ma_params) in
      env,[Iclone(false,ma_func', ma_name', abstract_ops ,theories)] @ modappf

    let rec toec_item env m modf_args (mod_arg,asmOp,imports,go,eval_glob) =
      function
      | Mprog.MsMod sm -> 
        let current_abs_theories = Env.abstract_array_theories env in
        let current_alias = Env.array_alias env in
        Env.set_abstract_array_theories env (Aarraytheory.empty);
        Env.set_array_alias env (Aarraytheory.empty);
        let env, i = extract_module env sm mod_arg asmOp imports go eval_glob in
        Env.set_abstract_array_theories env current_abs_theories;
        Env.set_array_alias env current_alias;
        let env = Env.add_module_module env m.Mprog.name sm.name in
        let env =
          if sm.params <> [] then env
          else 
            let add_item get add env = List.fold_left (fun env v -> add env m.name v) env (get env sm.name) in
            let env = add_item Env.get_module_vars Env.add_module_var env in
            let env = add_item Env.get_module_funcs Env.add_module_fun env in
            add_item Env.get_module_modules Env.add_module_module env  
        in
        env, i
      | MsModApp mapp -> toec_modapp env m mapp mod_arg
      | MsGlob (v,e) ->
        let env = Env.set_var env v in
        let env = Env.add_module_var env m.name v in
        let signed = Option.default go.ToEC.gsign (ToEC.gsign_of_annot v.v_annot) = ToEC.GlobSigned in
        let w_of_z ws z = Eapp (Eident [fmt_Wsz ws; "of_int"], [Econst z]) in
        let e = match eval_glob (v, e) with
          | Some (_, Global.Gword (ws, w)) ->
            w_of_z ws (if signed then Conv.z_of_word ws w else Conv.z_unsigned_of_word ws w)
          | Some (x, Global.Garr (p, t)) ->
            let ws, t = Conv.to_array ~signed x.v_ty p t in
            EA.add_jarray env ws (Array.length t);
            Eapp (EA.of_list env ws (Array.length t), [Elist (List.map (w_of_z ws) (Array.to_list t))])
          | None ->
          begin match e with
          | GEword e -> toec_expr env e
          | GEarray es ->
             match es with
            | [] -> Eapp ((EA.of_list env U64 0), [Elist []]) 
            | e:: _ ->
              begin match ty_expr e with
                | Bty (U ws) -> Eapp ((EA.of_list env ws (List.length es)),[Elist (List.map (toec_expr env) es)])
                | _ -> assert false
              end     
          end in
        let decl = match Option.default go.ToEC.gmodel (ToEC.gmodel_of_annot v.v_annot) with
          | ToEC.GlobAbbrev -> Iabbrev (ec_vars env v, e)
          | GlobOp opts -> Iop (ec_vars env v, opts, e) in
        env, [decl]
      | MsFun f -> 
          let f = wi2i_fun { f with f_body = insert_copy_and_fix_length f.f_body } in
          let f = fill_in_missing_names { f with f_body = remove_for (toec_while f.f_body) } in
          add_arrsz env f;
          let env = Env.set_fun env f in
          let env = Env.add_module_fun env m.name f.f_name in
          let funs = [toec_fun asmOp env f] in
          let fsig = {
            Mprog.name= f.f_name;
            fs_tyin = f.f_tyin;
            fs_tyout = f.f_tyout
          } in
          let fname = Env.get_funname env f.f_name in
          let cfname = "M__"^ fname in
          let mname = Env.get_module env m.name  |> snd in
          let modargs = if modf_args <> "" then [(mname^"_args",mname^"_args")] else []  in
          let app = match List.map fst (modargs @ mod_arg) with
            | [] -> ""
            | l -> "(" ^ String.concat ", " l ^ ")" in
          let f = [Imodule {
            name=cfname;
            params = modargs @ mod_arg;
            ty = None;
            vars = global_leakage_vars env;
            funs;
          }] in
          let env = Env.rename_fun env fsig (cfname^app^"."^fname) in
          env, f

    and extract_module env m mod_arg asmOp imports go eval_glob =
      let imports' = if imports then List.map (fun m -> IrequireImport [m]) m.Mprog.requires else [] in

      let env, params, pfuns = set_module_params env m.Mprog.params in
      let env, name = Env.set_module env m.name params in

      let env, init_items, end_items, modf_args = setup_theory env m name pfuns in

      let early, late =
        if m.params = [] then [], m.items
        else List.partition (function
            | Mprog.MsModApp mapp -> List.for_all (function Mprog.MaParam _ -> true | _ -> false) mapp.ma_args
            | _ -> false) m.items in
      List.iter (function Mprog.MsModApp mapp -> add_modapp_alias env mapp | _ -> ()) early;

      let toec_items env l = List.fold_left (fun (env, items) sm ->
          let env, i = toec_item env m modf_args (mod_arg,asmOp,imports,go,eval_glob) sm in   
          env, items @ i
      ) (env,[]) l in
      let env, early_items = toec_items env early in
      let env, items = toec_items env late in

      let init_abstract_arrays = List.map (fun (ma,i) -> 
        let t, arr = fmt_abstract_array_theory ma i in
        let ops,theories = get_array_params env ma in
        Iclone(true,t, arr, ops,theories)
      ) (Aarraytheory.to_list (Env.abstract_array_theories env)) in

      let alias_imports = match List.map snd (Aarraytheory.to_list (Env.array_alias env)) with
        | [] -> []
        | l -> [Iimport l] in

      let env = Env.exit_module env m.name in

      env, imports' @ init_items @ early_items @ alias_imports @ init_abstract_arrays @ items @ end_items

  let toec_mprog mprog env asmOp imports go eval_glob =
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
          IfromRequireImport ("Jasmin", [jmodel env;"JByte_array"; "JArray"; "JWord_array"; "JWord"]); 
          Iimport [lib_slh env];
      ] in
      let env, items = List.fold_left (fun acc m ->
        let env, items = acc in
        let env, items_m = extract_module env m mod_arg asmOp imports go eval_glob in
        (env, items @ items_m)
      ) (env, []) mprog in
      env,
      glob_imports @
      (leakage_imports env) @
      pp_array_theories (Env.array_theories env) @
      (ec_randombytes env) @
      items
      

  let rec add_randombytes_c env c = List.iter (add_randombytes_i env) c
  and add_randombytes_i env i =
    match i.i_desc with
    | Csyscall ([x], Syscall_t.RandomBytes _, _) ->
      begin match ty_lval x with
      | Arr (ws, n) when get_int n <> None -> Env.add_randombytes env ws (Option.get (get_int n))
      | Arr (ws, _) when EA.of_byte_list <> None -> Env.add_randombytes env ws 0
      | _ -> hierror ~loc:(Lone i.i_loc.base_loc) ~kind:"EasyCrypt extraction" "randombytes on an array of abstract size is not supported"
      end
    | Cif (_, c1, c2) | Cwhile (_, c1, _, _, c2) -> add_randombytes_c env c1; add_randombytes_c env c2
    | Cfor (_, _, c) -> add_randombytes_c env c
    | Cassgn _ | Copn _ | Csyscall _ | Cassert _ | Ccall _ -> ()

  let rec add_randombytes_m env m =
    List.iter (function
      | Mprog.MsFun f -> add_randombytes_c env f.f_body
      | MsMod sm -> add_randombytes_m env sm
      | _ -> ()) m.Mprog.items

  let pp_mprog mprog env asmOp go fmt =
    let eval_glob = Subst.eval_glob_modular () in
    List.iter (add_randombytes_m env) mprog;
    match fmt with
    | [f] ->
      let env, ec_items = toec_mprog mprog env asmOp false go eval_glob in
      Format.fprintf f "%a@." pp_ec_prog ec_items;
      Env.fun_names env
    | fmt -> 
      let env, items = List.fold_left (fun (env,items) m ->
        let env, i = toec_mprog [m] env asmOp true go eval_glob in
        env, items @ [i]
      ) (env,[]) mprog in
      List.iter2 (fun fmt i -> Format.fprintf fmt "%a@." pp_ec_prog i) fmt items;
      Env.fun_names env

end

let extract_modular mprog arch pd msfsz asmOp (model: model) amodel global_options _fnames array_dir fmt =
   let save_array_theories array_theories =
    match array_dir with
    | Some prefix ->
        begin
          Sarraytheory.iter (save_array_theory ~prefix) array_theories
    end
    | None -> 
      ()
  in
  let array_theories = ref Sarraytheory.empty in
  let abs_array_theories = ref Aarraytheory.empty in
  let env = Env.empty arch pd msfsz array_theories abs_array_theories in
  let module EA: EcArray = (val match amodel with
    | ToEC.ArrayOld -> (module EcArrayOld: EcArray)
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
  let names = E.pp_mprog mprog env asmOp global_options fmt in
  save_array_theories (Env.array_theories env);
  names

let extract_equiv arch (model: model) flat_file mfiles flat_names mod_names fmt =
  if model <> Normal then
    hierror ~loc:Lnone ~kind:"EasyCrypt extraction" "the equivalence proofs are only generated for the normal model";
  let jmodel = match arch with
    | X86_64 -> "JModel_x86"
    | ARM_M4 -> "JModel_m4"
    | ARMv8A -> "JModel_armv8a"
    | RISCV  -> "JModel_riscv" in
  let ident s = String.map (fun c -> if BatChar.is_letter c || BatChar.is_digit c || c = '_' then c else '_') s in
  let pairs = List.concat_map (fun (f, fec) ->
      let ps = List.filter_map (fun (g, gec) ->
          if Proc_mjazz.get_flat_funname g = f then Some (fec, gec) else None) mod_names in
      if ps = [] then warning Always Location.i_dummy "no modular counterpart for function %s, its equivalence is not proved" f;
      ps) flat_names in
  let sc = List.exists (fun (_, fec) -> String.exists fec ("(" ^ syscall_mod_arg ^ ")")) flat_names in
  let glob = if sc then Format.sprintf "Glob.mem, glob %s" syscall_mod_arg else "Glob.mem" in
  let pp_lemma fmt (fec, gec) =
    Format.fprintf fmt "@[<v>lemma eq_%s : equiv [%s.%s ~ %s :@   ={arg, %s} ==> ={res, %s}].@ proof. proc; inline *; sim. qed.@]@ @ "
      (ident gec) flat_file fec gec glob glob in
  Format.fprintf fmt "@[<v>require import AllCore.@ from Jasmin require import %s.@ require import %s.@ require %s.@ @ " 
    jmodel (String.concat " " mfiles) flat_file;
  if sc then
    Format.fprintf fmt "section.@ @ declare module %s <: %s.%s {-Glob}.@ @ " syscall_mod_arg flat_file syscall_mod_sig;
  List.iter (pp_lemma fmt) pairs;
  if sc then Format.fprintf fmt "end section.@ ";
  Format.fprintf fmt "@]@."
