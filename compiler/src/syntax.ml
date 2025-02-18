open Annotations
open Utils
(* -------------------------------------------------------------------- *)
module L = Location

(* -------------------------------------------------------------------- *)
exception ParseError of Location.t * string option

let parse_error ?msg loc =
  raise (ParseError (loc, msg))

(* -------------------------------------------------------------------- *)
type arr_access = Warray_.arr_access

type sign = [ `Unsigned | `Signed ]

type vesize = [`W1 | `W2 | `W4 | `W8 | `W16 | `W32 | `W64 | `W128]
type vsize   = [ `V2 | `V4 | `V8 | `V16 | `V32 ]

type wsign = [ `Word of sign option | `WInt of sign]
type swsize  = wsize * wsign
type svsize  = vsize * sign * vesize

type castop1 = CSS of swsize | CVS of svsize
type castop = castop1 L.located option

type int_representation = string
let parse_int (i: int_representation) : Z.t =
  let s = String.filter (( <> ) '_') i in
  Z.of_string s

let bits_of_wsize : wsize -> int = Annotations.int_of_ws

let string_of_sign : sign -> string =
  function
  | `Unsigned -> "u"
  | `Signed -> "s"

let suffix_of_wsign = function
  | `Word None -> "w"
  | `Word (Some s) -> string_of_sign s
  | `WInt s -> Format.sprintf "%si" (string_of_sign s)

let string_of_swsize_op (sz,sg) =
  Format.sprintf "%d%s" (bits_of_wsize sz) (suffix_of_wsign sg)

let string_of_swsize_ty (sz,sg) =
  Format.sprintf "%s%d" (suffix_of_wsign sg) (bits_of_wsize sz)

let int_of_vsize : vsize -> int =
  function
  | `V2  -> 2
  | `V4  -> 4
  | `V8  -> 8
  | `V16 -> 16
  | `V32 -> 32

let bits_of_vesize : vesize -> int =
  function
  | `W1   -> 1
  | `W2   -> 2
  | `W4   -> 4
  | `W8   -> 8
  | `W16  -> 16
  | `W32  -> 32
  | `W64  -> 64
  | `W128 -> 128

let string_of_svsize (sv,sg,ve) =
  Format.sprintf "%d%s%d"
    (int_of_vsize sv) (string_of_sign sg) (bits_of_vesize ve)

let string_of_osign = function
  | None -> ""
  | Some s -> string_of_sign s

(* -------------------------------------------------------------------- *)
type cast = [ `ToWord  of swsize | `ToInt of sign option]

type peop1 = [
  | `Cast of cast
  | `Not  of castop
  | `Neg  of castop
]

type peop2 = [
  | `And
  | `Or
  | `Add  of castop
  | `Sub  of castop
  | `Mul  of castop
  | `Div  of sign option * castop
  | `Mod  of sign option * castop
  | `BAnd of castop
  | `BOr  of castop
  | `BXOr of castop
  | `ShR  of sign option * castop
  | `ROR  of castop
  | `ROL  of castop
  | `ShL  of castop

  | `Eq   of castop
  | `Neq  of castop
  | `Lt   of sign option * castop
  | `Le   of sign option * castop
  | `Gt   of sign option * castop
  | `Ge   of sign option * castop
]

let string_of_castop1 : castop1 -> string =
  function
  | CSS sw -> string_of_swsize_op sw
  | CVS sv -> string_of_svsize sv

let string_of_castop : castop -> string =
  function
  | None   -> ""
  | Some c -> string_of_castop1 (L.unloc c)

let string_of_cast s =
  match s with
  | `ToWord s -> string_of_swsize_op s
  | `ToInt s   -> Format.sprintf "%sint" (string_of_osign s)

let string_of_peop1 : peop1 -> string =
  let f s p = Format.sprintf "%s%s" p (string_of_castop s) in
  function
  | `Cast s -> Format.sprintf "(%s)" (string_of_cast s)
  | `Not s -> f s "!"
  | `Neg s -> f s "-"

let string_of_signcastop (s, c) =
  match s, c with
  | None, _ -> string_of_castop c
  | Some s, None -> string_of_sign s
  | Some s, Some c -> Format.sprintf "%s %s" (string_of_sign s) (string_of_castop1 (L.unloc c))

let string_of_peop2 : peop2 -> string =
  let f c p = Format.sprintf "%s%s" p (string_of_castop c) in
  let g c p = Format.sprintf "%s%s" p (string_of_signcastop c) in
  function
  | `And -> "&&"
  | `Or  -> "||"
  | `Add c -> f c "+"
  | `Sub c -> f c "-"
  | `Mul c -> f c "*"
  | `Div c -> g c "/"
  | `Mod c -> g c "%"

  | `BAnd c -> f c "&"
  | `BOr  c -> f c "|"
  | `BXOr c -> f c "^"
  | `ShR c -> g c ">>"
  | `ShL c -> f c "<<"
  | `ROR c -> f c ">>r"
  | `ROL c -> f c "<<r"
  | `Eq  c -> f c "=="
  | `Neq c -> f c "!="
  | `Lt c -> g c "<"
  | `Le c -> g c "<="
  | `Gt c -> g c ">"
  | `Ge c -> g c ">="

(* -------------------------------------------------------------------- *)
module W = Wsize

(* -------------------------------------------------------------------- *)

type pexpr_r =
  | PEParens of pexpr
  | PEVar    of pident
  | PEGet    of [`Aligned|`Unaligned] option * arr_access * swsize L.located option * pident * pexpr * pexpr option
  | PEFetch  of mem_access
  | PEpack   of svsize * pexpr list
  | PEBool   of bool
  | PEInt    of int_representation
  | PECall   of pident * pexpr list
  | PECombF  of pident * pexpr list
  | PEPrim   of pident * pexpr list
  | PEOp1    of peop1 * pexpr
  | PEOp2    of peop2 * (pexpr * pexpr)
  | PEIf of pexpr * pexpr * pexpr

and pexpr = pexpr_r L.located

and mem_access = [ `Aligned | `Unaligned ] option * swsize L.located option * pident * ([`Add | `Sub] * pexpr) option

(* -------------------------------------------------------------------- *)
and psizetype = TypeWsize of swsize | TypeSizeAlias of pident
and ptype_r = TBool | TInt | TWord of swsize | TArray of psizetype * pexpr | TAlias of pident
and ptype   = ptype_r L.located

(* -------------------------------------------------------------------- *)
type writable = [`Constant | `Writable]
type ptr      = [`Pointer of writable option | `Direct ]
type pstorage = [ `Reg of ptr | `Stack of ptr | `Inline | `Global]

(* -------------------------------------------------------------------- *)
type pstotype = pstorage * ptype
type annot_pstotype = annotations * pstotype
(* -------------------------------------------------------------------- *)
type plvalue_r =
  | PLIgnore
  | PLVar   of pident
  | PLArray of [`Aligned|`Unaligned] option * arr_access * swsize L.located option * pident * pexpr * pexpr option
  | PLMem   of mem_access

type plvalue = plvalue_r L.located

(* -------------------------------------------------------------------- *)
type peqop = [
  | `Raw
  | `Add  of castop
  | `Sub  of castop
  | `Mul  of castop
  | `Div  of sign option * castop
  | `Mod  of sign option * castop
  | `ShR  of sign option * castop
  | `ROR  of castop
  | `ROL  of castop
  | `ShL  of castop
  | `BAnd of castop
  | `BXOr of castop
  | `BOr  of castop
]

(* -------------------------------------------------------------------- *)
type align = [`Align | `NoAlign]

type plvals = annotations L.located option * plvalue list


type vardecl = pident * pexpr option
type vardecls = pstotype * vardecl L.located list

let var_decl_id (v, _ : vardecl) : pident = v

type pinstr_r =
  | PIArrayInit of pident
      (** ArrayInit(x); *)
  | PIAssign    of plvals * peqop * pexpr * pexpr option
      (** x, y += z >> 4 if c; *)
  | PIIf        of pexpr * pblock * pblock option
      (** if e { … } else { … } *)
  | PIFor       of pident * (fordir * pexpr * pexpr) * pblock
      (** for i = 0 to N { … } *)
  | PIWhile     of pblock option * pexpr * pblock option
      (** while { … } (x > 0) { … } *)
  | PIdecl      of vardecls
      (** reg u32 x y z; *)

and pblock_r = pinstr list
and fordir   = [ `Down | `Up ]

and pinstr = annotations * pinstr_r L.located
and pblock = pblock_r L.located

let string_of_sizetype =
  function
  | TypeWsize ws -> string_of_swsize_ty ws
  | TypeSizeAlias pident -> L.unloc pident

let pp_writable = function
  | Some `Constant -> " const"
  | Some `Writable -> " mut"
  | None  -> ""

let pp_pointer = function
  | `Pointer w-> pp_writable w ^ " ptr"
  | `Direct  -> ""

let pp_storage = function
  | `Reg(ptr) -> "reg" ^ (pp_pointer ptr)
  | `Stack ptr -> "stack" ^ (pp_pointer ptr)
  | `Inline -> "inline"
  | `Global -> "global"

(* -------------------------------------------------------------------- *)
type pparam = {
  ppa_ty   : ptype;
  ppa_name : pident;
  ppa_init : pexpr;
}

(* -------------------------------------------------------------------- *)
type pfunbody = {
  pdb_instr : pinstr list;
  pdb_ret   : pident list option L.located;
}

(* -------------------------------------------------------------------- *)
type pcall_conv = [
  | `Export
  | `Inline
]

type paramdecls = pstotype * pident list

type pfundef = {
  pdf_annot : annotations;
  pdf_cc   : pcall_conv option;
  pdf_name : pident;
  pdf_args : (annotations * paramdecls) list;
  pdf_rty  : (annotations * pstotype) list option;
  pdf_body : pfunbody;
}

(* -------------------------------------------------------------------- *)
type gpexpr =
  | GEword  of pexpr
  | GEarray of pexpr list
  | GEstring of string L.located

type pglobal = { pgd_type: ptype; pgd_name: pident ; pgd_val: gpexpr }

(* -------------------------------------------------------------------- *)
type pexec = {
  pex_name: pident;
  pex_mem: (int_representation * int_representation) list;
}

(* -------------------------------------------------------------------- *)
type prequire = string L.located

(* -------------------------------------------------------------------- *)
type pitem =
  | PFundef of pfundef
  | PParam of pparam
  | PGlobal of pglobal
  | Pexec of pexec
  | Prequire of (pident option * prequire list)
  | PNamespace of pident * pitem L.located list
  | PTypeAlias of pident * ptype

(* -------------------------------------------------------------------- *)
type pprogram = pitem L.located list

