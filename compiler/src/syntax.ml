(* -------------------------------------------------------------------- *)
module L = Location

(* -------------------------------------------------------------------- *)
exception ParseError of Location.t * string option

let parse_error ?msg loc =
  raise (ParseError (loc, msg))

(* -------------------------------------------------------------------- *)
type symbol = string
type pident = symbol L.located

(* -------------------------------------------------------------------- *)
type wsize = [ `W8 | `W16 | `W32 | `W64 | `W128 | `W256 ]

type sign = [ `Unsigned | `Signed ]

type swsize = (sign * wsize option) option

let bits_of_wsize : wsize -> int =
  function
  | `W8 -> 8
  | `W16 -> 16
  | `W32 -> 32
  | `W64 -> 64
  | `W128 -> 128
  | `W256 -> 256

let suffix_of_sign : sign -> string =
  function
  | `Unsigned -> "u"
  | `Signed -> "s"

let string_of_swsize : swsize -> string =
  function
  | None -> ""
  | Some (sg, None) -> suffix_of_sign sg
  | Some (sg, Some sz) ->
    Format.sprintf "%d%s"
      (bits_of_wsize sz)
      (suffix_of_sign sg)

(* -------------------------------------------------------------------- *)
type peop1 = [ `Cast of sign * wsize | `Not | `Neg of swsize ]

type peop2 = [
  | `Add of swsize
  | `Sub of swsize
  | `Mul of swsize
  | `And
  | `Or
  | `BAnd of swsize
  | `BOr of swsize
  | `BXOr of swsize
  | `ShR of swsize
  | `ShL of swsize

  | `Eq of swsize
  | `Neq of swsize
  | `Lt of swsize
  | `Le of swsize
  | `Gt of swsize
  | `Ge of swsize
]

let string_of_peop2 : peop2 -> string =
  let f s p = Format.sprintf "%s%s" p (string_of_swsize s) in
  function
  | `Add s -> f s "+"
  | `Sub s -> f s "-"
  | `Mul s -> f s "*"
  | `And -> "&&"
  | `Or  -> "||"
  | `BAnd s -> f s "&"
  | `BOr s -> f s "|"
  | `BXOr s -> f s "^"
  | `ShR s -> f s ">>"
  | `ShL s -> f s "<<"
  | `Eq s -> f s "=="
  | `Neq s -> f s "!="
  | `Lt s -> f s "<"
  | `Le s -> f s "<="
  | `Gt s -> f s ">"
  | `Ge s -> f s ">="

(* -------------------------------------------------------------------- *)
type pexpr_r =
  | PEParens of pexpr
  | PEVar    of pident
  | PEGet    of pident * pexpr
  | PEFetch  of ptype option * pident * pexpr
  | PEBool   of bool
  | PEInt    of Bigint.zint
  | PECall   of pident * pexpr list
  | PEPrim   of pident * pexpr list
  | PEOp1    of peop1 * pexpr
  | PEOp2    of peop2 * (pexpr * pexpr)
  | PEIf of pexpr * pexpr * pexpr

and pexpr = pexpr_r L.located

(* -------------------------------------------------------------------- *)
and ptype_r = TBool | TInt | TWord of wsize | TArray of wsize * pexpr
and ptype   = ptype_r L.located

(* -------------------------------------------------------------------- *)
type pstorage = [ `Reg | `Stack | `Inline ]

(* -------------------------------------------------------------------- *)
type pstotype = pstorage * ptype

(* -------------------------------------------------------------------- *)
type plvalue_r =
  | PLIgnore
  | PLVar   of pident
  | PLArray of pident * pexpr
  | PLMem   of ptype option * pident * pexpr

type plvalue = plvalue_r L.located

(* -------------------------------------------------------------------- *)
type peqop = [
  `Raw
  | `Add of swsize
  | `Sub of swsize
  | `Mul of swsize
  | `ShR of swsize
  | `ShL of swsize
  | `BAnd of swsize
  | `BXOr of swsize
  | `BOr of swsize
]

(* -------------------------------------------------------------------- *)
type pinstr_r =
  | PIArrayInit of pident
  | PIAssign    of plvalue list * peqop * pexpr * pexpr option
  | PIIf        of pexpr * pblock * pblock option
  | PIFor       of pident * (fordir * pexpr * pexpr) * pblock
  | PIWhile     of pblock option * pexpr * pblock option

and pblock_r = pinstr list
and fordir   = [ `Down | `Up ]

and pinstr = pinstr_r L.located
and pblock = pblock_r L.located

(* -------------------------------------------------------------------- *)
type pparam = {
  ppa_ty   : ptype;
  ppa_name : pident;
  ppa_init : pexpr;
}

(* -------------------------------------------------------------------- *)
type pfunbody = {
  pdb_vars  : (pstotype * pident list) list;
  pdb_instr : pinstr list;
  pdb_ret   : pident list option;
}

(* -------------------------------------------------------------------- *)
type pcall_conv = [
  | `Export
  | `Inline
]

type pfundef = {
  pdf_cc   : pcall_conv option;
  pdf_name : pident;
  pdf_args : (pstotype * pident) list;
  pdf_rty  : pstotype list option;
  pdf_body : pfunbody;
}

(* -------------------------------------------------------------------- *)
type pglobal = { pgd_type: ptype; pgd_name: pident ; pgd_val: pexpr }

(* -------------------------------------------------------------------- *)
type pitem = PFundef of pfundef | PParam of pparam
  | PGlobal of pglobal

(* -------------------------------------------------------------------- *)
type pprogram = pitem L.located list
