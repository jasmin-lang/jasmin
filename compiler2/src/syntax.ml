(* -------------------------------------------------------------------- *)
module L = Location

open Utils

(* -------------------------------------------------------------------- *)
exception ParseError of Location.t * string option

let parse_error ?msg loc =
  raise (ParseError (loc, msg))

(* -------------------------------------------------------------------- *)
type symbol = string
type pident = symbol L.located

(* -------------------------------------------------------------------- *)
type peop1 = [ `Not ]

type peop2 = [
  `Add | `Sub | `Mul | `And | `Or  | `BAnd | `BOr | `BXOr |
  `ShR | `ShL | `Eq  | `Neq | `Lt  | `Le   | `Gt  | `Ge 
]

(* -------------------------------------------------------------------- *)
type pexpr_r =
  | PEParens of pexpr
  | PEVar    of pident
  | PEGet    of pident * pexpr
  | PEBool   of bool
  | PEInt    of Bigint.zint
  | PEOp1    of peop1 * pexpr
  | PEOp2    of peop2 * (pexpr * pexpr)

and pexpr = pexpr_r L.located

(* -------------------------------------------------------------------- *)
type wsize   = [ `W8 | `W16 | `W32 | `W64 | `W128 | `W256 ]
type ptype_r = TBool | TInt | TWord of wsize | TArray of wsize * pexpr
type ptype   = ptype_r L.located

(* -------------------------------------------------------------------- *)
type pstorage = [ `Reg | `Stack | `Inline ]

(* -------------------------------------------------------------------- *)
type pstotype = pstorage * ptype

(* -------------------------------------------------------------------- *)
type plvalue_r =
  | PLIgnore
  | PLVar   of pident
  | PLArray of pident * pexpr
  | PLMem   of pident * pexpr

and plvalue = plvalue_r L.located

(* -------------------------------------------------------------------- *)
type peqop = [
  `Raw | `Add | `Sub | `ShR | `ShL | `BAnd | `BXOr | `BOr  | `Mul
]

(* -------------------------------------------------------------------- *)
type pinstr_r =
  | PIAssign of plvalue list * peqop * pexpr * pexpr option
  | PIMove   of plvalue list * pexpr * pexpr option
  | PIIf     of pexpr * pblock * pblock option
  | PIFor    of pident * (pexpr pair) * pblock
  | PIWhile  of pexpr * pblock
  | PICall   of pident * pexpr list

and pblock_r = pinstr list

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
  pdb_vars  : (pstotype * pident) list;
  pdb_instr : pinstr list;
  pdb_ret   : pident list option;
}

(* -------------------------------------------------------------------- *)
type pfundef = {
  pdf_name : pident;
  pdf_args : (pstotype * pident) list;
  pdf_rty  : pstotype list option;
  pdf_body : pfunbody;
}

(* -------------------------------------------------------------------- *)
type pitem = PFundef of pfundef | PParam of pparam

(* -------------------------------------------------------------------- *)
type pprogram = pitem list
