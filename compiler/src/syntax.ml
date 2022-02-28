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

type vesize = [`W1 | `W2 | `W4 | `W8 | `W16 | `W32 | `W64 | `W128]
type vsize   = [ `V2 | `V4 | `V8 | `V16 | `V32 ]

type swsize  = wsize * sign
type sowsize  = wsize option * sign
type svsize  = vsize * sign * vesize

type castop1 = CSS of sowsize | CVS of svsize 
type castop = castop1 L.located option

let bits_of_wsize : wsize -> int =
  function
  | `W8   -> 8
  | `W16  -> 16
  | `W32  -> 32
  | `W64  -> 64
  | `W128 -> 128
  | `W256 -> 256

let suffix_of_sign : sign -> string =
  function
  | `Unsigned -> "u"
  | `Signed -> "s"

let string_of_swsize (sz,sg) = 
   Format.sprintf "%d%s" (bits_of_wsize sz) (suffix_of_sign sg) 
  
let string_of_sowsize : sowsize -> string =
  function
  | (None, sg) -> suffix_of_sign sg
  | (Some sz, sg) -> string_of_swsize (sz, sg)

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
    (int_of_vsize sv) (suffix_of_sign sg) (bits_of_vesize ve)

(* -------------------------------------------------------------------- *)
type cast = [ `ToWord  of swsize | `ToInt ]

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
  | `Div  of castop
  | `Mod  of castop
  | `BAnd of castop
  | `BOr  of castop
  | `BXOr of castop
  | `ShR  of castop
  | `ShL  of castop

  | `Eq   of castop
  | `Neq  of castop
  | `Lt   of castop
  | `Le   of castop
  | `Gt   of castop
  | `Ge   of castop
]

let string_of_castop1 : castop1 -> string =
  function
  | CSS sw -> string_of_sowsize sw
  | CVS sv -> string_of_svsize sv

let string_of_castop : castop -> string = 
  function
  | None   -> ""
  | Some c -> string_of_castop1 (L.unloc c)

let string_of_cast s = 
  match s with
  | `ToWord s -> string_of_swsize s
  | `ToInt    -> "int"

let string_of_peop1 : peop1 -> string = 
  let f s p = Format.sprintf "%s%s" p (string_of_castop s) in
  function 
  | `Cast s -> Format.sprintf "(%s)" (string_of_cast s)
  | `Not s -> f s "!"
  | `Neg s -> f s "-"

let string_of_peop2 : peop2 -> string =
  let f s p = Format.sprintf "%s%s" p (string_of_castop s) in
  function
  | `And -> "&&"
  | `Or  -> "||"
  | `Add s -> f s "+"
  | `Sub s -> f s "-"
  | `Mul s -> f s "*"
  | `Div s -> f s "/"
  | `Mod s -> f s "%"

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
  | PEGet    of wsize option * pident * pexpr
  | PEFetch  of mem_access
  | PEpack   of svsize * pexpr list
  | PEBool   of bool
  | PEInt    of Z.t
  | PECall   of pident * pexpr list
  | PEPrim   of pident * pexpr list
  | PEOp1    of peop1 * pexpr
  | PEOp2    of peop2 * (pexpr * pexpr)
  | PEIf of pexpr * pexpr * pexpr

and pexpr = pexpr_r L.located

and mem_access = wsize option * pident * ([`Add | `Sub] * pexpr) option

(* -------------------------------------------------------------------- *)
and ptype_r = TBool | TInt | TWord of wsize | TArray of wsize * pexpr
and ptype   = ptype_r L.located

(* -------------------------------------------------------------------- *)
type pstorage = [ `Reg | `Stack | `Inline | `Global]

(* -------------------------------------------------------------------- *)
type pstotype = pstorage * ptype

(* -------------------------------------------------------------------- *)
type plvalue_r =
  | PLIgnore
  | PLVar   of pident
  | PLArray of wsize option * pident * pexpr
  | PLMem   of mem_access 

type plvalue = plvalue_r L.located

(* -------------------------------------------------------------------- *)
type peqop = [
  | `Raw
  | `Add  of castop 
  | `Sub  of castop
  | `Mul  of castop
  | `ShR  of castop
  | `ShL  of castop
  | `BAnd of castop
  | `BXOr of castop
  | `BOr  of castop
]

(* -------------------------------------------------------------------- *)
type align = [`Align | `NoAlign]

type pinstr_r =
  | PIArrayInit of pident
  | PIAssign    of plvalue list * peqop * pexpr * pexpr option
  | PIIf        of pexpr * pblock * pblock option
  | PIFor       of pident * (fordir * pexpr * pexpr) * pblock
  | PIWhile     of align * pblock option * pexpr * pblock option

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
type pexec = {
  pex_name: pident;
  pex_mem: (Z.t * Z.t) list;
}

type pexec_ct = {
  pexc_name1: pident;
  pexc_name2: pident;
  pexc_mem: (Z.t * Z.t) list;
}

(* -------------------------------------------------------------------- *)
type pitem =
  | PFundef of pfundef
  | PParam of pparam
  | PGlobal of pglobal
  | Pexec of pexec
  | Pexec_ct of pexec_ct
(* -------------------------------------------------------------------- *)
type pprogram = pitem L.located list
