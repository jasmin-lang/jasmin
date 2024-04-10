open Annotations
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

type swsize  = wsize * sign
type sowsize  = wsize option * sign
type svsize  = vsize * sign * vesize

type castop1 = CSS of sowsize | CVS of svsize 
type castop = castop1 L.located option

let bits_of_wsize : wsize -> int = Annotations.int_of_ws 

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
  | `ROR  of castop
  | `ROL  of castop
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
  | `ROR s -> f s ">>r"
  | `ROL s -> f s "<<r"
  | `Eq s -> f s "=="
  | `Neq s -> f s "!="
  | `Lt s -> f s "<"
  | `Le s -> f s "<="
  | `Gt s -> f s ">"
  | `Ge s -> f s ">="

(* -------------------------------------------------------------------- *)
module W = Wsize

(* -------------------------------------------------------------------- *)

type pexpr_r =
  | PEParens of pexpr
  | PEVar    of pident
  | PEGet    of [`Aligned|`Unaligned] option * arr_access * wsize option * pident * pexpr * pexpr option
  | PEFetch  of mem_access
  | PEpack   of svsize * pexpr list
  | PEBool   of bool
  | PEInt    of Z.t
  | PECall   of pident * pexpr list
  | PECombF  of pident * pexpr list
  | PEPrim   of pident * pexpr list
  | PEOp1    of peop1 * pexpr
  | PEOp2    of peop2 * (pexpr * pexpr)
  | PEIf of pexpr * pexpr * pexpr

and pexpr = pexpr_r L.located

and mem_access = [ `Aligned | `Unaligned ] option * wsize option * pident * ([`Add | `Sub] * pexpr) option

(* -------------------------------------------------------------------- *)
and ptype_r = TBool | TInt | TWord of wsize | TArray of wsize * pexpr
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
  | PLArray of [`Aligned|`Unaligned] option * arr_access * wsize option * pident * pexpr * pexpr option
  | PLMem   of mem_access 

type plvalue = plvalue_r L.located

(* -------------------------------------------------------------------- *)
type peqop = [
  | `Raw
  | `Add  of castop 
  | `Sub  of castop
  | `Mul  of castop
  | `Div  of castop
  | `Mod  of castop
  | `ShR  of castop
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

type vardecls = pstotype * pident list

type pinstr_r =
  | PIArrayInit of pident
  | PIAssign    of plvals * peqop * pexpr * pexpr option
  | PIIf        of pexpr * pblock * pblock option
  | PIFor       of pident * (fordir * pexpr * pexpr) * pblock
  | PIWhile     of pblock option * pexpr * pblock option
  | PIdecl      of vardecls

and pblock_r = pinstr list
and fordir   = [ `Down | `Up ]

and pinstr = annotations * pinstr_r L.located
and pblock = pblock_r L.located

(* -------------------------------------------------------------------- *)
type pparam = {
  ppa_ty   : ptype;
  ppa_name : pident;
  ppa_init : pexpr;
}

(* -------------------------------------------------------------------- *)
type pfunbody = {
  pdb_instr : pinstr list;
  pdb_ret   : pident list option;
}

(* -------------------------------------------------------------------- *)
type pcall_conv = [
  | `Export
  | `Inline
]

type pfundef = {
  pdf_annot : annotations;
  pdf_cc   : pcall_conv option;
  pdf_name : pident;
  pdf_args : (annotations * vardecls) list;
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
  pex_mem: (Z.t * Z.t) list;
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

(* -------------------------------------------------------------------- *)
type pprogram = pitem L.located list
