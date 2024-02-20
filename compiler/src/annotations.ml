(* -------------------------------------------------------------------- *)
type symbol = string
type pident = symbol Location.located

(* -------------------------------------------------------------------- *)
type wsize = [ `W8 | `W16 | `W32 | `W64 | `W128 | `W256 ]

(* -------------------------------------------------------------------- *)
type simple_attribute =
  | Aint    of Z.t
  | Aid     of symbol
  | Astring of string
  | Aws     of wsize
  | Astruct of annotations

and attribute = simple_attribute Location.located

and annotation = pident * attribute option

and annotations = annotation list

type returnaddress_kind =
  | OnStack
  | OnReg

type f_annot = {
    retaddr_kind          : returnaddress_kind option;
    stack_allocation_size : Z.t option;
    stack_size            : Z.t option;
    stack_align           : wsize option;
    max_call_depth        : Z.t option;
    f_user_annot          : annotations;
}

let f_annot_empty = {
    retaddr_kind          = None;
    stack_allocation_size = None;
    stack_size            = None;
    stack_align           = None;
    max_call_depth        = None;
    f_user_annot          = [];
  }

(* CHECKME: could be useful *)
(* type assert_kind = *)
(*   | Assert *)
(*   | Assume *)
(*   | Cut *)

(* type a_annot = { *)
(*     aty: assert_kind; *)
(*   } *)

let has_symbol s annot =
  List.exists (fun (k, _) -> String.equal (Location.unloc k) s) annot

let add_symbol ~loc s annot =
  if has_symbol s annot
  then annot
  else (Location.mk_loc loc s, None) :: annot
