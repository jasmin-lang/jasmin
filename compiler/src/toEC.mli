type amodel =
  | ArrayOld
  | WArray
  | BArray

(* How a Jasmin global variable is extracted: either as an EasyCrypt
   abbreviation, or as an EasyCrypt operator declared with the given options
   (the options are not interpreted, they are printed as such between brackets:
   "op [opaque] x = e."). *)
type gmodel =
  | GlobAbbrev
  | GlobOp of string

val string_of_gmodel : gmodel -> string

(* How the machine words of global variables are printed: as signed integers
   (in [-2^(n-1), 2^(n-1))) or as unsigned ones (in [0, 2^n)).  Both denote the
   same words; unsigned values avoid the unary minus. *)
type gsign =
  | GlobSigned
  | GlobUnsigned

val string_of_gsign : gsign -> string

(* How global variables are extracted, as given by the --global-model
   command-line option of jasmin2ec. *)
type global_options = {
  gmodel : gmodel;
  gsign : gsign;
}

val default_global_options : global_options

val ty_expr : Prog.expr -> Prog.ty
val ty_lval : Prog.lval -> Prog.ty
val extract :
  ('info, ('asm_op, 'extra_op) Arch_extra.extended_op_gen) Prog.prog ->
  Utils.architecture ->
  Wsize.wsize ->
  Wsize.wsize ->
  ('asm_op, 'extra_op) Arch_extra.extended_op_gen Sopn.asmOp ->
  Utils.model ->
  amodel ->
  global_options ->
  string list ->
  string option ->
  Format.formatter ->
  unit
