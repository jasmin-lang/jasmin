open Prog

val pp_warning_msg :  Format.formatter -> Compiler_util.warning_msg -> unit

val pp_list :
   ('a, 'b, 'c, 'd, 'd, 'a) CamlinternalFormatBasics.format6 ->
   (Format.formatter -> 'e -> unit) ->
   Format.formatter -> 'e list -> unit

val pp_bool : Format.formatter -> bool -> unit

val pp_string0 : Format.formatter -> char list -> unit

val pp_print_X : Format.formatter -> Z.t -> unit

val pp_kind  : Format.formatter -> v_kind -> unit

val pp_glv : (Format.formatter -> 'a Prog.gty Prog.gvar -> unit) -> Format.formatter -> 'a Prog.gty Prog.glval -> unit

val pp_iloc  : Format.formatter -> i_loc -> unit 
val pp_pvar  : Format.formatter -> pvar -> unit
val pp_ptype : Format.formatter -> pty -> unit
val pp_plval : Format.formatter -> pty glval -> unit
val pp_pexpr : Format.formatter -> pexpr -> unit
val pp_pprog : Format.formatter -> 'info pprog -> unit

val pp_var   : debug:bool -> Format.formatter -> var -> unit

val string_of_op1 : Expr.sop1 -> string
val string_of_op2 : Expr.sop2 -> string
val string_of_opN : Expr.opN -> string
val pp_opn : Expr.sopn -> string

val pp_align : Format.formatter -> Expr.align -> unit

val pp_ty : Format.formatter -> ty -> unit

val pp_expr  : debug:bool -> Format.formatter -> expr -> unit

val pp_instr : debug:bool -> Format.formatter -> 'info instr -> unit

val pp_stmt  : debug:bool -> Format.formatter -> 'info stmt  -> unit

val pp_ifunc : debug:bool -> (Format.formatter -> 'info -> unit) ->
               Format.formatter -> 'info func -> unit

val pp_func  : debug:bool ->
               Format.formatter -> 'info func -> unit

val pp_iprog : debug:bool -> (Format.formatter -> 'info -> unit) ->
               Format.formatter -> 'info prog -> unit

val pp_prog  : debug:bool ->
               Format.formatter -> 'info prog -> unit

(* val pp_cprog : Format.formatter -> Expr.prog -> unit *)

