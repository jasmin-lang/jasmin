open Jasmin
open Prog
open Apron

module Config = SafetyConfig

(*---------------------------------------------------------------*)
val ty_expr : Prog.expr -> Prog.ty
val ty_lval : Prog.lval -> Prog.ty

(*---------------------------------------------------------------*)
exception Aint_error of string

(*---------------------------------------------------------------*)
val only_rel_print : bool ref

(*---------------------------------------------------------------*)
val debug : (unit -> unit) -> unit
val timestamp : unit -> _ Prog.func -> [ `Call of Prog.L.i_loc | `Ret ] -> unit

(*---------------------------------------------------------------*)
val ident : 'a -> 'a
val oget : 'a option -> 'a
val obind2 : ('a -> 'b -> 'c option) -> 'a option -> 'b option -> 'c option

val assoc_up : 'a -> ('b -> 'b) -> ('a * 'b) list -> ('a * 'b) list
val combine3 : 'a list -> 'b list -> 'c list -> ('a * 'b * 'c) list
val fold_left3 :
  ('a -> 'b -> 'c -> 'd -> 'a) ->
  'a -> 'b list -> 'c list -> 'd list -> 'a

(*---------------------------------------------------------------*)
type analyzer_param = {
  relationals : string list option;
  pointers : string list option;
}

(*------------------------------------------------------------*)
val get_fun_def : 'a * ('b, 'c, 'asm) gfunc list -> funname -> ('b, 'c, 'asm) gfunc option

(*------------------------------------------------------------*)
val wsize_of_int : int -> Wsize.wsize
                            
(*------------------------------------------------------------*)
val env_of_list : Var.t list -> Apron.Environment.t
 
(*------------------------------------------------------------*)
(* Mpq Utils *)

val mpq_pow : int -> Mpqf.t
val mpq_pow_minus : int -> int -> Mpqf.t
val mpq_of_z : Z.t -> 'a Mpq.tt
val mpqf_of_z : Z.t -> Mpqf.t


(*------------------------------------------------------------*)
(* Coeff and Interval Utils *)
                                 
val scalar_to_zint   : Scalar.t   -> Z.t option
val interval_to_zint : Interval.t -> Z.t option
    
val to_int          : Coeff.t  -> Coeff.t
val s_to_mpqf       : Scalar.t -> Mpqf.t
                                    
val scalar_add      : Scalar.t -> Scalar.t -> Scalar.t
val coeff_add       : Coeff.t  -> Coeff.t  -> Coeff.t
                                              
val interval_join   : Interval.t -> Interval.t -> Interval.t
val interval_meet   : Interval.t -> Interval.t -> Interval.t


(*------------------------------------------------------------*)
(* Fix-point computation *)
val fpt : ('a -> 'a) -> ('a -> 'a -> bool) -> 'a -> 'a

(*---------------------------------------------------------------*)
(* Pretty Printers *)

val pp_list :
  ?sep:(Format.formatter -> unit -> unit) ->
  (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a list -> unit
val pp_opt :
  (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a option -> unit
val pp_call_strategy : Format.formatter -> Config.call_strategy -> unit
