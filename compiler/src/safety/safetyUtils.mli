open Prog
open Apron

module Config = SafetyConfig
  
(*---------------------------------------------------------------*)
exception Aint_error of string

(*---------------------------------------------------------------*)
val only_rel_print : bool ref

(*---------------------------------------------------------------*)
val debug : (unit -> unit) -> unit

(*---------------------------------------------------------------*)
val ident : 'a -> 'a
val oget : 'a option -> 'a
val obind2 : ('a -> 'b -> 'c option) -> 'a option -> 'b option -> 'c option

val assoc_up : 'a -> ('b -> 'b) -> ('a * 'b) list -> ('a * 'b) list
val combine3 : 'a list -> 'b list -> 'c list -> ('a * 'b * 'c) list

(*---------------------------------------------------------------*)
type analyzer_param = {
  relationals : string list option;
  pointers : string list option;
}

(*------------------------------------------------------------*)
val get_fun_def : 'a * ('b, 'c) gfunc list -> funname -> ('b, 'c) gfunc option

(*------------------------------------------------------------*)
val env_of_list : Var.t list -> Apron.Environment.t
 
(*------------------------------------------------------------*)
(* Mpq Utils *)

val mpq_pow : int -> Mpqf.t
val mpq_pow_minus : int -> int -> Mpqf.t
val mpq_of_bigint : B.zint -> 'a Mpq.tt
val mpqf_of_bigint : B.zint -> Mpqf.t


(*------------------------------------------------------------*)
(* Coeff and Interval Utils *)
                                 
val scalar_to_int   : Scalar.t   -> int option
val interval_to_int : Interval.t -> int option
    
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
