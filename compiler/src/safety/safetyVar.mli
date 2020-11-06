open Utils
open Prog
open Wsize
    
type mem_loc = MemLoc of ty gvar


(*---------------------------------------------------------------*)
module MemAccess : sig
  type kind = Load | Store
  type mem_access = {
    line_number : int;
    size : Wsize.wsize;
    var : Prog.var;
    offset_expr : Prog.expr;
    kind : kind;
    base_var : mem_loc option;
  }
  
  type t
  val make : mem_access -> t
  val unwrap : t -> mem_access
  val to_string : t -> string
  val pp_kind : Format.formatter -> kind -> unit
end

(*---------------------------------------------------------------*)
type atype =
  | Avar of ty gvar
  | Aarray of ty gvar
  | AarrayEl of ty gvar * wsize * int

type mvar =
  | Temp of string * int * ty
  | WTemp of string * int * ty
  | Mglobal of Name.t * ty
  | Mvalue of atype
  | MinValue of ty gvar
  | MvarOffset of ty gvar
  | MNumInv of L.t
  | MmemRange of mem_loc
  | MmemAccess of MemAccess.t

(*---------------------------------------------------------------*)
val weak_update : mvar -> bool

(*---------------------------------------------------------------*)
val string_of_mvar : mvar -> string
  
val pp_mvar : Format.formatter -> mvar -> unit

(*---------------------------------------------------------------*)
val dummy_mvar : mvar

(*---------------------------------------------------------------*)
val svariables_ignore : string      -> bool
val variables_ignore  : Apron.Var.t -> bool

(*---------------------------------------------------------------*)
val arr_range : 'a gty gvar -> 'a
val arr_size  : 'a gty gvar -> wsize
val ty_mvar   : mvar -> ty

(*---------------------------------------------------------------*)
val avar_of_mvar : mvar -> Apron.Var.t
                             
val mvar_of_svar : string      -> mvar
val mvar_of_avar : Apron.Var.t -> mvar
val mvar_of_var  : ty gvar     -> mvar

(*---------------------------------------------------------------*)
val u8_blast_at   : blast_arrays:bool -> atype      -> mvar list
val u8_blast_var  : blast_arrays:bool -> mvar       -> mvar list
val u8_blast_ats  : blast_arrays:bool -> atype list -> mvar list
val u8_blast_vars : blast_arrays:bool -> mvar list  -> mvar list

(*---------------------------------------------------------------*)
val expand_arr_vars  : mvar list          -> mvar list
val expand_arr_tys   : int gty list       -> int gty list
val expand_arr_exprs : int gty gexpr list -> int gty gexpr list

(*---------------------------------------------------------------*)
val is_var    : mvar -> bool
val is_offset : mvar -> bool
  
val ty_gvar_of_mvar : mvar -> ty gvar option

(*---------------------------------------------------------------*)
module Sm : Set.S with type elt = mvar
module Mm : Map.S with type key = mvar 

(*---------------------------------------------------------------*)
module Sml : Set.S with type elt = mem_loc
module Mml : Map.S with type key = mem_loc

(*---------------------------------------------------------------*)
module Bvar : sig
  type t
  val compare  : t -> t -> int
  val equal    : t -> t -> bool
  val make     : mvar -> bool -> t
  val not      : t -> t
  val is_neg   : t -> bool
  val var_name : t -> string
  val get_mv   : t -> mvar
  val positive : t -> t
  val print    : Format.formatter -> t -> unit
end

(*---------------------------------------------------------------*)
module Mbv : Map.S with type key = Bvar.t
