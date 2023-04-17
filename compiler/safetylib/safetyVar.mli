open Jasmin
open Utils
open Prog
open Wsize

type v_scope = Expr.v_scope
                 
type mem_loc = MemLoc of var

type slice = var * wsize * int
             
type atype =
  | Avar of var                     (* Variable *)
  | Aarray of var                   (* Array *)
  | AarraySlice of slice

type mvar =
  | Temp of string * int * ty
  | WTemp of string * int * ty
  | Mglobal of atype
  | Mlocal of atype
  | MinLocal of var
  | MvarOffset of var
  | MNumInv of L.i_loc
  | MmemRange of mem_loc

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
val mvar_ignore  : mvar -> bool
  
(*---------------------------------------------------------------*)
val arr_range : var -> int
val arr_size  : var -> wsize
val ty_mvar   : mvar -> ty

(*---------------------------------------------------------------*)
val of_scope  : Expr.v_scope -> atype -> mvar
val get_scope : mvar -> Expr.v_scope
val get_at    : mvar -> atype

(*---------------------------------------------------------------*)
(** Resets the conversion table between [mvar] and [avar]. To
  be called between two analyses. *)
val reset : unit -> unit

(*---------------------------------------------------------------*)
val avar_of_mvar : mvar -> Apron.Var.t
                             
val mvar_of_svar : string         -> mvar
val mvar_of_avar : Apron.Var.t    -> mvar

val mvar_of_scoped_var : Expr.v_scope -> Prog.var -> mvar
val mvar_of_var        : int Prog.ggvar -> mvar


(*---------------------------------------------------------------*)
val u8_blast_at   : blast_arrays:bool -> v_scope -> atype      -> mvar list
val u8_blast_ats  : blast_arrays:bool -> v_scope -> atype list -> mvar list

val u8_blast_var  : blast_arrays:bool -> mvar       -> mvar list
val u8_blast_vars : blast_arrays:bool -> mvar list  -> mvar list

(*---------------------------------------------------------------*)
val expand_arr_vars  : mvar list          -> mvar list

(*---------------------------------------------------------------*)
val is_local_var : mvar -> bool
val is_offset    : mvar -> bool
  
val ty_gvar_of_mvar : mvar -> var option

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
