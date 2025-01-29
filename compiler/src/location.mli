(* -------------------------------------------------------------------- *)
open Lexing

(* -------------------------------------------------------------------- *)
type t = {
  loc_fname : string;
  loc_start : int * int;
  loc_end   : int * int;
  loc_bchar : int;
  loc_echar : int;
}

type i_loc = private { 
    uid_loc  : int; 
    base_loc : t;
    stack_loc: t list;
  }

(* -------------------------------------------------------------------- *)
val _dummy    : t
val make      : position -> position -> t
val of_lexbuf : lexbuf -> t
val tostring  : t -> string
val pp_loc    : Format.formatter -> t -> unit
val pp_sloc   : Format.formatter -> t -> unit
val pp_iloc   : Format.formatter -> i_loc -> unit
val pp_iloc_short : Format.formatter -> i_loc -> unit
val merge     : t -> t -> t
val isdummy   : t -> bool

(* -------------------------------------------------------------------- *)
type 'a located = {
  pl_loc  : t;
  pl_desc : 'a;
}

val loc    : 'a located -> t
val unloc  : 'a located -> 'a
val mk_loc : t -> 'a -> 'a located

(* -------------------------------------------------------------------- *)
val i_loc : t -> t list -> i_loc
val i_loc0 : t -> i_loc
val of_loc : 'a located -> i_loc

val i_dummy : i_loc

val refresh_i_loc : i_loc -> i_loc
