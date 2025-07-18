(* -------------------------------------------------------------------- *)
module Set  : sig include module type of BatSet end
module Map  : sig include module type of BatMap end
module Hash : sig include module type of BatHashtbl end

module Sint : Set.S with type elt = int 
module Mint : Map.S with type key = int 

module Ss   : Set.S with type elt = string
module Ms   : Map.S with type key = string

module Hiloc : Hash.S with type key = Location.i_loc
module Miloc : Map.S with type key = Location.i_loc
module Siloc : Set.S with type elt = Location.i_loc

module Option : sig include module type of BatOption end

(* -------------------------------------------------------------------- *)
val identity : 'a -> 'a

val (|-) : ('a -> 'b) -> ('c -> 'a) -> 'c -> 'b

(* -------------------------------------------------------------------- *)
type 'a tuple0 = unit
type 'a tuple1 = 'a
type 'a tuple2 = 'a * 'a
type 'a tuple3 = 'a * 'a * 'a
type 'a pair   = 'a tuple2

(* -------------------------------------------------------------------- *)
val as_seq0 : 'a list -> 'a tuple0
val as_seq1 : 'a list -> 'a tuple1
val as_seq2 : 'a list -> 'a tuple2
val as_seq3 : 'a list -> 'a tuple3

(* -------------------------------------------------------------------- *)
val oget       : ?exn:exn -> 'a option -> 'a

(* -------------------------------------------------------------------- *)
module Uniq : sig
  val gen : unit -> int
end

(* -------------------------------------------------------------------- *)
module ISet : sig
  include module type of BatISet
end

(* -------------------------------------------------------------------- *)
module String : sig
  include module type of BatString

  val drop_end : int -> string -> string
end

(* -------------------------------------------------------------------- *)
module IO : sig
  include module type of BatIO
end

(* -------------------------------------------------------------------- *)
module Buffer : sig
  include module type of BatBuffer
end

(* -------------------------------------------------------------------- *)
module List : sig
  include module type of BatList

  val find_map_opt : ('a -> 'b option) -> 'a list -> 'b option

  (* Aliases to exception-less functions *)
  val opick   : ('a -> 'b option) -> 'a list -> 'b option

  (* Functions working on 2 lists in parallel *)
  module Parallel : sig
    val map_fold2 : ('a -> 'b -> 'c -> 'a * 'd) -> 'a -> 'b list -> 'c list -> 'a * 'd list
  end

  include module type of Parallel

  (*------------------------------------------------------------------ *)
  val modify_last : ('a -> 'a) -> 'a list -> 'a list

  val map_fold   : ('a -> 'b -> 'a * 'c) -> 'a -> 'b list -> 'a * 'c list
  val mapi_fold  : (int -> 'a -> 'b -> 'a * 'c) -> 'a -> 'b list -> 'a * 'c list
  val pmap       : ('a -> 'b option) -> 'a list -> 'b list

end

(* -------------------------------------------------------------------- *)
type 'a pp = Format.formatter -> 'a -> unit

val pp_list : ('a, 'b, 'c, 'd, 'd, 'a) format6 -> 'e pp -> 'e list pp

(* -------------------------------------------------------------------- *)
val pp_paren : 'a pp -> 'a pp 

(* -------------------------------------------------------------------- *)
val pp_string : string pp

(* -------------------------------------------------------------------- *)
val fuel: Datatypes.nat

(* -------------------------------------------------------------------- *)
type architecture =
  | X86_64
  | ARM_M4
  | RISCV

(* -------------------------------------------------------------------- *)
type model = 
  | ConstantTime
  | ConstantTimeGlobal
  | Normal

(* -------------------------------------------------------------------- *)
(* Enables colors in errors and warnings.                               *)
val enable_colors : unit -> unit

(* -------------------------------------------------------------------- *)
type error_loc = Lnone | Lone of Location.t | Lmore of Location.i_loc
type hierror = {
  err_msg      : Format.formatter -> unit; (* a printer of the main error message              *)
  err_loc      : error_loc;                (* the location                                     *)
  err_funname  : string option;            (* the name of the function, if any                 *)
  err_kind     : string;                   (* kind of error (e.g. typing, compilation)         *)
  err_sub_kind : string option;            (* sub-kind (e.g. the name of the compilation pass) *)
  err_internal : bool;                     (* whether the error is unexpected                  *)
}
exception HiError of hierror

val add_iloc : hierror -> Location.i_loc -> hierror
val pp_hierror : Format.formatter -> hierror -> unit

val pp_print_bold_red : (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a -> unit

val hierror :
      loc:error_loc -> ?funname:string -> kind:string
   -> ?sub_kind:string -> ?internal:bool
   -> ('a, Format.formatter, unit, 'b) format4 -> 'a

(* -------------------------------------------------------------------- *)
val pp_now  : Format.formatter -> unit

(* -------------------------------------------------------------------- *)
type warning = 
  | ExtraAssignment 
  | UseLea
  | IntroduceNone
  | IntroduceArrayCopy
  | InlinedCallToExport
  | KeptRenaming
  | SimplifyVectorSuffix
  | DuplicateVar
  | UnusedVar
  | SCTchecker
  | Linter
  | Deprecated
  | Experimental
  | Always
  | PedanticPretyping

val set_warn_recoverable : bool -> unit
val set_all_warnings : unit -> unit
val nowarning : unit -> unit
val add_warning : warning -> unit -> unit
val remove_warning : warning -> unit
val to_warn : warning -> bool
val warning :
      warning -> Location.i_loc
   -> ('a, Format.formatter, unit) format -> 'a
