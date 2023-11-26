(* -------------------------------------------------------------------- *)
module Set  : sig include module type of BatSet end
module Map  : sig include module type of BatMap end
module Hash : sig include module type of BatHashtbl end

module Sint : Set.S with type elt = int 
module Mint : Map.S with type key = int 

module Ss   : Set.S with type elt = string
module Ms   : Map.S with type key = string
                         
module Option : sig include module type of BatOption end

(* -------------------------------------------------------------------- *)
val timed : ('a -> 'b) -> 'a -> float * 'b

(* -------------------------------------------------------------------- *)
val identity : 'a -> 'a

val (^~) : ('a -> 'b -> 'c) -> ('b -> 'a -> 'c)
val (-|) : ('a -> 'b) -> ('c -> 'a) -> 'c -> 'b
val (|-) : ('a -> 'b) -> ('c -> 'a) -> 'c -> 'b

(* -------------------------------------------------------------------- *)
type 'a tuple0 = unit
type 'a tuple1 = 'a
type 'a tuple2 = 'a * 'a
type 'a tuple3 = 'a * 'a * 'a
type 'a tuple4 = 'a * 'a * 'a * 'a
type 'a tuple5 = 'a * 'a * 'a * 'a * 'a
type 'a tuple6 = 'a * 'a * 'a * 'a * 'a * 'a
type 'a tuple7 = 'a * 'a * 'a * 'a * 'a * 'a * 'a
type 'a tuple8 = 'a * 'a * 'a * 'a * 'a * 'a * 'a * 'a
type 'a tuple9 = 'a * 'a * 'a * 'a * 'a * 'a * 'a * 'a * 'a
type 'a pair   = 'a tuple2

(* -------------------------------------------------------------------- *)
val as_seq0 : 'a list -> 'a tuple0
val as_seq1 : 'a list -> 'a tuple1
val as_seq2 : 'a list -> 'a tuple2
val as_seq3 : 'a list -> 'a tuple3
val as_seq4 : 'a list -> 'a tuple4
val as_seq5 : 'a list -> 'a tuple5
val as_seq6 : 'a list -> 'a tuple6
val as_seq7 : 'a list -> 'a tuple7

(* -------------------------------------------------------------------- *)
val fst_map : ('a -> 'c) -> 'a * 'b -> 'c * 'b
val snd_map : ('b -> 'c) -> 'a * 'b -> 'a * 'c

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

  module Smart : sig
    val map      : ('a -> 'a) -> 'a list -> 'a list
    val map_fold : ('a -> 'b -> 'a * 'b) -> 'a -> 'b list -> 'a * 'b list
  end

  val find_map_opt : ('a -> 'b option) -> 'a list -> 'b option

  (* Aliases to exception-less functions *)
  val opick   : ('a -> 'b option) -> 'a list -> 'b option
  val opicki  : (int -> 'a -> 'b option) -> 'a list -> (int * 'b) option

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

val pp_if : bool -> 'a pp -> 'a pp -> 'a pp 
val pp_maybe :  bool -> ('a pp -> 'a pp) -> 'a pp -> 'a pp

(* -------------------------------------------------------------------- *)
val pp_enclose : 
      pre:('a, 'b, 'c, 'd, 'd, 'a) format6
   -> post:('a, 'b, 'c, 'd, 'd, 'a) format6
   -> 'a pp -> 'a pp 

(* -------------------------------------------------------------------- *)
val pp_paren : 'a pp -> 'a pp 

(* -------------------------------------------------------------------- *)
val pp_maybe_paren : bool -> 'a pp -> 'a pp

(* -------------------------------------------------------------------- *)
val pp_string : string pp
 
(* -------------------------------------------------------------------- *)
type model = 
  | ConstantTime
  | Safety
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
  | SimplifyVectorSuffix
  | DuplicateVar 
  | UnusedVar 
  | SCTchecker
  | Deprecated
  | Experimental
  | Always

val nowarning : unit -> unit
val add_warning : warning -> unit -> unit 
val warning :
      warning -> Location.i_loc
   -> ('a, Format.formatter, unit) format -> 'a
