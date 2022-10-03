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
exception Unexpected

val unexpected : unit -> 'a

(* -------------------------------------------------------------------- *)
type 'data cb = Cb : 'a * ('data -> 'a -> unit) -> 'data cb

(* -------------------------------------------------------------------- *)
val tryexn : (exn -> bool) -> (unit -> 'a) -> 'a option
val try_nf : (unit -> 'a) -> 'a option

val try_finally : (unit -> 'a) -> (unit -> unit) -> 'a

val timed : ('a -> 'b) -> 'a -> float * 'b

(* -------------------------------------------------------------------- *)
val identity : 'a -> 'a

val pred0: 'a -> bool
val predT: 'a -> bool

val (^~) : ('a -> 'b -> 'c) -> ('b -> 'a -> 'c)
val (-|) : ('a -> 'b) -> ('c -> 'a) -> 'c -> 'b
val (|-) : ('a -> 'b) -> ('c -> 'a) -> 'c -> 'b

val (|>) : 'a -> ('a -> 'b) -> 'b
val (<|) : ('a -> 'b) -> 'a -> 'b

val curry   : ('a1 -> 'a2 -> 'b) -> 'a1 * 'a2 -> 'b
val uncurry : ('a1 * 'a2 -> 'b) -> 'a1 -> 'a2 -> 'b

val curry3   : ('a1 -> 'a2 -> 'a3 -> 'b) -> 'a1 * 'a2 * 'a3 -> 'b
val uncurry3 : ('a1 * 'a2 * 'a3 -> 'b) -> 'a1 -> 'a2 -> 'a3 -> 'b

(* -------------------------------------------------------------------- *)
val copy : 'a -> 'a

(* -------------------------------------------------------------------- *)
val reffold  : ('a -> 'b * 'a) -> 'a ref -> 'b
val postincr : int ref -> int

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
val in_seq1: ' a -> 'a list

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
val t2_map : ('a -> 'b) -> 'a tuple2 -> 'b tuple2
val t3_map : ('a -> 'b) -> 'a tuple3 -> 'b tuple3

(* -------------------------------------------------------------------- *)
val int_of_bool : bool -> int

(* -------------------------------------------------------------------- *)
val proj3_1 : 'a * 'b * 'c -> 'a
val proj3_2 : 'a * 'b * 'c -> 'b
val proj3_3 : 'a * 'b * 'c -> 'c

val proj4_1 : 'a * 'b * 'c * 'd -> 'a
val proj4_2 : 'a * 'b * 'c * 'd -> 'b
val proj4_3 : 'a * 'b * 'c * 'd -> 'c
val proj4_4 : 'a * 'b * 'c * 'd -> 'd

val fst_map : ('a -> 'c) -> 'a * 'b -> 'c * 'b
val snd_map : ('b -> 'c) -> 'a * 'b -> 'a * 'c

val swap: 'a * 'b -> 'b * 'a

(* -------------------------------------------------------------------- *)
type 'a eq  = 'a -> 'a -> bool
type 'a cmp = 'a -> 'a -> int

val pair_equal : 'a eq -> 'b eq -> ('a * 'b) eq
val opt_equal  : 'a eq -> 'a option eq

(* -------------------------------------------------------------------- *)
val none : 'a option
val some : 'a -> 'a option

val is_none : 'a option -> bool
val is_some : 'a option -> bool

val funnone : 'a -> 'b option

(* -------------------------------------------------------------------- *)
val oiter      : ('a -> unit) -> 'a option -> unit
val obind      : ('a -> 'b option) -> 'a option -> 'b option
val ofold      : ('a -> 'b -> 'b) -> 'b -> 'a option -> 'b
val omap       : ('a -> 'b) -> 'a option -> 'b option
val oif        : ('a -> bool) -> 'a option -> bool
val odfl       : 'a -> 'a option -> 'a
val ofdfl      : (unit -> 'a) -> 'a option -> 'a
val oget       : ?exn:exn -> 'a option -> 'a
val oall2      : ('a -> 'b -> bool) -> 'a option -> 'b option -> bool
val otolist    : 'a option -> 'a list
val oeq        : ('a -> 'a -> bool) -> ('a option -> 'a option -> bool)
val ocompare   : 'a cmp -> 'a option cmp
val omap_dfl   : ('a -> 'b) -> 'b -> 'a option -> 'b

module OSmart : sig
  val omap : ('a -> 'a) -> 'a option -> 'a option
  val omap_fold : ('a -> 'b -> 'a * 'b) -> 'a -> 'b option -> 'a * 'b option
end

(* -------------------------------------------------------------------- *)
type ('a, 'b) tagged = Tagged of ('a * 'b option)

val tg_val : ('a, 'b) tagged -> 'a
val tg_tag : ('a, 'b) tagged -> 'b option
val tg_map : ('a -> 'b) -> ('a, 'c) tagged -> ('b, 'c) tagged
val notag  : 'a -> ('a, 'b) tagged

(* -------------------------------------------------------------------- *)
val iterop: ('a -> 'a) -> int -> 'a -> 'a
val iter: ('a -> 'a) -> 'a -> 'b

(* -------------------------------------------------------------------- *)
module Uniq : sig
  val gen : unit -> int
end

(* -------------------------------------------------------------------- *)
module OneShot : sig
  type t

  val mk  : (unit -> unit) -> t
  val now : t -> unit
end

(* -------------------------------------------------------------------- *)
module Counter : sig
  type t

  val create : unit -> t
  val next   : t -> int
end

(* -------------------------------------------------------------------- *)
module Disposable : sig
  type 'a t

  exception Disposed

  val create  : ?cb:('a -> unit) -> 'a -> 'a t
  val get     : 'a t -> 'a
  val dispose : 'a t -> unit
end

(* -------------------------------------------------------------------- *)
module Os : sig
  val getenv  : string -> string option
  val listdir : string -> string list
end

(* -------------------------------------------------------------------- *)
module ISet : sig
  include module type of BatISet
end

(* -------------------------------------------------------------------- *)
module String : sig
  include module type of BatString

  val split_lines : string -> string list
  val drop : int -> string -> string
  val drop_end : int -> string -> string
end

(* -------------------------------------------------------------------- *)
module IO : sig
  include module type of BatIO
end

(* -------------------------------------------------------------------- *)
module Buffer : sig
  include module type of BatBuffer

  val from_string : ?size:int -> string -> t
  val from_char   : ?size:int -> char -> t
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
  val ocons   : 'a option -> 'a list -> 'a list
  val ohead   : 'a list -> 'a option
  val otail   : 'a list -> 'a list option
  val olast   : 'a list -> 'a option
  val ofind   : ('a -> bool) -> 'a list -> 'a option
  val opick   : ('a -> 'b option) -> 'a list -> 'b option
  val opicki  : (int -> 'a -> 'b option) -> 'a list -> (int * 'b) option
  val oindex  : ('a -> bool) -> 'a list -> int option
  val orindex : ('a -> bool) -> 'a list -> int option

  (* Functions working on 2 lists in parallel *)
  module Parallel : sig
    val iter2i    : (int -> 'a -> 'b -> unit) -> 'a list -> 'b list -> unit
    val iter2o    : ('a option -> 'b option -> unit) -> 'a list -> 'b list -> unit
    val filter2   : ('a -> 'b -> bool) -> 'a list -> 'b list -> 'a list * 'b list
    val all2      : ('a -> 'b -> bool) -> 'a list -> 'b list -> bool
    val map_fold2 : ('a -> 'b -> 'c -> 'a * 'd) -> 'a -> 'b list -> 'c list -> 'a * 'd list
    val prefix2   : 'a list -> 'b list -> ('a list * 'a list) * ('b list * 'b list)
  end

  include module type of Parallel

  (*------------------------------------------------------------------ *)
  val fst : ('a * 'b) list -> 'a list
  val snd : ('a * 'b) list -> 'b list
  val modify_last : ('a -> 'a) -> 'a list -> 'a list
  val span_at_most : ('a -> bool) -> int -> 'a list -> 'a list * 'a list

  val mbfilter   : ('a -> bool) -> 'a list -> 'a list
  val fusion     : ('a -> 'a -> 'a) -> 'a list -> 'a list -> 'a list
  val is_unique  : ?eq:('a -> 'a -> bool) -> 'a list -> bool
  val fpick      : (unit -> 'a option) list -> 'a option
  val pivot_at   : int -> 'a list -> 'a list * 'a * 'a list
  val find_pivot : ('a -> bool) -> 'a list -> 'a list * 'a * 'a list
  val map_fold   : ('a -> 'b -> 'a * 'c) -> 'a -> 'b list -> 'a * 'c list
  val mapi_fold  : (int -> 'a -> 'b -> 'a * 'c) -> 'a -> 'b list -> 'a * 'c list
  val pmap       : ('a -> 'b option) -> 'a list -> 'b list
  val rev_pmap   : ('a -> 'b option) -> 'a list -> 'b list
  val rotate     : [`Left|`Right] -> int -> 'a list -> int * 'a list

  (* ------------------------------------------------------------------ *)
  val ksort:
        ?stable:bool -> ?rev:bool
     -> key:('a -> 'b)
     -> cmp:('b -> 'b -> int)
     -> 'a list -> 'a list
end

(* -------------------------------------------------------------------- *)
module Parray : sig
  type 'a t

  val empty : 'a t
  val get : 'a t -> int -> 'a
  val length : 'a t -> int
  val of_list : 'a list -> 'a t
  val to_list : 'a t -> 'a list
  val of_array : 'a array -> 'a t
  val init : int -> (int -> 'a) -> 'a t
  val map : ('a -> 'b) -> 'a t -> 'b t
  val fmap : ('a -> 'b) -> 'a list -> 'b t
  val fold_left : ('a -> 'b -> 'a) -> 'a -> 'b t -> 'a
  val fold_right : ('b -> 'a -> 'a) -> 'b t -> 'a -> 'a
  val iter : ('a -> unit) -> 'a t -> unit
  val iter2 : ('a -> 'b -> unit) -> 'a t -> 'b t -> unit
  val split : ('a * 'b) t -> ('a t * 'b t)
  val exists : ('a -> bool) -> 'a t -> bool
  val for_all : ('a -> bool) -> 'a t -> bool
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

val hierror :
      loc:error_loc -> ?funname:string -> kind:string
   -> ?sub_kind:string -> ?internal:bool
   -> ('a, Format.formatter, unit, 'b) format4 -> 'a

(* -------------------------------------------------------------------- *)
type warning = 
  | ExtraAssignment 
  | UseLea
  | IntroduceNone
  | IntroduceArrayCopy 
  | Always

val nowarning : unit -> unit
val add_warning : warning -> unit -> unit 
val warning :
      warning -> Location.i_loc
   -> ('a, Format.formatter, unit) format -> 'a


(* -------------------------------------------------------------------- *)

type input_error =
  | FileNotFound of string
  | FileIsDirectory of string

val pp_input_error : input_error -> string
