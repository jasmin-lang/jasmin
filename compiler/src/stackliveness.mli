open Prog

type live_elem = 
  | NotArray (* the full variable is in live *)
  | Array of ByteSet.t (* The set of bytes in live *)

module Live : sig
  type t
  val empty : t 
  val incl  : t -> t -> bool
  val union : t -> t -> t 
  val get   : var -> t -> live_elem 
  val set   : var -> live_elem -> t -> t
  val remove : var -> t -> t
end

type live_info = {
    before : Live.t;
    after  : Live.t;
  }

val pp_live_info : Format.formatter -> live_info -> unit

val live_fd : 'info func -> live_info func

