(* -------------------------------------------------------------------------- *)
(* CLI errors. *)

type cli_error

val pp_cli_error : cli_error -> string

exception CLIerror of cli_error

(* -------------------------------------------------------------------------- *)
(* Checkers. *)

(* Check input file before setting [infile].
   @raises CLIerror if input file name is invalid. *)
val check_infile : string -> unit

(* Check CLI options.
   @raises CLIerror if any option is invalid. *)
val check_options : unit -> unit
