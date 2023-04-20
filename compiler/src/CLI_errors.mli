(* -------------------------------------------------------------------------- *)
(* CLI errors. *)

type cli_error =
   | RedundantInputFile of string * string
   | FileNotFound of string
   | FileIsDirectory of string
   | FilePathNotFound of string

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
