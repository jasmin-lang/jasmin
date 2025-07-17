open Jasmin.Utils

val check_dir :
  (architecture list -> string -> 'a -> 'a) ->
  architecture list ->
  string ->
  'a ->
  'a

val disable_warnings : warning list -> unit -> unit
