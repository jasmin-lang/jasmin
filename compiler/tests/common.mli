open Jasmin.Utils

val check_dir :
  (architecture list -> string -> 'a -> 'a) ->
  architecture list ->
  string ->
  'a ->
  'a
(** [check_dir f arch path acc] recursively traverses the directory [path] and
    calls [f] on the names of encountered files that are not directory and whose
    name ends in .jazz, threading a state whose initial value is [acc]. In any
    encountered directory, files are enumerated in alphabetical order. The list
    of architectures is the initial value [arch] complemented with any
    architecture matching the name of a parent directory (with the special
    “common” matching any architecture). *)

val disable_warnings : warning list -> unit -> unit
(** Disable the warnings given as argument (and enable all the others). *)
