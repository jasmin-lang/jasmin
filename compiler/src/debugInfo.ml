open Utils
open Location
open Format

(** Give a unique number to the given file name.
    Second return value is true the first time this file name is seed. *)
let internFile =
  (* TODO: remove global mutable state *)
  let count = ref 0 in
  let internedFiles = Hashtbl.create 17 in
  fun s ->
    match Hashtbl.find internedFiles s with
    | v -> (v, false)
    | exception Not_found ->
        incr count;
        let v = !count in
        Hashtbl.add internedFiles s v;
        (v, true)

let source_positions ii =
  if (not !Glob_options.dwarf) || Location.isdummy ii then []
  else
    let n, isFresh = internFile ii.loc_fname in
    let line, col = ii.loc_start in
    let loc = [ asprintf ".loc %d %d %d\n" n line col ] in
    if isFresh then asprintf ".file %d %S\n" n ii.loc_fname :: loc else loc
