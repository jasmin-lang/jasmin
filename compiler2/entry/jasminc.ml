(* -------------------------------------------------------------------- *)
module J = Jasmin

open Jasmin.Utils

(* -------------------------------------------------------------------- *)
exception UsageError

(*-------------------------------------------------------------------- *)
let usage ?status () =
  Printf.eprintf "Usage: jasminc [filename]\n%!";
  oiter (fun i -> exit i) status

(* -------------------------------------------------------------------- *)
let main () =
  try
    if Array.length Sys.argv - 1 <> 1 then
      raise UsageError;

    let fname = Sys.argv.(1) in
    let ast   = J.Parseio.parse_program ~name:fname in
    let ast   = BatFile.with_file_in fname ast in
    let _ast  = J.Typing.tt_program J.Typing.Env.empty ast in

    Printf.eprintf "parsed & typed\n%!";
    ignore (J.Conv.cprogram_of_program : _ -> _);
    ()

  with
  | UsageError ->
      usage ~status:1 ()

  | J.Syntax.ParseError (loc, None) ->
      Printf.eprintf "%s: parse error\n%!"
        (J.Location.tostring loc)

  | J.Syntax.ParseError (loc, Some msg) ->
      Printf.eprintf "%s: parse error: %s\n%!"
        (J.Location.tostring loc) msg

(* -------------------------------------------------------------------- *)
let () = main ()
