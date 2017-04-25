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
    let _, pprog  = J.Typing.tt_program J.Typing.Env.empty ast in
    Printf.eprintf "parsed & typed\n%!";
    let prog = J.Subst.remove_params pprog in
    Printf.eprintf "params removed \n%!";
    let _tbl, _cprog = J.Conv.cprog_of_prog prog in
     Printf.eprintf "translated to coq \n%!";
    ()

  with
  | UsageError ->
      usage ~status:1 ()

  | J.Syntax.ParseError (loc, None) ->
      Format.eprintf "%s: parse error\n%!"
        (J.Location.tostring loc)

  | J.Syntax.ParseError (loc, Some msg) ->
      Format.eprintf "%s: parse error: %s\n%!"
        (J.Location.tostring loc) msg

  | J.Typing.TyError (loc, code) ->
      Format.eprintf "%s: typing error: %a\n%!"
        (J.Location.tostring loc)
        J.Typing.pp_tyerror code

(* -------------------------------------------------------------------- *)
let () = main ()
