open Jasmin
open Common

let path = "fail"

let load_and_check name =
  Format.printf "File %s:@." name;
  let ((_, fds) as p) = load_file (Filename.concat path name) in
  List.iter
    (fun fd ->
      if fd.Prog.f_cc <> Internal then
        let f = fd.Prog.f_name.fn_name in
        try
          ty_prog p [ f ];
          Format.eprintf "Did not fail: %s.@." f;
          assert false
        with Utils.HiError e ->
          Format.printf "Failed as expected %s: %a@." f Utils.pp_hierror e)
    fds

let () =
  let cases = Sys.readdir path in
  Array.sort String.compare cases;
  Array.iter load_and_check cases
