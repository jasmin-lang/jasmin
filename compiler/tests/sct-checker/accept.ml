open Jasmin
open Common
open Sct_checker_forward

let path = "success"

let load_and_check name =
  Format.printf "File %s:@." name;
  let p = load_file (Filename.concat path name) in
  match ty_prog Arch.is_ct_sopn p [] with
  | exception Utils.HiError e ->
      Format.eprintf "%a@." Utils.pp_hierror e;
      exit 1
  | r -> List.iter (Format.printf "%a@." pp_funty) r

let () =
  let cases = Sys.readdir path in
  Array.sort String.compare cases;
  Array.iter load_and_check cases
