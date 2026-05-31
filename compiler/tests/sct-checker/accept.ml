open Jasmin
open Utils
open Common
open Sct_checker_forward

let path = "success"

let load_and_check n name =
  Format.printf "File %s:@." name;
  set_warn_recoverable true;
  set_all_warnings ();
  if String.equal name "unused-msf.jazz" then
    List.iter remove_warning [ SCTchecker; UnusedVar ];
  let p = load_file (Filename.concat path name) in
  match ty_prog Arch.is_ct_sopn p [] with
  | exception Utils.HiError e ->
      Format.eprintf "%a@." Utils.pp_hierror e;
      n + 1
  | r ->
      List.iter (Format.printf "%a@." pp_funty) r;
      n

let () =
  let cases = Sys.readdir path in
  Array.sort String.compare cases;
  Array.fold_left load_and_check 0 cases |> exit
