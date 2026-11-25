open Jasmin
open Utils
open Architecture
let rec check_dir check_file archs prefix errors =
  let dir = Sys.readdir prefix in
  Array.sort String.compare dir;
  Array.fold_left (check_path check_file archs prefix) errors dir

and check_path check_file archs prefix errors filename =
  let path = Filename.concat prefix filename in
  if Sys.is_directory path then
    (* A directory is named after an architecture, current or former name
       (the tests of the Cortex-M4 are in arm-m4). *)
    let archs =
      try
        List.assoc filename
          (List.map
             (fun (name, arch) -> (name, arch :: archs))
             (architectures @ deprecated_architectures)
           @ [
               ("risc-v", RISCV :: archs);
               ("common", all_architectures);
             ])
      with Not_found -> archs
    in
    check_dir check_file archs path errors
  else if String.ends_with filename ".jazz" then check_file archs path errors
  else errors

let disable_warnings ws () =
  set_all_warnings ();
  List.iter remove_warning ws
