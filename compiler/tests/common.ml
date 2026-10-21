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
    let archs =
      try
        List.assoc filename
          (("x86-64", X86_64 :: archs)
           :: List.map (fun c -> (c.Arm_mcore.name, ARM_M c :: archs)) Arm_mcore.all
           @ [
               ("armv8a", ARMv8A :: archs);
               ("risc-v", RISCV :: archs);
               ("common", List.map snd architectures);
             ])
      with Not_found -> archs
    in
    check_dir check_file archs path errors
  else if String.ends_with filename ".jazz" then check_file archs path errors
  else errors

let disable_warnings ws () =
  set_all_warnings ();
  List.iter remove_warning ws
