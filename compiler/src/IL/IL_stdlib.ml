open Core.Std
open IL_Lang

let std_lib_file = "lib/std.rs"

let std_protos () =
  let s = In_channel.read_all std_lib_file in
  (* eprintf "Parsing %s as %s\n\n%!" file ftype; *)
  match IL_Parse.modul std_lib_file s with
  | `ParseOk res        -> res.mod_funprotos
  | `ParseError(pinfos) -> P.failloc_c s pinfos
