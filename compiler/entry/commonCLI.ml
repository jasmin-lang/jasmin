open Jasmin
open Cmdliner

let get_arch_module arch call_conv : (module Arch_full.Arch) =
  (module Arch_full.Arch_from_Core_arch
            ((val match arch with
                  | Utils.X86_64 ->
                      (module (val CoreArchFactory.core_arch_x86 ~use_lea:false
                                     ~use_set0:false call_conv)
                      : Arch_full.Core_arch)
                  | Utils.ARM_M4 ->
                      (module CoreArchFactory.Core_arch_ARM
                      : Arch_full.Core_arch))))

let arch =
  let alts = [ ("x86-64", Utils.X86_64); ("arm-m4", Utils.ARM_M4) ] in
  let doc =
    Format.asprintf "The target architecture (%s)" (Arg.doc_alts_enum alts)
  in
  let arch = Arg.enum alts in
  Arg.(value & opt arch Utils.X86_64 & info [ "arch" ] ~doc)

let call_conv =
  let alts =
    [ ("linux", Glob_options.Linux); ("windows", Glob_options.Windows) ]
  in
  let doc = Format.asprintf "Undocumented (%s)" (Arg.doc_alts_enum alts) in
  let call_conv = Arg.enum alts in
  Arg.(
    value
    & opt call_conv Glob_options.Linux
    & info [ "call-conv"; "cc" ] ~docv:"OS" ~doc)
