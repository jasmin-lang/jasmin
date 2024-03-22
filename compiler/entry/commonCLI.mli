open Jasmin
open Cmdliner

type arch

val get_arch_module : arch -> Glob_options.call_conv -> (module Arch_full.Arch)
val arch : arch Term.t
val call_conv : Glob_options.call_conv Term.t
