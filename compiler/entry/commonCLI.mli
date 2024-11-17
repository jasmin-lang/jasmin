open Jasmin
open Cmdliner

val get_arch_module : Utils.architecture -> Glob_options.call_conv -> (module Arch_full.Arch)
val arch : Utils.architecture Term.t
val call_conv : Glob_options.call_conv Term.t
val nowarning : bool Term.t
