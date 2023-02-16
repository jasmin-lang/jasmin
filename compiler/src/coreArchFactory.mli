module Core_arch_ARM : Arch_full.Core_arch

val core_arch_x86 :
  use_lea:bool ->
  use_set0:bool ->
  Glob_options.call_conv ->
  (module Arch_full.Core_arch)
