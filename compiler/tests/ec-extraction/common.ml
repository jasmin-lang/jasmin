open Jasmin
open Utils

module type Arch_ToCL = sig
  module C : Arch_full.Core_arch
end

let parse_and_extract ?(amodel=false) file functions =
  let (module ACL : Arch_ToCL) =
    (module struct
      module C =
        (val CoreArchFactory.core_arch_x86 ~use_lea:false ~use_set0:false Linux)
    end)
  in
  let module A = Arch_full.Arch_from_Core_arch (ACL.C) in

  let _env, pprog, _ast = Compile.parse_file A.arch_info file in
  let prog =
    try Compile.preprocess A.reg_size A.asmOp pprog
    with Typing.TyError (loc, code) ->
      hierror ~loc:(Lmore loc) ~kind:"typing error" "%s" code
  in
  let amodel = if amodel then ToEC.ArrayOld else ToEC.ArrayEclib in
  let fmt = Format.std_formatter in
  ToEC.extract prog X86_64 A.reg_size A.asmOp Normal amodel functions None fmt
