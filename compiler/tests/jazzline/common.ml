module J = Jasmin
open Jasmin
open Utils
open Prog

module type Arch_ToCL = sig
  module C : Arch_full.Core_arch
  val baseop : bool -> (module  ToCL.BaseOp
                       with type op = C.asm_op
                        and type extra_op = C.extra_op)
end

let parse_and_print file funname =

  let (module ACL : Arch_ToCL) =
    (module struct
      module C = (val CoreArchFactory.core_arch_x86 ~use_lea:false ~use_set0:false Linux)
      let baseop = ToCL.x86BaseOpsign
    end)
  in
  let module A = Arch_full.Arch_from_Core_arch (ACL.C) in

  try
    let _, pprog, _ =
      try Compile.parse_file A.arch_info file with
      | Annot.AnnotationError (loc, code) ->
        hierror ~loc:(Lone loc) ~kind:"annotation error" "%t" code
      | Pretyping.TyError (loc, code) ->
        hierror ~loc:(Lone loc) ~kind:"typing error" "%a" Pretyping.pp_tyerror code
      | Syntax.ParseError (loc, msg) ->
        let msg =
          match msg with
          | None -> "unexpected token" (* default message *)
          | Some msg -> msg
        in
        hierror ~loc:(Lone loc) ~kind:"parse error" "%s" msg
    in

    let prog =
      try Compile.preprocess A.reg_size A.asmOp pprog
      with Typing.TyError(loc, code) ->
        hierror ~loc:(Lmore loc) ~kind:"typing error" "%s" code
    in

    let funname,annot =
      try
        let fd = List.find (fun fd -> fd.Prog.f_name.fn_name = funname) (snd prog) in
        fd.Prog.f_name,fd.Prog.f_annot
      with Not_found ->
        hierror ~loc:Lnone ~kind:"typing error" "unknow function %s" funname in

    let add_inline f = { f with f_cc = Internal} in
    let prog = (fst prog, List.map add_inline (snd prog)) in

    let cprog = Conv.cuprog_of_prog prog in

    let prog = Compile.compile_CL (module A) cprog funname in
    let prog = Conv.prog_of_cuprog ((* FIXME *) Obj.magic prog) in

    let trans annot =
      let l =
        ["t", true ; "f", false]
      in
      let mk_trans = Annot.filter_string_list None l in
      let atran annot =
        match Annot.ensure_uniq1 "signed" mk_trans annot with
        | None -> false
        | Some s -> s
      in
      atran annot
    in
    let signed = trans annot.f_user_annot in

    let module CL = ToCL.Mk(val ACL.baseop signed) in
    let proc = CL.fun_to_proc (snd prog) (List.nth (snd prog) 0) in

    let out, close = (stdout, ignore) in
    let fmt = Format.formatter_of_out_channel out in
    ToCL.CL.Proc.pp_proc fmt proc;
    close out
  with
  | Utils.HiError e ->
    Format.eprintf "%a@." pp_hierror e;
    exit 1
