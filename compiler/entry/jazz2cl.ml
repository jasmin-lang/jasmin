module J = Jasmin
open Jasmin
open Utils
open Prog

type arch = Amd64 | CortexM


let add_inline f =
  { f with f_cc = Internal}

module type Arch_ToCL = sig
  module C : Arch_full.Core_arch
  val test : bool -> (module  ToCL.BaseOp
                       with type op = C.asm_op
                        and type extra_op = C.extra_op)
end

let parse_and_print print arch call_conv ecoutput joutput output file funname =
  let _ = if print then Glob_options.set_all_print () in

  let (module ACL : Arch_ToCL) =
    match arch with
    | Amd64 ->
      (module struct
        module C = (val CoreArchFactory.core_arch_x86 ~use_lea:false ~use_set0:false call_conv)
        let test = ToCL.x86BaseOpsign
      end)
    | CortexM ->
      (module struct
        module C = CoreArchFactory.Core_arch_ARM
        let test  = ToCL.armeBaseOpsign
      end)
  in
  let module A = Arch_full.Arch_from_Core_arch (ACL.C) in

  try
    let _, pprog, _ =
      (* FIXME: This code is a cut and paste of main_compiler *)
      try Compile.parse_file A.arch_info file with
      | Annot.AnnotationError (loc, code) -> hierror ~loc:(Lone loc) ~kind:"annotation error" "%t" code
      | Pretyping.TyError (loc, code) -> hierror ~loc:(Lone loc) ~kind:"typing error" "%a" Pretyping.pp_tyerror code
      | Syntax.ParseError (loc, msg) ->
          let msg =
            match msg with
            | None -> "unexpected token" (* default message *)
            | Some msg -> msg
          in
          hierror ~loc:(Lone loc) ~kind:"parse error" "%s" msg
    in

    let prog =
      (* FIXME: same here, maybe the solution will be to add the version that catch the error *)
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
    let module CL = ToCL.Mk(val ACL.test signed) in

     (* First step: annot all call site with inline *)
     let prog = (fst prog, List.map add_inline (snd prog)) in
     let cprog = Conv.cuprog_of_prog prog in

     let prog = Compile.compile_CL (module A) cprog funname in
     let prog = Conv.prog_of_cuprog ((* FIXME *) Obj.magic prog) in

     begin match joutput with
     | None -> ()
     | Some file ->
         let out, close = open_out file, close_out in
         let fmt = Format.formatter_of_out_channel out in
         Format.fprintf fmt "%a@." (Printer.pp_prog ~debug:true A.reg_size A.asmOp) prog;
         close out
     end;

     begin match ecoutput with
     | None -> ()
     | Some file ->
         let out, close = open_out file, close_out in
         let fmt = Format.formatter_of_out_channel out in
         let fnames = [funname.fn_name] in
         BatPervasives.finally
          (fun () -> close out)
          (fun () -> ToEC.extract A.reg_size A.asmOp fmt Normal prog fnames)
          ()
     end;

     let out, close =
       match output with
       | None -> (stdout, ignore)
       | Some file -> (open_out file, close_out)
     in

     let proc = CL.fun_to_proc (snd prog) (List.nth (snd prog) 0) in
     let fmt = Format.formatter_of_out_channel out in
     ToCL.CL.Proc.pp_proc fmt proc;
     close out
  with
  | Utils.HiError e ->
    Format.eprintf "%a@." pp_hierror e;
    exit 1

open Cmdliner

(* This should be shared with jazz2tex and jasminc *)

let file =
  let doc = "The Jasmin source file" in
  Arg.(required & pos 0 (some non_dir_file) None & info [] ~docv:"JAZZ" ~doc)

let output =
  let doc =
    "The file in which the result is written (instead of the standard output)"
  in
  Arg.(value & opt (some string) None & info [ "o"; "output" ] ~docv:"CL" ~doc)

let joutput =
  let doc =
    "Print the program before extraction to cryptoline to the file JAZZFILE"
  in
  Arg.(value & opt (some string) None & info [ "j"; "joutput" ] ~docv:"JAZZFILE" ~doc)

let ecoutput =
 let doc =
    "Extract (to EC) the program before extraction to cryptoline to the file ECFILE"
  in
  Arg.(value & opt (some string) None & info [ "e"; "ecoutput" ] ~docv:"ECFILE" ~doc)

(*
let print =
  let alts =
    List.map
      (fun p ->
        let (s, _msg) = glob_options.print_string p in
          (s, p))
      Compiler.compiler_step_list in
  let doc =
    Format.asprintf "The step to print (%s)" (Arg.doc_alts_enum alts)
  in
  let print = Arg.enum alts in
  Arg.(value & opt_all arch [] & info [ "p"; "print" ] ~doc)

*)

let print =
  let doc = "print result after each step" in
  Arg.(value & flag & info ["pall"] ~docv:"JAZZ" ~doc)

let funname =
  let doc =
    "The function to extract to CryptoLine"
  in
  Arg.(required & opt (some string) None & info [ "f"; "funname" ] ~docv:"CL" ~doc)


let arch =
  let alts = [ ("x86-64", Amd64); ("arm-m4", CortexM) ] in
  let doc =
    Format.asprintf "The target architecture (%s)" (Arg.doc_alts_enum alts)
  in
  let arch = Arg.enum alts in
  Arg.(value & opt arch Amd64 & info [ "arch" ] ~doc)

let call_conv =
  let alts =
    [ ("linux", J.Glob_options.Linux); ("windows", J.Glob_options.Windows) ]
  in
  let doc = Format.asprintf "Undocumented (%s)" (Arg.doc_alts_enum alts) in
  let call_conv = Arg.enum alts in
  Arg.(
    value
    & opt call_conv J.Glob_options.Linux
    & info [ "call-conv"; "cc" ] ~docv:"OS" ~doc)


let () =
  let doc = "Pretty-print Jasmin source programs into Cryptoline" in
  let man =
    [
      `S Manpage.s_environment;
      Manpage.s_environment_intro;
      `I ("OCAMLRUNPARAM", "This is an OCaml program");
      `I ("JASMINPATH", "To resolve $(i,require) directives");
    ]
  in
  let info =
    Cmd.info "jazz2cl" ~version:J.Glob_options.version_string ~doc ~man
  in
  Cmd.v info Term.(const parse_and_print $ print $ arch $ call_conv $ ecoutput $ joutput $ output $ file $ funname)
  |> Cmd.eval |> exit
