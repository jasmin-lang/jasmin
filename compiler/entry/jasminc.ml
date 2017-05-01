(* -------------------------------------------------------------------- *)
module J = Jasmin

(* -------------------------------------------------------------------- *)
exception UsageError

(*--------------------------------------------------------------------- *)
let infile = ref ""
let outfile = ref ""
let typeonly = ref false
let debug = ref false
let coqfile = ref ""
let coqonly = ref false

let set_coqonly s =
  coqfile := s;
  coqonly := true

let options = [
    "-o"       , Arg.Set_string outfile, "[filename]: name of the output file";
    "-typeonly", Arg.Set typeonly      , ": stop after typechecking";
    "-debug"   , Arg.Set debug         , ": print debug information";
    "-coq"     , Arg.Set_string coqfile, "[filename]: generate the corresponding coq file";
    "-coqonly" , Arg.String set_coqonly, "[filename]: generate the corresponding coq file, and exit"
  ]

let usage_msg = "Usage : jasminc [option] filename"

let parse () =
  let error () = raise UsageError in
  let set_in s =
    if !infile <> "" then error();
    infile := s  in
  Arg.parse options set_in usage_msg;
  if !infile = "" then error()

(* -------------------------------------------------------------------- *)
let main () =
  try

    parse();

    let fname = !infile in
    let ast   = J.Parseio.parse_program ~name:fname in
    let ast   = BatFile.with_file_in fname ast in
    let _, pprog  = J.Typing.tt_program J.Typing.Env.empty ast in
    if !debug then begin
      Printf.eprintf "parsed & typed\n%!";
      Format.eprintf "%a@." J.Printer.pp_pprog pprog
    end;
    if !typeonly then exit 0;

    let prog = J.Subst.remove_params pprog in
    if !debug then begin
      Printf.eprintf "params removed \n%!";
      Format.eprintf "%a@." (J.Printer.pp_prog ~debug:true) prog
    end;

    (* Generate the coq program if needed *)
    if !coqfile <> "" then begin
      let out = open_out !coqfile in
      let fmt = Format.formatter_of_out_channel out in
      Format.fprintf fmt "%a@." J.Coq_printer.pp_prog prog;
      close_out out;
      if !debug then Format.eprintf "coq program extracted@."
    end;

    if !coqonly then exit 0;

    (* Now call the coq compiler *)
    let tbl, cprog = J.Conv.cprog_of_prog prog in
    if !debug then Printf.eprintf "translated to coq \n%!";

    let fdef_of_cfdef fn cfd = J.Conv.fdef_of_cfdef tbl (fn,cfd) in
    let cfdef_of_fdef fd = snd (J.Conv.cfdef_of_fdef tbl fd) in
    let apply trans fn cfd =
      let fd = fdef_of_cfdef fn cfd in
      let fd = trans fd in
      cfdef_of_fdef fd in

    let rename_fd = apply J.Subst.clone_func in
    let expand_fd = apply J.Array_expand.arrexp_func in
    let var_alloc_fd  = 
      apply J.Varalloc.alloc_stack_fd in
    let reg_alloc_fd  = apply J.Regalloc.regalloc in
    let stk_alloc_fd _fn _cfd = assert false in
    let print_prog s cp =
      if !debug then begin
        let p = J.Conv.prog_of_cprog tbl cp in
        Format.eprintf "After %s@." (J.Conv.string_of_string0 s);
        Format.eprintf "%a@." J.Printer.pp_cprog cp;
        Format.eprintf "%a@." (J.Printer.pp_prog ~debug:true) p
      end;
      cp
    in

    let pp_var_i fmt vi = 
      let vi = J.Conv.vari_of_cvari tbl vi in
      J.Printer.pp_var ~debug:true fmt (J.Prog.L.unloc vi)
    in

    let rec pp_comp_err fmt = function 
      | J.Compiler_util.Cerr_varalloc(x,y,msg) ->
        Format.fprintf fmt "Variable allocation %a and %a: %s"
          pp_var_i x pp_var_i y (J.Conv.string_of_string0 msg)
      | J.Compiler_util.Cerr_inline _ ->
        Format.fprintf fmt "Inlining error"
      | J.Compiler_util.Cerr_Loop s ->
        Format.fprintf fmt "loop iterator to small in %s"
          (J.Conv.string_of_string0 s)
      | J.Compiler_util.Cerr_fold2 s ->
        Format.fprintf fmt "fold2 error in %s"
          (J.Conv.string_of_string0 s)
      | J.Compiler_util.Cerr_neqop2(_, _, s) ->
        Format.fprintf fmt "op2 not equal in %s"
          (J.Conv.string_of_string0 s)
      | J.Compiler_util.Cerr_neqop(_,_, s) ->
        Format.fprintf fmt "opn not equal in %s"
          (J.Conv.string_of_string0 s)
      | J.Compiler_util.Cerr_neqdir(s) ->
        Format.fprintf fmt "dir not equal in %s"
          (J.Conv.string_of_string0 s)
      | J.Compiler_util.Cerr_neqexpr(_,_,s) ->
        Format.fprintf fmt "expression not equal in %s"
          (J.Conv.string_of_string0 s)
      | J.Compiler_util.Cerr_neqrval(_,_,s) ->
        Format.fprintf fmt "lval not equal in %s"
          (J.Conv.string_of_string0 s)
      | J.Compiler_util.Cerr_neqfun(_,_,s) ->
        Format.fprintf fmt "funname not equal in %s"
           (J.Conv.string_of_string0 s)
      | J.Compiler_util.Cerr_neqinstr(_,_,s) ->
        Format.fprintf fmt "instruction not equal in %s"
           (J.Conv.string_of_string0 s)
      | J.Compiler_util.Cerr_unknown_fun(f1,s) ->
        Format.fprintf fmt "unknown function %s during %s"
         (J.Conv.fun_of_cfun tbl f1).fn_name
         (J.Conv.string_of_string0 s)
      | J.Compiler_util.Cerr_in_fun f ->
        pp_comp_ferr fmt f
      | J.Compiler_util.Cerr_arr_exp _ ->
        Format.fprintf fmt "err arr exp"
      | J.Compiler_util.Cerr_arr_exp_v _ ->
        Format.fprintf fmt "err arr exp: lval"
      | J.Compiler_util.Cerr_stk_alloc s ->
        Format.fprintf fmt "stack_alloc error %s"
          (J.Conv.string_of_string0 s)
      | J.Compiler_util.Cerr_linear s ->
        Format.fprintf fmt "linearisation error %s"
          (J.Conv.string_of_string0 s)
      | J.Compiler_util.Cerr_assembler s ->
        Format.fprintf fmt "assembler error %s"
          (J.Conv.string_of_string0 s)

    and pp_comp_ferr fmt = function
      | J.Compiler_util.Ferr_in_body(f1,f2,(_ii, err_msg)) ->  
        let f1 = J.Conv.fun_of_cfun tbl f1 in
        let f2 = J.Conv.fun_of_cfun tbl f2 in
(*        let (i_loc, _) = J.Conv.get_iinfo tbl ii in *)
        Format.fprintf fmt "in functions %s and %s at position s: %a"
          f1.fn_name f2.fn_name (* (J.Prog.L.tostring i_loc)  *)
          pp_comp_err err_msg 
      | J.Compiler_util.Ferr_neqfun(f1,f2) ->
        let f1 = J.Conv.fun_of_cfun tbl f1 in
        let f2 = J.Conv.fun_of_cfun tbl f2 in
        Format.fprintf fmt "function %s and %s not equal"
          f1.fn_name f2.fn_name
      | J.Compiler_util.Ferr_neqprog  -> 
        Format.fprintf fmt "program not equal"
      | J.Compiler_util.Ferr_loop     ->
        Format.fprintf fmt "loop iterator to small" in

    let cparams = {
      J.Compiler.rename_fd    = rename_fd;
      J.Compiler.expand_fd    = expand_fd;
      J.Compiler.var_alloc_fd = var_alloc_fd;
      J.Compiler.reg_alloc_fd = reg_alloc_fd;
      J.Compiler.stk_alloc_fd = stk_alloc_fd;
      J.Compiler.print_prog   = print_prog;
    } in
    begin match 
      J.Compiler.compile_prog_to_x86 cparams
        cprog with
    | J.Utils0.Error e -> 
      Format.eprintf "compilation error %a@.PLEASE REPORT@."
          pp_comp_ferr e
    | _ -> ()
    end

  with
  | UsageError ->
     Arg.usage options usage_msg;
     exit 1;

  | J.Syntax.ParseError (loc, None) ->
      Format.eprintf "%s: parse error\n%!"
        (J.Location.tostring loc)

  | J.Syntax.ParseError (loc, Some msg) ->
      Format.eprintf "%s: parse error: %s\n%!"
        (J.Location.tostring loc) msg

  | J.Typing.TyError (loc, code) ->
      Format.eprintf "%s: typing error: %a\n%!"
        (J.Location.tostring loc)
        J.Typing.pp_tyerror code

(* -------------------------------------------------------------------- *)
let () = main ()
