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

(*--------------------------------------------------------------------- *)

let pp_var_i tbl fmt vi = 
  let vi = Conv.vari_of_cvari tbl vi in
  Printer.pp_var ~debug:true fmt (Prog.L.unloc vi)

let rec pp_comp_err tbl fmt = function 
  | Compiler_util.Cerr_varalloc(x,y,msg) ->
    Format.fprintf fmt "Variable allocation %a and %a: %s"
     (pp_var_i tbl) x (pp_var_i tbl) y (Conv.string_of_string0 msg)
  | Compiler_util.Cerr_inline _ ->
    Format.fprintf fmt "Inlining error"
  | Compiler_util.Cerr_Loop s ->
    Format.fprintf fmt "loop iterator to small in %s"
      (Conv.string_of_string0 s)
  | Compiler_util.Cerr_fold2 s ->
    Format.fprintf fmt "fold2 error in %s"
      (Conv.string_of_string0 s)
  | Compiler_util.Cerr_neqop2(_, _, s) ->
    Format.fprintf fmt "op2 not equal in %s"
      (Conv.string_of_string0 s)
  | Compiler_util.Cerr_neqop(_,_, s) ->
    Format.fprintf fmt "opn not equal in %s"
      (Conv.string_of_string0 s)
  | Compiler_util.Cerr_neqdir(s) ->
    Format.fprintf fmt "dir not equal in %s"
      (Conv.string_of_string0 s)
  | Compiler_util.Cerr_neqexpr(_,_,s) ->
    Format.fprintf fmt "expression not equal in %s"
      (Conv.string_of_string0 s)
  | Compiler_util.Cerr_neqrval(_,_,s) ->
    Format.fprintf fmt "lval not equal in %s"
      (Conv.string_of_string0 s)
  | Compiler_util.Cerr_neqfun(_,_,s) ->
    Format.fprintf fmt "funname not equal in %s"
       (Conv.string_of_string0 s)
  | Compiler_util.Cerr_neqinstr(_,_,s) ->
    Format.fprintf fmt "instruction not equal in %s"
       (Conv.string_of_string0 s)
  | Compiler_util.Cerr_unknown_fun(f1,s) ->
    Format.fprintf fmt "unknown function %s during %s"
     (Conv.fun_of_cfun tbl f1).fn_name
     (Conv.string_of_string0 s)
  | Compiler_util.Cerr_in_fun f ->
    (pp_comp_ferr tbl) fmt f
  | Compiler_util.Cerr_arr_exp _ ->
    Format.fprintf fmt "err arr exp"
  | Compiler_util.Cerr_arr_exp_v _ ->
    Format.fprintf fmt "err arr exp: lval"
  | Compiler_util.Cerr_stk_alloc s ->
    Format.fprintf fmt "stack_alloc error %s"
      (Conv.string_of_string0 s)
  | Compiler_util.Cerr_linear s ->
    Format.fprintf fmt "linearisation error %s"
      (Conv.string_of_string0 s)
  | Compiler_util.Cerr_assembler s ->
    Format.fprintf fmt "assembler error %s"
      (Conv.string_of_string0 s)

and pp_comp_ferr tbl fmt = function
  | Compiler_util.Ferr_in_body(f1,f2,(_ii, err_msg)) ->  
    let f1 = Conv.fun_of_cfun tbl f1 in
    let f2 = Conv.fun_of_cfun tbl f2 in
      (* let (i_loc, _) = Conv.get_iinfo tbl ii in *)
    Format.fprintf fmt "in functions %s and %s at position s: %a"
      f1.fn_name f2.fn_name (* (Prog.L.tostring i_loc)  *)
      (pp_comp_err tbl) err_msg 
  | Compiler_util.Ferr_neqfun(f1,f2) ->
    let f1 = Conv.fun_of_cfun tbl f1 in
    let f2 = Conv.fun_of_cfun tbl f2 in
    Format.fprintf fmt "function %s and %s not equal"
      f1.fn_name f2.fn_name
  | Compiler_util.Ferr_neqprog  -> 
    Format.fprintf fmt "program not equal"
  | Compiler_util.Ferr_loop     ->
      Format.fprintf fmt "loop iterator to small" 

(* -------------------------------------------------------------------- *)
let main () =
  try

    parse();

    let fname = !infile in
    let ast   = Parseio.parse_program ~name:fname in
    let ast   = BatFile.with_file_in fname ast in
    let _, pprog  = Typing.tt_program Typing.Env.empty ast in
    if !debug then begin
      Printf.eprintf "parsed & typed\n%!";
      Format.eprintf "%a@." Printer.pp_pprog pprog
    end;
    if !typeonly then exit 0;

    let prog = Subst.remove_params pprog in
    if !debug then begin
      Printf.eprintf "params removed \n%!";
      Format.eprintf "%a@." (Printer.pp_prog ~debug:true) prog
    end;

    (* Generate the coq program if needed *)
    if !coqfile <> "" then begin
      let out = open_out !coqfile in
      let fmt = Format.formatter_of_out_channel out in
      Format.fprintf fmt "%a@." Coq_printer.pp_prog prog;
      close_out out;
      if !debug then Format.eprintf "coq program extracted@."
    end;

    if !coqonly then exit 0;

    (* Now call the coq compiler *)
    let tbl, cprog = Conv.cprog_of_prog prog in
    if !debug then Printf.eprintf "translated to coq \n%!";

    let fdef_of_cfdef fn cfd = Conv.fdef_of_cfdef tbl (fn,cfd) in
    let cfdef_of_fdef fd = snd (Conv.cfdef_of_fdef tbl fd) in
    let apply trans fn cfd =
      let fd = fdef_of_cfdef fn cfd in
      let fd = trans fd in
      cfdef_of_fdef fd in

    let rename_fd = apply Subst.clone_func in
    let expand_fd = apply Array_expand.arrexp_func in
    let var_alloc_fd  = apply Varalloc.merge_var_inline_fd in
    let share_stk_fd  = apply Varalloc.alloc_stack_fd in
    let reg_alloc_fd  = apply Regalloc.regalloc in
    let stk_alloc_fd _fn _cfd = assert false in
    let print_prog s cp =
      if !debug then begin
        let p = Conv.prog_of_cprog tbl cp in
        Format.eprintf "After %s@." (Conv.string_of_string0 s);
        Format.eprintf "%a@." Printer.pp_cprog cp;
        Format.eprintf "%a@." (Printer.pp_prog ~debug:true) p
      end;
      cp
    in
 
    let cparams = {
      Compiler.rename_fd    = rename_fd;
      Compiler.expand_fd    = expand_fd;
      Compiler.var_alloc_fd = var_alloc_fd;
      Compiler.share_stk_fd = share_stk_fd;
      Compiler.reg_alloc_fd = reg_alloc_fd;
      Compiler.stk_alloc_fd = stk_alloc_fd;
      Compiler.print_prog   = print_prog;
    } in
    begin match 
      Compiler.compile_prog_to_x86 cparams
        cprog with
    | Utils0.Error e -> 
      Utils.hierror "compilation error %a@.PLEASE REPORT"
         (pp_comp_ferr tbl) e
    | _ -> ()
    end

  with
  | Utils.HiError s ->
    Format.eprintf "%s\n%!" s

  | UsageError ->
     Arg.usage options usage_msg;
     exit 1;

  | Syntax.ParseError (loc, None) ->
      Format.eprintf "%s: parse error\n%!"
        (Location.tostring loc)

  | Syntax.ParseError (loc, Some msg) ->
      Format.eprintf "%s: parse error: %s\n%!"
        (Location.tostring loc) msg

  | Typing.TyError (loc, code) ->
      Format.eprintf "%s: typing error: %a\n%!"
        (Location.tostring loc)
        Typing.pp_tyerror code

(* -------------------------------------------------------------------- *)
let () = main ()
