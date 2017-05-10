open Prog

(* -------------------------------------------------------------------- *)
exception UsageError

(*--------------------------------------------------------------------- *)
let infile = ref ""
let outfile = ref ""
let typeonly = ref false
let debug = ref false
let coqfile = ref ""
let coqonly = ref false
let print_list = ref []

let set_coqonly s =
  coqfile := s;
  coqonly := true

let poptions = [
    Compiler.Typing
  ; Compiler.ParamsExpansion
  ; Compiler.Inlining
  ; Compiler.RemoveUnusedFunction
  ; Compiler.Unrolling
  ; Compiler.AllocInlineAssgn
  ; Compiler.DeadCode_AllocInlineAssgn
  ; Compiler.ShareStackVariable
  ; Compiler.DeadCode_ShareStackVariable
  ; Compiler.RegArrayExpansion
  ; Compiler.LowerInstruction
  ; Compiler.RegAllocation
  ; Compiler.DeadCode_RegAllocation
  ; Compiler.StackAllocation
  ; Compiler.Linearisation
  ; Compiler.Assembly ]

let set_printing p () =
  print_list := p :: !print_list

let set_all_print () =
  print_list := poptions

let print_strings = function
  | Compiler.Typing                      -> "typing"  , "typing"
  | Compiler.ParamsExpansion             -> "cstexp"  , "constant expansion"
  | Compiler.Inlining                    -> "inline"  , "inlining"
  | Compiler.RemoveUnusedFunction        -> "rmfunc"  , "remove unused function"
  | Compiler.Unrolling                   -> "unroll"  , "unrolling"
  | Compiler.AllocInlineAssgn            -> "valloc"  , "inlined variables allocation"
  | Compiler.DeadCode_AllocInlineAssgn   -> "vallocd" , "dead code after inlined variables allocation"
  | Compiler.ShareStackVariable          -> "vshare"  , "sharing of stack variables"
  | Compiler.DeadCode_ShareStackVariable -> "vshared" , "dead code after sharing of stack variables"
  | Compiler.RegArrayExpansion           -> "arrexp"  , "expansion of register arrays"
  | Compiler.LowerInstruction            -> "lowering", "lowering of instructions"
  | Compiler.RegAllocation               -> "ralloc"  , "register allocation"
  | Compiler.DeadCode_RegAllocation      -> "rallocd" , "dead code after register allocation"
  | Compiler.StackAllocation             -> "stkalloc", "stack allocation"
  | Compiler.Linearisation               -> "linear"  , "linearisation"
  | Compiler.Assembly                    -> "asm"     , "generation of assembly"

let print_option p =
  let s, msg = print_strings p in
  ("-p"^s, Arg.Unit (set_printing p), "print program after "^msg)

let options = [
    "-o"       , Arg.Set_string outfile, "[filename]: name of the output file";
    "-typeonly", Arg.Set typeonly      , ": stop after typechecking";
    "-debug"   , Arg.Set debug         , ": print debug information";
    "-coq"     , Arg.Set_string coqfile, "[filename]: generate the corresponding coq file";
    "-coqonly" , Arg.String set_coqonly, "[filename]: generate the corresponding coq file, and exit";
    "-pall"    , Arg.Unit set_all_print, "print program after each compilation steps"
  ] @  List.map print_option poptions

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
  | Compiler_util.Cerr_neqop1(_, _, s) ->
    Format.fprintf fmt "op1 not equal in %s"
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
  | Compiler_util.Ferr_uniqfun ->
    Format.fprintf fmt "two function declarations with the same name"

(* -------------------------------------------------------------------- *)

let eprint step pp_prog p =
  if List.mem step !print_list then
    let (_, msg) = print_strings step in
    Format.eprintf
"(* -------------------------------------------------------------------- *)@.";
    Format.eprintf "(* After %s *)@.@." msg;
    Format.eprintf "%a@.@.@." pp_prog p

(* -------------------------------------------------------------------- *)
let main () =
  try

    parse();

    let fname = !infile in
    let ast   = Parseio.parse_program ~name:fname in
    let ast   = BatFile.with_file_in fname ast in

    let _, pprog  = Typing.tt_program Typing.Env.empty ast in
    eprint Compiler.Typing Printer.pp_pprog pprog;
    if !typeonly then exit 0;

    let prog = Subst.remove_params pprog in
    eprint Compiler.ParamsExpansion (Printer.pp_prog ~debug:true) prog;

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

    let lowering_vars = Lowering.(
        let b n = Conv.fresh_cvar tbl n (Bty Bool) in
        { fresh_OF = b "OF"
        ; fresh_CF = b "CF"
        ; fresh_SF = b "SF"
        ; fresh_PF = b "PF"
        ; fresh_ZF = b "ZF"
        }) in

    let fdef_of_cfdef fn cfd = Conv.fdef_of_cfdef tbl (fn,cfd) in
    let cfdef_of_fdef fd = snd (Conv.cfdef_of_fdef tbl fd) in
    let apply msg trans fn cfd =
      if !debug then Format.eprintf "START %s@." msg;
      let fd = fdef_of_cfdef fn cfd in
      if !debug then Format.eprintf "back to ocaml@.";
      let fd = trans fd in
      cfdef_of_fdef fd in

    let stk_alloc_fd fn cfd =
      let fd = fdef_of_cfdef fn cfd in
      if !debug then Format.eprintf "START stack alloc@." ;

      let alloc, sz, fd = Array_expand.stk_alloc_func fd in
      let alloc =
        let trans (v,i) = Conv.cvar_of_var tbl v, Conv.z_of_int i in
        List.map trans alloc in
      let sz = Conv.z_of_int sz in
      let cfd = cfdef_of_fdef fd in
      let sfd = {
        Stack_alloc.sf_iinfo  = cfd.Expr.f_iinfo;
        Stack_alloc.sf_stk_sz = sz;
        Stack_alloc.sf_stk_id =
          Var0.Var.vname (Conv.cvar_of_var tbl Prog.vstack);
        Stack_alloc.sf_params = cfd.Expr.f_params;
        Stack_alloc.sf_body   = cfd.Expr.f_body;
        Stack_alloc.sf_res    = cfd.Expr.f_res; } in
      alloc, sfd
    in

    let pp_cprog fmt cp =
      let p = Conv.prog_of_cprog tbl cp in
      Printer.pp_prog ~debug:true fmt p in

    let cparams = {
      Compiler.rename_fd    = apply "rename_fd" Subst.clone_func;
      Compiler.expand_fd    = apply "arr exp" Array_expand.arrexp_func;
      Compiler.var_alloc_fd = apply "var alloc" Varalloc.merge_var_inline_fd;
      Compiler.share_stk_fd = apply "share stk" Varalloc.alloc_stack_fd;
      Compiler.reg_alloc_fd = apply "reg alloc" Regalloc.regalloc;
      Compiler.stk_alloc_fd = stk_alloc_fd;
      Compiler.lowering_vars = lowering_vars;
      Compiler.print_prog   = (fun s p -> eprint s pp_cprog p; p);
    } in

    let entries =
      let ep = List.filter (fun fd -> fd.f_cc = Export) prog in
      List.map (fun fd -> Conv.cfun_of_fun tbl fd.f_name) ep in

    begin match
      Compiler.compile_prog_to_x86 cparams entries cprog with
    | Utils0.Error e ->
      Utils.hierror "compilation error %a@.PLEASE REPORT"
         (pp_comp_ferr tbl) e
    | _ -> ()
    end

  with
  | Utils.HiError s ->
      Format.eprintf "%s\n%!" s; exit 1

  | UsageError ->
      Arg.usage options usage_msg;
      exit 1;

  | Syntax.ParseError (loc, None) ->
      Format.eprintf "%s: parse error\n%!"
        (Location.tostring loc);
      exit 1

  | Syntax.ParseError (loc, Some msg) ->
      Format.eprintf "%s: parse error: %s\n%!"
        (Location.tostring loc) msg;
      exit 1

  | Typing.TyError (loc, code) ->
      Format.eprintf "%s: typing error: %a\n%!"
        (Location.tostring loc)
        Typing.pp_tyerror code;
      exit 1

(* -------------------------------------------------------------------- *)
let () = main ()
