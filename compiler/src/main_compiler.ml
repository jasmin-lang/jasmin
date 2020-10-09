open Utils
open Prog
open Glob_options

(* -------------------------------------------------------------------- *)
exception UsageError

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

let pp_clval tbl fmt lv =
  Conv.lval_of_clval tbl lv |>
  Printer.(pp_glv (pp_var ~debug:true)) fmt

let rec pp_comp_err tbl fmt =
  let open Printer in
  function
  | Compiler_util.Cerr_varalloc(x,y,msg) ->
    Format.fprintf fmt "Variable allocation %a and %a: %a"
     (pp_var_i tbl) x (pp_var_i tbl) y pp_string0 msg
  | Compiler_util.Cerr_inline _ ->
    Format.fprintf fmt "Inlining error"
  | Compiler_util.Cerr_Loop s ->
    Format.fprintf fmt "loop iterator to small in %a"
      pp_string0 s
  | Compiler_util.Cerr_fold2 s ->
    Format.fprintf fmt "fold2 error in %a"
      pp_string0 s
  | Compiler_util.Cerr_neqty (_, _, s) ->
    Format.fprintf fmt "neqty %a"
      pp_string0 s
  | Compiler_util.Cerr_neqop1(_, _, s) ->
    Format.fprintf fmt "op1 not equal in %a"
      pp_string0 s
  | Compiler_util.Cerr_neqop2(_, _, s) ->
    Format.fprintf fmt "op2 not equal in %a"
      pp_string0 s
  | Compiler_util.Cerr_neqopN(_, _, s) ->
    Format.fprintf fmt "opN not equal in %a"
      pp_string0 s
  | Compiler_util.Cerr_neqop(_,_, s) ->
    Format.fprintf fmt "opn not equal in %a"
      pp_string0 s
  | Compiler_util.Cerr_neqdir(s) ->
    Format.fprintf fmt "dir not equal in %a"
      pp_string0 s
  | Compiler_util.Cerr_neqexpr(_,_,s) ->
    Format.fprintf fmt "expression not equal in %a"
      pp_string0 s
  | Compiler_util.Cerr_neqlval(lv1, lv2, s) ->
    Format.fprintf fmt "lval not equal in %a: %a and %a"
      pp_string0 s (pp_clval tbl) lv1 (pp_clval tbl) lv2
  | Compiler_util.Cerr_neqfun(_,_,s) ->
    Format.fprintf fmt "funname not equal in %a"
       pp_string0 s
  | Compiler_util.Cerr_neqinstr(_,_,s) ->
    Format.fprintf fmt "instruction not equal in %a"
       pp_string0 s
  | Compiler_util.Cerr_unknown_fun(f1,s) ->
    Format.fprintf fmt "unknown function %s during %a"
     (Conv.fun_of_cfun tbl f1).fn_name
     pp_string0 s
  | Compiler_util.Cerr_in_fun f ->
    (pp_comp_ferr tbl) fmt f
  | Compiler_util.Cerr_arr_exp (e1, e2) ->
    Format.fprintf fmt "err arr exp %a and %a"
      (Printer.pp_expr ~debug:true) (Conv.expr_of_cexpr tbl e1)
      (Printer.pp_expr ~debug:true) (Conv.expr_of_cexpr tbl e2)
  | Compiler_util.Cerr_arr_exp_v _ ->
    Format.fprintf fmt "err arr exp: lval"
  | Compiler_util.Cerr_stk_alloc s ->
    Format.fprintf fmt "stack_alloc error %a"
      pp_string0 s
  | Compiler_util.Cerr_linear s ->
    Format.fprintf fmt "linearisation error %a"
      pp_string0 s
  | Compiler_util.Cerr_assembler c ->
    begin match c with
    | Compiler_util.AsmErr_string s ->
      Format.fprintf fmt "assembler error %a"
        pp_string0 s
    | Compiler_util.AsmErr_cond e ->
      Format.fprintf fmt "assembler error: invalid condition %a"
        (Printer.pp_expr ~debug:true) (Conv.expr_of_cexpr tbl e)
    end

and pp_comp_ferr tbl fmt = function
  | Compiler_util.Ferr_in_body(f1,f2,(ii, err_msg)) ->
    let f1 = Conv.fun_of_cfun tbl f1 in
    let f2 = Conv.fun_of_cfun tbl f2 in
    let (i_loc, _) = Conv.get_iinfo tbl ii in
    Format.fprintf fmt "in functions %s and %s at position %a: %a"
      f1.fn_name f2.fn_name Printer.pp_iloc i_loc
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
  | Compiler_util.Ferr_uniqglob ->
    Format.fprintf fmt "two global declarations with the same name"
  | Compiler_util.Ferr_topo ->
    Format.fprintf fmt "program is not a topological sorting of the call-graph"
  | Compiler_util.Ferr_lowering ->
    Format.fprintf fmt "lowering check fails"
  | Ferr_glob_neq ->
    Format.fprintf fmt "error global not equal"
  | Ferr_fun (f, err_msg) ->
    let f =  Conv.fun_of_cfun tbl f in
    Format.fprintf fmt "in function %s: %a"
      f.fn_name (pp_comp_err tbl) err_msg
  | Ferr_remove_glob (ii, x) ->
    let i_loc, _ = Conv.get_iinfo tbl ii in
    Format.fprintf fmt "Cannot remove global variable %a at %a"
     (pp_var_i tbl) x
     Printer.pp_iloc i_loc
  | Ferr_remove_glob_dup (_, _) ->
    Format.fprintf fmt "duplicate global: please report"


(* -------------------------------------------------------------------- *)
let check_safety_p s p source_p =
  let s1,s2 = Glob_options.print_strings s in
  Format.eprintf "@[<v>At compilation pass: %s@;%s@;@;\
                  %a@;@]@."
    s1 s2
    (Printer.pp_prog ~debug:true) p;

  let () = match !safety_config with
    | Some conf -> SafetyConfig.load_config conf
    | None -> () in
  
  let () =
    List.iter (fun f_decl ->
        if f_decl.f_cc = Export then
          let () = Format.eprintf "@[<v>Analyzing function %s@;@]@."
              f_decl.f_name.fn_name in

          let source_f_decl = List.find (fun source_f_decl ->
              f_decl.f_name.fn_name = source_f_decl.f_name.fn_name
            ) (snd source_p) in
          let module AbsInt = Safety.AbsAnalyzer(struct
              let main_source = source_f_decl
              let main = f_decl
              let prog = p
            end) in

          AbsInt.analyze ())
      (snd p) in
  exit 0 

(* -------------------------------------------------------------------- *)
let check_overlap_p s p source_p =
  let s1,s2 = Glob_options.print_strings s in
  Format.eprintf "@[<v>At compilation pass: %s@;%s@;@;\
                  %a@;@]@."
    s1 s2
    (Printer.pp_prog ~debug:true) p;

  List.map (fun f_decl ->
      if f_decl.f_cc = Export then
        let () = Format.eprintf "@[<v>Analyzing function %s@;@]@."
            f_decl.f_name.fn_name in

        let source_f_decl = List.find (fun source_f_decl ->
            f_decl.f_name.fn_name = source_f_decl.f_name.fn_name
          ) (snd source_p) in
        let module AbsInt = Safety.AbsAnalyzer(struct
            let main_source = source_f_decl
            let main = f_decl
            let prog = p
          end) in

        Some (AbsInt.annotate_export ())
      else None)
    (snd p)

(* -------------------------------------------------------------------- *)
let main () =
  try

    parse();

    let fname = !infile in
    let ast   = Parseio.parse_program ~name:fname in
    let ast   = BatFile.with_file_in fname ast in

    if !latexfile <> "" then begin
      let out = open_out !latexfile in
      let fmt = Format.formatter_of_out_channel out in
      Format.fprintf fmt "%a@." Latex_printer.pp_prog ast;
      close_out out;
      if !debug then Format.eprintf "Pretty printed to LATEX@."
    end;

    let env, pprog  = Typing.tt_program Typing.Env.empty ast in
    eprint Compiler.Typing Printer.pp_pprog pprog;
    if !typeonly then exit 0;

    let prog = Subst.remove_params pprog in
    eprint Compiler.ParamsExpansion (Printer.pp_prog ~debug:true) prog;

    (* The source program, before any compilation pass. *)
    let source_prog = prog in
    
    if SafetyConfig.sc_comp_pass () = Compiler.ParamsExpansion &&
       !check_safety
    then check_safety_p Compiler.ParamsExpansion prog source_prog
    else
            
    if !ec_list <> [] then begin
      let fmt, close =
        if !ecfile = "" then Format.std_formatter, fun () -> ()
        else
          let out = open_out !ecfile in
          let fmt = Format.formatter_of_out_channel out in
          fmt, fun () -> close_out out in
      begin try
        BatPervasives.finally
          (fun () -> close ())
          (fun () -> ToEC.extract fmt !model prog !ec_list)
          ()
      with e ->
        BatPervasives.ignore_exceptions
          (fun () -> if !ecfile <> "" then Unix.unlink !ecfile) ();
        raise e end;
      exit 0
    end;

    let prog = Inline_array_copy.doit prog in

    (* Generate the coq program if needed *)
    if !coqfile <> "" then begin
      assert false
(*      let out = open_out !coqfile in
      let fmt = Format.formatter_of_out_channel out in
      Format.fprintf fmt "%a@." Coq_printer.pp_prog prog;
      close_out out;
      if !debug then Format.eprintf "coq program extracted@." *)
    end;
    if !coqonly then exit 0;

    (* Now call the coq compiler *)
    let tbl, cprog = Conv.cprog_of_prog Regalloc.X64.all_registers () prog in
    if !debug then Printf.eprintf "translated to coq \n%!";

    let to_exec = Typing.Env.Exec.get env in
    if to_exec <> [] then begin
        let exec (f, m) =
          try
            let pp_range fmt (ptr, sz) =
              Format.fprintf fmt "%a:%a" B.pp_print ptr B.pp_print sz in
            Format.printf "Evaluation of %s (@[<h>%a@]):@." f.fn_name
              (pp_list ",@ " pp_range) m;
            let _m, vs =
              (** TODO: allow to configure the initial stack pointer *)
              let live = List.map (fun (ptr, sz) -> Conv.int64_of_bi ptr, Conv.z_of_bi sz) m in
              (match Low_memory.Memory.coq_M.init live (Conv.int64_of_bi (Bigint.of_string "1024")) with Utils0.Ok m -> m | Utils0.Error err -> raise (Evaluator.Eval_error (Coq_xH, err))) |>
              Evaluator.exec cprog (Conv.cfun_of_fun tbl f) in
            Format.printf "@[<v>%a@]@."
              (pp_list "@ " Evaluator.pp_val) vs
          with Evaluator.Eval_error (ii,err) ->
            Format.eprintf "%a" Evaluator.pp_error (tbl, ii, err)
        in
        List.iter exec to_exec
      end;


    let lowering_vars = Lowering.(
        let f ty n = Conv.fresh_cvar tbl n ty in
        let b = f tbool in
        { fresh_OF = (b "OF").vname
        ; fresh_CF = (b "CF").vname
        ; fresh_SF = (b "SF").vname
        ; fresh_PF = (b "PF").vname
        ; fresh_ZF = (b "ZF").vname
        ; fresh_multiplicand = (fun sz -> (f (Bty (U sz)) "multiplicand").vname)
        }) in

    let fdef_of_cfdef fn cfd = Conv.fdef_of_cfdef tbl (fn,cfd) in
    let cfdef_of_fdef fd = snd (Conv.cfdef_of_fdef tbl fd) in
    let apply msg trans fn cfd =
      if !debug then Format.eprintf "START %s@." msg;
      let fd = fdef_of_cfdef fn cfd in
      if !debug then Format.eprintf "back to ocaml@.";
      let fd = trans fd in
      cfdef_of_fdef fd in

    let stk_alloc_fd cfd =
      let fd = Conv.fdef_of_cfdef tbl cfd in
      if !debug then Format.eprintf "START stack alloc@." ;
      let stk_i =
        Var0.Var.vname (Conv.cvar_of_var tbl Array_expand.vstack) in
      let alloc, sz, to_save, p_stack = Array_expand.stk_alloc_func fd in
      let alloc =
        let trans (v,i) = Conv.cvar_of_var tbl v, Conv.z_of_int i in
        List.map trans alloc in
      let sz = Conv.z_of_int sz in
      let p_stack = 
        match p_stack with
        | None -> Stack_alloc.SavedStackNone
        | Some (`InReg x) -> Stack_alloc.SavedStackReg (Conv.cvar_of_var tbl x)
        | Some (`InStack p) -> Stack_alloc.SavedStackStk (Conv.z_of_int p) in
      
      let to_save = List.map (Conv.cvar_of_var tbl) (Sv.elements to_save) in
      ((sz, stk_i), alloc), (to_save, p_stack) 
    in

    let is_var_in_memory cv : bool =
      let v = Conv.vari_of_cvari tbl cv |> L.unloc in
      v.v_kind = Stack in

    let pp_linear fmt lp =
      PrintLinear.pp_prog tbl fmt lp in

    let rename_fd ii fn cfd =
      let ii,_ = Conv.get_iinfo tbl ii in
      let doit fd =
        let fd = Subst.clone_func fd in
        Subst.extend_iinfo ii fd in
      apply "rename_fd" doit fn cfd in

    let warning ii msg =
      let loc,_ = Conv.get_iinfo tbl ii in
      Format.eprintf "WARNING: at %a, %a@." Printer.pp_iloc loc Printer.pp_warning_msg msg;
      ii in

    let inline_var x =
      let x = Conv.var_of_cvar tbl x in
      x.v_kind = Inline in

    let translate_var = Conv.var_of_cvar tbl in

    let is_glob x =
      let x = Conv.var_of_cvar tbl x in
      x.v_kind = Global in

    let fresh_id gd x =
      let x = (Conv.var_of_cvar tbl x).v_name in
      let ns = List.map (fun (g,_) -> snd (Conv.global_of_cglobal g)) gd in
      let s = Ss.of_list ns in
      let x =
        if Ss.mem x s then
          let rec aux i =
            let x = x ^ "_" ^ string_of_int i in
            if Ss.mem x s then aux (i+1)
            else x in
          aux 0
        else x in
      Conv.string0_of_string x in

    (* Check safety and calls exit(_). *)
    let check_safety_cp s cp =
      let p = Conv.prog_of_cprog tbl cp in
      check_safety_p s p source_prog in
    
    let pp_cprog s cp =
      if s = SafetyConfig.sc_comp_pass () && !check_safety then
        check_safety_cp s cp
      else
        if !pipeline_instrumentation && s = Compiler.DeadCode_RegAllocation then begin
          Format.eprintf "WARNING: Pipeline analyzer @.";
          let p = Conv.prog_of_cprog tbl cp in
          let overlap = check_overlap_p s p source_prog in
          match List.hd overlap with
            | Some annotated_p ->
              (* Instrument the program with the overlap information *)
              let ip = Pipeline_instrumentation.instrument_prog p annotated_p !pipeline_naive in
              (* Computes invariants on costMin and costMax *)
              check_safety_p s ip source_prog
            | None -> Format.eprintf "No information for the alias analysis @."
        end else
          eprint s (fun fmt cp ->
              let p = Conv.prog_of_cprog tbl cp in
              Printer.pp_prog ~debug:true fmt p) cp
    in

    let cparams = {
      Compiler.rename_fd    = rename_fd;
      Compiler.expand_fd    = apply "arr exp" Array_expand.arrexp_func;
      Compiler.var_alloc_fd = apply "var alloc" Varalloc.merge_var_inline_fd;
      Compiler.share_stk_fd = apply "share stk" Varalloc.alloc_stack_fd;
      Compiler.reg_alloc_fd = apply "reg alloc" (Regalloc.regalloc translate_var);
      Compiler.stk_alloc_fd = stk_alloc_fd;
      Compiler.lowering_vars = lowering_vars;
      Compiler.is_var_in_memory = is_var_in_memory;
      Compiler.print_prog   = (fun s p -> pp_cprog s p; p);
      Compiler.print_linear = (fun p -> eprint Compiler.Linearisation pp_linear p; p);
      Compiler.warning      = warning;
      Compiler.inline_var   = inline_var;
      Compiler.lowering_opt = Lowering.{ use_lea = !Glob_options.lea;
                                         use_set0 = !Glob_options.set0; };
      Compiler.is_glob     = is_glob;
      Compiler.fresh_id    = fresh_id;
    } in

    let entries =
      let ep = List.filter (fun fd -> fd.f_cc = Export) (snd prog) in
      List.map (fun fd -> Conv.cfun_of_fun tbl fd.f_name) ep in

    begin match
      Compiler.compile_prog_to_x86 cparams entries cprog with
    | Utils0.Error e ->
      Utils.hierror "compilation error %a@.PLEASE REPORT"
         (pp_comp_ferr tbl) e
    | Utils0.Ok asm ->
      if !outfile <> "" then begin
        BatFile.with_file_out !outfile (fun out ->
          let fmt = BatFormat.formatter_of_out_channel out in
          Format.fprintf fmt "%a%!" (Ppasm.pp_prog tbl) asm);
          if !debug then Format.eprintf "assembly listing written@."
      end else if List.mem Compiler.Assembly !print_list then
          Format.printf "%a%!" (Ppasm.pp_prog tbl) asm
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

  | Pipeline_instrumentation.NotSupportedError (loc, msg) ->
      Format.eprintf "%s: unsupported feature error: %s\n%!"
        (Location.tostring loc)
        msg;
      exit 1

  | Pipeline_instrumentation.LogicalError msg ->
      Format.eprintf "The pipeline printer has made a logical error: %s\n%!"
        msg;
      exit 1

  | Pipeline.InstructionUnsupported msg ->
      Format.eprintf "The pipeline simulator configuration file is incomplete: %s\n%!"
        msg;
      exit 1

(* -------------------------------------------------------------------- *)
let () = main ()
