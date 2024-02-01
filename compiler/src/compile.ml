open Utils
open Prog
open Glob_options

let preprocess reg_size asmOp p =
  let p =
    p |> Subst.remove_params |> Insert_copy_and_fix_length.doit reg_size
  in
  Typing.check_prog reg_size asmOp p;
  p

(* -------------------------------------------------------------------- *)

let parse_file arch_info fname =
  let env =
    List.fold_left Pretyping.Env.add_from Pretyping.Env.empty
      !Glob_options.idirs
  in
  Pretyping.tt_program arch_info env fname

(* -------------------------------------------------------------------- *)
let rec warn_extra_i pd asmOp i =
  match i.i_desc with
  | Cassgn (_, tag, _, _) | Copn (_, tag, _, _) -> (
      match tag with
      | AT_rename ->
          warning ExtraAssignment i.i_loc
            "@[<v>extra assignment introduced:@;<0 2>%a@]"
            (Printer.pp_instr ~debug:false pd asmOp)
            i
      | AT_inline ->
          hierror ~loc:(Lmore i.i_loc) ~kind:"compilation error" ~internal:true
            "@[<v>AT_inline flag remains in instruction:@;<0 2>@[%a@]@]"
            (Printer.pp_instr ~debug:false pd asmOp)
            i
      | _ -> ())
  | Cif (_, c1, c2) | Cwhile (_, c1, _, c2) ->
      List.iter (warn_extra_i pd asmOp) c1;
      List.iter (warn_extra_i pd asmOp) c2
  | Cfor _ ->
      hierror ~loc:(Lmore i.i_loc) ~kind:"compilation error" ~internal:true
        "for loop remains"
  | Ccall _ | Csyscall _ | Cassert _ -> ()

let warn_extra_fd pd asmOp (_, fd) = List.iter (warn_extra_i pd asmOp) fd.f_body

(*--------------------------------------------------------------------- *)

module CompilerParams (Arch : Arch_full.Arch) =
struct

  module Regalloc = Regalloc.Regalloc (Arch) 
  module StackAlloc = StackAlloc.StackAlloc (Arch) 

  let fdef_of_cufdef fn cfd = Conv.fdef_of_cufdef (fn, cfd)
  let cufdef_of_fdef fd = snd (Conv.cufdef_of_fdef fd)

  let apply msg trans fn cfd =
    if !debug then Format.eprintf "START %s@." msg;
    let fd = fdef_of_cufdef fn cfd in
    if !debug then Format.eprintf "back to ocaml@.";
    let fd = trans fd in
    cufdef_of_fdef fd


  let translate_var = Conv.var_of_cvar

  let memory_analysis up : Compiler.stack_alloc_oracles =
    StackAlloc.memory_analysis
      (Printer.pp_err ~debug:!debug)
      ~debug:!debug up
 
  let global_regalloc fds =
    if !debug then Format.eprintf "START regalloc@.";
    let fds = List.map Conv.fdef_of_csfdef fds in

    CheckAnnot.check_stack_size fds;

    let fds =
      Regalloc.alloc_prog translate_var
        (fun _fd extra ->
          match extra.Expr.sf_save_stack with
          | Expr.SavedStackReg _ | Expr.SavedStackStk _ -> true
          | Expr.SavedStackNone -> false)
        fds
    in
    let fds = List.map (fun (y, _, x) -> (y, x)) fds in
    let fds = List.map Conv.csfdef_of_fdef fds in
    fds

  let pp_cuprog visit_prog_after_pass s cp =
    Conv.prog_of_cuprog cp |> visit_prog_after_pass ~debug:true s

  let pp_csprog fmt cp =
    let p = Conv.prog_of_csprog cp in
    Printer.pp_sprog ~debug:true Arch.pointer_data Arch.asmOp fmt p

  let pp_linear fmt lp = PrintLinear.pp_prog Arch.pointer_data Arch.asmOp fmt lp

  let rename_fd ii fn cfd =
    let ii, _ = ii in
    let doit fd =
      let fd = Subst.clone_func fd in
      Subst.extend_iinfo ii fd
    in
    apply "rename_fd" doit fn cfd

  let expand_fd ~onlyreg fn cfd =
    let fd = Conv.fdef_of_cufdef (fn, cfd) in
    let vars, harrs = Array_expand.init_tbl ~onlyreg fd in
    let cvar = Conv.cvar_of_var in
    let vars = List.map cvar (Sv.elements vars) in
    let arrs = ref [] in
    let doarr x (ws, xs) =
      arrs :=
        Array_expansion.
          {
            vi_v = cvar x;
            vi_s = ws;
            vi_n =
              List.map (fun x -> (cvar x).Var0.Var.vname) (Array.to_list xs);
          }
        :: !arrs
    in
    Hv.iter doarr harrs;

    let f_cc =
      match fd.f_cc with
      | Subroutine si ->
          (* Since some arguments/returns are expended we need to fix the info *)
          let tbl = Hashtbl.create 17 in
          let newpos = ref 0 in
          let mk_n x =
            match x.v_kind, x.v_ty with
            | Reg (_, Direct), Arr (_, n) -> n
            | _, _ -> 1
          in
          let doarg i x =
            Hashtbl.add tbl i !newpos;
            newpos := !newpos + mk_n x
          in
          List.iteri doarg fd.f_args;
          let doret o x =
            match o with
            | Some i -> [Some (Hashtbl.find tbl i)]
            | None -> List.init (mk_n (L.unloc x)) (fun _ -> None)
          in
          let returned_params =
            List.flatten (List.map2 doret si.returned_params fd.f_ret) in
          FInfo.Subroutine { returned_params }

      | _ -> fd.f_cc
    in
    let do_outannot x a =
      try
        let (_, va) = Hv.find harrs (L.unloc x) in
        List.init (Array.length va) (fun _ -> [])
      with Not_found -> [a] in
    let f_outannot = List.flatten (List.map2 do_outannot fd.f_ret fd.f_outannot) in
    let finfo = fd.f_loc, fd.f_annot, f_cc, f_outannot in
    { Array_expansion.vars; arrs = !arrs; finfo }

  let refresh_instr_info fn f =
    (fn, f) |> Conv.fdef_of_cufdef |> refresh_i_loc_f |> Conv.cufdef_of_fdef |> snd

  let warning ii msg =
    (if not !Glob_options.lea then
     let loc, _ = ii in
     warning UseLea loc "%a" Printer.pp_warning_msg msg);
    ii

  let fresh_id _gd x =
    let x = Conv.var_of_cvar x in
    Prog.V.clone x

  let split_live_ranges_fd fd = Regalloc.split_live_ranges fd 

  let renaming_fd fd = Regalloc.renaming fd 

  let remove_phi_nodes_fd fd = Regalloc.remove_phi_nodes fd

  let removereturn sp =
    let fds, _data = Conv.prog_of_csprog sp in
    let tokeep = RemoveUnusedResults.analyse fds in
    tokeep

  let warn_extra s p =
    if s = Compiler.DeadCode_RegAllocation then
      let fds, _ = Conv.prog_of_csprog p in
      List.iter (warn_extra_fd Arch.pointer_data Arch.asmOp) fds

  let slh_info up =
    let p = Conv.prog_of_cuprog up in
    let ttbl = Sct_checker_forward.compile_infer_msf p in
    fun fn ->
      try Hf.find ttbl fn with Not_found -> assert false
 
  let cparams ~onlyreg visit_prog_after_pass = 
    {
      Compiler.rename_fd;
      Compiler.expand_fd = expand_fd ~onlyreg;
      Compiler.split_live_ranges_fd =
        apply "split live ranges" split_live_ranges_fd;
      Compiler.renaming_fd = apply "alloc inline assgn" renaming_fd;
      Compiler.remove_phi_nodes_fd =
        apply "remove phi nodes" remove_phi_nodes_fd;
      Compiler.stack_register_symbol =
        Var0.Var.vname (Conv.cvar_of_var Arch.rsp_var);
      Compiler.global_static_data_symbol =
        Var0.Var.vname (Conv.cvar_of_var Arch.rip);
      Compiler.stackalloc = memory_analysis;
      Compiler.removereturn;
      Compiler.regalloc = global_regalloc;
      Compiler.print_uprog =
        (fun s p ->
          pp_cuprog visit_prog_after_pass s p;
          p);
      Compiler.print_sprog =
        (fun s p ->
          warn_extra s p;
          eprint s pp_csprog p;
          p);
      Compiler.print_linear =
        (fun s p ->
          eprint s pp_linear p;
          p);
      Compiler.refresh_instr_info;
      Compiler.warning;
      Compiler.lowering_opt = Arch.lowering_opt;
      Compiler.fresh_id;
      Compiler.fresh_var_ident = Conv.fresh_var_ident;
      Compiler.slh_info;
    }

end

(*--------------------------------------------------------------------- *)

let compile (type reg regx xreg rflag cond asm_op extra_op)
    (module Arch : Arch_full.Arch
      with type reg = reg
       and type regx = regx
       and type xreg = xreg
       and type rflag = rflag
       and type cond = cond
       and type asm_op = asm_op
       and type extra_op = extra_op) visit_prog_after_pass prog cprog =

  let module CP = CompilerParams(Arch) in
  let open CP in
 
  let export_functions =
    let conv fd = fd.f_name in
    List.fold_right
      (fun fd acc ->
        match fd.f_cc with
        | Export -> conv fd :: acc
        | Internal | Subroutine _ -> acc)
      (snd prog) []
  in

  Compiler.compile_prog_to_asm Arch.asm_e Arch.call_conv Arch.aparams 
    (cparams ~onlyreg:true visit_prog_after_pass)
    export_functions
    (Expr.to_uprog Build_Tabstract Arch.asmOp cprog)
(*--------------------------------------------------------------------- *)


let compile_CL (type reg regx xreg rflag cond asm_op extra_op)
 (module Arch : Arch_full.Arch
  with type reg = reg
   and type regx = regx
   and type xreg = xreg
   and type rflag = rflag
   and type cond = cond
   and type asm_op = asm_op
   and type extra_op = extra_op) cprog toextract =
  let module CP = CompilerParams(Arch) in
  let open CP in

  let visit_prog_after_pass ~debug s p = 
    eprint s (Printer.pp_prog ~debug Arch.reg_size Arch.asmOp) p in

  let cparams = CP.cparams ~onlyreg:false visit_prog_after_pass in

  (* Add array copy after inlining every where *)
  let is_array_init e = 
    match e with
    | Parr_init _ -> true
    | _ -> false in

  let rec add_array_copy_i i = 
    { i with i_desc = add_array_copy_id i.i_desc }

  and add_array_copy_id i = 
  match i with
  | Cif(e,c1,c2) -> Cif(e, add_array_copy_c c1, add_array_copy_c c2)
  | Cfor(x,r,c)  -> Cfor(x,r, add_array_copy_c c)
  | Cwhile(a,c1,e,c2) -> Cwhile(a, add_array_copy_c c1, e, add_array_copy_c c2)
  | Cassgn(Lvar x, t, _ty, e) when is_arr x.pl_desc && not (is_array_init e) ->
      let (ws,n) = array_kind x.pl_desc.v_ty in
      Copn([Lvar x],t, Opseudo_op (Ocopy(ws, Conv.pos_of_int n)), [e])
  | Cassgn(Lasub (_, ws, n,_, _) as x, t, _ty, e) when not (is_array_init e) ->
      Copn([x],t, Opseudo_op (Ocopy(ws, Conv.pos_of_int n)), [e])
  | Cassert _ | Ccall _ | Copn _ | Csyscall _ | Cassgn _ -> i

  and add_array_copy_c c = 
    List.map add_array_copy_i c in

  let add_array_copy_f f = 
   { f with f_body = add_array_copy_c f.f_body } in
  let add_array_copy (g,fds) = (g, List.map add_array_copy_f fds) in  
  
  let doit f p = 
    match f p with
    | Utils0.Error e ->
      let e = Conv.error_of_cerror (Printer.pp_err ~debug:!debug) e in
      raise (HiError e)
    | Utils0.Ok p -> p in

  let cprog =   
    doit 
      (Compiler.compiler_CL_first_part Arch.asm_e Arch.aparams cparams
         [toextract])
      (Expr.to_uprog Build_Tabstract Arch.asmOp cprog) in
     
  let cprog = 
    let p = Conv.prog_of_cuprog (Obj.magic cprog) in
(*    Format.eprintf "Before add copy@.%a@." (Printer.pp_prog ~debug:true Arch.reg_size Arch.asmOp) p; *)
    let p = add_array_copy p in
(*    Format.eprintf "After add copy@.%a@." (Printer.pp_prog ~debug:true Arch.reg_size Arch.asmOp) p; *)
    let cp = Conv.cuprog_of_prog p in
    cp in      
  doit (Compiler.compiler_CL_second_part Arch.asm_e Arch.aparams cparams [toextract])
      (Expr.to_uprog Build_Tabstract Arch.asmOp cprog)
