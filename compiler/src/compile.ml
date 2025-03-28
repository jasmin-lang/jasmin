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

let parse_jasmin_path s =
  s |> String.split_on_char ':' |> List.map (String.split ~by:"=")

let get_jasminpath () =
  match Sys.getenv "JASMINPATH" with
  | exception Not_found -> []
  | path ->
  try parse_jasmin_path path with
  | Not_found ->
  warning Always Location.i_dummy "ill-formed value for the JASMINPATH environment variable";
  []

let parse_file arch_info ?(idirs=[]) fname =
  let idirs = idirs @ get_jasminpath () in
  let env = List.fold_left Pretyping.Env.add_from Pretyping.Env.empty idirs in
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
  | Cif (_, c1, c2) | Cwhile (_, c1, _, _, c2) ->
      List.iter (warn_extra_i pd asmOp) c1;
      List.iter (warn_extra_i pd asmOp) c2
  | Cfor _ ->
      hierror ~loc:(Lmore i.i_loc) ~kind:"compilation error" ~internal:true
        "for loop remains"
  | Ccall _ | Csyscall _ -> ()

let warn_extra_fd pd asmOp (_, fd) = List.iter (warn_extra_i pd asmOp) fd.f_body

(* -------------------------------------------------------------------- *)

let do_spill_unspill asmop ?(debug = false) cp =
  let p = Conv.cuprog_of_prog cp in
  match
    Lower_spill.spill_uprog asmop
      (fun k ii -> Conv.fresh_var_ident k ii (Uint63.of_int 0))
      p
  with
  | Utils0.Error msg -> Error (Conv.error_of_cerror (Printer.pp_err ~debug) msg)
  | Utils0.Ok p -> Ok (Conv.prog_of_cuprog p)

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
  let module Regalloc = Regalloc.Regalloc (Arch) in
  let module StackAlloc = StackAlloc.StackAlloc (Arch) in
  let fdef_of_cufdef fn cfd = Conv.fdef_of_cufdef (fn, cfd) in
  let cufdef_of_fdef fd = snd (Conv.cufdef_of_fdef fd) in

  let apply msg trans fn cfd =
    if !debug then Format.eprintf "START %s@." msg;
    let fd = fdef_of_cufdef fn cfd in
    if !debug then Format.eprintf "back to ocaml@.";
    let fd = trans fd in
    cufdef_of_fdef fd
  in

  let translate_var = Conv.var_of_cvar in

  (* Kind of duplicate of pp_sub_region... *)
  let pp_sr sr =
    let open Compiler_util in
    pp_vbox [
      pp_nobox [
        PPEstring "{ region = ";
        PPEstring (Format.asprintf "%a" Pp_stack_alloc.pp_region sr.Stack_alloc.sr_region);
        PPEstring ";"];
      pp_nobox [
        PPEstring "  zone = ";
        PPEstring (Format.asprintf "%a" Pp_stack_alloc.pp_symbolic_zone sr.Stack_alloc.sr_zone);
        PPEstring " }"]];
  in

  let print_trmap ii table rmap =
    let open Pp_stack_alloc in
    let pp_ii fmt ii =
      let (loc, _) = ii in
      Format.fprintf fmt "==========@,%a@,==========" Location.pp_iloc loc
    in
    Format.eprintf "@[<v>%a@,%a@,%a@]@." pp_ii ii pp_table table pp_rmap rmap
  in

  let print_trmap ii table rmap =
    if !Glob_options.print_stack_alloc_checker then print_trmap ii table rmap;
    (table, rmap)
  in

  let memory_analysis up : Compiler.stack_alloc_oracles =
    StackAlloc.memory_analysis
      print_trmap
      pp_sr
      (Printer.pp_err ~debug:!debug)
      ~debug:!debug up
  in

  let global_regalloc fds =
    if !debug then Format.eprintf "START regalloc@.";
    let fds = List.map Conv.fdef_of_csfdef fds in

    CheckAnnot.check_stack_size fds;


    let get_internal_size _fd sfe =
      let stk_size =
        BinInt.Z.add sfe.Expr.sf_stk_sz sfe.Expr.sf_stk_extra_sz in
      Conv.z_of_cz (Memory_model.round_ws sfe.sf_align stk_size)
    in

    let fds =
      Regalloc.alloc_prog translate_var
        (fun _fd extra ->
          match extra.Expr.sf_save_stack with
          | Expr.SavedStackReg _ | Expr.SavedStackStk _ -> true
          | Expr.SavedStackNone -> false)
        get_internal_size
        fds
    in
    let fds = List.map (fun (y, _, x) -> (y, x)) fds in
    let fds = List.map Conv.csfdef_of_fdef fds in
    fds
  in

  let pp_cuprog s cp =
    Conv.prog_of_cuprog cp |> visit_prog_after_pass ~debug:true s
  in

  let pp_csprog fmt cp =
    let p = Conv.prog_of_csprog cp in
    Printer.pp_sprog ~debug:true Arch.pointer_data Arch.asmOp fmt p
  in

  let pp_linear fmt lp = PrintLinear.pp_prog Arch.pointer_data Arch.asmOp fmt lp in

  let rename_fd ii fn cfd =
    let ii, _ = ii in
    let doit fd =
      let fd = Subst.clone_func fd in
      Subst.extend_iinfo ii fd
    in
    apply "rename_fd" doit fn cfd
  in

  let expand_fd fn cfd =
    let fd = Conv.fdef_of_cufdef (fn, cfd) in
    let vars, harrs = Array_expand.init_tbl fd in
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
  in

  let refresh_instr_info fn f =
    (fn, f) |> Conv.fdef_of_cufdef |> refresh_i_loc_f |> Conv.cufdef_of_fdef |> snd
  in

  let warning ii msg =
    (if not !Glob_options.lea then
     let loc, _ = ii in
     warning UseLea loc "%a" Printer.pp_warning_msg msg);
    ii
  in

  let fresh_id _gd x =
    let x = Conv.var_of_cvar x in
    Prog.V.clone x
  in

  let split_live_ranges_fd fd = Regalloc.split_live_ranges fd in
  let renaming_fd fd = Regalloc.renaming fd in
  let remove_phi_nodes_fd fd = Regalloc.remove_phi_nodes fd in

  let removereturn sp =
    let fds, _data = Conv.prog_of_csprog sp in
    let tokeep = RemoveUnusedResults.analyse fds in
    tokeep
  in

  let warn_extra s p =
    if s = Compiler.DeadCode_RegAllocation then
      let fds, _ = Conv.prog_of_csprog p in
      List.iter (warn_extra_fd Arch.pointer_data Arch.asmOp) fds
  in

  let slh_info up =
    let p = Conv.prog_of_cuprog up in
    let ttbl = Sct_checker_forward.compile_infer_msf p in
    fun fn ->
      try Hf.find ttbl fn with Not_found -> assert false
  in

  let tbl_annot =
    let tbl = Hf.create 17 in
    let add (fn, cfd) =
      let fd = fdef_of_cufdef fn cfd in
      Hf.add tbl fn fd.f_annot
    in
    List.iter add cprog.Expr.p_funcs;
    tbl
  in

  let get_annot fn =
    try Hf.find tbl_annot fn
    with Not_found ->
           hierror
             ~loc:Lnone
             ~funname:fn.fn_name
             ~kind:"compiler error"
             ~internal:true
             "invalid annotation table."
  in

  let szs_of_fn fn =
    (get_annot fn).stack_zero_strategy
  in

  (* This implements an analysis returning the set of variables becoming dead
     after each instruction. It is based on the liveness analysis available
     in Liveness. *)
  let dead_vars_fd (f : _ func) =
    let hvars = Hashtbl.create 97 in
    let live = Liveness.live_fd false f in
    let rec analyze (i : _ ginstr) =
      begin match i.i_desc with
      | Cif (_, c1, c2) -> List.iter analyze c1; List.iter analyze c2
      | Cfor (_, _, c) -> List.iter analyze c
      | Cwhile (_, c, _, _, c') -> List.iter analyze c; List.iter analyze c'
      | _ -> ()
      end;
      let (in_set, out_set) = i.i_info in
      let s = Conv.csv_of_sv (Sv.diff in_set out_set) in
      Hashtbl.add hvars i.i_loc s
    in
    List.iter analyze live.f_body;

    fun ii ->
      let loc, _ = ii in
      try Hashtbl.find hvars loc with
      | Not_found ->
          hierror ~loc:(Lmore loc) ~kind:"compilation error" ~internal:true
            "dead_vars_fd: location not found"
  in

  (* We expose a version of dead_vars_fd for _ufun_decl. *)
  let dead_vars_ufd (f : _ Expr._ufun_decl) =
    let f = Conv.fdef_of_cufdef f in
    dead_vars_fd f
  in

  (* We expose a version of dead_vars_fd for _sfun_decl. *)
  let dead_vars_sfd (f : _ Expr._sfun_decl) =
    let _, f = Conv.fdef_of_csfdef f in
    dead_vars_fd f
  in

  let cparams =
    {
      Compiler.rename_fd;
      Compiler.expand_fd;
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
          pp_cuprog s p;
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
      Compiler.stack_zero_info = szs_of_fn;
      Compiler.dead_vars_ufd;
      Compiler.dead_vars_sfd;
      Compiler.print_trmap;
      Compiler.pp_sr;
    }
  in

  let export_functions =
    let conv fd = fd.f_name in
    List.fold_right
      (fun fd acc ->
        match fd.f_cc with
        | Export _ -> conv fd :: acc
        | Internal | Subroutine _ -> acc)
      (snd prog) []
  in

  Compiler.compile_prog_to_asm Arch.asm_e Arch.call_conv Arch.aparams cparams
    export_functions
    (Expr.to_uprog Arch.asmOp cprog)
