open Utils
open Prog
open Glob_options

let preprocess pd msfsize asmOp p =
  let p =
    p |> Subst.remove_params |> Insert_copy_and_fix_length.doit pd
  in
  Typing.check_prog pd msfsize asmOp p;
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
let rec warn_extra_i pd msfsize asmOp i =
  match i.i_desc with
  | Cassgn (_, tag, _, _) | Copn (_, tag, _, _) -> (
      match tag with
      | AT_rename ->
          warning ExtraAssignment i.i_loc
            "@[<v>extra assignment introduced:@;<0 2>%a@]"
            (Printer.pp_instr ~debug:false pd msfsize asmOp)
            i
      | AT_inline ->
          hierror ~loc:(Lmore i.i_loc) ~kind:"compilation error" ~internal:true
            "@[<v>AT_inline flag remains in instruction:@;<0 2>@[%a@]@]"
            (Printer.pp_instr ~debug:false pd msfsize asmOp)
            i
      | _ -> ())
  | Cif (_, c1, c2) | Cwhile (_, c1, _, _, c2) ->
      List.iter (warn_extra_i pd msfsize asmOp) c1;
      List.iter (warn_extra_i pd msfsize asmOp) c2
  | Cfor _ ->
      hierror ~loc:(Lmore i.i_loc) ~kind:"compilation error" ~internal:true
        "for loop remains"
  | Ccall _ | Csyscall _ | Cassert _ -> ()

let warn_extra_fd pd msfsize asmOp (_, fd) = List.iter (warn_extra_i pd msfsize asmOp) fd.f_body

(* -------------------------------------------------------------------- *)

let do_spill_unspill asmop ?(debug = false) cp =
  let p = Conv.cuprog_of_prog cp in
  match Lower_spill.spill_uprog asmop Conv.fresh_var_ident p with
  | Utils0.Error msg -> Error (Conv.error_of_cerror (Printer.pp_err ~debug) msg)
  | Utils0.Ok p -> Ok (Conv.prog_of_cuprog p)

let catch_error cp =
  match cp with
  | Utils0.Ok cp -> cp
  | Utils0.Error e ->
    let e = Conv.error_of_cerror (Printer.pp_err ~debug:false) e in
    raise (HiError e)

let do_wint_int
   (type reg regx xreg rflag cond asm_op extra_op)
    (module Arch : Arch_full.Arch
      with type reg = reg
       and type regx = regx
       and type xreg = xreg
       and type rflag = rflag
       and type cond = cond
       and type asm_op = asm_op
       and type extra_op = extra_op) prog =
  let fdsi = snd prog in
  let get_info p =
    let p = Conv.prog_of_cuprog p in
    let fv = List.fold_left (fun fv fd -> Sv.union fv (vars_fc_contracts fd)) Sv.empty (snd p) in
    let m =
      Sv.fold (fun x m ->
          match x.v_ty with
          | Bty (U _) ->
            begin match Annotations.has_wint x.v_annot with
            | None -> m
            | Some sg ->
              let annot = Annotations.remove_wint x.v_annot in
              let xi = V.mk x.v_name x.v_kind tint x.v_dloc annot in
              Mv.add x (sg, Conv.cvar_of_var xi) m
            end
          | _ -> m)
      fv Mv.empty in
    let info x =
      let x = Conv.var_of_cvar x in
      Mv.find_opt x m in
    Conv.csv_of_sv fv ,info
  in
  let cp = Conv.cuprog_of_prog prog in
  let cp = Wint_int.wi2i_prog Arch.asmOp Arch.pointer_data Arch.msf_size get_info cp in
  let cp = catch_error cp in
  let (gd, fdso) = Conv.prog_of_cuprog cp in
  (* Restore type of array in the functions signature *)
  let restore_ty tyi tyo =
    match tyi, tyo with
    | Arr(ws1, l1), Arr(ws2, l2) -> assert (arr_size ws1 l1 = arr_size ws2 l2); tyi
    | Bty (U _), Bty Int -> tyo
    | _, _ -> assert (tyi = tyo); tyo
  in
  let restore_sig fdi fdo =
    { fdo with
      f_tyin = List.map2 restore_ty fdi.f_tyin fdo.f_tyin;
      f_tyout = List.map2 restore_ty fdi.f_tyout fdo.f_tyout;
    } in
  let fds = List.map2 restore_sig fdsi fdso in
  (gd, fds)


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
  let module RA = Regalloc.Regalloc (Arch) in
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

  (* Kind of duplicate of pp_sub_region... *)
  let pp_sr sr =
    let open Compiler_util in
    pp_vbox [
      pp_nobox [
        PPEstring "{ region = ";
        PPEstring (Format.asprintf "%a" (Pp_stack_alloc.pp_region ~debug:!debug) sr.Stack_alloc.sr_region);
        PPEstring ";"];
      pp_nobox [
        PPEstring "  zone = ";
        PPEstring (Format.asprintf "%a" (Pp_stack_alloc.pp_symbolic_zone ~debug:!debug) sr.Stack_alloc.sr_zone);
        PPEstring " }"]];
  in

  let memory_analysis up : Compiler.stack_alloc_oracles =
    StackAlloc.memory_analysis
      pp_sr
      (Printer.pp_err ~debug:!debug)
      ~debug:!debug up
  in

  let global_regalloc fds =
    if !debug then Format.eprintf "START regalloc@.";
    let fds = List.map Conv.fdef_of_csfdef fds in

    CheckAnnot.check_stack_size fds;


    let return_addresses =
      let ra = Hf.create 17 in
      List.iter (fun (extra, fd) ->
          let conv = Conv.var_of_cvar in
          let oconv = Option.map conv in
          let r =
          match extra.Expr.sf_return_address with
          | RAstack (None, _, _, _)
          | RAnone -> Regalloc.StackDirect
          | RAreg (r, tmp) -> ByReg (conv r, oconv tmp)
          | RAstack (Some call, return, _, tmp) -> StackByReg (conv call, oconv return, oconv tmp)
          in Hf.add ra fd.f_name r
          ) fds;
      ra
    in

    let subst, _killed, fds = RA.alloc_prog return_addresses fds in
    let subst_sf_return_address : Expr.stk_fun_extra -> Expr.stk_fun_extra =
      let subst x = x |> Conv.var_of_cvar |> subst |> Conv.cvar_of_var in
      let osubst = Option.map subst in
      fun fe ->
      { fe with
        Expr.sf_return_address =
          match fe.Expr.sf_return_address with
          | RAnone -> RAnone;
          | RAreg (ret, tmp) -> RAreg (subst ret, osubst tmp)
          | RAstack (c, r, n, t) -> RAstack (osubst c, osubst r, n, osubst t)
      }
    in
    let fds = List.map (fun (e, fd) -> subst_sf_return_address e, fd) fds in
    let fds = List.map Conv.csfdef_of_fdef fds in
    fds
  in

  let pp_cuprog s cp =
    Conv.prog_of_cuprog cp |> visit_prog_after_pass ~debug:true s
  in

  let pp_csprog fmt cp =
    let p = Conv.prog_of_csprog cp in
    Printer.pp_sprog ~debug:true Arch.pointer_data Arch.msf_size Arch.asmOp fmt p
  in

  let pp_linear fmt lp = PrintLinear.pp_prog Arch.pointer_data Arch.msf_size Arch.asmOp fmt lp in

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

    let do_outannot x a =
      try
        let (_, va) = Hv.find harrs (L.unloc x) in
        List.init (Array.length va) (fun _ -> [])
      with Not_found -> [a] in
    let ret_annot = List.flatten (List.map2 do_outannot fd.f_ret fd.f_ret_info.ret_annot) in
    let finfo = fd.f_loc, fd.f_annot, fd.f_cc, { fd.f_ret_info with ret_annot } in
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

  let split_live_ranges_fd fd = Ssa.split_live_ranges true fd in
  let renaming_fd fd = RA.renaming fd in
  let remove_phi_nodes_fd fd = Ssa.remove_phi_nodes fd in

  let removereturn sp =
    let fds, _data = Conv.prog_of_csprog sp in
    let tokeep = RemoveUnusedResults.analyse fds in
    tokeep
  in

  let remove_wint_annot fd =
    let vars = Prog.vars_fc fd in
    let subst =
      Sv.fold (fun x s ->
          if Annotations.has_wint x.v_annot = None then s
          else
            let annot = Annotations.remove_wint x.v_annot in
            let x' = V.mk x.v_name x.v_kind x.v_ty x.v_dloc annot in
            Mv.add x x' s)
        vars Mv.empty in
    Subst.vsubst_func subst fd
  in

  let warn_extra s p =
    if s = Compiler.DeadCode_RegAllocation then
      let fds, _ = Conv.prog_of_csprog p in
      List.iter (warn_extra_fd Arch.pointer_data Arch.msf_size Arch.asmOp) fds
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
      if Hashtbl.mem hvars i.i_loc then begin
          (* If there is an entry already, the i_locs have duplicates:
             this should not happen, hence the warning, but we can safely continue by
             assuming that no variable dies here *)
          Utils.warning Always i.i_loc "Bug! Please report.";
          Hashtbl.replace hvars i.i_loc Var0.SvExtra.Sv.empty
      end else
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
      Compiler.insert_renaming =
        if !Glob_options.introduce_export_renaming then
          fun (_, _, cc, _) -> FInfo.is_export cc
        else Fun.const false;
      Compiler.remove_wint_annot =
        apply "remove wint annot" remove_wint_annot;
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
      Compiler.pp_sr;
    }
  in

  let export_functions =
    let conv fd = fd.f_name in
    List.fold_right
      (fun fd acc ->
        match fd.f_cc with
        | Export -> conv fd :: acc
        | Internal | Subroutine -> acc)
      (snd prog) []
  in

  Compiler.compile_prog_to_asm Arch.asm_e Arch.call_conv Arch.aparams cparams
    export_functions
    (Expr.to_uprog Arch.asmOp cprog)
