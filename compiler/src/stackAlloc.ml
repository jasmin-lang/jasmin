open Utils
open Prog
open Regalloc

let memory_analysis pp_comp_ferr ~debug tbl up = 
  if debug then Format.eprintf "START memory analysis@.";
  let p = Conv.prog_of_cuprog tbl up in
  let gao, sao = Varalloc.alloc_stack_prog p in
  
  (* build coq info *)
  let crip = Var0.Var.vname (Conv.cvar_of_var tbl Prog.rip) in
  let do_slots slots = 
    List.map (fun (x,ws,ofs) -> ((Conv.cvar_of_var tbl x, ws), Conv.z_of_int ofs)) slots in                            
  let cglobs = do_slots gao.gao_slots in
  
  let mk_csao fn = 
    let sao = Hf.find sao fn in
    let align = sao.sao_align in
    let size = sao.sao_size in
    let conv_pi (pi:Varalloc.param_info) = 
      Stack_alloc.({
        pp_ptr = Conv.cvar_of_var tbl pi.pi_ptr;
        pp_writable = pi.pi_writable;
        pp_align    = pi.pi_align;
      }) in
    let conv_sub (i:Interval.t) = 
      Stack_alloc.{ smp_ofs = Conv.z_of_int i.min; 
                    smp_len = Conv.z_of_int (Interval.size i) } in
    let conv_ptr_kind x = function
      | Varalloc.Stack(s, i) -> Stack_alloc.PIstack (Conv.cvar_of_var tbl s, conv_sub i)
      | Glob (s, i)          -> Stack_alloc.PIglob (Conv.cvar_of_var tbl s, conv_sub i)
      | RegPtr s             -> Stack_alloc.PIregptr(Conv.cvar_of_var tbl s)
      | StackPtr s           -> 
        let xp = V.clone x in
        Stack_alloc.PIstkptr(Conv.cvar_of_var tbl s, 
                             conv_sub Interval.{min = 0; max = size_of_ws U64}, Conv.cvar_of_var tbl xp) in
  
    let conv_alloc (x,k) = Conv.cvar_of_var tbl x, conv_ptr_kind x k in
  
    let sao = Stack_alloc.{
        sao_align  = align;
        sao_size   = Conv.z_of_int size;
        sao_extra_size = Z0;
        sao_params = List.map (omap conv_pi) sao.sao_params;
        sao_return = List.map (omap Conv.nat_of_int) sao.sao_return;
        sao_slots  = do_slots sao.sao_slots;
        sao_alloc  = List.map conv_alloc (Hv.to_list sao.sao_alloc); 
        sao_to_save = [];
        sao_rsp     = SavedStackNone; 
        sao_return_address = RAnone;
        } in 
    sao in
  
  let atbl = Hf.create 117 in 
  let get_sao fn = 
    try Hf.find atbl fn 
    with Not_found -> 
      let csao = mk_csao fn in
      Hf.add atbl fn csao;
      csao in
  
  let cget_sao fn = get_sao (Conv.fun_of_cfun tbl fn) in
  
  let sp' = 
    match Stack_alloc.alloc_prog crip gao.gao_data cglobs cget_sao up with
    | Utils0.Ok sp -> sp 
    | Utils0.Error e ->
      Utils.hierror "compilation error %a@." (pp_comp_ferr tbl) e in
  let fds, _ = Conv.prog_of_csprog tbl sp' in
  
  if debug then
    Format.eprintf "After memory analysis@.%a@."
      (Printer.pp_prog ~debug:true) ([], (List.map snd fds));
  
  (* remove unused result *)
  let tokeep = RemoveUnusedResults.analyse fds in
  let tokeep fn = tokeep (Conv.fun_of_cfun tbl fn) in
  let deadcode (extra, fd) =
    let (fn, cfd) = Conv.cufdef_of_fdef tbl fd in
    let fd = 
      match Dead_code.dead_code_fd tokeep fn cfd with
      | Utils0.Ok cfd -> Conv.fdef_of_cufdef tbl (fn, cfd) 
      | Utils0.Error _ -> assert false in 
    (extra,fd) in
  let fds = List.map deadcode fds in
  if debug then
    Format.eprintf "After remove unused return @.%a@."
      (Printer.pp_prog ~debug:true) ([], (List.map snd fds));
  
  (* register allocation *)
  let translate_var = Conv.var_of_cvar tbl in
  let has_stack f = f.f_cc = Export && (Hf.find sao f.f_name).sao_modify_rsp in
  let fds, _rev_alloc, _extra_free_registers, _live_calls = 
    Regalloc.alloc_prog translate_var (fun fd _ -> has_stack fd) fds in
  
  let fix_csao (_, ro, fd) =
    let fn = fd.f_name in
    let sao = Hf.find sao fn in
    let csao = get_sao fn in 
    let to_save = if fd.f_cc = Export then ro.ro_to_save else [] in
    let has_stack = has_stack fd || to_save <> [] in
    let rastack = odfl OnReg fd.f_annot.retaddr_kind = OnStack in
    let rsp = V.clone rsp in
    let ra = V.mk "RA" (Stack Direct) u64 L._dummy in
    let extra =
      let extra = to_save in
      let extra = if rastack then ra :: extra else extra in
      if has_stack && ro.ro_rsp = None then rsp :: extra
      else extra in
    let size, align, extrapos = Varalloc.extend_sao sao extra in
    let align = 
      Sf.fold (fun fn align ->
        let fn_algin = (get_sao fn).Stack_alloc.sao_align in
        if wsize_lt align fn_algin then fn_algin else align) sao.sao_calls align in
    let saved_stack = 
      if has_stack then
        match ro.ro_rsp with
        | Some x -> Expr.SavedStackReg (Conv.cvar_of_var tbl x)
        | None   -> Expr.SavedStackStk (Conv.z_of_int (List.assoc rsp extrapos))
      else Expr.SavedStackNone in
  
    let conv_to_save x =
      Conv.cvar_of_var tbl x,
      (try List.assoc x extrapos with Not_found -> -1) |> Conv.z_of_int
    in
  
    let csao = 
      Stack_alloc.{ csao with
        sao_align = align;
        sao_extra_size = Conv.z_of_int size;
        sao_to_save = List.map conv_to_save ro.ro_to_save;
        sao_rsp  = saved_stack;
        sao_return_address =
          if rastack
          then RAstack (Conv.z_of_int (List.assoc ra extrapos))
          else match ro.ro_return_address with
               | None -> RAnone
               | Some ra -> RAreg (Conv.cvar_of_var tbl ra)
      } in
    Hf.replace atbl fn csao in
  List.iter fix_csao (List.rev fds);
  
  Compiler.({
    ao_globals      = gao.gao_data;
    ao_global_alloc = cglobs;
    ao_stack_alloc  = 
      fun fn -> 
      try Hf.find atbl (Conv.fun_of_cfun tbl fn)
      with Not_found -> assert false
  }) 
         
