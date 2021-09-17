open Utils
open Prog
open Regalloc

let pp_var = Printer.pp_var ~debug:true

let pp_var_ty fmt x =
 Format.fprintf fmt "%a %a" Printer.pp_ty x.v_ty pp_var x

let pp_param_info tbl fmt pi =
  let open Stack_alloc in
  match pi with
  | None -> Format.fprintf fmt "_"
  | Some pi ->
    Format.fprintf fmt "%s %a aligned on %s"
      (if pi.pp_writable then "mut" else "const")
      pp_var_ty (Conv.var_of_cvar tbl pi.pp_ptr)
      (string_of_ws pi.pp_align)

let pp_slot tbl fmt ((x, ws), ofs) =
  Format.fprintf fmt "%a: %a aligned on %s"
    Bigint.pp_print (Conv.bi_of_z ofs)
    pp_var_ty (Conv.var_of_cvar tbl x)
    (string_of_ws ws)

let pp_zone fmt z =
  let open Stack_alloc in
  Format.fprintf fmt "[%a:%a]"
    Bigint.pp_print (Conv.bi_of_z z.z_ofs)
    Bigint.pp_print (Conv.bi_of_z z.z_len)

let pp_ptr_kind_init tbl fmt pki =
  let open Stack_alloc in
  match pki with
  | PIdirect (v, z, sc) ->
    Format.fprintf fmt "%s %a %a"
      (if sc = Sglob then "global" else "stack")
      pp_var (Conv.var_of_cvar tbl v)
      pp_zone z
  | PIregptr v ->
    Format.fprintf fmt "reg ptr %a"
      pp_var (Conv.var_of_cvar tbl v)
  | PIstkptr (v, z, x) ->
    Format.fprintf fmt "stack ptr %a %a (pseudo-reg %a)"
      pp_var_ty (Conv.var_of_cvar tbl v)
      pp_zone z
      pp_var_ty (Conv.var_of_cvar tbl x)

let pp_alloc tbl fmt (x, pki) =
    Format.fprintf fmt "%a -> %a" pp_var (Conv.var_of_cvar tbl x) (pp_ptr_kind_init tbl) pki

let pp_return fmt n =
  match n with
  | None -> Format.fprintf fmt "_"
  | Some n -> Format.fprintf fmt "%d" (Conv.int_of_nat n)

let pp_sao tbl fmt sao =
  let open Stack_alloc in
    Format.fprintf fmt "alignment = %s; size = %a; extra size = %a; max size = %a@;params =@;<2 2>@[<v>%a@]@;return = @[<hov>%a@]@;slots =@;<2 2>@[<v>%a@]@;alloc= @;<2 2>@[<v>%a@]@;saved register = @[<hov>%a@]@;saved stack = %a@;return address = %a@]"
   (string_of_ws sao.sao_align)
    Bigint.pp_print (Conv.bi_of_z sao.sao_size)
    Bigint.pp_print (Conv.bi_of_z sao.sao_extra_size)
    Bigint.pp_print (Conv.bi_of_z sao.sao_max_size)
    (pp_list "@;" (pp_param_info tbl)) sao.sao_params
    (pp_list "@;" pp_return) sao.sao_return
    (pp_list "@;" (pp_slot tbl)) sao.sao_slots
    (pp_list "@;" (pp_alloc tbl)) sao.sao_alloc
    (pp_list "@;" (Printer.pp_to_save ~debug:true tbl)) sao.sao_to_save
    (Printer.pp_saved_stack ~debug:true tbl) sao.sao_rsp
    (Printer.pp_return_address ~debug:true tbl) sao.sao_return_address

let pp_oracle tbl up fmt saos =
  let open Compiler in
  let { ao_globals; ao_global_alloc; ao_stack_alloc } = saos in
  let pp_global fmt global =
    Format.fprintf fmt "%a" Bigint.pp_print (Conv.bi_of_word U8 global)
  in
  let pp_stack_alloc fmt f =
    let sao = ao_stack_alloc (Conv.cfun_of_fun tbl f.f_name) in
    Format.fprintf fmt "@[<v 2>%s@;%a@]" f.f_name.fn_name (pp_sao tbl) sao
  in
  let _, fs = Conv.prog_of_cuprog tbl up in
  Format.fprintf fmt "@[<v>Global data:@;<2 2>@[<hov>%a@]@;Global slots:@;<2 2>@[<v>%a@]@;Stack alloc:@;<2 2>@[<v>%a@]@]"
    (pp_list "@;" pp_global) ao_globals
    (pp_list "@;" (pp_slot tbl)) ao_global_alloc
    (pp_list "@;" pp_stack_alloc) fs

let memory_analysis pp_err ~debug tbl up =
  if debug then Format.eprintf "START memory analysis@.";
  let p = Conv.prog_of_cuprog tbl up in
  let gao, sao = Varalloc.alloc_stack_prog p in
  
  (* build coq info *)
  let crip = Var0.Var.vname (Conv.cvar_of_var tbl Prog.rip) in
  let crsp = Var0.Var.vname (Conv.cvar_of_var tbl Prog.rsp) in
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
      Stack_alloc.{ z_ofs = Conv.z_of_int i.min; 
                    z_len = Conv.z_of_int (Interval.size i) } in
    let conv_ptr_kind x = function
      | Varalloc.Direct (s, i, sc) -> Stack_alloc.PIdirect (Conv.cvar_of_var tbl s, conv_sub i, sc)
      | RegPtr s                   -> Stack_alloc.PIregptr(Conv.cvar_of_var tbl s)
      | StackPtr s                 ->
        let xp = V.clone x in
        Stack_alloc.PIstkptr(Conv.cvar_of_var tbl s, 
                             conv_sub Interval.{min = 0; max = size_of_ws U64}, Conv.cvar_of_var tbl xp) in
  
    let conv_alloc (x,k) = Conv.cvar_of_var tbl x, conv_ptr_kind x k in
  
    let sao = Stack_alloc.{
        sao_align  = align;
        sao_size   = Conv.z_of_int size;
        sao_extra_size = Z0;
        sao_max_size = Z0;
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

  if !Glob_options.print_stack_alloc then begin
    let saos =
      Compiler.({
        ao_globals      = gao.gao_data;
        ao_global_alloc = cglobs;
        ao_stack_alloc  = cget_sao
      })
    in
    Format.eprintf
"(* -------------------------------------------------------------------- *)@.";
    Format.eprintf "(* Intermediate results of the stack allocation oracle *)@.@.";
    Format.eprintf "%a@.@.@." (pp_oracle tbl up) saos
  end;

  let sp' = 
    match Stack_alloc.alloc_prog false crip crsp gao.gao_data cglobs cget_sao up with
    | Utils0.Ok sp -> sp 
    | Utils0.Error e ->
      let e = Conv.error_of_cerror (pp_err tbl) tbl e in
      raise (HiError e)
  in
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
  let fds, _extra_free_registers =
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
    let extra_size, align, extrapos = Varalloc.extend_sao sao extra in
    let align, max_stk = 
      Sf.fold (fun fn (align, max_stk) ->
          let sao = get_sao fn in
          let fn_algin = sao.Stack_alloc.sao_align in
          let align = if wsize_lt align fn_algin then fn_algin else align in
          let fn_max = Conv.bi_of_z (sao.Stack_alloc.sao_max_size) in
          let max_stk = if Bigint.lt max_stk fn_max then fn_max else max_stk in
          align, max_stk
        ) sao.sao_calls (align, Bigint.zero) in
    let max_size = 
      let stk_size = 
        Bigint.add (Conv.bi_of_z csao.Stack_alloc.sao_size)
                   (Bigint.of_int extra_size) in
      let stk_size = 
        match fd.f_cc with
        | Export       -> Bigint.add stk_size (Bigint.of_int (size_of_ws align - 1))
        | Subroutine _ -> 
          Conv.bi_of_z (Memory_model.round_ws align (Conv.z_of_bi stk_size))
        | Internal -> assert false in
      Bigint.add max_stk stk_size in
    let saved_stack = 
      if has_stack then
        match ro.ro_rsp with
        | Some x -> Expr.SavedStackReg (Conv.cvar_of_var tbl x)
        | None   -> Expr.SavedStackStk (Conv.z_of_int (List.assoc rsp extrapos))
      else Expr.SavedStackNone in

    let conv_to_save x =
      Conv.cvar_of_var tbl x,
      try List.assoc x extrapos with Not_found -> -1
    in

    let compare_to_save (_, x) (_, y) = Stdlib.Int.compare y x in

    (* Stack slots for saving callee-saved registers are sorted in increasing order to simplify the check that they are all disjoint. *)
    let convert_to_save m =
      m |> List.rev_map conv_to_save |> List.sort compare_to_save |> List.rev_map (fun (x, n) -> x, Conv.z_of_int n)
    in

    let csao =
      Stack_alloc.{ csao with
        sao_align = align;
        sao_extra_size = Conv.z_of_int extra_size;
        sao_max_size = Conv.z_of_bi max_size;
        sao_to_save = convert_to_save ro.ro_to_save;
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
  
  let saos =
    Compiler.({
      ao_globals      = gao.gao_data;
      ao_global_alloc = cglobs;
      ao_stack_alloc  =
        fun fn ->
        try Hf.find atbl (Conv.fun_of_cfun tbl fn)
        with Not_found -> assert false
    })
  in

  if !Glob_options.print_stack_alloc then begin
    Format.eprintf
"(* -------------------------------------------------------------------- *)@.";
    Format.eprintf "(* Final results of the stack allocation oracle *)@.@.";
    Format.eprintf "%a@.@.@." (pp_oracle tbl up) saos
  end;

  saos
