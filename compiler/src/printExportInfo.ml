open Utils
open Prog
open PrintCommon
open Printer
open Arch_decl
module W = Wsize
module T = Type
module E = Expr
module F = Format

(** Pretty printer for displaying export inforamation after compilation *)

type export_info = { funcs : export_info_fn list }

and export_info_fn = {
  name : funname;
  args : export_info_arg list;
  rets : export_info_ret list; (* TODO: add contracts*)
}

and export_info_arg = { arg_var : var; arg_alignment : W.wsize }
and export_info_ret = { ret_var : var }

let collect_export_info_args fn_prog fn_asm =
  List.map2
    (fun arg_prog arg_align ->
      { arg_var = arg_prog; arg_alignment = arg_align })
    fn_prog.f_args (snd fn_asm).asm_fd_align_args

let collect_export_info_rets fn_prog =
  List.map
    (fun ret ->
      let unlock_ret = L.unloc ret in
      { ret_var = unlock_ret })
    fn_prog.f_ret

let collect_export_info_fn (fn_prog, fn_asm) =
  {
    name = fn_prog.f_name;
    args = collect_export_info_args fn_prog fn_asm;
    rets = collect_export_info_rets fn_prog;
  }

let collect_export_info prog asm_prog =
  let funcs_prog = snd prog in

  (* merge together the prog and the associated assembly of exported functions *)
  let funcs =
    List.filter_map
      (fun ((fname, asm_func) as asm) ->
        match
          List.find_opt (fun func_prog -> func_prog.f_name = fname) funcs_prog
        with
        | Some p when asm_func.asm_fd_export -> Some (p, asm)
        | _ -> None)
      asm_prog.asm_funcs
  in
  let funcs = List.map collect_export_info_fn funcs in
  { funcs }

(***********************************************************************)

let pp_size fmt i = F.fprintf fmt "%i" i

let pp_type_with_ptr fmt var =
  if is_ptr var.v_kind then
    F.fprintf fmt "ptr %a" (pp_gtype ?w:None pp_size) var.v_ty
  else F.fprintf fmt "%a" (pp_gtype ?w:None pp_size) var.v_ty

(***********************************************************************)

let pp_export_info_readable fmt export_info =
  let pp_fn_types fmt (args, rets) =
    let pp_type_arg fmt arg =
      F.fprintf fmt "@[%a : %a %a@]" (pp_var ~debug:false) arg.arg_var pp_kind
        arg.arg_var.v_kind (pp_gtype pp_size) arg.arg_var.v_ty
    in
    let pp_ret_typ fmt rets =
      let rets =
        List.filter_map
          (fun ret ->
            if List.exists (fun arg -> arg.arg_var.v_id = ret.ret_var.v_id) args
            then None
            else Some ret.ret_var)
          rets
      in

      if rets <> [] then
        F.fprintf fmt "%a" (pp_list ",@ " pp_type_with_ptr) rets
      else F.fprintf fmt "()"
    in
    F.fprintf fmt "@[<hov>@ %a@ -> %a@]"
      (pp_list "@ -> " pp_type_arg)
      args pp_ret_typ rets
  in

  let pp_aligned_args fmt args =
    let aligned_args =
      (* filter only important alignements (>8) *)
      List.filter (fun arg -> arg.arg_alignment <> U8) args
    in

    let pp_aligned_arg fmt arg =
      F.fprintf fmt "@[%a : %a@]" (pp_var ~debug:false) arg.arg_var pp_wsize
        arg.arg_alignment
    in

    F.fprintf fmt "@[<v>%a@]" (pp_list ", " pp_aligned_arg) aligned_args
  in

  let pp_export_info_fn fmt fn =
    F.fprintf fmt "@[<v>%s:@[<v>@ type : %a @ argument alignment : [%a]@]@ @]"
      fn.name.fn_name pp_fn_types (fn.args, fn.rets) pp_aligned_args fn.args
  in
  F.fprintf fmt "@[<v>%a@]@."
    (pp_list "@ " pp_export_info_fn)
    (List.rev export_info.funcs)

let pp_export_info_json fmt export_info =
  let pp_args fmt args =
    let pp_arg fmt arg =
      F.fprintf fmt
        "@[{@[\"name\": \"%a\", \"kind\" : \"%a\", \"type\" : \"%a\", \
         \"align\" : %a @]}@]"
        (pp_var ~debug:false) arg.arg_var pp_kind arg.arg_var.v_kind
        (pp_gtype pp_size) arg.arg_var.v_ty pp_wsize arg.arg_alignment
    in
    F.fprintf fmt "@[<v>%a@]" (pp_list ", " pp_arg) args
  in

  let pp_rets fmt rets =
    let pp_ret fmt ret =
      F.fprintf fmt
        "@[{\"name\": \"%a\", \"kind\" : \"%a\", \"type\": \"%a\"}@]"
        (pp_var ~debug:false) ret.ret_var pp_kind ret.ret_var.v_kind
        (pp_gtype pp_size) ret.ret_var.v_ty
    in

    F.fprintf fmt "@[%a@]" (pp_list ",@ " pp_ret) rets
  in

  let pp_func fmt func =
    F.fprintf fmt
      "@[<v>{@[<v>@ \"name\" : \"%s\",@ \"args\" : [%a],@ \"rets\" : [%a]@]@\n\
       }@]"
      func.name.fn_name pp_args func.args pp_rets func.rets
  in

  F.fprintf fmt "@[<v>{@ @[<v>\"functions\": [@[<v>@ %a@ @]]@]@ }@]@."
    (pp_list ",@\n" pp_func)
    (List.rev export_info.funcs)

let pp_export_info ?(json = true) fmt prog asm_prog =
  let export_info = collect_export_info prog asm_prog in
  if json then pp_export_info_json fmt export_info
  else pp_export_info_readable fmt export_info
