open Utils
open Prog
open PrintCommon
open Printer
open Arch_decl
open Pretyping
module W = Wsize
module T = Type
module E = Expr
module F = Format

(** Pretty printer for displaying export inforamation after compilation *)

type export_info = {
  funcs : export_info_fn list;
  params : (pexpr_ gvar * pexpr_ gexpr) list;
}

and export_info_fn = {
  name : funname;
  args : export_info_arg list;
  rets : export_info_ret list;
  annotations : Annotations.annotations;
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
    annotations = fn_prog.f_annot.f_user_annot;
  }

let collect_export_info env prog asm_prog =
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
  let params =
    List.filter_map
      (fun pmod -> match pmod with MIparam p -> Some p | _ -> None)
      (Env.decls env)
  in
  { funcs; params }

(***********************************************************************)

let pp_size fmt i = F.fprintf fmt "%i" i

let pp_type_with_ptr fmt var =
  if is_ptr var.v_kind then
    F.fprintf fmt "ptr %a" (pp_gtype ?w:None pp_size) var.v_ty
  else F.fprintf fmt "%a" (pp_gtype ?w:None pp_size) var.v_ty

(* same function as in src/printer.ml but slightly modified to be compatible
  with a json output
*)
let rec pp_simple_attribute_json fmt = function
  | Annotations.Aint z -> Z.pp_print fmt z
  | Aid s | Astring s -> F.fprintf fmt "%S" s
  | Aws ws -> F.fprintf fmt "%s" (string_of_ws ws)
  | Astruct a -> F.fprintf fmt "%a" pp_annotations_json a

and pp_attribute_json fmt = function
  | None -> ()
  | Some a ->
      Format.fprintf fmt "\"attribute\": @[%a@]" pp_simple_attribute_json
        (L.unloc a)

and pp_annotation_json fmt (k, v) =
  F.fprintf fmt "@[<v>{\"name\": %S,@ %a}@]" (L.unloc k) pp_attribute_json v

and pp_annotations_json fmt a =
  Format.fprintf fmt "@[%a@]" (pp_list ",@ " pp_annotation_json) a

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

(***********************************************************************)

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
      "@[<v>{@[<v>@ \"name\" : \"%s\",@ \"args\" : [%a],@ \"rets\" : [%a],@ \
       \"annotations\" : [%a]@]@\n\
       }@]"
      func.name.fn_name pp_args func.args pp_rets func.rets pp_annotations_json
      func.annotations
  in

  let pp_params fmt globals =
    let pp_param fmt (var, expr) =
      let pp_gvar fmt var = F.fprintf fmt "%S" var.v_name in
      F.fprintf fmt "@[<v>{@[<hov>\"name\" : %a,@ \"value\": \"%a\"@]}@]"
        pp_gvar var pp_pexpr expr
    in
    F.fprintf fmt "@[<v>%a@]" (pp_list ",@ " pp_param) globals
  in

  F.fprintf fmt
    "@[<v>{@ @[<v>\"functions\": [@[<v>@ %a@ @]],@ \"params\" : [@[%a]@]@]@ \
     }@]@."
    (pp_list ",@\n" pp_func)
    (List.rev export_info.funcs)
    pp_params
    (List.rev export_info.params)

let pp_export_info ?(json = true) fmt env prog asm_prog =
  let export_info = collect_export_info env prog asm_prog in
  if json then pp_export_info_json fmt export_info
  else pp_export_info_readable fmt export_info
