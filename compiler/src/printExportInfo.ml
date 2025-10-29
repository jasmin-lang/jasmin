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
  arch_target : architecture;
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
  let arch_target = !Glob_options.target_arch in
  { arch_target; funcs; params }

(***********************************************************************)

let pp_size = PrintCommon.pp_len ~debug:false
(* FIXME: maybe print only consts and assert false or fail for other cases *)

let escape_string_json s =
  String.replace_chars (function
      | '"' -> "\\\""
      | '\\' -> "\\\\"
      | '/' -> "\\/"
      | '\b' -> "\\b"
      | '\012' -> "\\f"
      | '\n' -> "\\n"
      | '\r' -> "\\r"
      | '\t' -> "\\t"
      | c -> String.of_char c)
    s

(* same function as in src/printer.ml but slightly modified to be compatible
  with a json output
*)
let rec pp_simple_attribute_json fmt = function
  | Annotations.Aint z -> Z.pp_print fmt z
  | Aid s -> F.fprintf fmt "%s" s
  | Astring s -> F.fprintf fmt "\"%s\"" (escape_string_json s)
  | Aws ws -> F.fprintf fmt "%s" (string_of_ws ws)
  | Astruct a -> F.fprintf fmt "%a" pp_annotations_json a

and pp_attribute_json fmt = function
  | None -> ()
  | Some a ->
      Format.fprintf fmt "\"attribute\": @[%a@]" pp_simple_attribute_json
        (L.unloc a)

and pp_annotation_json fmt (k, v) =
  F.fprintf fmt "@[<v>{\"name\": %S, %a}@]" (L.unloc k) pp_attribute_json v

and pp_annotations_json fmt a =
  Format.fprintf fmt "@[<v>%a@]" (pp_list ",@ " pp_annotation_json) a

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
    F.fprintf fmt "@[<v>%a@]" (pp_list ",@ " pp_arg) args
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
      F.fprintf fmt "@[<v>{@[<hov>\"name\" : %a,@ \"expr\" : @[<h>\"%a\"@]@]}@]"
        pp_gvar var (pp_pexpr ~debug:false) expr
    in
    F.fprintf fmt "@[<v>%a@]" (pp_list ",@ " pp_param) globals
  in

  (* force expression to be inlined, because multi line strings doesn't exists in json *)
  F.set_margin max_int;

  F.fprintf fmt
    "@[<v>{@ \"arch_target\": %S,@ @[<v>\"functions\": [@[<v>@ %a@ @]],@ \
     \"params\" : [@[%a]@]@]@ }@]@."
    (architecture_to_string export_info.arch_target)
    (pp_list ",@\n" pp_func)
    (List.rev export_info.funcs)
    pp_params
    (List.rev export_info.params)

let pp_export_info_json fmt env prog asm_prog =
  let export_info = collect_export_info env prog asm_prog in
  pp_export_info_json fmt export_info
