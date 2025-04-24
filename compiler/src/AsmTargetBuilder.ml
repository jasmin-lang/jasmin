open PrintASM
open Arch_decl
open Utils
open Asm_utils
open PrintCommon
open CoreIdent

type ('reg, 'regx, 'xreg, 'rflag, 'cond, 'asm_op) asm_printer = {
  headers : asm_element list;
  data_segment_header : asm_element list;
  function_header : asm_element list;
  function_tail : asm_element list;
  pp_instr_r :
    Name.t ->
    ('reg, 'regx, 'xreg, 'rflag, 'cond, 'asm_op) Arch_decl.asm_i_r ->
    asm_element list;
}

let asm_of_prog printer =
  let asm_debug_info ({ Location.base_loc = ii; _ }, _) =
    List.map (fun x -> Dwarf x) (DebugInfo.source_positions ii)
  in

  let pp_instr name instr =
    let Arch_decl.{ asmi_i = i; asmi_ii = ii } = instr in
    asm_debug_info ii @ printer.pp_instr_r name i
  in

  let pp_instrs name instrs = List.concat_map (pp_instr name) instrs in

  let pp_body name decl = pp_instrs name decl.asm_fd_body in

  let pp_function_header name decl =
    if decl.asm_fd_export then
      [ Label (mangle name); Label name ] @ printer.function_header
    else []
  in

  let pp_function_tail decl =
    if decl.asm_fd_export then printer.function_tail else []
  in

  let pp_function (fname, decl) =
    let name = escape fname.fn_name in
    let headers = pp_function_header name decl in
    let body = pp_body name decl in
    let tail = pp_function_tail decl in
    headers @ body @ tail
  in

  let pp_functions funcs = List.concat_map pp_function funcs in

  let pp_function_decl
      ((name, decl) : CoreIdent.funname * (_, _, _, _, _, _) asm_fundef) =
    if decl.asm_fd_export then
      let fn = escape name.fn_name in
      [ Instr (".global", [ mangle fn ]); Instr (".global", [ fn ]) ]
    else []
  in

  let pp_functions_decl funcs = List.concat_map pp_function_decl funcs in

  let pp_data_segment_body globs names =
    Asm_utils.format_glob_data globs names
  in

  let pp_data_segment globs names =
    if not (List.is_empty globs) then
      let headers = printer.data_segment_header in
      let data = pp_data_segment_body globs names in
      headers @ data
    else []
  in

  fun asm : asm_element list ->
    let headers = printer.headers in
    let functions_head = pp_functions_decl asm.asm_funcs in
    let functions_body = pp_functions asm.asm_funcs in
    let data_segment = pp_data_segment asm.asm_globs asm.asm_glob_names in
    headers @ functions_head @ functions_body @ data_segment
