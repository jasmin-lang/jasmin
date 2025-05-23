open Jasmin.Prog
open Error.CompileError

let build_uf_error fname loc =
  {
    location = loc;
    error_strategy = Error.CompileError.Fail;
    code = "UF-E001";
    to_text =
      (fun fmt ->
        Format.fprintf fmt "Function %s is never called" fname.fn_name
      );
  }

(**
return the set of unexplored functions
*)
let check_prog (_,funcs) =
  let functions = Mf.of_list (List.map (fun f -> (f.f_name,f)) funcs) in
  let explored_functions = ref Sf.empty in

  let rec explore_function (fn: ('info,'asm) Jasmin.Prog.func) =
    let check_instr instr =
      match instr.i_desc with
      | Ccall (_, f, _) -> begin
        match Mf.find_opt f functions with
        | Some fn -> explore_function fn
        | None -> assert false
      end
      | _ -> ()
      in
    if not (Sf.mem fn.f_name !explored_functions) then
        iter_instr check_instr fn.f_body;
        explored_functions := Sf.add fn.f_name !explored_functions;
  in

  let check_func (fn: ('info,'asm) Jasmin.Prog.func) =
    match fn.f_cc with
    | Export _ ->
      explore_function fn
    | Subroutine _
    | Internal -> ()
  in
  List.iter check_func funcs;
  let unreached_functions = Sf.diff (Sf.of_list (List.map (fun f -> f.f_name) funcs)) !explored_functions in
  List.rev (
    Sf.fold (
    fun fn acc ->
      let fn = Mf.find fn functions in
      let loc = fn.f_loc in
      let err = build_uf_error fn.f_name loc in
      err :: acc
    )
    unreached_functions
    []
  )