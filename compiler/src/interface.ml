open Wsize

type interface_type = 
| U of Wsize.wsize 

type interface_alignment = 
  | Align of Wsize.wsize 
  | Unaligned (*unaligned is u8*)

(* type interface_call_conv = () *)

type cc = 
| Register (* u32 or u64 depending on the architecture*)
| Vector (*u256 *)
| Extra

type interface_argument = {
  var : Prog.var;
  alignment : interface_alignment;
  arg_type : interface_type;
  (* cc : cc *)
}

type function_interface = {
  export : bool;
  name : string;
  args : interface_argument list;
  tyout : interface_type list;
}

type program_interface = function_interface list


(* assert false on bool and array*)
let make_type_interface (ty : Prog.ty) = 
  match ty with
  | Arr (ws, len) -> assert false
  | Bty ty -> 
    match ty with 
    | Bool -> assert false
    | Int -> assert false
    | U ws -> U ws

let make_func_interface 
  (stk_alloc_finder : (CoreIdent.funname -> Stack_alloc.stk_alloc_oracle_t)) 
  (f : ('info,'asm)Prog.func) 
 = 
  let open Stack_alloc in
  let open CoreIdent in
  let stack_alloc_info = stk_alloc_finder f.f_name in
  let name = f.f_name.fn_name in
  let export = (
    match f.f_cc with
    | Export arg_ret_info -> true
    | Subroutine arg_ret_info -> false
    | Internal  -> false 
  ) in
  let args = List.map2 (
    fun var p_info -> 
      let arg_type = make_type_interface var.v_ty in 
      match p_info with
      | None -> 
        {
          var = var; 
          alignment = Unaligned; 
          arg_type = arg_type;
        }
      | Some stack_info -> 
        {
          var = var; 
          alignment = Align stack_info.pp_align; 
          arg_type = arg_type;
        }
  ) f.f_args stack_alloc_info.sao_params in
  let tyout = List.map make_type_interface f.f_tyout in
  {
    export = export; 
    name = name; 
    args = args; 
    tyout = tyout;
  }

let make_prog_interface (stk_alloc_finder : CoreIdent.funname -> Stack_alloc.stk_alloc_oracle_t) ((_,funcs) : ('info,'asm) Prog.prog) = 
  List.map (make_func_interface stk_alloc_finder) funcs

let string_of_cc = 
  function
  | Register -> "register"
  | Vector -> "vector"
  | Extra -> "extra"

let string_of_interface_align align = 
  match align with 
  | Align ws -> Format.asprintf "align on %s" (Wsize.string_of_wsize ws)
  | Unaligned -> "unaligned"

let pp_interface_type fmt ty = 
  match ty with 
  | U ws -> Format.fprintf fmt "u%s" (string_of_wsize ws)

let pp_interface_arg fmt arg = 
  Format.fprintf fmt "%a : [%s] (%a)"
  (Printer.pp_var ~debug:true) arg.var
  (string_of_interface_align arg.alignment)
  pp_interface_type arg.arg_type


let pp_interface_func fmt (func:function_interface) = 
  Format.fprintf fmt "@[fn '%s' @.  @[args : %a@]@.  @[return : @]@]%a" 
  func.name
  ((Format.pp_print_list ~pp_sep:(fun f _ -> Format.fprintf f ", ")) pp_interface_arg ) func.args
  ((Format.pp_print_list ~pp_sep:(fun f _ -> Format.fprintf f ", ")) pp_interface_type ) func.tyout

let pp_interface_prog fmt (prog:program_interface) =  
  Format.fprintf fmt "@[%a @]@." 
  ((Format.pp_print_list ~pp_sep:(fun f _ -> Format.fprintf f "@ ")) pp_interface_func) prog

