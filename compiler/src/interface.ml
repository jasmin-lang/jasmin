open Wsize

type interface_type = 
| U of Wsize.wsize 

type interface_alignment = 
  | Align of Wsize.wsize 
  | Unaligned (*unaligned is u8*)

(* type interface_call_conv = () *)

type interface_argument = {
  name : string;
  alignment : interface_alignment;
  arg_type : interface_type;
  (* cc : interface_call_conv need to find where this info is stored*)
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
      let name = var.v_name in 
      let arg_type = make_type_interface var.v_ty in 
      match p_info with
      | None -> 
        {
          name = name; 
          alignment = Unaligned; 
          arg_type = arg_type;
        }
      | Some stack_info -> 
        {
          name = name; 
          alignment = Align stack_info.pp_align; 
          arg_type = arg_type;
        }
  ) f.f_args stack_alloc_info.sao_params in
  {
    export = export; 
    name = name; 
    args = args; 
    tyout = []
  }

let make_prog_interface (stk_alloc_finder : CoreIdent.funname -> Stack_alloc.stk_alloc_oracle_t) ((_,funcs) : ('info,'asm) Prog.prog) = 
  List.map (make_func_interface stk_alloc_finder) funcs