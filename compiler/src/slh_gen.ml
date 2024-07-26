open Prog

let add_slh_instr (i: ('len,'info,'asm) ginstr ) = i

let add_slh_func (func : ('info, 'asm) func) =
  {func with f_body = List.map add_slh_instr func.f_body}

let add_slh (prog : ('info, 'asm) prog) =
  let globals, funcs = prog in
  let funcs  = List.map add_slh_func funcs in
  (globals,funcs)
