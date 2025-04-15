open PrintASM
open Arch_decl
open Utils
open Asm_utils
open PrintCommon
open CoreIdent

module type AsmTarget = sig 

    type reg
    type regx
    type xreg
    type rflag
    type cond
    type asm_op

    val headers : asm_element list
    val pp_data_segment_header : Obj.t list -> ((Var0.Var.var * Wsize.wsize) * BinNums.coq_Z) list -> asm_element list
    val pp_function_tail    : funname -> (reg, regx, xreg, rflag, cond, asm_op) asm_fundef -> asm_element list
    val pp_instr_r : funname -> (reg, regx, xreg, rflag, cond, asm_op) Arch_decl.asm_i_r -> asm_element list
    val pp_function_header  : funname -> (reg, regx, xreg, rflag, cond, asm_op) asm_fundef -> asm_element list

end


module AsmTargetBuilder = struct 


    module type S = sig 
        type reg
        type regx
        type xreg
        type rflag
        type cond
        type asm_op
    
        val asm_of_prog : (reg,regx,xreg,rflag,cond,asm_op) asm_prog -> asm_element list
    end
    module Make(Target : AsmTarget) : S 
    with type reg = Target.reg
    and type regx = Target.regx
    and type xreg = Target.xreg
    and type rflag = Target.rflag
    and type cond = Target.cond
    and type asm_op = Target.asm_op
    = struct 

        type reg = Target.reg
        type regx = Target.regx
        type xreg = Target.xreg
        type rflag = Target.rflag
        type cond = Target.cond
        type asm_op = Target.asm_op


        let asm_debug_info ({Location.base_loc = ii; _}, _) =
            List.map (fun x -> Dwarf x) (DebugInfo.source_positions ii)
        
        let pp_instr name instr =
            let Arch_decl.({ asmi_i = i; asmi_ii = ii}) = instr in
            asm_debug_info ii @ Target.pp_instr_r name i
        
            let pp_instrs name instrs =
            List.fold_left (fun acc instr ->
                acc @ (pp_instr name instr)
            ) [] instrs
        
        let pp_body name decl 
            =   
            pp_instrs name decl.asm_fd_body 

        let pp_function (name,decl) =
            let headers = Target.pp_function_header name decl in
            let body = pp_body name decl in
            let tail = Target.pp_function_tail name decl in 
            headers @ body @ tail

    
        let pp_functions funcs =
        List.fold_left (fun acc (func) ->
            acc @ (pp_function func)
        ) [] funcs
    
        
        let pp_function_decl (name, decl : CoreIdent.funname * (_,_,_,_,_,_) asm_fundef) =
        if decl.asm_fd_export then
            let fn = escape name.fn_name in
            (* Same as .globl, see : 
            - https://stackoverflow.com/questions/50568399/what-is-the-difference-between-global-and-globl
            - https://sourceware.org/binutils/docs/as/Global.html
            *)
        [
            Instr (".global", [mangle fn]);
            Instr (".global", [fn])
        ]
        else []
    
        let pp_functions_decl (funcs) =
        List.fold_left (fun acc (func) ->
            acc @ (pp_function_decl func)
        ) [] funcs
    
        
        let pp_data_segment_body globs names =
        let datas = Asm_utils.format_glob_data globs names in
        List.fold_left (fun acc data ->
            acc @ [(data)]
        ) [] datas
    
        let pp_data_segment globs names =
        if not (List.is_empty globs) then
            let headers = Target.pp_data_segment_header globs names in
            let data = pp_data_segment_body globs names in
            headers @ data
        else
            []
    
        let asm_of_prog (asm: (reg,regx,xreg,rflag,cond,asm_op) asm_prog) : asm_element list =
        let headers = Target.headers in
        let functions_head = pp_functions_decl asm.asm_funcs in
        let functions_body = pp_functions asm.asm_funcs in
        let data_segment = pp_data_segment asm.asm_globs asm.asm_glob_names in
        headers @ functions_head @ functions_body @ data_segment
    

    end

end