open PrintASM
open Arch_decl
open Utils
open Asm_utils
open PrintCommon
open CoreIdent

module type AsmTarget = sig 

    val headers : asm_element list
    val pp_data_segment_header : Obj.t list -> ((Var0.Var.var * Wsize.wsize) * BinNums.coq_Z) list -> asm_element list
    val pp_function_tail : (_,_,_,_,_,_) asm_fundef -> asm_element list
    val pp_instr_align      : funname -> asm_element list
    val pp_instr_label      : funname -> Label.label_kind -> BinNums.positive -> asm_element list
    val pp_instr_storelabel : funname -> 'reg -> BinNums.positive -> asm_element list
    val pp_instr_jmp        : funname -> Label.remote_label -> asm_element list
    val pp_instr_jmpi       : funname -> (BinNums.positive,_,_,_,_) asm_arg -> asm_element list
    val pp_instr_jcc        : funname -> BinNums.positive -> 'cond -> asm_element list
    val pp_instr_jal        : funname -> 'reg -> Label.remote_label -> asm_element list
    val pp_instr_call       : funname -> Label.remote_label -> asm_element list
    val pp_instr_pop_pc     : funname -> asm_element list
    val pp_instr_syscall    : funname -> BinNums.positive Syscall_t.syscall_t -> asm_element list
    val pp_instr_op         : funname -> 'asm_op -> ('reg, 'regx, 'xreg, 'rflag, 'cond) asm_args -> asm_element list
        

end


module AsmTargetBuilder = struct 


    module Make(Target : AsmTarget) = struct 

        let pp_instr_r name (instr_r : (_,_,_,_,_,_) Arch_decl.asm_i_r) = 
            match instr_r with 
            | ALIGN                     -> Target.pp_instr_align        name
            | LABEL (kind, label)       -> Target.pp_instr_label        name kind label
            | STORELABEL (dst, label)   -> Target.pp_instr_storelabel   name dst label
            | JMP label                 -> Target.pp_instr_jmp          name label
            | JMPI label                -> Target.pp_instr_jmpi         name label
            | Jcc (label, condt)        -> Target.pp_instr_jcc          name label condt
            | JAL (fname,label)         -> Target.pp_instr_jal          name fname label
            | CALL (label)              -> Target.pp_instr_call         name label
            | POPPC                     -> Target.pp_instr_pop_pc       name
            | SysCall (op)              -> Target.pp_instr_syscall      name op
            | AsmOp (op,args)           -> Target.pp_instr_op           name op args

        let asm_debug_info ({Location.base_loc = ii; _}, _) =
            List.map (fun x -> Dwarf x) (DebugInfo.source_positions ii)
        
        let pp_instr name instr =
            let Arch_decl.({ asmi_i = i; asmi_ii = ii}) = instr in
            asm_debug_info ii @ pp_instr_r name i
        
            let pp_instrs name instrs =
            List.fold_left (fun acc instr ->
                acc @ (pp_instr name instr)
            ) [] instrs
        

        let pp_function_header (name:CoreIdent.funname) (decl:('a,'b,'c,'d,'e,'f) asm_fundef)  =
            let name = name.fn_name in
            let export = decl.asm_fd_export in
            if export then
                let name = escape name in
                [
                Label (mangle (name));
                Label (name);
                ]
            else
                []

        let pp_body name decl 
            =   
            pp_instrs name decl.asm_fd_body 

        let pp_function (name,decl) =
            let headers = pp_function_header name decl in
            let body = pp_body name decl in
            let tail = Target.pp_function_tail decl in 
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
        
            let asm_of_prog (asm: (_,_,_,_,_,_) asm_prog) =
            let headers = Target.headers in
            let functions_head = pp_functions_decl asm.asm_funcs in
            let functions_body = pp_functions asm.asm_funcs in
            let data_segment = pp_data_segment asm.asm_globs asm.asm_glob_names in
            headers @ functions_head @ functions_body @ data_segment
        

    end

end