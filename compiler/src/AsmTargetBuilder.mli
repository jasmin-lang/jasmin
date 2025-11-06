open PrintASM

(**
Module AsmTarget :
    This module defines the interface for generating assembly code for a target architecture.
    You need to provide archtecture types as defined in Arch_decl module.
    You also need to provide the header, function header, function tail and instruction generation function.
*)
module type AsmTarget = sig

    (* type definitions for target architecture*)
    type reg
    type regx
    type xreg
    type rflag
    type cond
    type asm_op

    (* Header of the file*)
    val headers             : PrintASM.asm_element list

    (* Data segment header*)
    val data_segment_header : PrintASM.asm_element list

    val function_directives : asm_element list
    (** Meta-data to print before the function definition *)

    (* Start of the function*)
    val function_header     : PrintASM.asm_element list

    (* Function return instructions
    It is called only on exported functions.
    *)
    val function_tail       : PrintASM.asm_element list

    (* Pretty print of instruction*)
    val pp_instr_r : CoreIdent.Name.t -> (reg, regx, xreg, rflag, cond, asm_op) Arch_decl.asm_i_r -> PrintASM.asm_element list

end


module type S = sig
    (* type definitions for target architecture*)
    type reg
    type regx
    type xreg
    type rflag
    type cond
    type asm_op

    (*
        Entrypoint of assembly printer : generate a list of instructions defined in PrintASM module.
        args :
            - asm_prog : assembly program
        returns :
            - asm_line list : assembly program

    *)
    val asm_of_prog : (reg, regx, xreg, rflag, cond, asm_op) Arch_decl.asm_prog -> PrintASM.asm_element list
end

(**
    Module AsmTargetBuilder.Make:
        Functor abstration that take an architecture module and generate corresponding assembly printer.
*)
module Make :
  functor (Target : AsmTarget) -> S with
      type reg = Target.reg
      and type regx = Target.regx
      and type xreg = Target.xreg
      and type rflag = Target.rflag
      and type cond = Target.cond
      and type asm_op = Target.asm_op
