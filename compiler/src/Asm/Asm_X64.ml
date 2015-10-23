(* * Minimal X86-64 for crypto

See http://ref.x86asm.net/coder64-abc.html for a quick overview.

*)

open Util

module F = Format


(* ** We parameterize our semantics by the values.
 * ------------------------------------------------------------------------ *)

module type VAL = sig
  type qword
  type address
  val qword_to_string : qword -> string
  val address_to_string : address -> string
end

module V64 = struct
  type qword = int64
  type address = int64
  let qword_to_string = Int64.to_string
  let address_to_string = Int64.to_string
end

(* ** Instructions are a functor
 * ------------------------------------------------------------------------ *)

module Make_Instr(V : VAL) = struct

(* *** Registers and instructions
 * ------------------------------------------------------------------------ *)

  type reg =
    | RAX | RBX | RCX | RDX | RDI | RSI | RBP | RSP
    | R8  | R9  | R10 | R11 | R12 | R13 | R14 | R15

  type cond =
    | CfSet of bool

  type binop =
    | Add          (* addition:ignore carry flag *)
    | Adc          (* addition use    carry flag *)
    | And          (* bitwise and                *)
    | Sub          (* subtraction: ignore carry flag *)
    | Sbb          (* subtraction: use    carry flag *)
    | Mov          (* move *)
    | Cmov of cond (* conditional move *)
    | Shr          (* shift right *)
    | Shl          (* shift left *)
    | Xor          (* bitwise xor *) 

  type unop =
    | Mul          (* multiplication *)
    | Push
    | Pop

  type triop =
    | IMul         (* multiplication *)


  type offset = int64
    
  type src =
    | Sreg of reg          (* Sreg(r): use register *)
    | Simm of V.qword      (* Simm(i): $i *)
    | Smem of reg * offset (* Smem(r,i): i(%r) *)

  type dest =
    | Dreg of reg          (* Dreg(r): use register *)
    | Dmem of reg * offset (* Dmem(r,i): i(%r) *)

  type instr =
    | Unop of  unop * src
    | Binop of binop * src * dest
    | Triop of triop * src(*src1*) * src(*src2*) * dest(*dest*)
    | Label of string (* _test:, ... *)
    | Ret
    | Section of string  (* .text ... *)
    | Global of string  (* .globl test ... *)
    | Comment of string

type afun = {
  af_name : string;
  af_args : reg list;   (* arguments expected in these registers *)
  af_body : instr list;
  af_ret  : reg list;   (* return values available in these registers *)
}

(* *** Utility functions
 * ------------------------------------------------------------------------ *)

  let dest_to_src = function
    | Dreg(r)   -> Sreg(r)
    | Dmem(r,o) -> Smem(r,o)

  let reg_of_int = function
    | 0  -> RAX (* return 1 *)
    | 1  -> RDX (* return 2/ arg 3 *)
    | 2  -> RDI (* arg 1 *)
    | 3  -> RSI (* arg 2 *)
    | 4  -> RCX (* arg 4 *)
    | 5  -> R8  (* arg 5 *)
    | 6  -> R9  (* arg 6 *)
    | 7  -> RBP
    | 8  -> R10
    | 9  -> R11
    | 10 -> R12
    | 11 -> R13
    | 12 -> R14
    | 13 -> R15
    | 14 -> RBX
    | _  -> failwith "invalid register index for X86-64"

  let int_of_reg = function
    | RAX -> 0 (* return 1 *)
    | RDX -> 1 (* return 2/ arg 3 *)
    | RDI -> 2 (* arg 1 *)
    | RSI -> 3 (* arg 2 *)
    | RCX -> 4 (* arg 4 *)
    | R8  -> 5 (* arg 5 *)
    | R9  -> 6 (* arg 6 *)
    (* end argument *)
    | RBP -> 7
    | R10 -> 8
    | R11 -> 9
    | R12 -> 10
    | R13 -> 11
    | R14 -> 12
    | R15 -> 13
    | RBX -> 14
    | _   -> failwith "invalid register index for X86-64"

  let arg_regs = [ RDI; RSI; RDX; RCX; R8; R9 ]

(* *** Pretty printing
 * ------------------------------------------------------------------------ *)

  let string_of_reg = function
    | RAX -> "%rax"
    | RBX -> "%rbx"
    | RCX -> "%rcx"
    | RDX -> "%rdx"
    | RDI -> "%rdi"
    | RSI -> "%rsi"
    | RBP -> "%rbp"
    | RSP -> "%rsp"
    | R8  -> "%r8"
    | R9  -> "%r9"
    | R10 -> "%r10"
    | R11 -> "%r11"
    | R12 -> "%r12"
    | R13 -> "%r13"
    | R14 -> "%r14"
    | R15 -> "%r15"

  let reg_of_string = function
    | "rax" -> RAX
    | "rbx" -> RBX
    | "rcx" -> RCX
    | "rdx" -> RDX
    | "rdi" -> RDI
    | "rsi" -> RSI
    | "rbp" -> RBP
    | "rsp" -> RSP
    | "r8"  -> R8
    | "r9"  -> R9
    | "r10" -> R10
    | "r11" -> R11
    | "r12" -> R12
    | "r13" -> R13
    | "r14" -> R14
    | "r15" -> R15
    | s     -> failwith ("string_of_reg: unknown register "^s)

  let pp_reg fmt r = F.fprintf fmt "%s" (string_of_reg r)

  let binop_to_string = function
    | Add  -> "addq"
    | Adc  -> "adcq"
    | And  -> "andq"
    | Sub  -> "subq"
    | Sbb  -> "sbbq"
    | Mov  -> "movq"
    | Cmov(CfSet(true)) -> "cmovc"
    | Cmov(CfSet(false)) -> "cmovae"
    | Shr  -> "shr"
    | Shl  -> "shl"
    | Xor  -> "xor"

  let unop_to_string = function
    | Mul  -> "mulq"
    | Push -> "pushq"
    | Pop  -> "popq"

  let triop_to_string = function
    | IMul -> "imul"

  let pp_src fmt = function
    | Sreg(r)     -> pp_string fmt (string_of_reg r)
    | Simm(i)     -> F.fprintf fmt "$%s" (V.qword_to_string i)
    | Smem(reg,i) -> F.fprintf fmt "%s(%s)" (Int64.to_string i) (string_of_reg reg)

  let pp_dest fmt d = pp_src fmt (dest_to_src d)

  let pp_instr fmt = function
    | Unop (o,src) ->
      F.fprintf fmt "%s %a" (unop_to_string o) pp_src src
    | Triop(o,s1,s2,d) ->
      F.fprintf fmt "%s %a, %a, %a" (triop_to_string o) pp_src s1 pp_src s2 pp_dest d
    | Binop(o,s,d) ->
      F.fprintf fmt "%s %a, %a" (binop_to_string o) pp_src s pp_dest d
    | Label(s) ->
      F.fprintf fmt "%s:" s
    | Ret ->
      F.fprintf fmt "retq"
    | Section(s) ->
      F.fprintf fmt ".%s" s
    | Global(s) ->
      F.fprintf fmt ".globl %s" s
    | Comment(s) ->
      F.fprintf fmt "# %s" s

  let pp_instrs fmt is =
    F.fprintf fmt "%a\n" (pp_list "\n" pp_instr) is

  let pp_return fmt names =
    F.fprintf fmt "return %a" (pp_list "," pp_reg) names

  let pp_afun fmt af =
    F.fprintf fmt "@[<v 0>extern %s(%a) {@\n  @[<v 0>%a@\n%a@]@\n}@]"
      af.af_name
      (pp_list "," pp_reg) af.af_args
      pp_instrs af.af_body
      pp_return af.af_ret
  
end

(* ** Instruction module (functor application)
 * ------------------------------------------------------------------------ *)

module Instr = Make_Instr(V64)

include Instr

