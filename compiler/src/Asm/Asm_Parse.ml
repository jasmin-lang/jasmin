(* * Parsing functions for assembly *)

open Core_kernel.Std

module S = String
module F = Format
module PU = ParserUtil

let convert_error f =
  PU.wrap_error
    (fun sbuf ->
      try  f sbuf
      with Asm_Parser.Error -> raise PU.ParserError)

let instr = convert_error (Asm_Parser.instr Asm_Lexer.lex)

let instrs = convert_error (Asm_Parser.instrs Asm_Lexer.lex)
