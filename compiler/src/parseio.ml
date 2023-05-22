(* -------------------------------------------------------------------- *)
open Utils

module P = Parser
module L = Lexing

(* -------------------------------------------------------------------- *)
let lexbuf_from_channel = fun name channel ->
  let lexbuf = Lexing.from_function channel in
    lexbuf.Lexing.lex_curr_p <- {
        Lexing.pos_fname = name;
        Lexing.pos_lnum  = 1;
        Lexing.pos_bol   = 0;
        Lexing.pos_cnum  = 0
      };
    lexbuf

(* -------------------------------------------------------------------- *)
let parserfun_entry =
    MenhirLib.Convert.Simplified.traditional2revised P.module_

(* -------------------------------------------------------------------- *)
let lexer (lexbuf : L.lexbuf) =
  let token = Lexer.main lexbuf in
  (token, L.lexeme_start_p lexbuf, L.lexeme_end_p lexbuf)

(* -------------------------------------------------------------------- *)
let parse_program ?(name = "") (inc : IO.input) =
  let lexbuf = lexbuf_from_channel name @@ fun buf n ->
  try IO.input inc buf 0 n with IO.No_more_input -> 0 in
  parserfun_entry (fun () -> lexer lexbuf)
