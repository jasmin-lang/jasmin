(* -------------------------------------------------------------------- *)
open Utils

(* -------------------------------------------------------------------- *)
let lexbuf_from_function = fun name f ->
  let lexbuf = Lexing.from_function f in
  Lexing.set_filename lexbuf name;
  lexbuf

(* -------------------------------------------------------------------- *)
let parse_program ?(name = "") (inc : IO.input) =
  let lexbuf = lexbuf_from_function name @@ fun buf n ->
  try IO.input inc buf 0 n with IO.No_more_input -> 0 in
  Parser.module_ Lexer.main lexbuf
