open Core.Std
module S = String
module F = Format

(* Use this in your lexer *)
exception LexerError of string

(* Replace menhir Parser/Error error using this error *)
exception ParserError

let charpos_to_linepos s cp =
  let module E = struct exception Found of int * int * string end in
  let lines = String.split_lines s in
  let cur_line = ref 1 in
  let cur_cp = ref cp in
  try 
    List.iter lines
      ~f:(fun ls ->
            let len = String.length ls in
            if !cur_cp < len then
              raise (E.Found(!cur_line,!cur_cp,ls));
            incr cur_line;
            cur_cp := !cur_cp - len - 1
         );
    assert false
  with
    E.Found(l,cp,s) -> (l,cp,s)

let wrap_error f s =
  let sbuf = Lexing.from_string s in
  try
    `ParseOk (f sbuf)
  with
  | LexerError msg ->
    let start_pos = Lexing.lexeme_start sbuf in
    let end_pos = Lexing.lexeme_start sbuf in
    let len = end_pos - start_pos in
    let (line_pos,lstart_pos,line) = charpos_to_linepos s start_pos in
    `ParseError (line_pos,lstart_pos,lstart_pos+len,line,msg)
  | ParserError ->
    let start_pos = Lexing.lexeme_start sbuf in
    let end_pos = Lexing.lexeme_start sbuf in
    let len = end_pos - start_pos in
    let (line_pos,lstart_pos,line) = charpos_to_linepos s start_pos in
    `ParseError (line_pos,lstart_pos,lstart_pos+len,line,"parse error")
  | e ->
    failwith
      (F.sprintf "Unexpected error while lexing/parsing: %s,\n%s"
         (Exn.to_string e)
         (Exn.backtrace ()))

let error_string file (line_start,start_pos,end_pos,line,msg) =
  (F.sprintf "%s:%i:%i %i:%i error: %s\n" file line_start start_pos line_start end_pos msg)
  ^(F.sprintf "%s\n" line)
  ^(F.sprintf "%s%s\n" (String.make start_pos ' ') "^")
