(* * Utility functions for parsing *)

(* ** Imports and abbreviations *)
open Core_kernel.Std

module S = String
module F = Format
module L = Lexing

(* ** Error handling
 * ------------------------------------------------------------------------ *)

(* Use this in your lexer *)
exception LexerError of string

(* Replace menhir ParserError error using this error *)
exception ParserError

exception UParserError of int * int * string

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
    (0,0,"<undefined>")
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
    let (line_pos,lstart_pos,line) = charpos_to_linepos s start_pos in
    let len = min (end_pos - start_pos) (String.length line - lstart_pos) in
    `ParseError (line_pos,lstart_pos,len,line,msg)
  | ParserError ->
    let start_pos = Lexing.lexeme_start sbuf in
    let end_pos = Lexing.lexeme_start sbuf in
    let (line_pos,lstart_pos,line) = charpos_to_linepos s start_pos in
    let len = min (end_pos - start_pos) (String.length line - lstart_pos) in
    `ParseError (line_pos,lstart_pos,len,line,"parse error")
  | UParserError(start_pos,end_pos,err) -> 
    let (line_pos,lstart_pos,line) = charpos_to_linepos s start_pos in
    let len = min (end_pos - start_pos) (String.length line - lstart_pos) in
    `ParseError (line_pos,lstart_pos,len,line,err)
  | e ->
    failwith
      (F.sprintf "Unexpected error while lexing/parsing: %s,\n%s"
         (Exn.to_string e)
         (Exn.backtrace ()))

let error_string file (line_start,start_pos,len,line,msg) =
  let len = max 1 (len - 1) in
  (F.sprintf "%s:%i:%i %i:%i error: %s\n" file line_start start_pos line_start (start_pos+len) msg)
  ^(F.sprintf "%s\n" line)
  ^(F.sprintf "%s%s\n" (String.make start_pos ' ') (String.make len '^'))

let parse ~parse file s =
  begin match parse s with
  | `ParseOk pres -> pres
  | `ParseError(pinfo) ->
    let s = error_string file pinfo in
    failwith s
  end

(* ** Positions
 * ------------------------------------------------------------------------ *)

(* FIXME: type duplicated since deriving expects compare/sexp in Lexing module *)

type pos = {
  pos_fname : string;
  pos_lnum : int;
  pos_cnum : int;
  pos_bol : int
} with compare, sexp

let pos_of_lexing_pos (p : L.position) =
  { pos_fname = p.L.pos_fname;
    pos_lnum  = p.L.pos_lnum;
    pos_cnum  = p.L.pos_cnum;
    pos_bol   = p.L.pos_bol;
  }

let dummy_pos = pos_of_lexing_pos L.dummy_pos

type loc = {
  loc_start : pos;
  loc_end   : pos;
} with compare, sexp

let loc_of_lexing_loc (spos,epos) =
  { loc_start = pos_of_lexing_pos spos;
    loc_end   = pos_of_lexing_pos epos;
  }

let dummy_loc = loc_of_lexing_loc (L.dummy_pos, L.dummy_pos)

let pp_pos fmt p =
  F.fprintf fmt "%s:%i:%i" p.pos_fname p.pos_lnum p.pos_cnum

let pp_loc fmt l = pp_pos fmt l.loc_start
