(* * Utility functions for parsing *)

(* ** Imports and abbreviations *)
open Core_kernel.Std

module S = String
module F = Format
module L = Lexing

(* ** Error handling
 * ------------------------------------------------------------------------ *)

module Lexing =
  struct
    include Lexing
    let compare_position _p1 _p2 = failwith "Lexing.compare undefined"
    let position_of_sexp _p = failwith "Lexing.compare undefined"
    let sexp_of_position _p = failwith "Lexing.compare undefined"
    let pp_pos fmt p =
      F.fprintf fmt "%s:%i:%i" p.pos_fname p.pos_lnum p.pos_cnum

    type loc = { loc_start : position; loc_end : position }
      with sexp, compare
    let pp_loc fmt l = (* FIXME: also print end of range *)
      F.fprintf fmt "%s:%i:%i" l.loc_start.pos_fname l.loc_start.pos_lnum l.loc_start.pos_cnum
    let mk_loc (ps,pe) = { loc_start = ps; loc_end = pe }
    let dummy_loc = mk_loc (dummy_pos,dummy_pos)
    type 'a located = {
      l_val : 'a;
      l_loc : loc
    } with sexp, compare

  end

(* ** Error handling
 * ------------------------------------------------------------------------ *)

(* our custom parse error *)
exception ParseError of Lexing.loc * string

let failparse loc s = raise (ParseError(loc,s))

(* Use this in your lexer *)
exception LexerError of string

(* Replace menhir ParserError error using this error *)
exception ParserError

let lexbuf_from_string name s = 
  let lexbuf = Lexing.from_string s in
  lexbuf.Lexing.lex_curr_p <- {
      Lexing.pos_fname = name;
      Lexing.pos_lnum  = 1;
      Lexing.pos_bol   = 0;
      Lexing.pos_cnum  = 0
    };
  lexbuf

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

let wrap_error f fname s =
  let open Lexing in
  let sbuf = lexbuf_from_string fname s in
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
  | ParseError(loc,err) ->
    let start_pos = loc.loc_start.L.pos_cnum in
    let end_pos   = loc.loc_end.L.pos_cnum in    
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
  let start_pos = max start_pos 0 in
  let spos = max (start_pos + 1) 0 in
  (F.sprintf "%s:%i:%i: %i:%i error: %s\n" file line_start spos line_start (spos+len) msg)
  ^(F.sprintf "%s\n" line)
  ^(F.sprintf "%s%s\n" (String.make start_pos ' ') (String.make (len + 1) '^'))

let parse ~parse file s =
  match parse s with
  | `ParseOk pres      -> pres
  | `ParseError(pinfo) -> failwith (error_string file pinfo)

let failloc loc s msg =
  let open Lexing in
  let start_pos = loc.loc_start.L.pos_cnum in
  let end_pos   = loc.loc_end.L.pos_cnum in
  let (line_pos,lstart_pos,line) = charpos_to_linepos s start_pos in
  let len = min (end_pos - start_pos) (String.length line - lstart_pos) in
  let pinfo = (line_pos,lstart_pos,len,line,msg) in
  let fname = loc.loc_start.L.pos_fname in
  eprintf "%s%!" (error_string fname pinfo);
  (* let msg = fsprintf "%a: %s" L.pp_loc loc msg in *)
  (* prerr_endline msg; *)
  exit (-1)
