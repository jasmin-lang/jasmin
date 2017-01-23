(* * License
 * -----------------------------------------------------------------------
 * Copyright 2016--2017 IMDEA Software Institute
 * Copyright 2016--2017 Inria
 *
 * Permission is hereby granted, free of charge, to any person obtaining
 * a copy of this software and associated documentation files (the
 * "Software"), to deal in the Software without restriction, including
 * without limitation the rights to use, copy, modify, merge, publish,
 * distribute, sublicense, and/or sell copies of the Software, and to
 * permit persons to whom the Software is furnished to do so, subject to
 * the following conditions:
 *
 * The above copyright notice and this permission notice shall be
 * included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
 * EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.
 * IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY
 * CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT,
 * TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE
 * SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 * ----------------------------------------------------------------------- *)

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
    let compare_position p1 p2 =
      [%compare: string * int * int * int ]
        (p1.pos_fname, p1.pos_lnum, p1.pos_bol, p1.pos_cnum)
        (p2.pos_fname, p2.pos_lnum, p2.pos_bol, p2.pos_cnum)
    let position_of_sexp _p = failwith "position_of_sexp undefined"
    let sexp_of_position _p = failwith "sexp_of_position undefined"
    let pp_pos fmt p =
      F.fprintf fmt "%s:%i:%i" p.pos_fname p.pos_lnum p.pos_cnum

    type loc = { loc_start : position; loc_end : position }
     [@@deriving compare,sexp]
    let pp_loc fmt l = (* FIXME: also print end of range *)
      F.fprintf fmt "%s:%i:%i" l.loc_start.pos_fname l.loc_start.pos_lnum l.loc_start.pos_cnum
    let mk_loc (ps,pe) = { loc_start = ps; loc_end = pe }
    let dummy_loc = mk_loc (dummy_pos,dummy_pos)
    type 'a located = {
      l_val : 'a;
      l_loc : loc
    } [@@deriving compare,sexp]

  end

(* ** Error handling
 * ------------------------------------------------------------------------ *)

(* our custom parse error *)
exception ParseError of (Lexing.loc * string) list

let failparse loc s = raise (ParseError([loc,s]))

let failparse_l locs_s = raise (ParseError(locs_s))

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

let convert_error s (loc,err) =
  let open Lexing in
  let start_pos = loc.loc_start.L.pos_cnum in
  let end_pos   = loc.loc_end.L.pos_cnum in    
  let (line_pos,lstart_pos,line) = charpos_to_linepos s start_pos in
  let len = min (end_pos - start_pos) (String.length line - lstart_pos) in
  let fname = loc.loc_start.L.pos_fname in
  (fname,line_pos,lstart_pos,len,line,err)

let wrap_error f fname s =
  let sbuf = lexbuf_from_string fname s in
  try
    `ParseOk (f sbuf)
  with
  | LexerError msg ->
    let start_pos = Lexing.lexeme_start sbuf in
    let end_pos = Lexing.lexeme_start sbuf in
    let (line_pos,lstart_pos,line) = charpos_to_linepos s start_pos in
    let len = min (end_pos - start_pos) (String.length line - lstart_pos) in
    `ParseError [ (fname,line_pos,lstart_pos,len,line,msg) ]
  | ParserError ->
    let start_pos = Lexing.lexeme_start sbuf in
    let end_pos = Lexing.lexeme_start sbuf in
    let (line_pos,lstart_pos,line) = charpos_to_linepos s start_pos in
    let len = min (end_pos - start_pos) (String.length line - lstart_pos) in
    `ParseError [ (fname,line_pos,lstart_pos,len,line,"parse error") ]
  | ParseError(loc_errs) ->
    `ParseError (List.map ~f:(convert_error s) loc_errs)
  | e ->
    failwith
      (F.sprintf "Unexpected error while lexing/parsing: %s,\n%s"
         (Exn.to_string e)
         (Exn.backtrace ()))

let error_string (fname,line_start,start_pos,len,line,msg) =
  let len = max 1 (len - 1) in
  let start_pos = max start_pos 0 in
  let spos = max (start_pos + 1) 0 in
  (F.sprintf "%s:%i:%i: %i:%i error: %s\n" fname line_start spos line_start (spos+len) msg)
  ^(F.sprintf "%s\n" line)
  ^(F.sprintf "%s%s\n" (String.make start_pos ' ') (String.make (len + 1) '^'))

let error_string_list errs =
  String.concat ~sep:"" @@ List.map ~f:error_string errs

let parse ~parse s =
  match parse s with
  | `ParseOk pres     -> pres
  | `ParseError(errs) -> failwith (error_string_list errs)

let failloc_c _s errs =
  let err_s = error_string_list errs in
  eprintf "%s%!" err_s;
  exit (-1)

let failloc s errs =
  let errs = List.map ~f:(convert_error s) errs in
  let err_s = error_string_list errs in
  eprintf "%s%!" err_s;
  exit (-1)
