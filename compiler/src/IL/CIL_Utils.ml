(* * Utility functions for conversion to and from Coq language *)

(* ** Imports and abbreviations *)
open Core_kernel.Std
open Arith

module F  = Format
module DE = Dmasm_expr
module DU = Dmasm_utils
module DT = Dmasm_type
module DV = Dmasm_var
module Lex = ParserUtil.Lexing
module HT = Hashtbl

(* ** Conversions for strings, numbers, ...
 * ------------------------------------------------------------------------ *)

let rec pos_of_bi bi =
  let open Big_int_Infix in
  if bi <=! Big_int.unit_big_int then BinNums.Coq_xH
  else 
    let p = pos_of_bi (bi >>! 1) in
    if (bi %! (Big_int.big_int_of_int 2)) === Big_int.unit_big_int 
    then BinNums.Coq_xI p 
    else BinNums.Coq_xO p 

let rec bi_of_pos pos =
  let open Big_int_Infix in
  match pos with
  | BinNums.Coq_xH   -> Big_int.unit_big_int
  | BinNums.Coq_xO p -> (bi_of_pos p) <!< 1
  | BinNums.Coq_xI p -> ((bi_of_pos p) <!< 1) +! Big_int.unit_big_int

let int_of_pos pos = Big_int.int_of_big_int (bi_of_pos pos)

let pos_of_int pos = pos_of_bi (Big_int.big_int_of_int pos)

let coqZ_of_bi bi =
  let open Big_int_Infix in
  if bi === Big_int.zero_big_int then
    BinNums.Z0
  else if bi <! Big_int.zero_big_int then 
    BinNums.Zneg (pos_of_bi (Big_int.minus_big_int bi))
  else 
    BinNums.Zpos (pos_of_bi bi)
  
let bi_of_coqZ z =
  match z with
  | BinNums.Zneg p -> Big_int.minus_big_int (bi_of_pos p)
  | BinNums.Z0 -> Big_int.zero_big_int
  | BinNums.Zpos p -> bi_of_pos p

let ascii_of_char x = 
  let x = int_of_char x in
  let bit i = 
    if x lsr (7 - i) land 1 = 1 then Datatypes.Coq_true 
    else Datatypes.Coq_false in
  Ascii.Ascii(bit 0, bit 1, bit 2, bit 3, bit 4, bit 5, bit 6, bit 7)

let char_of_ascii c = 
  let Ascii.Ascii(b7, b6, b5, b4, b3, b2, b1, b0) = c in
  let cv b i = if b = Datatypes.Coq_true  then 1 lsl i else 0 in
  let i =
    (cv b7 7) + (cv b6 6) + (cv b5 5) + (cv b4 4) + (cv b3 3) + (cv b2 2) + (cv b1 1) + (cv b0 0) 
  in
  char_of_int i

let string0_of_string s = 
  let s0 = ref String0.EmptyString in
  for i = String.length s - 1 downto 0 do
    s0 := String0.String (ascii_of_char s.[i], !s0) 
  done;
  !s0

let string_of_string0 s0 =
  let rec go acc s0 =
    match s0 with
    | String0.EmptyString   -> List.rev acc
    | String0.String (c,s0) ->
      go ((char_of_ascii c)::acc) s0
  in
  String.of_char_list (go [] s0)

let cbool_of_bool b =
  if b then Datatypes.Coq_true else Datatypes.Coq_false

let bool_of_cbool cb =
  match cb with
  | Datatypes.Coq_true  -> true
  | Datatypes.Coq_false -> false

let list_of_clist cl =
  let rec go acc cl =
    match cl with
    | Datatypes.Coq_nil -> List.rev acc
    | Datatypes.Coq_cons(c,cl) ->
      go (c::acc) cl
  in
  go [] cl

let clist_of_list l =
  let rec go acc l =
    match l with
    | [] -> acc
    | x::l ->
      go (Datatypes.Coq_cons(x,acc)) l
  in
  go Datatypes.Coq_nil (List.rev l)

let cpair_of_pair (x,y) =
  Datatypes.Coq_pair(x,y)

let pair_of_cpair cp =
  let Datatypes.Coq_pair(x,y) = cp in
  (x,y)

let sword = DT.Coq_sword
let sbool = DT.Coq_sbool
let sint  = DT.Coq_sint

let sarr i = DT.Coq_sarr(pos_of_bi i)
