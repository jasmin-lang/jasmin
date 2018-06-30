open BinInt
open BinNums
open Datatypes
open Eqtype
open SsrZ
open Ssralg
open Type
open Utils0
open Word0

module Zcmp = struct
  type t = coq_Z
  let compare (x:t)(y:t) = compare x y
end

module Mz = Map.Make(Zcmp)

type w8 = GRing.ComRing.sort (* u8 *)

type mem = GRing.ComRing.sort Mz.t

let empty = Mz.empty 

let read_mem8 (m:mem) (p:coq_Z) : w8 = 
  try Mz.find p m 
  with Not_found -> wrepr U8 Z0

let of_pointer (p:GRing.ComRing.sort) : coq_Z = 
  wunsigned U64 p

let nb_blocs (sz:wsize) = 
  match sz with
  | U8   -> 1
  | U16  -> 2
  | U32  -> 4
  | U64  -> 8
  | U128 -> 16
  | U256 -> 32

let positions (p:GRing.ComRing.sort) (sz:wsize) = 
  let rec aux p n = 
    if n = 0 then []
    else p :: aux (BinInt.Z.add p (Zpos Coq_xH)) (n-1) in
  aux (of_pointer p) (nb_blocs sz)
 
let is_align ptr ws =
  let w = wunsigned U64 ptr in
  eq_op coq_Z_eqType (Obj.magic Z.modulo w (wsize_size ws)) (Obj.magic Z0) 

(* FIXME check is_align *)
let read_mem (m:mem) (p:GRing.ComRing.sort) (sz:wsize) = 
  let pos = positions p sz in
  let w8s = List.map (fun p -> read_mem8 m p) pos in
  Ok(make_vec U8 sz w8s)

let rec nat_of_int n = 
  if n <= 0 then O else S (nat_of_int (n-1))

let n8 = nat_of_int 8 

(* FIXME check is_align *)
let write_mem (m:mem) (p:GRing.ComRing.sort) 
              (sz:wsize) (w:GRing.ComRing.sort) =
  let l = split_vec sz n8 w in
  let pos = positions p sz in
  Ok (List.fold_left2 (fun m w p -> Mz.add p (wrepr U8 w) m) m l pos)
