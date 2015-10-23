(* * Utility functions (mostly for testing) *)


(* ** Imports and abbreviations *)
open Big_int
open Core_kernel.Std

module F = Format

(* ** Arithmetic
 * ------------------------------------------------------------------------ *)

(* only for testing, this is biased *)
let sample_bigint_insecure p =
  let rec go ~pos ~rem ~res =
    if eq_big_int rem zero_big_int then res
    else (
      let i = Random.bits () in
      go
        ~pos:(pos + 30)
        ~rem:(shift_right_towards_zero_big_int rem 30)
        ~res:(add_big_int (shift_left_big_int (big_int_of_int i) pos) res)
    )
  in mod_big_int (go ~pos:0 ~rem:p ~res:(big_int_of_int 0)) p

module Big_int_Infix = struct
  include Big_int
  let (+!)  = add_big_int
  let ( *!) = mult_big_int
  let (-!)  = sub_big_int
  let (^!)  = power_int_positive_int
  let (&!)  x i = extract_big_int x i (i + 1)
  let (>>!) x i = shift_right_big_int x i
  let (<!<) x i = shift_left_big_int x i
  let (===) = eq_big_int
  let (<!)  = lt_big_int
end

module U64 = struct
  open Unsigned
  include Unsigned.UInt64
  let mask_low  = UInt64.of_string "0xffffffff"
  let mask_high = UInt64.of_string "0xffffffff00000000"

  (* FIXME: check this *)
  let add_carry x y cf_in =
    let x = if cf_in then UInt64.succ x else x in
    if x = UInt64.zero && cf_in then (
      (y,true)
    ) else (
      let c = UInt64.add x y in
      let cf = UInt64.compare c y < 0 in
      (c,cf)
    )

  (* FIXME: check this too *)
  let mul x y =
    let low u = UInt64.logand mask_low u in
    let high u = UInt64.shift_right (UInt64.logand mask_high u) 32 in
    let x_low  = low x in
    let y_low  = low y in
    let x_high = high x in
    let y_high = high y in
    
    let z0  = UInt64.mul x_low y_low in
    let z2  = UInt64.mul x_high y_high in

    let z11 = UInt64.mul x_low y_high in
    let z12 = UInt64.mul x_high y_low in
    let z11_low  = UInt64.shift_left (low  z11) 32 in
    let z11_high = high z11 in
    let z12_low  = UInt64.shift_left (low  z12) 32 in
    let z12_high = high z12 in
    
    let (u,cf)  = add_carry z0 z11_low false in
    let (w,cf) = add_carry z11_high z12_high cf in
    assert (not cf);
    let (u,cf) = add_carry u z12_low false in
    let (w,cf) = add_carry w z2 cf in
    assert (not cf);
    (w,u)

  let to_big_int x = big_int_of_string (UInt64.to_string x)
  let of_big_int x = UInt64.of_string (string_of_big_int x)
  let is_zero x = compare (of_int 0) x = 0
  let is_one x = compare (of_int 1) x = 0
  (* let equal x y = compare x y = 0 *)
  module T = struct
    type t = Unsigned.UInt64.t
    let t_of_sexp s = of_string (string_of_sexp s)
    let sexp_of_t x = sexp_of_string (to_string x)
    let compare = compare
    let hash v = Hashtbl.hash v
  end
  include Comparable.Make(T)
  include Hashable.Make(T)
end

type u64 = U64.t

let compare_u64 = U64.compare
let u64_of_sexp s = U64.of_string (string_of_sexp s)
let sexp_of_u64 u = sexp_of_string (U64.to_string u)

module Limb4 = struct
  let of_big_int i =
    let open Big_int_Infix in
    assert (i <! (2^!256));
    (U64.of_big_int (extract_big_int i 0 64),
     U64.of_big_int (extract_big_int i 64 64),
     U64.of_big_int (extract_big_int i 128 64),
     U64.of_big_int (extract_big_int i 192 64))

  let to_big_int (x0,x1,x2,x3) =
    Big_int_Infix.(
      (U64.to_big_int x0)
      +! ((U64.to_big_int x1) <!< 64)
      +! ((U64.to_big_int x2) <!< 128)
      +! ((U64.to_big_int x3) <!< 192)
    )
end

(* ** Pretty-printing
 * ------------------------------------------------------------------------ *)

(* pretty printing as in hex notation with blocks containing i bytes *)
let pph digit_size fmt i =
  let pp_digit i = F.sprintf "%x" i in
  let rec go ~i ~digits =
    if (eq_big_int (big_int_of_int 0) i) then "" else (
      (go ~i:(shift_right_big_int i 4) ~digits:(digits + 1))
      ^(pp_digit (int_of_big_int (extract_big_int i 0 4)))
      ^(if digits mod digit_size = 0 then "|" else "")
    )
  in
  F.fprintf fmt "%s" (go ~i:i ~digits:0)

let pp_string fmt s = F.fprintf fmt "%s" s

let pp_pair sep ppa ppb fmt (a,b) = F.fprintf fmt "%a%s%a" ppa a sep ppb b

let pp_int fmt i = F.fprintf fmt "%i" i

let pp_uint64 fmt i = F.fprintf fmt "%s" (U64.to_string i)

let pp_int64 fmt i = F.fprintf fmt "%s" (Int64.to_string i)

let pp_bool fmt b = F.fprintf fmt "%s" (if b then "true" else "false")

let pp_big_int fmt bi = F.fprintf fmt "%s" (Big_int.string_of_big_int bi)

let rec pp_list sep pp_elt f l =
  match l with
  | [] -> ()
  | [e] -> pp_elt f e
  | e::l -> F.fprintf f "%a%(%)%a" pp_elt e sep (pp_list sep pp_elt) l

let opt mx f y =
  match mx with
  | Some x -> f x
  | None   -> y

let fsprintf fmt =
  let buf  = Buffer.create 127 in
  let fbuf = F.formatter_of_buffer buf in
  F.kfprintf
    (fun _ ->
      F.pp_print_flush fbuf ();
      (Buffer.contents buf))
    fbuf fmt

let linit l = List.rev l |> List.tl_exn |> List.rev
