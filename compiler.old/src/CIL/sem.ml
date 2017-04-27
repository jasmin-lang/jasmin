open BinInt
open BinNums
open Datatypes
open Expr
open Seq

(** val wrange : dir -> coq_Z -> coq_Z -> coq_Z list **)

let wrange d n1 n2 =
  let n = Z.to_nat (Z.sub n2 n1) in
  (match d with
   | UpTo -> map (fun i -> Z.add n1 (Z.of_nat i)) (iota O n)
   | DownTo -> map (fun i -> Z.sub n2 (Z.of_nat i)) (iota O n))
