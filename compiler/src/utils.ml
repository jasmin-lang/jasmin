(* -------------------------------------------------------------------- *)
module Map    = BatMap
module Set    = BatSet
module Hash   = BatHashtbl

module Sint = Set.Make (BatInt)
module Mint = Map.Make (BatInt)

(* -------------------------------------------------------------------- *)
module Ss = Set.Make(String)
module Ms = Map.Make(String)

(* -------------------------------------------------------------------- *)
let timed f x =
  let t1   = Unix.gettimeofday () in
  let aout = f x in
  let t2   = Unix.gettimeofday () in
  (t2 -. t1, aout)

let identity x = x

let (^~) f = fun x y -> f y x

let (-|) f g = fun x -> f (g x)
let (|-) g f = fun x -> g (f x)

(* -------------------------------------------------------------------- *)
type 'a tuple0 = unit
type 'a tuple1 = 'a
type 'a tuple2 = 'a * 'a
type 'a tuple3 = 'a * 'a * 'a
type 'a tuple4 = 'a * 'a * 'a * 'a
type 'a tuple5 = 'a * 'a * 'a * 'a * 'a
type 'a tuple6 = 'a * 'a * 'a * 'a * 'a * 'a
type 'a tuple7 = 'a * 'a * 'a * 'a * 'a * 'a * 'a
type 'a tuple8 = 'a * 'a * 'a * 'a * 'a * 'a * 'a * 'a
type 'a tuple9 = 'a * 'a * 'a * 'a * 'a * 'a * 'a * 'a * 'a
type 'a pair   = 'a * 'a

(* -------------------------------------------------------------------- *)
let as_seq0 = function [] -> () | _ -> assert false
let as_seq1 = function [x] -> x | _ -> assert false
let as_seq2 = function [x1; x2] -> (x1, x2) | _ -> assert false
let as_seq3 = function [x1; x2; x3] -> (x1, x2, x3) | _ -> assert false

let as_seq4 = function
  | [x1; x2; x3; x4] -> (x1, x2, x3, x4)
  | _ -> assert false

let as_seq5 = function
  | [x1; x2; x3; x4; x5] -> (x1, x2, x3, x4, x5)
  | _ -> assert false

let as_seq6 = function
  | [x1; x2; x3; x4; x5; x6] -> (x1, x2, x3, x4, x5, x6)
  | _ -> assert false

let as_seq7 = function
  | [x1; x2; x3; x4; x5; x6; x7] -> (x1, x2, x3, x4, x5, x6, x7)
  | _ -> assert false

(* -------------------------------------------------------------------- *)
let fst_map (f : 'a -> 'c) ((x, y) : 'a * 'b) =
  (f x, y)

let snd_map (f : 'b -> 'c) ((x, y) : 'a * 'b) =
  (x, f y)

(* -------------------------------------------------------------------- *)
module Option = BatOption

(* -------------------------------------------------------------------- *)
let oiter (f : 'a -> unit) (x : 'a option) =
  match x with None -> () | Some x -> f x

let obind (f : 'a -> 'b option) (x : 'a option) =
  match x with None -> None | Some x -> f x

let otolist (x : 'a option) =
  match x with None -> [] | Some x -> [x]

let ofold (f : 'a -> 'b -> 'b) (v : 'b) (x : 'a option) =
  match x with
  | None   -> v
  | Some x -> f x v

let omap (f : 'a -> 'b) (x : 'a option) =
  match x with None -> None | Some x -> Some (f x)

let omap_dfl (f : 'a -> 'b) (d : 'b) (x : 'a option) =
  match x with None -> d  | Some x -> f x

let odfl (d : 'a) (x : 'a option) =
  match x with None -> d | Some x -> x

let ofdfl (d : unit -> 'a) (x : 'a option) =
  match x with None -> d () | Some x -> x

let oget ?exn (x : 'a option) =
  match x, exn with
  | None  , None     -> assert false
  | None  , Some exn -> raise exn
  | Some x, _        -> x

(* -------------------------------------------------------------------- *)
let iterop (op : 'a -> 'a) (n : int) (x : 'a) =
  let rec doit n x = if n <= 0 then x else doit (n-1) (op x) in
  if n < 0 then invalid_arg "[iterop]: n < 0";
  doit n x

(* -------------------------------------------------------------------- *)
let iter (op : 'a -> 'a) (x : 'a) =
  let rec doit x = doit (op x) in doit x

(* -------------------------------------------------------------------- *)
module Uniq = struct
  let gen () = Oo.id (object end)
end

(* -------------------------------------------------------------------- *)
module ISet = BatISet

(* -------------------------------------------------------------------- *)
module List = struct
  include BatList

  (* ------------------------------------------------------------------ *)
  module Smart = struct
    let rec map f xs =
      match xs with
      | [] -> []
      | y :: ys ->
          let z  = f y in
          let zs = map f ys in
          if y == z && ys == zs then xs else (z :: zs)

    let map_fold f a xs =
      let r   = ref a in
      let f x = let (a, x) = f !r x in r := a; x in
      let xs  = map f xs in
      (!r, xs)
  end

  (* ------------------------------------------------------------------ *)
  let opick = Exceptionless.find_map

  (* ------------------------------------------------------------------ *)
  module Parallel = struct
    let map_fold2 f =
      let rec doit a xs1 xs2 =
        match xs1, xs2 with
        | [], [] -> (a, [])

        | x1 :: xs1, x2 :: xs2 ->
            let (a, x ) = f a x1 x2 in
            let (a, xs) = doit a xs1 xs2 in
            (a, x :: xs)

        | _, _ -> invalid_arg "List.map_fold2"

      in fun a xs1 xs2 -> doit a xs1 xs2

  end

  include Parallel

  (* ------------------------------------------------------------------ *)
  let last (s : 'a list) =
    match Exceptionless.last s with
    | None   -> failwith "List.last"
    | Some x -> x

  let rec find_map_opt f = function
    | [] -> None
    | x :: l ->
      begin match f x with
        | Some _ as result -> result
        | None -> find_map_opt f l
      end

  let rec pmap (f : 'a -> 'b option) (xs : 'a list) =
    match xs with
    | []      -> []
    | x :: xs ->
      let v = f x in
      let bs = pmap f xs in
        match v with
          Some b -> b :: bs
        | None -> bs

  let mapi_fold f a xs =
    let a  = ref a in
    let xs = List.mapi (fun i b ->
      let (a', b') = f i !a b in a := a'; b')
      xs
    in (!a, xs)

  let map_fold f a xs =
    mapi_fold (fun (_ : int) x -> f x) a xs

end

(* -------------------------------------------------------------------- *)
module String = struct
  include BatString
end

(* -------------------------------------------------------------------- *)
module IO = BatIO

(* -------------------------------------------------------------------- *)
module Buffer = BatBuffer


(* -------------------------------------------------------------------- *)
exception HiError of string

let hierror fmt =
  let buf  = Buffer.create 127 in
  let bfmt = Format.formatter_of_buffer buf in

  Format.kfprintf
    (fun _ ->
      Format.pp_print_flush bfmt ();
      raise (HiError (Buffer.contents buf)))
    bfmt fmt

(* -------------------------------------------------------------------- *)
type 'a pp = Format.formatter -> 'a -> unit

let rec pp_list sep pp fmt xs =
  let pp_list = pp_list sep pp in
  match xs with
  | []      -> ()
  | [x]     -> Format.fprintf fmt "%a" pp x
  | x :: xs -> Format.fprintf fmt "%a%(%)%a" pp x sep pp_list xs

(* -------------------------------------------------------------------- *)
let pp_if c pp1 pp2 fmt x =
  match c with
  | true  -> Format.fprintf fmt "%a" pp1 x
  | false -> Format.fprintf fmt "%a" pp2 x

(* -------------------------------------------------------------------- *)
let pp_maybe c tx pp fmt x =
  pp_if c (tx pp) pp fmt x

(* -------------------------------------------------------------------- *)
let pp_enclose ~pre ~post pp fmt x =
  Format.fprintf fmt "%(%)%a%(%)" pre pp x post

(* -------------------------------------------------------------------- *)
let pp_paren pp fmt x =
  pp_enclose ~pre:"(" ~post:")" pp fmt x

(* -------------------------------------------------------------------- *)
let pp_maybe_paren c pp =
  pp_maybe c pp_paren pp
  
(* -------------------------------------------------------------------- *)
let pp_string fmt s = 
  Format.fprintf fmt "%s" s

(* -------------------------------------------------------------------- *)

type model = 
  | ConstantTime
  | Safety
  | Normal
