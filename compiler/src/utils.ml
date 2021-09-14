(* -------------------------------------------------------------------- *)
module Map    = BatMap
module Set    = BatSet
module Hash   = BatHashtbl

module Sint = Set.Make (BatInt)
module Mint = Map.Make (BatInt)

(* -------------------------------------------------------------------- *)
module Scmp = struct 
  type t = string
  let compare = compare 
end
module Ss = Set.Make(Scmp)
module Ms = Map.Make(Scmp)
    
(* -------------------------------------------------------------------- *)
exception Unexpected

let unexpected () = raise Unexpected

(* -------------------------------------------------------------------- *)
type 'data cb = Cb : 'a * ('data -> 'a -> unit) -> 'data cb

(* -------------------------------------------------------------------- *)
type 'a eq  = 'a -> 'a -> bool
type 'a cmp = 'a -> 'a -> int

(* -------------------------------------------------------------------- *)
let tryexn (ignoreexn : exn -> bool) (f : unit -> 'a) =
  try  Some (f ())
  with e -> if ignoreexn e then None else raise e

let try_nf (f : unit -> 'a) =
  tryexn (function Not_found -> true | _ -> false) f

let try_finally (body : unit -> 'a) (cleanup : unit -> unit) =
  let aout =
    try  body ()
    with e -> cleanup (); raise e
  in
    cleanup (); aout

let timed f x =
  let t1   = Unix.gettimeofday () in
  let aout = f x in
  let t2   = Unix.gettimeofday () in
  (t2 -. t1, aout)

let identity x = x

let pred0 (_ : 'a) = false
let predT (_ : 'a) = true

let (^~) f = fun x y -> f y x

let (-|) f g = fun x -> f (g x)
let (|-) g f = fun x -> g (f x)

let (|>) x f = f x
let (<|) f x = f x

let curry   f (x, y) = f x y
let uncurry f x y = f (x, y)

let curry3   f (x, y, z) = f x y z
let uncurry3 f x y z = f (x, y, z)

(* -------------------------------------------------------------------- *)
let copy (x : 'a) : 'a =
  Obj.obj (Obj.dup (Obj.repr x))

(* -------------------------------------------------------------------- *)
let reffold (f : 'a -> 'b * 'a) (r : 'a ref) : 'b =
  let (x, v) = f !r in r := v; x

let postincr (i : int ref) = incr i; !i

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
let t2_map (f : 'a -> 'b) (x, y) =
  (f x, f y)

let t3_map (f : 'a -> 'b) (x, y, z) =
  (f x, f y, f z)

(* -------------------------------------------------------------------- *)
let in_seq1 (x : 'a) = [x]

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
let int_of_bool (b : bool) = if b then 1 else 0

(* -------------------------------------------------------------------- *)
let proj3_1 (x, _, _) = x
let proj3_2 (_, x, _) = x
let proj3_3 (_, _, x) = x

let proj4_1 (x, _, _, _) = x
let proj4_2 (_, x, _, _) = x
let proj4_3 (_, _, x, _) = x
let proj4_4 (_, _, _, x) = x

let fst_map (f : 'a -> 'c) ((x, y) : 'a * 'b) =
  (f x, y)

let snd_map (f : 'b -> 'c) ((x, y) : 'a * 'b) =
  (x, f y)

let pair_equal tx ty (x1, y1) (x2, y2) =
  (tx x1 x2) && (ty y1 y2)

let swap (x, y) = (y, x)

(* -------------------------------------------------------------------- *)
module Option = BatOption

(* -------------------------------------------------------------------- *)
let opt_equal (f : 'a -> 'a -> bool) o1 o2 =
  match o1, o2 with
  | Some x1, Some x2 -> f x1 x2
  | None   , None    -> true
  | _      , _       -> false

(* -------------------------------------------------------------------- *)
let none = None
let some = fun x -> Some x

let is_none = function None   -> true | _ -> false
let is_some = function Some _ -> true | _ -> false

let funnone (_ : 'a) : 'b option = None

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

let oif (test : 'a -> bool) (x : 'a option) =
  match x with None -> false | Some x -> test x

let oget ?exn (x : 'a option) =
  match x, exn with
  | None  , None     -> assert false
  | None  , Some exn -> raise exn
  | Some x, _        -> x

let oall2 f x y =
  match x, y with
  | Some x, Some y -> f x y
  | None  , None   -> true
  | _     , _      -> false

let oeq f o1 o2 =
  match o1, o2 with
  | None   , None    -> true
  | Some x1, Some x2 -> f x1 x2
  | _      , _       -> false

let ocompare f o1 o2 =
  match o1, o2 with
  | None   , None    -> 0
  | None   , Some _  -> -1
  | Some _ , None    -> 1
  | Some x1, Some x2 -> f x1 x2

module OSmart = struct
  let omap (f : 'a -> 'b) (x : 'a option) =
    match x with
    | None   -> x
    | Some y ->
        let y' = f y in
          if y == y' then x else Some y'

  let omap_fold (f : 'a -> 'b -> 'a * 'c) (v : 'a) (x : 'b option) =
    match x with
    | None   -> (v, x)
    | Some y ->
        let (v, y') = f v y in
          (v, if y == y' then x else Some y')
end

(* -------------------------------------------------------------------- *)
type ('a, 'b) tagged = Tagged of ('a * 'b option)

let tg_val (Tagged (x, _)) = x
let tg_tag (Tagged (_, t)) = t
let tg_map f (Tagged (x, t)) = Tagged (f x, t)
let notag x = Tagged (x, None)

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
module OneShot : sig
  type t

  val mk  : (unit -> unit) -> t
  val now : t -> unit
end = struct
  type t = unit Lazy.t

  let mk (f : unit -> unit) : t =
    Lazy.from_fun f

  let now (susp : t) : unit =
    Lazy.force susp
end

(* -------------------------------------------------------------------- *)
module Counter : sig
  type t

  val create : unit -> t
  val next   : t -> int
end = struct
  type t = {
    mutable state : int;
  }

  let create () = { state = 0; }

  let next (state : t) =
    let aout = state.state in
      state.state <- state.state + 1;
      aout
end

(* -------------------------------------------------------------------- *)
module Disposable : sig
  type 'a t

  exception Disposed

  val create  : ?cb:('a -> unit) -> 'a -> 'a t
  val get     : 'a t -> 'a
  val dispose : 'a t -> unit
end = struct
  type 'a t = ((('a -> unit) option * 'a) option) ref

  exception Disposed

  let get (p : 'a t) =
    match !p with
    | None        -> raise Disposed
    | Some (_, x) -> x

  let dispose (p : 'a t) =
    let do_dispose p =
      match p with
      | Some (Some cb, x) -> cb x
      | _ -> ()
    in

    let oldp = !p in
      p := None; do_dispose oldp

  let create ?(cb : ('a -> unit) option) (x : 'a) =
    let r = ref (Some (cb, x)) in
      Gc.finalise (fun r -> dispose r) r; r
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
  let ohead = Exceptionless.hd
  let otail = Exceptionless.tl
  let olast = Exceptionless.last
  let ofind = Exceptionless.find
  let opick = Exceptionless.find_map

  let ocons o xs = match o with None -> xs | Some x -> x :: xs

  (* ------------------------------------------------------------------ *)
  let oindex (f : 'a -> bool) (xs : 'a list) : int option =
    Exceptionless.findi (fun _ -> f) xs |> omap fst

  let orindex (f : 'a -> bool) (xs : 'a list) : int option =
    omap (fun i -> List.length xs - i - 1) (oindex f (List.rev xs))

  (* ------------------------------------------------------------------ *)
  module Parallel = struct
    let iter2i f xs ys =
      let rec doit i = function
        | [], [] -> ()
        | x :: xs, y :: ys -> f i x y; doit (i + 1) (xs, ys)
        | _, _ -> failwith "List.iter2i"
      in doit 0 (xs, ys)

    let rec filter2 f la lb =
      match la, lb with
      | [], [] -> [], []
      | a :: la, b :: lb ->
          let ((la, lb) as r) = filter2 f la lb in
          if f a b then (a :: la, b :: lb) else r
      | _, _ -> invalid_arg "List.filter2"

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

    let rec iter2o f xs ys =
      match xs, ys with
      | []   , []    -> ()
      | x::xs, []    -> f (Some x) (None  ); iter2o f xs []
      | []   , y::ys -> f (None  ) (Some y); iter2o f [] ys
      | x::xs, y::ys -> f (Some x) (Some y); iter2o f xs ys

    let all2 (f : 'a -> 'b -> bool) xs ys =
      let rec all2 = function
        | ([]     , []     ) -> true
        | (x :: xs, y :: ys) -> (f x y) && (all2 (xs, ys))
        | (_      , _      ) -> false
      in all2 (xs, ys)

    let prefix2 =
      let rec prefix2 (r1, r2) xs ys =
        match xs, ys with
        | [], _ | _, [] -> (List.rev r1, xs), (List.rev r2, ys)
        | x::xs, y::ys  -> prefix2 (x::r1, y::r2) xs ys
      in fun xs ys -> prefix2 ([], []) xs ys
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
  
  let mbfilter (p : 'a -> bool) (s : 'a list) =
    match s with [] | [_] -> s | _ -> List.filter p s

  let rec fusion f xs ys =
    match xs, ys with
    | zs, [] | [], zs  -> zs
    | x :: xs, y :: ys -> let z = f x y in z :: (fusion f xs ys)

  let pivot_at n l =
    let rec aux r n l =
      match n, l with
      | _, [] -> raise Not_found
      | 0, x::l -> r, x, l
      | _, x::l -> aux (x::r) (n-1) l
    in if n < 0 then invalid_arg "List.pivot_at"; aux [] n l

  let find_pivot f xs =
    let rec aux acc xs =
      match xs with
      | [] -> raise Not_found
      | y :: ys -> if f y then acc, y, ys else aux (y::acc) ys
    in aux [] xs

  let rec pmap (f : 'a -> 'b option) (xs : 'a list) =
    match xs with
    | []      -> []
    | x :: xs -> let v = f x in ocons v (pmap f xs)

  let rev_pmap (f : 'a -> 'b option) (xs : 'a list) =
    let rec aux acc xs =
      match xs with
      | []      -> acc
      | x :: xs -> aux (ocons (f x) acc) xs
    in aux [] xs

  let mapi_fold f a xs =
    let a  = ref a in
    let xs = List.mapi (fun i b ->
      let (a', b') = f i !a b in a := a'; b')
      xs
    in (!a, xs)

  let map_fold f a xs =
    mapi_fold (fun (_ : int) x -> f x) a xs

  let rec fpick (xs : (unit -> 'a option) list) =
    match xs with
    | []      -> None
    | x :: xs -> begin
        match x () with
        | None   -> fpick xs
        | Some v -> Some v
    end

  let rec is_unique ?(eq = (=)) (xs : 'a list) =
    match xs with
    | []      -> true
    | x :: xs -> not (List.exists (eq x) xs) && (is_unique ~eq xs)

  let sum  xs = List.fold_left (+)  0  xs

  let rotate (d : [`Left|`Right]) (i : int) (xs : 'a list) =
    if i < 0 then invalid_arg "List.rotate: [i < 0]";
    let i = i mod List.length xs in

    if i = 0 then (0, xs) else

    let mrev   = match d with `Left -> identity | `Right -> rev in
    let hd, tl = takedrop i (mrev xs) in
    (i, mrev (tl @ hd))

  (* ------------------------------------------------------------------ *)
  let ksort ?(stable = false) ?(rev = false) ~key ~cmp xs =
    let cmp  =
      match rev with
      | false -> (fun x y -> cmp (key x) (key y))
      | true  -> (fun y x -> cmp (key x) (key y)) in
    let sort = if stable then List.stable_sort else List.sort in
    sort cmp xs

  (* ------------------------------------------------------------------ *)
  let fst xs = List.map fst xs
  let snd xs = List.map snd xs
end

(* -------------------------------------------------------------------- *)
module Parray = struct
  include Array

  type 'a t = 'a array

  let empty = [||]

  let of_array = Array.copy

  let fmap (f : 'a -> 'b) (xs : 'a list) =
    Array.map f (of_list xs)

  let split a =
    (Array.init (Array.length a) (fun i -> fst a.(i)),
     Array.init (Array.length a) (fun i -> snd a.(i)))

  let iter2 (f : 'a -> 'b -> unit) a1 a2 =
    for i = 0 to (min (length a1) (length a2)) - 1 do
      f a1.(i) a2.(i)
    done

  let exists f t =
    let rec aux i t =
      if i < Array.length t then f t.(i) || aux (i+1) t
      else false in
    aux 0 t

  let for_all f t =
    let rec aux i t =
      if i < Array.length t then f t.(i) && aux (i+1) t
      else true in
    aux 0 t
end

(* -------------------------------------------------------------------- *)
module String = struct
  include BatString

  let split_lines = split_on_string ~by:"\n"

  let trim (s : string) =
    let aout = BatString.trim s in
    if s == aout then BatString.copy aout else s

  let rev (s:string) = init (length s) (fun i -> s.[length s - 1 - i])

end

(* -------------------------------------------------------------------- *)
module IO = BatIO

(* -------------------------------------------------------------------- *)
module Buffer = struct
  include BatBuffer

  let from_string ?(size = 0) (s : string) : t =
    let buffer = BatBuffer.create size in
    BatBuffer.add_string buffer s; buffer

  let from_char ?(size = 0) (c : char) : t =
    let buffer = BatBuffer.create size in
    BatBuffer.add_char buffer c; buffer
end

(* -------------------------------------------------------------------- *)
module Os = struct
  let getenv (name : string) =
    try Some (Sys.getenv name) with Not_found -> None

  let listdir (dir : string) =
    BatEnum.fold (fun xs x -> x :: xs) [] (BatSys.files_of dir)
end

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

(* -------------------------------------------------------------------- *)
(* Functions used to add colors to errors and warnings.                 *)

(* for locations *)
let pp_print_bold pp =
  pp_enclose ~pre:"@{<\027[1m>" ~post:"@}" pp

(* for error kind *)
let pp_print_bold_red pp =
  pp_enclose ~pre:"@{<\027[1;31m>" ~post:"@}" pp

(* for warning kind *)
let pp_print_bold_magenta pp =
  pp_enclose ~pre:"@{<\027[1;35m>" ~post:"@}" pp

(* Enabling the interpretation of semantic tags for the error channel, so that
   error and warning messages are printed with colors.
*)
let enable_colors () =
  let mark_open_stag s =
    match s with
    | Format.String_tag s -> s
    | _ -> ""
  in
  let mark_close_stag _ = "\027[m" in
  let stag_functions = Format.{
    mark_open_stag;
    mark_close_stag;
    print_open_stag = (fun _ -> ());
    print_close_stag = (fun _ -> ());
  } in
  Format.pp_set_formatter_stag_functions Format.err_formatter stag_functions;
  Format.pp_set_mark_tags Format.err_formatter true

(* -------------------------------------------------------------------- *)
(* An [error_loc] is either unknown, a single location or a pair of a location
   and a list of locations (this list comes from the inlining pass).
   We could probably just have an [i_loc], though, since we can simulate
   the other cases with a dummy location and an empty list.
*)
type error_loc = Lnone | Lone of Location.t | Lmore of Location.i_loc
type hierror = {
  err_msg      : Format.formatter -> unit; (* a printer of the main error message              *)
  err_loc      : error_loc;                (* the location                                     *)
  err_funname  : string option;            (* the name of the function, if any                 *)
  err_kind     : string;                   (* kind of error (e.g. typing, compilation)         *)
  err_sub_kind : string option;            (* sub-kind (e.g. the name of the compilation pass) *)
  err_internal : bool;                     (* whether the error is unexpected                  *)
}
exception HiError of hierror

(* We fetch from [i_loc] the locations coming from the inlining pass *)
let add_iloc e i_loc =
  let err_loc =
    match e.err_loc with
    | Lnone -> Lmore i_loc
    | Lone loc -> Lmore (loc, snd i_loc)
    | Lmore _ as err_loc -> err_loc (* we already have a more precise location *)
  in
  { e with err_loc }

let pp_hierror fmt e =
  let pp_loc fmt =
    match e.err_loc with
    | Lnone -> ()
    | Lone l -> Format.fprintf fmt "%a:@ " (pp_print_bold Location.pp_loc) l
    | Lmore i_loc -> Format.fprintf fmt "%a:@ " (pp_print_bold Location.pp_iloc) i_loc
  in
  let pp_kind fmt =
    let pp fmt () =
      if e.err_internal then
        Format.fprintf fmt "internal %s" e.err_kind
      else
        Format.fprintf fmt "%s" e.err_kind
    in
    pp_print_bold_red pp fmt ()
  in
  let pp_funname fmt =
    match e.err_funname with
    | Some fn -> Format.fprintf fmt " in function %s" fn
    | None -> ()
  in
  (* this function decides whether we open a new line *)
  let pp_other_line fmt =
    if e.err_internal then
      (* if the error is internal, we go to a new line with an indent *)
      Format.fprintf fmt "@;<1 2>"
    else if e.err_funname <> None || e.err_sub_kind <> None then
      (* if there is at least a funname or a sub-kind, we go to a new line *)
      Format.fprintf fmt "@ "
    else
      (* otherwise, we keep the same line *)
      Format.fprintf fmt " "
  in
  let pp_err fmt =
    match e.err_sub_kind with
    | Some s -> Format.fprintf fmt "%s: %t" s e.err_msg
    | None -> Format.fprintf fmt "%t" e.err_msg
  in
  let pp_post fmt =
    if e.err_internal then
      Format.fprintf fmt "@ Please report at https://github.com/jasmin-lang/jasmin/issues"
  in
  Format.fprintf fmt "@[<v>%t%t%t:%t%t%t@]" pp_loc pp_kind pp_funname pp_other_line pp_err pp_post

(* In general, we want a [loc], that's why it is not optional. If you really
   don't want to give a [loc], pass [Lnone].
*)
let hierror ~loc ?funname ~kind ?sub_kind ?(internal=false) =
  Format.kdprintf
    (fun pp ->
      let err = {
        err_msg = pp;
        err_loc = loc;
        err_funname = funname;
        err_kind = kind;
        err_sub_kind = sub_kind;
        err_internal = internal;
      } in
      raise (HiError err))


(* -------------------------------------------------------------------- *)

type warning = 
  | ExtraAssignment 
  | UseLea
  | IntroduceNone 
  | Always

let warns = ref None

let add_warning (w:warning) () = 
  match !warns with
  | None -> warns  := Some [w]
  | Some ws ->
    if not (List.mem w ws) then
      warns := Some( w :: ws)

let nowarning () = warns := Some []

let to_warn w = 
  match !warns with
  | None -> true
  | Some ws -> w = Always || List.mem w ws 

let warning (w:warning) loc =
  Format.kdprintf (fun pp ->
    if to_warn w then
      let pp_warning fmt = pp_print_bold_magenta pp_string fmt "warning" in
      Format.eprintf "@[<v>%a:@ %t: %t@]@."
        (pp_print_bold Location.pp_iloc)
        loc pp_warning pp)
