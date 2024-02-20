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
let oget ?exn (x : 'a option) =
  match x, exn with
  | None  , None     -> assert false
  | None  , Some exn -> raise exn
  | Some x, _        -> x

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

  let opicki f xs =
    let rec loop i f xs =
      match xs with
      | [] ->
          None
      | x :: xs ->
          begin
            match f i x with
            | None -> loop (i + 1) f xs
            | Some y -> Some (i, y)
          end
    in
    loop 0 f xs

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

  (* ------------------------------------------------------------------ *)
  let modify_last f xs = modify_at (length xs - 1) f xs

end

(* -------------------------------------------------------------------- *)
module String = struct
  include BatString

  let drop_end n s = sub s 0 (length s - n)
end

(* -------------------------------------------------------------------- *)
module IO = BatIO

(* -------------------------------------------------------------------- *)
module Buffer = BatBuffer

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
    | Lone loc -> Lmore (Location.i_loc loc i_loc.stack_loc)
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
(** Splits a time in seconds into hours, minutes, seconds, and centiseconds.
  Number of hours must be below one hundred. *)
let hmsc f =
  let open Float in
  let cut f n =
    let r = rem f n in
    to_int r, (f -. r) /. n
  in
  let c, f = modf f in
  let s, f = cut f 60. in
  let m, f = cut f 60. in
  let h, f = cut f 100. in
  assert (f = 0.);
  h, m, s, to_int (100. *. c)

let pp_now =
  let open Unix in
  let timestamp = ref (-1.) in
  let pp_elapsed fmt now =
    let old = !timestamp in
    if old >= 0. then begin
      let diff = now -. old in
      let h, m, s, c = hmsc diff in
      Format.fprintf fmt "|";
      if h > 0 then Format.fprintf fmt "%2dh" h else Format.fprintf fmt "   ";
      if h > 0 || m > 0 then Format.fprintf fmt "%2dm" m else Format.fprintf fmt "   ";
      Format.fprintf fmt "%2ds%02d" s c
    end;
    timestamp := now
  in
  fun fmt ->
    let  now = gettimeofday () in
    let { tm_hour; tm_min; tm_sec; _ } = localtime now in
  Format.fprintf fmt "[%02d:%02d:%02d%a]" tm_hour tm_min tm_sec pp_elapsed now

(* -------------------------------------------------------------------- *)

type warning = 
  | ExtraAssignment 
  | UseLea
  | IntroduceNone 
  | IntroduceArrayCopy
  | SimplifyVectorSuffix
  | DuplicateVar 
  | UnusedVar 
  | SCTchecker
  | Deprecated
  | Experimental
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
      let pp_iloc fmt d =
        if not (Location.isdummy d.Location.base_loc) then
          Format.fprintf fmt "%a@ " (pp_print_bold Location.pp_iloc) d in
      Format.eprintf "@[<v>%a%t: %t@]@."
        pp_iloc loc
        pp_warning pp)
