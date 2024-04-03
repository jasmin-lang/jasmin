(* -------------------------------------------------------------------- *)
open Lexing

(* -------------------------------------------------------------------- *)
type t = {
  loc_fname : string;
  loc_start : int * int;
  loc_end   : int * int;
  loc_bchar : int;
  loc_echar : int;
}

let _dummy = {
  loc_fname = "";
  loc_start = (-1, -1);
  loc_end   = (-1, -1);
  loc_bchar = -1;
  loc_echar = -1;
}

type i_loc = {
    uid_loc  : int;
    base_loc : t;
    stack_loc: t list;
  }

(* -------------------------------------------------------------------- *)
let make (p1 : position) (p2 : position) =
  let mkpos (p : position) =
    (p.pos_lnum, p.pos_cnum - p.pos_bol)
  in
    { loc_fname = p1.pos_fname;
      loc_start = mkpos p1    ;
      loc_end   = mkpos p2    ;
      loc_bchar = p1.pos_cnum ;
      loc_echar = p2.pos_cnum ; }

let of_lexbuf (lb : lexbuf) =
  let p1 = Lexing.lexeme_start_p lb in
  let p2 = Lexing.lexeme_end_p lb in
  make p1 p2

let tostring_pos ?(full=false) (p : t) =
  if full then
    if p.loc_start = p.loc_end then
      Printf.sprintf "line %d (%d)"
        (fst p.loc_start) (snd p.loc_start)
    else if fst p.loc_start = fst p.loc_end then
      Printf.sprintf "line %d (%d-%d)"
        (fst p.loc_start) (snd p.loc_start) (snd p.loc_end)
    else
      Printf.sprintf "line %d (%d) to line %d (%d)"
        (fst p.loc_start) (snd p.loc_start)
        (fst p.loc_end  ) (snd p.loc_end  )
  else
    if fst p.loc_start = fst p.loc_end then
      Printf.sprintf "line %d"
        (fst p.loc_start)
    else
      Printf.sprintf "line %d to line %d"
        (fst p.loc_start)
        (fst p.loc_end  )

let tostring ?full (p : t) =
  let spos = tostring_pos ?full p in
  Printf.sprintf "\"%s\", %s" p.loc_fname spos

let pp_loc ?full fmt (p:t) =
  Format.fprintf fmt "%s" (tostring ?full p)

let pp_sloc fmt (p:t) =
  Format.fprintf fmt "line %d" (fst p.loc_start)

let pp_iloc ?full fmt { base_loc = l; stack_loc = ls; _ } =
  let last = ref _dummy in
  let pp_loc fmt l =
    if !last.loc_fname <> l.loc_fname then pp_loc ?full fmt l
    else Format.fprintf fmt "%s" (tostring_pos ?full l);
    last := l in
  let pp_sep fmt () = Format.fprintf fmt "@ from " in
  Format.fprintf fmt "@[<v>%a@]" (Format.pp_print_list ~pp_sep pp_loc) (l::ls)

let pp_iloc_short = pp_iloc ~full:false

let tostring = tostring ~full:true
let pp_loc = pp_loc ~full:true
let pp_iloc = pp_iloc ~full:true


let isdummy (p : t) =
  p.loc_bchar < 0 || p.loc_echar < 0

let merge (p1 : t) (p2 : t) =
  if isdummy p1 then p2
  else if isdummy p2 then p1
  else
    { loc_fname = p1.loc_fname;
      loc_start = min p1.loc_start p2.loc_start;
      loc_end   = max p1.loc_end   p2.loc_end  ;
      loc_bchar = min p1.loc_bchar p2.loc_bchar;
      loc_echar = max p1.loc_echar p2.loc_echar; }

let mergeall (p : t list) =
  match p with
  | []      -> _dummy
  | t :: ts -> List.fold_left merge t ts


(* -------------------------------------------------------------------- *)
type 'a located = {
  pl_loc  : t;
  pl_desc : 'a;
}

(* -------------------------------------------------------------------- *)
let loc    x = x.pl_loc
let unloc  x = x.pl_desc
let unlocs x = List.map unloc x

let lmap f x =
  { x with pl_desc = f x.pl_desc }

let mk_loc loc x =
  { pl_loc = loc; pl_desc = x; }

(* -------------------------------------------------------------------- *)
exception LocError of t * exn

let locate_error loc exn =
  match exn with
  | LocError _ -> raise exn
  | _ -> raise (LocError(loc,exn))

let set_loc loc f x =
  try f x with e -> locate_error loc e

let set_oloc oloc f x =
  match oloc with
  | None     -> f x
  | Some loc -> set_loc loc f x

(* -------------------------------------------------------------------- *)
let i_loc_uid = ref 0

let i_loc l ls =
  incr i_loc_uid;
  {
    uid_loc = !i_loc_uid;
    base_loc = l;
    stack_loc = ls
  }

let i_loc0 l = i_loc l []

let of_loc a = i_loc0 (loc a)

let i_dummy = i_loc0 _dummy

let refresh_i_loc il = i_loc il.base_loc il.stack_loc
