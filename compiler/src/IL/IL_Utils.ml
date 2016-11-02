(* * Utility functions for intermediate language *)

(* ** Imports and abbreviations *)
open Core_kernel.Std
open IL_Lang
open Arith
open Util

module L = ParserUtil.Lexing
module DS = Dest.Set
module SS = String.Set
module PS = Param.Set

(* ** Equality, indicator, accessor and mapping functions
 * ------------------------------------------------------------------------ *)

let dest_to_src d = Src(d)

let equal_pop_u64  x y = compare_pop_u64  x y = 0
let equal_pexpr    x y = compare_pexpr    x y = 0
let equal_dexpr    x y = compare_dexpr    x y = 0
let equal_pop_bool x y = compare_pop_bool x y = 0
let equal_pcond    x y = compare_pcond    x y = 0
let equal_fcond    x y = compare_fcond    x y = 0
let equal_op       x y = compare_op       x y = 0
let equal_ty       x y = compare_ty       x y = 0

let equal_src        x y = compare_src        x y = 0
let equal_dest       x y = compare_dest       x y = 0
let equal_base_instr x y = compare_base_instr x y = 0

let is_src_imm = function Imm _ -> true | _ -> false

let get_src_dest_exn = function Imm _ -> assert false | Src(d) -> d

let set_info_instr i = function
  | Block(bis,_)      -> Block(bis,i)
  | For(iv,lb,ub,s,_) -> For(iv,lb,ub,s,i)
  | If(c,s1,s2,_)     -> If(c,s1,s2,i)
  | While(wt,c,s,_)   -> While(wt,c,s,i)

let get_info_instr = function
  | Block(_,i)     -> i
  | For(_,_,_,_,i) -> i
  | If(_,_,_,i)    -> i
  | While(_,_,_,i) -> i

let map_info_instr ~f = function
  | Block(bis,i)      -> Block(bis,f i)
  | For(iv,lb,ub,s,i) -> For(iv,lb,ub,s,f i)
  | If(c,s1,s2,i)     -> If(c,s1,s2,f i)
  | While(wt,c,s,i)   -> While(wt,c,s,f i)

let tinfo_of_var v = (v.Var.stor, v.Var.ty)

let mk_param (l,(s,si)) =
  assert (si="");
  { Param.name = Pname.mk s; Param.ty = TInvalid; Param.loc = l }

let mk_var (l,(s,si)) =
  let num = if si="" then 0 else int_of_string si in
  { Var.name = Vname.mk s; Var.ty = TInvalid;
    Var.loc = l; Var.stor = SInvalid; Var.num=num }

let mk_fname (s,si) =
  assert (si="");
  Fname.mk s

let map_func modul fname ~f =
  { modul with
    m_funcs = Map.change modul.m_funcs fname
                ~f:(function | None        -> assert false
                             | Some(func) -> Some(f func)) }

let get_fundef ~err_s func =
  match func with
  | Foreign(_) -> failwith err_s
  | Native(fd) -> fd

(* ** Exceptions
 * ------------------------------------------------------------------------ *)

exception TypeError of L.loc * string

let failloc loc s = raise (TypeError(loc,s))

let failloc_ loc fmt =
  let buf  = Buffer.create 127 in
  let fbuf = F.formatter_of_buffer buf in
  F.kfprintf
    (fun _ ->
      F.pp_print_flush fbuf ();
      let s = Buffer.contents buf in
      failloc loc s)
    fbuf fmt

(* ** Operator view
 * ------------------------------------------------------------------------ *)

type op_view =
  | V_ThreeOp of three_op *               dest * src * src
  | V_Umul    of            dest        * dest * src * src
  | V_Carry   of carry_op * dest option * dest * src * src * src option
  | V_Cmov    of bool     *               dest * src * src * src
  | V_Shift   of dir      * dest option * dest * src * src

let view_op o ds ss =
  match o, ds, ss with

  | ThreeOp(o), [d1], [s1;s2] -> V_ThreeOp(o,d1,s1,s2)
  | ThreeOp(_), _,     _      -> assert false
    
  | Umul, [d1;d2], [s1;s2]    -> V_Umul(d1,d2,s1,s2)
  | Umul, _,       _          -> assert false
 
  | Carry(co), ds, ss ->
    let d1, d2 = match ds with
      | [d1;d2] -> Some d1,d2
      | [d2]    -> None,d2
      | _       -> assert false
    in
    let s1, s2, s3 = match ss with
      | [s1;s2;s3] -> s1,s2,Some(s3)
      | [s1;s2]    -> s1,s2,None
      | _          -> assert false
    in
    V_Carry(co,d1,d2,s1,s2,s3)
 
  | Cmov(neg), [d1], [s1;s2;s3] -> V_Cmov(neg,d1,s1,s2,s3) 
  | Cmov(_),    _,   _          -> assert false

  | Shift(dir), [d1],    [s1;s2] -> V_Shift(dir,None,d1,s1,s2)
  | Shift(dir), [d1;d2], [s1;s2] -> V_Shift(dir,Some(d1),d2,s1,s2)
  | Shift(_),   _,    _       -> assert false

(* ** Misc. utility functions
 * ------------------------------------------------------------------------ *)

let parse_value s =
  let open MParser in
  let u64 =
    many1 digit >>= fun s ->
    optional (char 'L') >>
    return (U64.of_string (String.of_char_list s))
  in
  let value =
    choice
      [ (u64 >>= fun u -> return (Vu64 u))
      ; (char '[' >>= fun _ ->
        (sep_by u64 (char ',' >> optional (char ' '))) >>= fun vs ->
        char ']' >>= fun _ ->
        let vs = U64.Map.of_alist_exn (List.mapi vs ~f:(fun i v -> (U64.of_int i, v))) in
        return (Varr(vs))) ]
  in
  match parse_string (value >>= fun x -> eof >>$ x) s () with
  | Success t   -> t
  | Failed(s,_) -> failwith_ "parse_value: failed for %s" s

(* ** Positions
 * ------------------------------------------------------------------------ *)

type pos = int list
  [@@deriving compare,sexp]

let pp_pos fmt pos = F.fprintf fmt "[%a]" (pp_list "," pp_int) pos

module Pos = struct
  module T = struct
    type t = pos [@@deriving compare,sexp]
    let compare = compare_pos
    let hash v = Hashtbl.hash v
  end
  include T
  include Comparable.Make(T)
  include Hashable.Make(T)
end
