open Jasmin
open Prog
open Apron
open Wsize
open Utils

type v_scope = Expr.v_scope
                 
open SafetyUtils
    
(* Memory locations *)
type mem_loc = MemLoc of var

(* (v,ws,i) is the slice [8*i; 8*i + ws[ of v. 
     Note that the slice offset is not scaled on the word-size. *)
type slice = var * wsize * int
             
type atype =
  | Avar of var                     (* Variable *)
  | Aarray of var                   (* Array *)
  | AarraySlice of slice

type mvar =
  | Temp of string * int * ty   (* Temporary variable *)
  | WTemp of string * int * ty  (* Temporary variable (weak updates) *)
  | Mglobal of atype            (* Global variable *)
  | Mlocal of atype             (* Local variable value *)
  | MinLocal of var             (* Local variable initial value *)
  | MvarOffset of var           (* Local variable offset *)
  | MNumInv of L.i_loc          (* Numerical Invariants *)
  | MmemRange of mem_loc        (* Memory location range *)

(*---------------------------------------------------------------*)
(* Must the variable [v] be handled as a weak variable. *)
let weak_update v = 
  let weak_update_kind = function
    | Const -> assert false     (* should not happen *)
    | Stack _
    | Reg _
    | Inline
    | Global -> false in

  match v with
  | Mglobal _ -> false (* global variable are read-only. *)
  | Temp _
  | MNumInv _ -> false

  | Mlocal at -> begin match at with
      | Avar gv | Aarray gv | AarraySlice (gv,_,_) ->
        weak_update_kind gv.v_kind
    end

  | MinLocal gv
  | MvarOffset gv ->  weak_update_kind gv.v_kind 

  | MmemRange _ -> true
  | WTemp _ -> true

(*---------------------------------------------------------------*)
let string_of_mloc = function
  | MemLoc s -> s.v_name

let string_of_atype = function
  | Avar s -> "v_" ^ s.v_name
  | Aarray t -> "a_" ^ t.v_name
  | AarraySlice (t,ws,int) ->
    Format.asprintf "ael_%s_%d_%d" t.v_name (int_of_ws ws) int

let string_of_mvar = function
  | Temp (s, i, _) -> "tmp_" ^ s ^ "_" ^ string_of_int i
  | WTemp (s, i, _) -> "wtmp_" ^ s ^ "_" ^ string_of_int i
  | Mglobal at -> "g_" ^ string_of_atype at
  | MinLocal s -> "inv_" ^ s.v_name
  | Mlocal at -> string_of_atype at
  | MvarOffset s -> "o_" ^ s.v_name
  | MNumInv lt -> "ni_" ^ string_of_int (fst lt.base_loc.loc_start)
  | MmemRange loc -> "mem_" ^ string_of_mloc loc

let pp_mvar fmt v = Format.fprintf fmt "%s" (string_of_mvar v)

(*---------------------------------------------------------------*)
let dummy_mvar = Mlocal (Avar (V.mk "__absint_empty_env"
                                 (Reg(Normal, Direct)) (Bty (U U8)) (L._dummy) []))

(*---------------------------------------------------------------*)
let svariables_ignore vs =
  match String.split_on_char '_' vs with
  | [] -> assert false
  | vs' :: _ -> match String.split_on_char '@' vs' with
    | "inv" :: _ -> true
    | "ael" :: _  -> Config.sc_arr_no_print ()
    | "g" :: _  -> Config.sc_glob_no_print ()
    | _ -> false

let variables_ignore v =
  let vs = Var.to_string v in
  svariables_ignore vs

let mvar_ignore = function
  | MinLocal _ -> true
  | Mlocal (AarraySlice _) -> Config.sc_arr_no_print ()
  | Mglobal _ -> Config.sc_glob_no_print ()
  | _ -> false
    
(*---------------------------------------------------------------*)
let arr_range (v : var) : int = match v.v_ty with
  | Arr (_,i) -> i
  | _ -> assert false

let arr_size v = match v.v_ty with
  | Arr (ws,_) -> ws
  | _ -> assert false

let ty_atype = function
  | Avar s -> s.v_ty
  | Aarray t -> t.v_ty
  | AarraySlice (_,ws,_) -> Bty (U ws)

let ty_mvar = function
  | Temp (_,_,ty) -> ty
  | WTemp (_,_,ty) -> ty
  | MinLocal s -> s.v_ty
  | Mglobal at | Mlocal at -> ty_atype at
  | MvarOffset _ -> Bty Int
  | MNumInv _ -> Bty Int
  | MmemRange _ -> Bty Int

(*---------------------------------------------------------------*)
let of_scope scope at = match scope with
  | Expr.Slocal -> Mlocal  at
  | Expr.Sglob  -> Mglobal at

(* Ignore the [MinLocal _] case. *)
let get_scope = function  
  | Mlocal  _ ->  Expr.Slocal
  | Mglobal _ -> Expr.Sglob
  | _ -> assert false

(* Ignore the [MinLocal _] case. *)
let get_at = function  
  | Mlocal at | Mglobal at -> at
  | _ -> assert false

(*---------------------------------------------------------------*)
(* We log the result to be able to inverse it. *)
let log_var = Hashtbl.create 16
let reset () = Hashtbl.reset log_var
    
let avar_of_mvar a =
  let s = string_of_mvar a in
  if not(Hashtbl.mem log_var s) then
    Hashtbl.add log_var s a;
  Var.of_string s

let mvar_of_svar s =
  try Hashtbl.find log_var s with
  | Not_found ->
    Format.eprintf "mvar_of_svar: unknown variable %s@." s;
    assert false

let mvar_of_avar v =
  let s = Var.to_string v in
  mvar_of_svar s

let mvar_of_scoped_var (s : Expr.v_scope) (uv : var) =
  let at = match uv.v_ty with
    | Bty _ -> Avar uv
    | Arr _ -> Aarray uv in

  of_scope s at

let mvar_of_var (v : int Prog.ggvar) =
  mvar_of_scoped_var v.gs (L.unloc v.gv)

(*---------------------------------------------------------------*)
(* Blasts array elements and arrays. *)
let u8_blast_at ~blast_arrays scope at =
  let ats = match at with
    | Aarray v ->
      if blast_arrays then
        let iws = size_of_ws (arr_size v) in
        let r = arr_range v in
        let vi i = AarraySlice (v,U8,i) in
        List.init (r * iws) vi
      else [at]

    | AarraySlice (v,ws,j) ->
      let iws = size_of_ws ws in
      let vi i = AarraySlice (v,U8,i + j) in
      List.init iws vi
    | _ -> [at]
  in
  List.map (of_scope scope) ats

let u8_blast_var ~blast_arrays v = match v with
  | Mlocal at  -> u8_blast_at ~blast_arrays Expr.Slocal at
  | Mglobal at -> u8_blast_at ~blast_arrays Expr.Sglob  at
  | _ -> [v]

let u8_blast_ats ~blast_arrays scope ats =
  List.concat (List.map (u8_blast_at ~blast_arrays scope) ats)

let u8_blast_vars ~blast_arrays vs =
  List.concat (List.map (u8_blast_var ~blast_arrays) vs)

let rec expand_arr_vars = function
  | [] -> []
  | (Mlocal (Aarray v) as head) :: t | (Mglobal (Aarray v) as head) :: t ->
    begin
      let scope = get_scope head in
      match v.v_ty with
      | Bty _ -> assert false
      | Arr (ws, n) ->
        let wsz = size_of_ws ws in
        List.init n (fun i -> of_scope scope (AarraySlice (v,ws,wsz * i)))
        @ expand_arr_vars t
    end
  | v :: t -> v :: expand_arr_vars t

(*------------------------------------------------------------*)
let is_local_var = function
  | Mlocal (Avar _) -> true
  | _ -> false

let is_offset = function
  | MvarOffset _ -> true
  | _ -> false

let ty_gvar_of_mvar = function
  | Mlocal (Avar v) -> Some v
  | _ -> None

(*------------------------------------------------------------*)
module Mmv = struct
  type t = mvar

  let compare v v' = Stdlib.compare (avar_of_mvar v) (avar_of_mvar v')
  let equal v v' = avar_of_mvar v = avar_of_mvar v'
end

module Mm = Map.Make(Mmv)
module Sm = Set.Make(Mmv)

(*------------------------------------------------------------*)
module Mmlv = struct
  type t = mem_loc

  let compare (MemLoc v) (MemLoc v') = Prog.V.compare v v'
  let equal   (MemLoc v) (MemLoc v') = Prog.V.equal v v'
end

module Mml = Map.Make(Mmlv)
module Sml = Set.Make(Mmlv)



(*********************)
(* Boolean Variables *)
(*********************)

(* A boolean variable is a positive of negative variable (of type [mvar]). *)
module Bvar : sig
  type t
  val compare : t -> t -> int
  val equal : t -> t -> bool

  (* the boolean is true if t is positive. *)
  val make : mvar -> bool -> t

  val not : t -> t

  val is_neg : t -> bool

  val var_name : t -> string

  val get_mv : t -> mvar

  (* Force the boolean variable to be positive *)
  val positive : t -> t

  val print : Format.formatter -> t -> unit
end = struct
  type t = mvar * bool          (* the boolean is true if t is positive. *)

  let compare (bv,b) (bv',b') = 
    match Stdlib.compare b b' with
    | 0 -> Stdlib.compare (avar_of_mvar bv) (avar_of_mvar bv')
    | _ as r -> r

  let equal (bv,b) (bv',b') = 
    avar_of_mvar bv = avar_of_mvar bv' && b = b'

  let make bv b = (bv,b)

  let is_neg (_,b) = not b
      
  let not (bv,b) = (bv,not b)                  
    
  let positive (bv,_) = (bv,true)

  let get_mv (bv,_) = bv
                  
  let var_name (bv,_) = Var.to_string (avar_of_mvar bv)

  let print fmt (bv,b) =
    let v = Var.to_string (avar_of_mvar bv) in
    if b then Format.fprintf fmt "%s" v
    else Format.fprintf fmt "NOT %s" v
end

module Mbv = Map.Make(Bvar)


