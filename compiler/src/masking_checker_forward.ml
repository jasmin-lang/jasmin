open Utils
open Prog
open SecurityAnnotations

module A = Annotations
module S = Syntax
module Pt = Pretyping
module CT = Ct_checker_forward


(* -----------------------------------------------------------*)

type masking = Masking.masking

type signature =
  | Scalar of CT.signature
  | Masked of Masking.signature

type ('info, 'asm) fenv = {
    env_ty       : signature Hf.t;
    env_def      : ('info, 'asm) func list;
  }

let pp_signature fmt = function
  | Scalar s -> CT.pp_signature fmt s
  | Masked s -> Masking.PP.signature fmt s

let set_sig fenv fn signature =
  Format.eprintf "signatue %s : %a@." fn.fn_name pp_signature signature;
  Hf.add fenv.env_ty fn signature


(* -----------------------------------------------------------*)
exception MaskingTypeError of Location.t * (Format.formatter -> unit)
exception MaskingTypeErrorI of Location.i_loc * (Format.formatter -> unit)

let error ~loc =
  Format.kdprintf (fun msg ->
      raise (MaskingTypeError (loc, msg)))

let ierror ~iloc =
  Format.kdprintf (fun msg ->
      raise (MaskingTypeErrorI (iloc, msg)))

let check_sig_annot fd sig_annot =
  match sig_annot with
  | None -> ()
  | Some s ->
      let sargs = List.length s.arguments in
      let sret  = List.length s.results in
      let fargs = List.length fd.f_args in
      let fret  = List.length fd.f_ret in
      if sargs <> fargs then
        error ~loc:fd.f_loc
          "invalid masking signature: the function expect %i arguments and %i are specified" fargs sargs;
      if sret <> fret then
        error ~loc:fd.f_loc
          "invalid masking signature: the function return %i results and %i are specified" fret sret

let get_annot f =
  let sig_annot =
    match Masking.get_signature f.f_annot.f_user_annot with
    (* If the function is annotated with a signature use it *)
    | Some _ as sig_ -> sig_
    (* Else try to recover the signature from variables annotations *)
    | None ->
      if List.exists (fun x -> Option.is_some (Masking.has_sharing_annot x.v_annot)) f.f_args ||
         List.exists (fun x -> Option.is_some (Masking.has_sharing_annot (L.unloc x).v_annot)) f.f_ret then
        let doty x =
          match Masking.has_sharing_annot x.v_annot with
          | Some sz -> Masking.Sharing sz
          | None -> Public in
        let arguments = List.map doty f.f_args in
        let results = List.map (fun x -> doty (L.unloc x)) f.f_ret in
        Some {arguments; results}
      else
        None in
  check_sig_annot f sig_annot;
  sig_annot




(* -----------------------------------------------------------*)
let max iloc m1 m2 =
  match m1, m2 with
  | Masking.Sharing sz1, Masking.Sharing sz2 when sz1 = sz2 -> m1
  | Share pos1, Share pos2 when pos1 = pos2 -> m1
  | _, Public -> m1
  | Public, _ -> m2
  | _, _ -> ierror ~iloc "cannot compare %a and %a" Masking.PP.masking m1 Masking.PP.masking m2

let maxs iloc ms =
  List.fold_left (max iloc) Public ms

let le m1 m2 =
  match m1, m2 with
  | Masking.Sharing sz1, Masking.Sharing sz2 when sz1 = sz2 -> true
  | Share pos1, Share pos2 when pos1 = pos2 -> true
  | Public, _ -> true
  | _, _ -> false

(* -----------------------------------------------------------*)
module Env : sig

  type env
  val empty : env

  val set  : env -> var -> masking -> env
  val seti : env -> var_i -> masking -> env

  val max : L.i_loc -> env -> env -> env
  val le  : env -> env -> bool

  val get : env -> var_i -> masking
  val gget : env -> int ggvar -> masking

  val pp : Format.formatter -> env -> unit
end = struct

  type env =
    { env_v : masking Mv.t }

  let empty =
    { env_v = Mv.empty }

  let get_var env x =
    try
      Mv.find (L.unloc x) env.env_v
    with Not_found -> Public

  let max iloc env1 env2 =
    let merge _ m1 m2 =
      match m1, m2 with
      | None, _ -> m2
      | _, None -> m1
      | Some m1, Some m2 ->
        Some (max iloc m1 m2)
    in
    { env_v  = Mv.merge merge env1.env_v env2.env_v; }

  let le env1 env2 =
    try
      let _ =
        Mv.merge (fun _ m1 m2 ->
            let lvl1 = Option.default Masking.Public m1 in
            let lvl2 = Option.default Masking.Public m2 in
            if le lvl1 lvl2 then None
            else raise Not_found) env1.env_v env2.env_v in
        true
    with Not_found -> false

  let set env x m =
    { env_v = Mv.add x m env.env_v }

  let seti env x m =
     set env (L.unloc x) m

  let get = get_var

  let gget env x =
    if is_gkvar x then get env x.gv
    else Public

  let pp fmt env =
    let pp_ty fmt (x, lvl) =
      Format.fprintf fmt "@[%a : %a@]" (Printer.pp_var ~debug:false) x Masking.PP.masking lvl
    in
    Format.fprintf fmt "@[<v>type = @[%a@]@]"
       (pp_list ";@ " pp_ty) (Mv.bindings env.env_v)
end

(* ----------------------------------------------------------- *)
(*
module FEnv = struct
  type t =
*)
(* ----------------------------------------------------------- *)
(* [ty_expr ~public env e] return [env', lvl] such that [env' |- e : lvl]
   and [env' <= env] i.e for all x, [env'(x) <= env(x)].
   Furthermore [public => lvl = Public.
   Remark we need the property: [env' <= env => env |- e : lvl => env' |- e : lvl]
 *)



let check_share loc msg sh sz pos len =
  if not (sh * sz <= pos && pos + len <= (sh+1) * sz) then
    error ~loc "%s overlap multiple share (sh = %i, sz = %i, pos = %i, len = %i)" msg
       sh sz pos len

let rec ty_expr iloc env (e:expr) =
  match e with
  | Pconst _ | Pbool _ | Parr_init _ -> Masking.Public

  | Pvar x -> Env.gget env x

  | Pget (_, aa, ws, x, e) ->
    begin match Env.gget env x with
    | Public -> Public
    | Share _ as m -> m
    | Sharing sz ->
      let len = size_of_ws ws in
      let loc = L.loc x.gv in
      let pos =
        match get_ofs aa ws e with
        | Some pos -> pos
        | None -> error ~loc "share access with non-constant indice is not suported"
      in
      let sh = pos / sz in
      check_share loc "array access" sh sz pos len;
      Share sh
    end

  | Psub (aa, ws, len, x, e) ->
    begin match Env.gget env x with
    | Public -> Public
    | Share _ as m -> m
    | Sharing sz ->
      let len = arr_size ws len in
      let loc = L.loc x.gv in
      let pos =
        match get_ofs aa ws e with
        | Some pos -> pos
        | None -> error ~loc "share access with non-constant indice is not suported"
      in
      let sh = pos / sz in
      check_share loc "subarray access" sh sz pos len;
      Share sh
    end
  | Pload (_, _, _) ->
    ierror ~iloc "load in expression"

  | Papp1(_o, e)        ->
    ty_expr iloc env e
  | Papp2(_o, e1, e2)   ->
    ty_exprs_max iloc env [e1; e2]
  | PappN(_o, es)       ->
    ty_exprs_max iloc env es
  | Pif(_, e1, e2, e3) -> ty_exprs_max iloc env [e1; e2; e3]

and ty_exprs iloc env es =
  List.map (ty_expr iloc env) es

and ty_exprs_max iloc env es =
  let ms = ty_exprs iloc env es in
  maxs iloc ms

(* -----------------------------------------------------------*)
let ty_lval iloc env lv m =
  match lv with
  | Lnone _ -> env
  | Lvar x ->
    (* If x is a sharing we do not change the type, but we check that the assign value is not a share *)
    begin match Env.get env x, m with
    | Masking.Sharing sz, Masking.Share i ->
      let loc = L.loc x in
      error ~loc "cannot assign a value of type share %i into a sharing %i" i sz;
    | Sharing _, (Sharing _ | Public) -> env
    | _, _ -> Env.seti env x m
    end
  | Lmem(_, _, _, _) ->
    ierror ~iloc "store in expression"

  | Laset(_, aa, ws, x, e) ->
    let loc = L.loc x in
    begin match Env.get env x, m with
    | Public, Public -> env

    | Public, Share _ -> Env.seti env x m
    | Share _, Public -> env
    | Share pos, Share pos' when pos = pos' -> env

    | Sharing _, Public -> env
    | Sharing sz, Share sh ->
      let len = size_of_ws ws in
      let pos =
        match get_ofs aa ws e with
        | Some pos -> pos
        | None -> error ~loc "share access with non-constant indice is not suported"
      in
      check_share loc "array set" sh sz pos len;
      env

    | _ as mx, _ ->
        error ~loc "cannot set a %a into a %a (%a)" Masking.PP.masking m Masking.PP.masking mx
          (Printer.pp_lval ~debug:false) lv
    end

  | Lasub(aa, ws, len, x, e) ->
    let loc = L.loc x in
    begin match Env.get env x, m with
    | Public, Public -> env

    | Share _, Public -> env
    | Share pos, Share pos' when pos = pos' -> env

    | Sharing _, Public -> env
    | Sharing sz, Share sh ->
      let len = arr_size ws len in
      let pos =
        match get_ofs aa ws e with
        | Some pos -> pos
        | None -> error ~loc "share access with non-constant indice is not suported"
      in
      check_share loc "subarray set" sh sz pos len;
      env

    | _ as mx, _ ->
      error ~loc "cannot set a %a into a %a (%a)" Masking.PP.masking m Masking.PP.masking mx
        (Printer.pp_lval ~debug:false) lv
    end


let ty_lvals iloc env xs lvls =
  List.fold_left2 (ty_lval iloc) env xs lvls

let ty_lvals1 iloc env xs lvl =
  List.fold_left (fun env x -> ty_lval iloc env x lvl) env xs

(* [ty_instr env i] return env' such that env |- i : env' *)

let get_max_shares iloc ms =
  match maxs iloc ms with
  | Masking.Sharing _ -> ierror ~iloc "scalar function can't be applied to sharing"
  | _ as m -> m

let to_ct_ty = function
  | Masking.Sharing _ -> assert false
  | Share _ -> CT.secret
  | Public -> CT.public

let of_ct_ty m lvl =
  if CT.is_public lvl then Masking.Public
  else m

let check_ct_tys iloc elvls ftys =
  let doit elvl ty =
    if CT.is_public ty && not (CT.is_public elvl) then
      ierror ~iloc "Some arguments need to be public"
  in
  List.iter2 doit elvls ftys

let check_subtypes iloc ems ms =
  let doit em m =
    if not (le em m) then
    ierror ~iloc "bad type for argument" in
  List.iter2 doit ems ms

let rec ty_instr fenv env i =
  let iloc = i.i_loc in
  match i.i_desc with
  | Cassgn(x, _, _, e) ->
    let m = ty_expr iloc env e in
    ty_lval iloc env x m

  | Copn (_, _, Sopn.Opseudo_op (Odeclassify _), [ _ ]) ->
     assert false

  | Copn(xs, _, _, es) ->
    let m = ty_exprs_max iloc env es in
    ty_lvals1 iloc env xs m

  | Csyscall(_xs, RandomBytes _, _es) ->
    ierror ~iloc "Random bytes"

  (* We ignore the contents of assertion *)
  | Cassert _ -> env

  | Cif(_e, c1, c2) ->
    let env1 = ty_cmd fenv env c1 in
    let env2 = ty_cmd fenv env c2 in
    Env.max iloc env1 env2

  | Cfor(_, _, _) ->
    assert false (* This check should be done after loop unrolling *)

  | Cwhile(_, c1, _e, _, c2) ->
    (* c1; while e do c2; c1 *)
    (* G |- c1 : G1   G1 |- e : public   G1 |- c2 : G2 <= G
       -----------------------------------------------
       G |- while c1 e c2 : G'
     *)

    let rec loop env =
      let env1 = ty_cmd fenv env c1 in   (* env |- c1 : env1 *)
      let env2 = ty_cmd fenv env1 c2 in  (* env1 |- c2 : env2 *)
      if Env.le env2 env then env1
      else loop (Env.max iloc env2 env) in
    loop env

  | Ccall (xs, f, es) ->
    let ms = ty_exprs iloc env es in
    begin match get_fun fenv f with
    | Scalar fty ->
        let m = get_max_shares iloc ms in
        let elvls = List.map to_ct_ty ms in
        check_ct_tys iloc elvls (CT.inputs fty);
        let olvls = CT.instanciate_fty fty elvls in
        let oms = List.map (of_ct_ty m) olvls in
        ty_lvals iloc env xs oms
    | Masked fty ->
      check_subtypes iloc ms fty.arguments;
      ty_lvals iloc env xs fty.results
    end

and ty_cmd fenv env c =
  List.fold_left (fun env i -> ty_instr fenv env i) env c

and get_fun fenv f =
  try Hf.find fenv.env_ty f
  with Not_found ->
    let fty = ty_fun fenv f in
    set_sig fenv f fty;
    fty

and ty_fun fenv fn =
(*  Format.eprintf "ty_fun %s@." fn.fn_name; *)
  let f = List.find (fun f -> F.equal f.f_name fn) fenv.env_def in
  let fty = Option.get (get_annot f) in
  (* Check the body only if the function is not annotated with "msk_assume" *)
  if (Masking.has_assume_annot f.f_annot.f_user_annot) then
    Format.eprintf "masking %s assumed@." f.f_name.fn_name
  else
    begin
      Format.eprintf "type checking %s@." f.f_name.fn_name;
      let env = List.fold_left2 Env.set Env.empty f.f_args fty.arguments in
      let locals = locals f in
      let add_local x env =
        match Masking.has_sharing_annot x.v_annot with
        | Some sz -> Env.set env x (Sharing sz)
        | None -> env in
      let env = Sv.fold add_local locals env in
      let env = ty_cmd fenv env f.f_body in
      let rty = List.map (Env.get env) f.f_ret in
      if not (List.for_all2 le rty fty.results) then
        error ~loc:(f.f_loc) "bad return masked type"
    end;
  Masked fty

let ty_prog (prog: ('info, 'asm) prog) =
  let ftys, err = CT.ty_prog (fun _ -> true) ~infer:true prog [] in
  begin match err with
  | Some (loc, e) -> error ~loc "%a" (fun fmt () -> e fmt) ()
  | None -> ()
  end;
  Format.eprintf "Masking CT check done %i@." (List.length ftys);
  let fenv = {
      env_ty = Hf.create 103;
      env_def = List.map fst ftys;
    } in

  List.iter
    (fun (f, fty) ->
      if get_annot f = None then
        begin
          set_sig fenv f.f_name (Scalar fty);
          Format.eprintf "add scalar %s@." f.f_name.fn_name
        end) ftys;

  Format.eprintf "Check masking@.";
  List.map (fun f ->
      get_fun fenv f.f_name) fenv.env_def
