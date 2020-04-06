open Utils
open Prog
open Apron
open ToEC
open Wsize

exception Aint_error of string

let debug a = if !Glob_options.debug then a () else ()

let () = debug (fun () ->
    Format.eprintf "Debug on: record backtrace@;";
    Printexc.record_backtrace true);;

(* REM *)
(* Printexc.record_backtrace true *)

let hndl_apr_exc e = match e with
  | Manager.Error exclog as e ->
    Printexc.print_backtrace stderr;
    Format.eprintf "@[<v>Apron Error Message:@;@[%a@]@;@]"
      Manager.print_exclog exclog;
    raise e
  | _ as e -> raise e


(***********************)
(* Analysis Parameters *)
(***********************)

module Aparam = struct
  (* Number of unrolling of a loop body before applying the widening. Higher
     values yield a more precise (and more costly) analysis. *)
  let k_unroll = 1;;

  assert (k_unroll >= 0)

  (* Rounding used. *)
  let round_typ = Texpr1.Zero

  (* Analysis strategy for abstract calls.
   ** CallWidening is untested ! ** *)
  type abs_call_strategy =
    | CallDirect
    | CallWidening

  let abs_call_strategy = CallDirect

  (* Widening outside or inside loops.
     Remark: if the widening is done inside loops, then termination is not
     guaranteed in general. Nonetheless, if the meet operator is monotonous
     then this should always terminates. *)
  let widening_out = false

  (* Widening with thresholds *)
  let use_threshold = false

  (* Dependency graph includes flow dependencies *)
  let flow_dep = false

  (* Add disjunction with if statement when possible *)
  let if_disj = true


  (***********************)
  (* Printing parameters *)
  (***********************)

  (* Turn on printing of array variables *)
  let arr_no_print = true

  (* Turn on printing of global variables *)
  let glob_no_print = true

  (* Turn on printing of non-relational variables *)
  let nrel_no_print = ref false

  (* Turn on printing of unconstrained variables *)
  let ignore_unconstrained = true
end

(* Turn on printing of only the relational part *)
let only_rel_print = ref false

(*************************)
(* Unique Variable Names *)
(*************************)

module MkUniq : sig

  val mk_uniq : unit func -> unit prog -> (unit func * unit prog) 

end = struct
  let ht_uniq = Hashtbl.create ~random:false 16

  let htv = Hashtbl.create ~random:false 16

  let rec mk_glob (x, i) = (mk_v None x, i)

  and mk_globs globs = List.map mk_glob globs

  and mk_f f_decl =
    { f_decl with
      f_args = List.map (mk_v (Some f_decl.f_name.fn_name)) f_decl.f_args;
      f_body = mk_stmt (Some f_decl.f_name.fn_name) f_decl.f_body;
      f_ret = List.map (mk_v_loc (Some f_decl.f_name.fn_name)) f_decl.f_ret }

  and mk_v fn v =
    if Hashtbl.mem htv (v.v_name, fn) then
      Hashtbl.find htv (v.v_name, fn)
    else if Hashtbl.mem ht_uniq v.v_name then
      let ext = 
        match fn with
        | None -> "##g"
        | Some fn -> "#" ^ fn in
      let nv = V.mk (v.v_name ^ ext) v.v_kind v.v_ty v.v_dloc in
      let () = Hashtbl.add htv (v.v_name, fn) nv in
      nv
    else
      let () = Hashtbl.add ht_uniq v.v_name () in
      let () = Hashtbl.add htv (v.v_name, fn) v in
      v

  and mk_v_loc fn v = L.mk_loc (L.loc v) (mk_v fn (L.unloc v))

  and mk_gv fn v = 
    let fn = if is_gkvar v then None else fn in
    { v with gv = mk_v_loc fn v.gv }

  and mk_lval fn lv = match lv with
    | Lnone _ -> lv
    | Lvar v -> Lvar (mk_v_loc fn v)
    | Lmem (ws,ty,e) -> Lmem (ws, mk_v_loc fn ty, mk_expr fn e)
    | Laset (aa,ws,v,e) -> Laset (aa,ws, mk_v_loc fn v, mk_expr fn e)
    | Lasub _ -> assert false

  and mk_range fn (dir, e1, e2) = (dir, mk_expr fn e1, mk_expr fn e2)

  and mk_lvals fn lvs = List.map (mk_lval fn) lvs

  and mk_instr fn st = { st with i_desc = mk_instr_r fn st.i_desc }

  and mk_instr_r fn st = match st with
    | Cassgn (lv, tag, ty, e) ->
      Cassgn (mk_lval fn lv, tag, ty, mk_expr fn e)
    | Copn (lvls, tag, opn, exprs) ->
      Copn (mk_lvals fn lvls, tag, opn, mk_exprs fn exprs)
    | Cif (e, st, st') ->
      Cif (mk_expr fn e, mk_stmt fn st, mk_stmt fn st')
    | Cfor (v, r, st) ->
      Cfor (mk_v_loc fn v, mk_range fn r, mk_stmt fn st)
    | Ccall (inlinf, lvs, c_fn, es) ->
      Ccall (inlinf, mk_lvals fn lvs, c_fn, mk_exprs fn es)
    | Cwhile (a, st1, e, st2) ->
      Cwhile (a, mk_stmt fn st1, mk_expr fn e, mk_stmt fn st2)

  and mk_stmt fn instrs = List.map (mk_instr fn) instrs

  and mk_expr fn expr = match expr with
    | Pconst _ | Pbool _ | Parr_init _ -> expr
    | Pvar v -> Pvar (mk_gv fn v)
    | Pget (aa,ws, v, e) -> Pget (aa,ws, mk_gv fn v, mk_expr fn e)
    | Psub _             -> assert false
    | Pload (ws, v, e) -> Pload (ws, mk_v_loc fn v, mk_expr fn e)
    | Papp1 (op, e) -> Papp1 (op, mk_expr fn e)
    | Papp2 (op, e1, e2) -> Papp2 (op, mk_expr fn e1, mk_expr fn e2)
    | PappN (op,es) -> PappN (op, List.map (mk_expr fn) es)
    | Pif (ty, e, el, er)  ->
      Pif (ty, mk_expr fn e, mk_expr fn el, mk_expr fn er)

  and mk_exprs fn exprs = List.map (mk_expr fn) exprs

  let mk_uniq main_decl (glob_decls, fun_decls) =
    Hashtbl.clear ht_uniq;
    Hashtbl.clear htv;

    let m_decl = mk_f main_decl in
    (m_decl, (mk_globs glob_decls, List.map mk_f fun_decls))

end


(*******************)
(* Pretty Printers *)
(*******************)

let pp_apr_env ppf e = Environment.print ppf e;;

let rec pp_list ?sep:(msep = Format.pp_print_space) pp_el fmt l = match l with
  | [] -> Format.fprintf fmt ""
  | h :: t -> Format.fprintf fmt "%a%a%a" pp_el h msep ()
                (pp_list ~sep:msep pp_el) t;;

let pp_opt pp_el fmt = function
  | None -> Format.fprintf fmt "None"
  | Some el -> Format.fprintf fmt "Some @[%a@]" pp_el el


(*************)
(* Profiling *)
(*************)

let rec assoc_up s f = function
  | [] -> raise Not_found
  | (a,b) :: t ->
    if a = s then (a, f b) :: t
    else (a,b) :: assoc_up s f t

module Prof : sig
  val record : string -> unit
  val call : string -> float -> unit
  val reset_all : unit -> unit

  val print : Format.formatter -> unit -> unit
end = struct
  let lrec = ref []

  let record s =
    let () = assert (not (List.mem_assoc s !lrec)) in
    lrec := (s,(0,0.)) :: !lrec;;

  let call s t =
    lrec := assoc_up s (fun (x,t') -> (x + 1,t +. t')) !lrec;;

  let reset_all () = lrec := []

  let print fmt () =
    let pp_el fmt (a, (b,f)) =
      Format.fprintf fmt "%10d %s : %1f seconds" b a f in

    Format.fprintf fmt "@[<v>Statistiques:@;@[<v>%a@]@]@."
      (pp_list pp_el) (List.sort (fun (a,(_,f)) (a',(_,f')) ->
          if a = a' then 0
          else if f > f' then -1 else 1) !lrec)
end


(************************)
(* Abstract Environment *)
(************************)

(* Memory locations *)
type mem_loc = MemLoc of var

type atype =
  | Avar of var                     (* Variable *)
  | Aarray of var                   (* Array *)
  | AarrayEl of var * wsize * int   (* Array element *)

type mvar =
  | Temp of string * int * ty   (* Temporary variable *)
  | WTemp of string * int * ty  (* Temporary variable (weak updates) *)
  | Mvalue of atype             (* Variable value *)
  | MinValue of var         (* Variable initial value *)
  | MvarOffset of var       (* Variable offset *)
  | MNumInv of L.t              (* Numerical Invariants *)
  | MmemRange of mem_loc        (* Memory location range *)

let weak_update v = match v with
  | Mvalue _
  | MinValue _
  | Temp _
  | MNumInv _
  | MvarOffset _ -> false
  | MmemRange _ -> true
  | WTemp _ -> true

let string_of_mloc = function
  | MemLoc s -> s.v_name

let string_of_atype = function
  | Avar s -> "v_" ^ s.v_name
  | Aarray t -> "a_" ^ t.v_name
  | AarrayEl (t,ws,int) ->
    Format.asprintf "ael_%s_%d_%d" t.v_name (int_of_ws ws) int

let string_of_mvar = function
  | Temp (s, i, _) -> "tmp_" ^ s ^ "_" ^ string_of_int i
  | WTemp (s, i, _) -> "wtmp_" ^ s ^ "_" ^ string_of_int i
  | MinValue s -> "inv_" ^ s.v_name
  | Mvalue at -> string_of_atype at
  | MvarOffset s -> "o_" ^ s.v_name
  | MNumInv lt -> "ni_" ^ string_of_int (fst lt.loc_start)
  | MmemRange loc -> "mem_" ^ string_of_mloc loc

let pp_mvar fmt v = Format.fprintf fmt "%s" (string_of_mvar v)

let dummy_mvar = Mvalue (Avar (V.mk "__absint_empty_env"
                                 (Reg Direct) (Bty (U U8)) (L._dummy)))


let svariables_ignore vs =
  match String.split_on_char '_' vs with
  | [] -> assert false
  | vs' :: _ -> match String.split_on_char '@' vs' with
    | "inv" :: _ -> true
    | "ael" :: _  -> Aparam.arr_no_print
    | "g" :: _  -> Aparam.glob_no_print
    | _ -> false

let variables_ignore v =
  let vs = Var.to_string v in
  svariables_ignore vs

let arr_range v = match v.v_ty with
  | Arr (_,i) -> i
  | _ -> assert false

let arr_size v = match v.v_ty with
  | Arr (ws,_) -> ws
  | _ -> assert false

let ty_atype = function
  | Avar s -> s.v_ty
  | Aarray t -> t.v_ty
  | AarrayEl (_,ws,_) -> Bty (U ws)

let ty_mvar = function
  | Temp (_,_,ty) -> ty
  | WTemp (_,_,ty) -> ty
  | MinValue s -> s.v_ty
  | Mvalue at -> ty_atype at
  | MvarOffset _ -> Bty Int
  | MNumInv _ -> Bty Int
  | MmemRange _ -> Bty Int

let avar_of_mvar a = string_of_mvar a |> Var.of_string


let u8_blast_at at = match at with
  | Aarray v ->
    let iws = (int_of_ws (arr_size v)) / 8 in
    let r = arr_range v in
    let vi i = Mvalue (AarrayEl (v,U8,i)) in
    List.init (r * iws) vi
  | AarrayEl (v,ws,j) ->
    let iws = (int_of_ws ws) / 8 in
    let vi i = Mvalue (AarrayEl (v,U8,i + iws * j )) in
    List.init iws vi
  | _ -> [Mvalue at]

let u8_blast_var v = match v with
  | Mvalue at -> u8_blast_at at
  | _ -> [v]

let u8_blast_ats ats =
  List.flatten (List.map u8_blast_at ats)

let u8_blast_vars vs =
  List.flatten (List.map u8_blast_var vs)

let rec expand_arr_vars = function
  | [] -> []
  | Mvalue (Aarray v) :: t -> begin match v.v_ty with
      | Bty _ -> assert false
      | Arr (ws, n) -> List.init n (fun i -> Mvalue (AarrayEl (v,ws,i)))
                       @ expand_arr_vars t end
  | v :: t -> v :: expand_arr_vars t

let rec expand_arr_tys = function
  | [] -> []
  | Arr (ws, n) :: t ->
    List.init n (fun _ -> Bty (U ws)) @ expand_arr_tys t
  | v :: t -> v :: expand_arr_tys t

let rec expand_arr_exprs = function
  | [] -> []
  | Pvar v :: t -> begin match (L.unloc v.gv).v_ty with
      | Arr (ws, n) ->
        List.init n (fun i -> Pget (Warray_.AAscale, ws, v, Pconst (B.of_int i)))
        @ expand_arr_exprs t
      | _ -> Pvar v :: expand_arr_exprs t end
  | h :: t -> h :: expand_arr_exprs t

let get_fun_def prog f = List.find_opt (fun x -> x.f_name = f) (snd prog)

let oget = function
  | Some x -> x
  | None -> raise (Failure "Oget")

type apr_env = Apron.Environment.t


(****************)
(* Pre Analysis *)
(****************)

module Pa : sig

  type dp = Sv.t Mv.t

  (* - pa_dp: for each variable, contains the set of variables that can modify
              it. Some dependencies are ignored depending on some heuristic.
     - pa_eq: for each variable v, contains a set of variables that can be equal
              to v (function calls and direct assignments) *)
  type pa_res = { pa_dp : dp;
                  pa_eq : dp;
                  while_vars : Sv.t;
                  if_conds : expr list }

  val dp_v : dp -> var -> Sv.t
  val pa_make : unit func -> unit prog -> pa_res

end = struct
  (* For each variable, we compute the set of variables that can modify it.
     Some dependencies are ignored depending on some heuristic we have. *)
  type dp = Sv.t Mv.t

  type pa_res = { pa_dp : dp;
                  pa_eq : dp;
                  while_vars : Sv.t;
                  if_conds : expr list }

  let dp_v dp v = Mv.find_default Sv.empty v dp

  let add_dep dp v v' ct =
    Mv.add v (Sv.union (Sv.singleton v') (Sv.union ct (dp_v dp v))) dp

  let add_eq eq v v' =
    Mv.add v (Sv.union (Sv.singleton v') (dp_v eq v)) eq

  (* Dependency heuristic for variable assignment *)
  let rec app_expr dp v e ct = match e with
    | Pconst _ -> dp
    | Pbool _ -> dp
    | Parr_init _ -> dp
    | Pvar v' -> 
      if is_gkvar v' then dp (* We ignore global variables *)
      else 
        begin match (L.unloc v'.gv).v_ty with
        | Bty _ -> add_dep dp v (L.unloc v'.gv) ct
        | Arr _ -> dp 
        end

    | Pget _ -> dp  (* We ignore array loads  *)
    | Psub _ -> assert false 

    (* We ignore loads for v, but we compute dependencies of v' in ei *)
    | Pload (_,v',ei) -> app_expr dp (L.unloc v') ei ct

    | Papp1 (_,e1) -> app_expr dp v e1 ct
    | Papp2  (_,e1,e2) -> app_expr (app_expr dp v e1 ct) v e2 ct
    | PappN (_,es) -> List.fold_left (fun dp e -> app_expr dp v e ct) dp es
    | Pif (_,b,e1,e2) ->
      app_expr (app_expr (app_expr dp v b ct) v e1 ct) v e2 ct

  (* State while building the dependency graph:
     - dp : dependency graph
     - dp : potential equalities graph
     - f_done : already analized functions
     - ct : variables in the context (for an example, look at the Cif case) *)
  type pa_st = { dp : dp;
                 eq : dp;
                 while_vars : Sv.t;
                 if_conds : expr list;
                 f_done : Ss.t;
                 ct : Sv.t }

  (* Compute the list of variables occuring in an expression, while updating
     the state during memory loads. *)
  let expr_vars st e =
    let rec aux (acc,st) = function
      | Pconst _ | Pbool _ | Parr_init _ | Pget _ -> acc, st
      | Psub _ -> assert false
      | Pvar v' -> 
        begin match (L.unloc v'.gv).v_ty with
        | Bty _ -> (L.unloc v'.gv) :: acc, st
        | Arr _ -> acc, st 
        end

      (* We ignore loads for v, but we compute dependencies of v' in ei *)
      | Pload (_,v',ei) ->
        let dp = app_expr st.dp (L.unloc v') ei st.ct in
        acc, { st with dp = dp }

      | Papp1 (_,e1) -> aux (acc,st) e1
      | Papp2  (_,e1,e2) -> aux (aux (acc,st) e1) e2
      | PappN (_,es) -> List.fold_left aux (acc,st) es
      | Pif (_,b,e1,e2) -> aux (aux (aux (acc,st) e1) e2) b in

    aux ([],st) e

  let st_merge st1 st2 ct =
    let mdp = Mv.merge (fun _ osv1 osv2 ->
        let sv1,sv2 = odfl Sv.empty osv1, odfl Sv.empty osv2 in
        Sv.union sv1 sv2 |> some) in
    { dp = mdp st1.dp st2.dp;
      eq = mdp st1.eq st2.eq;
      while_vars = Sv.union st1.while_vars st2.while_vars;
      f_done = Ss.union st1.f_done st2.f_done;
      if_conds = st1.if_conds @ st2.if_conds;
      ct = ct }

  let set_ct ct st = { st with ct = ct }

  let rec find_arg v vs es = match vs, es with
    | [],_ | _, [] -> assert false
    | v' :: vs', e' :: es' -> if v' = v then e' else find_arg v vs' es'

  let pa_expr st v e = { st with dp = app_expr st.dp v e st.ct }

  let pa_eq st v e = match e with
    | Pvar v' -> { st with eq = add_eq st.eq v (L.unloc v'.gv)}
    | _ -> st

  let pa_lv st lv e = match lv with
    | Lnone _ | Laset _ -> st   (* We ignore array stores *)
    | Lasub _ -> assert false
    | Lvar v -> pa_expr st (L.unloc v) e

    (* For memory stores, we are only interested in v and ei *)
    | Lmem (_, v, ei) -> pa_expr st (L.unloc v) ei

  let rec pa_instr prog st instr = match instr.i_desc with
    | Cassgn (lv, _, _, e) -> pa_lv st lv e
    | Copn (lvs, _, _, es) -> List.fold_left (fun st lv ->
        List.fold_left (fun st e -> pa_lv st lv e) st es) st lvs

    | Cif (b, c1, c2) ->
      let vs,st = expr_vars st b in
      let st = { st with if_conds = b :: st.if_conds } in

      let st' =
        if Aparam.flow_dep then
          { st with ct = Sv.union st.ct (Sv.of_list vs) }
        else st in

      (* Note that we reset the context after the merge *)
      st_merge (pa_stmt prog st' c1) (pa_stmt prog st' c2) st.ct

    | Cfor (_, _, c) ->
      (* We ignore the loop index, since we do not use widening for loops. *)
      pa_stmt prog st c

    | Cwhile (_, c1, b, c2) ->
      let vs,st = expr_vars st b in

      let st' =
        if Aparam.flow_dep then
          { st with ct = Sv.union st.ct (Sv.of_list vs) }
        else st in

      let st' = { st' with
                  while_vars = Sv.union st'.while_vars (Sv.of_list vs) } in

      (* Again, we reset the context after the merge *)
      pa_stmt prog st' (c1 @ c2)
      |> set_ct st.ct

    | Ccall (_, lvs, fn, es) ->
      let f_decl = get_fun_def prog fn |> oget in

      let st =
        if Ss.mem fn.fn_name st.f_done then st
        else pa_func prog st fn in

      let st = List.fold_left2 (fun st lv ret ->
          pa_lv st lv (Pvar (gkvar ret)))
          st lvs f_decl.f_ret in

      let st = List.fold_left2 pa_expr st f_decl.f_args es in

      List.fold_left2 pa_eq st f_decl.f_args es


  and pa_func prog st fn =
    let f_decl = get_fun_def prog fn |> oget in
    let st = { st with f_done = Ss.add fn.fn_name st.f_done } in
    pa_stmt prog st f_decl.f_body

  and pa_stmt prog st instrs = List.fold_left (pa_instr prog) st instrs

  let pa_make func prog =
    let st = { dp = Mv.empty;
               eq = Mv.empty;
               while_vars = Sv.empty;
               f_done = Ss.empty;
               if_conds = [];
               ct = Sv.empty } in
    let st = pa_func prog st func.f_name in

    debug (fun () ->
        Format.eprintf "@[<v 2>Dependency heuristic graph:@;%a@]@."
          (pp_list (fun fmt (v, sv) -> Format.fprintf fmt "@[<hov 4>%a <-- %a@]"
                       (Printer.pp_var ~debug:true) v
                       (pp_list ( Printer.pp_var ~debug:true))
                       (List.sort (fun v v' ->
                            Pervasives.compare v.v_name v'.v_name)
                           (Sv.elements sv))))
          (List.sort (fun (v,_) (v',_) -> Pervasives.compare v.v_name v'.v_name)
             (Mv.bindings st.dp)));

    { pa_dp = st.dp;
      pa_eq = st.eq;
      while_vars = st.while_vars;
      if_conds = List.sort_uniq Pervasives.compare st.if_conds }
end


(*************)
(* Mpq Utils *)
(*************)

(* Return 2^n *)
let mpq_pow n =
  let c_div = Mpq.of_int 1 in
  let mpq2 = Mpq.of_int 1 in
  Mpq.mul_2exp c_div mpq2 n;
  c_div

(* Return 2^n - y *)
let mpq_pow_minus n y =
  Mpqf.sub (mpq_pow n |> Mpqf.of_mpq) (Mpqf.of_int y)


(****************************)
(* Coeff and Interval Utils *)
(****************************)

let scalar_to_int scal =
  let tent_i = match scal with
    | Scalar.Float f -> int_of_float f
    | Scalar.Mpqf q -> Mpqf.to_float q |> int_of_float
    | Scalar.Mpfrf f -> Mpfrf.to_float f |> int_of_float in
  if Scalar.cmp_int scal tent_i = 0 then Some tent_i
  else None

let interval_to_int int =
  let open Interval in
  if Scalar.equal int.inf int.sup then scalar_to_int int.inf
  else None

let to_int c = match c with
  | Coeff.Scalar s -> Coeff.i_of_scalar s s
  | Coeff.Interval _ -> c

let s_to_mpqf = function
  | Scalar.Float f -> Mpqf.of_float f
  | Scalar.Mpqf x -> x
  | Scalar.Mpfrf f -> Mpfr.to_mpq f

let scalar_add s s' = Scalar.Mpqf (Mpqf.add (s_to_mpqf s) (s_to_mpqf s'))

let coeff_add c c' = match Coeff.reduce c, Coeff.reduce c' with
  | Coeff.Scalar s, Coeff.Scalar s' -> Coeff.Scalar (scalar_add s s')
  | _,_ ->
    match to_int c, to_int c' with
    | Coeff.Interval i, Coeff.Interval i' ->
      Coeff.Interval (Interval.of_scalar
                        (scalar_add i.inf i'.inf)
                        (scalar_add i.sup i'.sup))
    | _ -> assert false


(******************)
(* Texpr1 Wrapper *)
(******************)

module Mmv = struct
  type t = mvar

  let compare v v' = Pervasives.compare (avar_of_mvar v) (avar_of_mvar v')
  let equal v v' = avar_of_mvar v = avar_of_mvar v'
end

module Mm = Map.Make(Mmv)


module Mtexpr : sig
  type unop = Apron.Texpr0.unop
  type binop = Apron.Texpr0.binop
  type typ = Apron.Texpr0.typ
  type round = Apron.Texpr0.round

  type mexpr = private
    | Mcst of Coeff.t
    | Mvar of mvar
    | Munop of unop * mexpr * typ * round
    | Mbinop of binop * mexpr * mexpr * typ * round

  (* Careful, the environment should have already blasted array elements in
     U8 array elements. *)
  type t =  { mexpr : mexpr;
              env : apr_env }

  val to_aexpr : t -> Texpr1.t
  val to_linexpr : t -> apr_env -> Linexpr1.t option

  val cst : apr_env -> Coeff.t -> t
  val var : apr_env -> mvar -> t
  val unop : unop -> t -> t
  val binop : binop -> t -> t -> t

  val get_var_mexpr : mexpr -> mvar list
  val contains_mod : mexpr -> bool

  val extend_environment : t -> apr_env -> t

  val weak_cp : mvar -> int -> mvar
  val weak_transf : int Mm.t -> mexpr -> int Mm.t * mexpr

  val print : Format.formatter -> t -> unit

  val print_mexpr : Format.formatter -> mexpr -> unit
end = struct
  type unop = Texpr0.unop
  type binop = Texpr0.binop
  type typ = Apron.Texpr0.typ
  type round = Apron.Texpr0.round

  type mexpr =
    | Mcst of Coeff.t
    | Mvar of mvar
    | Munop of unop * mexpr * typ * round
    | Mbinop of binop * mexpr * mexpr * typ * round

  type t = { mexpr : mexpr;
             env : apr_env }

  (* Return sum_{j = 0}^{len - 1} (2^8)^(len - 1 - j) * (U8)v[offset + j] *)
  let rec build_term_array v offset len =
    let tv =
      Texpr1.Var (avar_of_mvar (Mvalue (AarrayEl (v,U8,offset + len - 1)))) in
    let ptwo = Texpr1.Cst (Coeff.s_of_mpq (mpq_pow (8 * (len - 1)))) in
    let t = Texpr1.Binop (Texpr1.Mul, ptwo, tv, Texpr1.Int, Aparam.round_typ) in
    if len = 1 then tv
    else Texpr1.Binop (Texpr1.Add,
                       t,
                       build_term_array v offset (len - 1),
                       Texpr1.Int, Aparam.round_typ)

  let rec e_aux = function
    | Mcst c -> Texpr1.Cst c
    | Mvar mvar -> begin match mvar with
        | Mvalue (AarrayEl (v,ws,i)) ->
          build_term_array v (((int_of_ws ws) / 8) * i) ((int_of_ws ws) / 8)
        | _ -> Texpr1.Var (avar_of_mvar mvar) end
    | Munop (op1, a, t, r) -> Texpr1.Unop (op1, e_aux a, t, r)
    | Mbinop (op2, a, b, t, r) -> Texpr1.Binop (op2, e_aux a, e_aux b, t, r)

  let to_aexpr t = Texpr1.of_expr t.env (e_aux t.mexpr)

  let print ppf t = to_aexpr t |> Texpr1.print ppf

  let print_mexpr ppf t = e_aux t |> Texpr1.print_expr ppf

  let cst env c = { mexpr = Mcst c; env = env }

  let var env v = { mexpr = Mvar v; env = env }

  let unop op1 a = { a with
                     mexpr = Munop (op1, a.mexpr, Texpr1.Int, Aparam.round_typ) }

  let binop op2 a b =
    if not (Environment.equal a.env b.env) then
      raise (Aint_error "Environment mismatch")
    else { mexpr = Mbinop (op2, a.mexpr, b.mexpr, Texpr1.Int, Aparam.round_typ);
           env = a.env }

  let weak_cp v i = Temp ("wcp_" ^ string_of_mvar v, i, ty_mvar v)

  let to_linexpr t env =
    let exception Linexpr_failure in

    let rec linexpr t =
      match t with
      | Mvar m ->
        let l = Linexpr1.make env in
        Linexpr1.set_list l [Coeff.s_of_int 1 ,avar_of_mvar m] None;
        l

      | Mcst c ->
        let l = Linexpr1.make env in
        Linexpr1.set_cst l c;
        l

      | Munop (op, e, Texpr0.Int, _) ->
        let l = linexpr e in
        begin match op with
          | Texpr0.Neg ->
            let l' = Linexpr1.make env in
            Linexpr1.iter (fun c v -> Linexpr1.set_coeff l' v (Coeff.neg c)) l;
            Linexpr1.set_cst l' (Coeff.neg (Linexpr1.get_cst l));
            l'
          | _ -> raise Linexpr_failure end

      | Mbinop (op, e1, e2, Texpr0.Int, _) ->
        let coef op c1 c2 =
          if op = Texpr0.Add then coeff_add c1 c2
          else coeff_add c1 (Coeff.neg c2) in

        let l1, l2 = linexpr e1, linexpr e2 in
        begin match op with
          | Texpr0.Add | Texpr0.Sub ->
            let lres = Linexpr1.make env in
            Linexpr1.set_cst lres
              (coef op (Linexpr1.get_cst l1) (Linexpr1.get_cst l2));

            let vars = ref [] in
            Linexpr1.iter (fun _ c -> vars := c :: !vars) l1;
            Linexpr1.iter (fun _ c -> vars := c :: !vars) l2;
            let vs = List.sort_uniq Pervasives.compare !vars in

            List.iter (fun v ->
                let c1,c2 = Linexpr1.get_coeff l1 v, Linexpr1.get_coeff l2 v in
                Linexpr1.set_coeff lres v (coef op c1 c2);
              ) vs;
            lres

          | _ -> raise Linexpr_failure end
      | _ -> raise Linexpr_failure in

    try Some (linexpr t.mexpr) with Linexpr_failure -> None


  (* We rewrite the expression to perform soundly weak updates *)
  let rec weak_transf map e =
    match e with
    | Mcst c -> (map, Mcst c)
    | Mvar mvar ->
      if weak_update mvar then
        let i = Mm.find_default 0 mvar map in
        let map' = Mm.add mvar (i + 1) map in
        (map', Mvar (weak_cp mvar i))
      else (map, Mvar mvar)

    | Munop (op1, a, t, r) ->
      let map',a' = weak_transf map a in
      (map', Munop (op1, a', t, r))

    | Mbinop (op2, a, b, t, r) ->
      let map',a' = weak_transf map a in
      let map'',b' = weak_transf map' b in
      (map'', Mbinop (op2, a', b', t, r))

  let get_var_mexpr e =
    let rec aux acc = function
      | Mcst _ -> acc
      | Mvar mvar -> mvar :: acc
      | Munop (_, a, _, _) -> aux acc a
      | Mbinop (_, a, b, _, _) -> aux (aux acc a) b in
    aux [] e
    |> u8_blast_vars
    |> List.sort_uniq Pervasives.compare

  let rec contains_mod = function
    | Mvar _ | Mcst _ -> false
    | Munop (_, a, _, _) -> contains_mod a
    | Mbinop (op2, a, b, _, _) ->
      (op2 = Texpr0.Mod) || (contains_mod a) || (contains_mod b)

  let extend_environment t apr_env =
    let cmp = Environment.compare t.env apr_env in
    if cmp = -1 || cmp = 0 then
      { t with env = apr_env }
    else begin
      Format.eprintf "@[%a@;%a@]@." pp_apr_env t.env pp_apr_env apr_env;
      raise (Aint_error "The environment is not compatible") end
end


(******************)
(* Tcons1 Wrapper *)
(******************)

module Mtcons : sig
  type t
  type typ = Apron.Lincons0.typ

  val make : Mtexpr.t -> typ -> t

  val to_atcons : t -> Tcons1.t
  val to_lincons : t -> apr_env -> Lincons1.t option

  val get_expr : t -> Mtexpr.t
  val get_typ : t -> typ

  val print : Format.formatter -> t -> unit
end = struct
  type typ = Apron.Lincons0.typ

  type t = { expr : Mtexpr.t;
             typ : typ }

  let make t ty = { expr = t; typ = ty }

  let to_atcons t = Tcons1.make (Mtexpr.to_aexpr t.expr) t.typ

  let to_lincons t env =
    omap (fun linexpr -> Lincons1.make linexpr t.typ)
      (Mtexpr.to_linexpr t.expr env)

  let get_expr t = t.expr
  let get_typ t = t.typ

  let print ppf t = to_atcons t |> Tcons1.print ppf
end


(**************)
(* More Utils *)
(**************)

let cst_of_mpqf apr_env n =
  Mtexpr.cst apr_env (Coeff.s_of_mpqf n)

(* Return the texpr 2^n - y *)
let cst_pow_minus apr_env n y =
  mpq_pow_minus n y
  |> cst_of_mpqf apr_env


(**********************)
(* Generic Thresholds *)
(**********************)

let int_thresholds =
  (* For unsigned *)
  List.map (fun i -> mpq_pow_minus i 1) [8;16;32;128;256]
  (* For signed *)
  @ List.map (fun i -> mpq_pow_minus i 1) [7;15;31;127;255]
  @ List.map (fun i -> mpq_pow_minus i 0) [7;15;31;127;255]

let neg i = Mpqf.neg i

let lcons env v i vneg iminus =
  let e = Linexpr1.make env in
  let ci = Coeff.s_of_mpqf (if iminus then neg i else i)
  and cv = Coeff.s_of_int (if vneg then -1 else 1) in
  let () = Linexpr1.set_list e [cv,v] (Some ci) in
  e

let thresholds env =
  let vars = Environment.vars env
             |> fst
             |> Array.to_list in

  List.fold_left (fun acc v ->
      List.fold_left (fun acc i ->
          let lc = lcons env v i in
          (Lincons1.make (lc true true) Lincons0.SUPEQ)
          :: (Lincons1.make (lc true false) Lincons0.SUPEQ)
          :: (Lincons1.make (lc false true) Lincons0.SUPEQ)
          :: (Lincons1.make (lc false false) Lincons0.SUPEQ)
          :: acc) acc int_thresholds)
    [] vars

(*******************)
(* Abstract Values *)
(*******************)

module type AprManager = sig
  type t

  val man : t Apron.Manager.t
end

module BoxManager : AprManager with type t = Box.t = struct
  type t = Box.t

  let man = Box.manager_alloc ()
end

module OctManager : AprManager = struct
  type t = Oct.t

  let man = Oct.manager_alloc ()
end

module PplManager : AprManager = struct
  type t = Ppl.strict Ppl.t

  let man = Ppl.manager_alloc_strict ()
end

module type AbsNumType = sig
  type t

  (* Make a top value defined on the given variables *)
  val make : mvar list -> t

  val meet : t -> t -> t
  val meet_list : t list -> t

  val join : t -> t -> t
  val join_list : t list -> t

  (* Because we do not have a backward analysis, we can give the loop condition
     to the widening, which uses it as threshold. *)
  val widening : Mtcons.t option -> t -> t -> t

  val forget_list : t -> mvar list -> t

  val is_included : t -> t -> bool
  val is_bottom : t -> bool
  val bottom : t -> t

  (* expand t v v_list : v and v_list cannot contain Mvalue (AarrayEl)
     elements *)
  val expand : t -> mvar -> mvar list -> t
  (* fold t v_list : v_list cannot contain Mvalue (AarrayEl)
     elements *)
  val fold : t -> mvar list -> t

  val bound_variable : t -> mvar -> Interval.t
  val bound_texpr : t -> Mtexpr.t -> Interval.t

  val assign_expr : ?force:bool -> t -> mvar -> Mtexpr.t -> t

  val meet_constr : t -> Mtcons.t -> t
  val meet_constr_list : t -> Mtcons.t list -> t

  (* Unify the two abstract values on their least common environment. *)
  val unify : t -> t -> t

  (* Variables that are removed are first existentially quantified, and
     variables that are introduced are unconstrained. *)
  val change_environment : t -> mvar list -> t
  val remove_vars : t -> mvar list -> t

  val to_box : t -> Box.t Abstract1.t
  val of_box : Box.t Abstract1.t -> t

  val get_env : t -> Environment.t

  val print : ?full:bool -> Format.formatter -> t -> unit
end


module AbsNumI (Manager : AprManager) : AbsNumType = struct

  type t = Manager.t Abstract1.t
  let man = Manager.man

  let is_relational () = Ppl.manager_is_ppl man

  let make l =
    let vars = u8_blast_vars l |> List.map avar_of_mvar |> Array.of_list
    and empty_var_array = Array.make 0 (Var.of_string "") in
    let env = Environment.make vars empty_var_array in
    Abstract1.top man env

  let lce a a' =
    let lce = Environment.lce (Abstract1.env a) (Abstract1.env a') in
    (Abstract1.change_environment man a lce false,
     Abstract1.change_environment man a' lce false)

  let env_lce l =
    if l = [] then raise (Aint_error "Lce of an empty list");
    List.fold_left Environment.lce (List.hd l) l

  let lce_list l =
    if l = [] then raise (Aint_error "Lce of an empty list");
    let lce = List.map Abstract1.env l |> env_lce in
    List.map (fun a -> Abstract1.change_environment man a lce false) l

  let meet a a' =
    let a,a' = lce a a' in
    Abstract1.meet man a a'

  let meet_list a_list =
    if a_list = [] then raise (Aint_error "Meet of an empty list");
    let a_list = lce_list a_list in
    Abstract1.meet_array man (Array.of_list a_list)

  let join a a' =
    let a,a' = lce a a' in
    Abstract1.join man a a'

  let join_list a_list =
    if a_list = [] then raise (Aint_error "Join of an empty list");
    let a_list = lce_list a_list in
    Abstract1.join_array man (Array.of_list a_list)


  let to_earray env l =
    let arr = Lincons1.array_make env (List.length l) in
    let () = List.iteri (fun i c -> Lincons1.array_set arr i c) l in
    arr

  let thrs_of_oc oc env =
    match omap_dfl (fun x -> Mtcons.to_lincons x env) None oc with
    | None -> []
    | Some lc ->
      debug(fun () -> Format.eprintf "threshold: %a\n" Lincons1.print lc);
      [lc]


  let widening oc a a' =
    let a,a' = lce a a' in
    let env = Abstract1.env a in
    (* Be careful to join a and a' before calling widening. Some abstract domain,
       e.g. Polka, seem to assume that a is included in a'
       (and may segfault otherwise!). *)
    if Aparam.use_threshold then
      let thrs = (thresholds env @ thrs_of_oc oc env)
                 |> to_earray env in
      Abstract1.widening_threshold man a a' thrs
    else Abstract1.widening_threshold man a a' ( thrs_of_oc oc env
                                                 |> to_earray env )

  let forget_list a l =
    let l = u8_blast_vars l in
    let env = Abstract1.env a in
    let al = List.filter
        (Environment.mem_var env) (List.map avar_of_mvar l) in
    Abstract1.forget_array man a (Array.of_list al) false

  let is_included a a' =
    let a,a' = lce a a' in
    Abstract1.is_leq man a a'

  let is_bottom a = Abstract1.is_bottom man a

  let bottom_man man a = Abstract1.bottom man (Abstract1.env a)

  let bottom = bottom_man man

  (* v and v_list should not contain Mvalue (AarrayEl) elements *)
  let expand_man man a v v_list =
    let v_array = Array.of_list (List.map avar_of_mvar v_list) in
    Abstract1.expand man a (avar_of_mvar v) v_array

  (* v and v_list should not contain Mvalue (AarrayEl) elements *)
  let fold_man man a v_list =
    let v_array = Array.of_list (List.map avar_of_mvar v_list) in
    Abstract1.fold man a v_array

  let expand a v v_list = expand_man man a v v_list

  let fold a v_list = fold_man man a v_list

  let add_weak_cp_man man a map =
    Mm.fold (fun v i a ->
        let vs = List.init i (Mtexpr.weak_cp v) in
        expand_man man a v vs) map a

  let rem_weak_cp_man man a map =
    Mm.fold (fun v i a ->
        let vs = List.init i (Mtexpr.weak_cp v) in
        fold_man man a (v :: vs)) map a

  let add_weak_cp = add_weak_cp_man man

  let rem_weak_cp = rem_weak_cp_man man

  let prepare_env env mexpr =
    let vars_mexpr =
      List.map avar_of_mvar (Mtexpr.get_var_mexpr mexpr) |> Array.of_list
    and empty_var_array = Array.make 0 (Var.of_string "") in
    let env_mexpr = Environment.make vars_mexpr empty_var_array in
    Environment.lce env env_mexpr

  let bound_texpr_man man a (e : Mtexpr.t) =
    (* We use a different variable for each occurrence of weak variables *)
    let map,mexpr = Mtexpr.weak_transf Mm.empty e.mexpr in
    let a = add_weak_cp_man man a map in

    let env = prepare_env (Abstract1.env a) e.mexpr in
    let a = Abstract1.change_environment man a env false in
    let e' = Mtexpr.to_aexpr { Mtexpr.mexpr = mexpr;
                               Mtexpr.env = env } in

    Abstract1.bound_texpr man a e'

  let bound_texpr = bound_texpr_man man

  let bound_variable t v = match v with
    | Mvalue (AarrayEl _) ->
      let env = Abstract1.env t in
      bound_texpr t (Mtexpr.var env v)
    | _ -> Abstract1.bound_variable man t (avar_of_mvar v)

  let env_add_mvar env v =
    let add_single v env =
      let av = avar_of_mvar v in
      if Environment.mem_var env av then env
      else
        Environment.add env
          (Array.of_list [av])
          (Array.make 0 (Var.of_string "")) in

    match v with
    (* | Mvalue (Avar at) | MvarOffset at ->
     *   add_single (Mvalue (Avar at)) env
     *   |> add_single (MvarOffset at) *)

    | Mvalue (AarrayEl _ ) ->
      List.fold_left (fun x y -> add_single y x) env (u8_blast_var v)

    | _ -> add_single v env

  (* Relational assignment. *)
  let assign_expr_rel force a v e =
    (* We use a different variable for each occurrence of weak variables *)
    let map,mexpr = Mtexpr.weak_transf Mm.empty Mtexpr.(e.mexpr) in

    let a = add_weak_cp a map in
    (* We do the same for the variable receiving the assignment *)
    let v_weak = weak_update v && not force in
    let a,v_cp = if v_weak then
        let v_cp = Temp ("weaklv_" ^ string_of_mvar v,0, ty_mvar v) in
        (expand a v [v_cp], v_cp)
      else (a, v) in
    (* If v is not in the environment, we add it *)
    let env = env_add_mvar (Abstract1.env a) v_cp in

    (* We add the variables in mexpr to the environment *)
    let env = prepare_env env mexpr in
    let a = Abstract1.change_environment man a env false in
    let e' = Mtexpr.to_aexpr { Mtexpr.mexpr = mexpr;
                               Mtexpr.env = env } in

    let a = Abstract1.assign_texpr man a (avar_of_mvar v_cp) e' None in

    (* We fold back the added variables *)
    let a = rem_weak_cp a map in
    if v_weak then fold a [v; v_cp] else a


  (* Forced non relational assignment *)
  let assign_expr_norel force a v e =
    (* We do a copy of v if we do a weak assignment *)
    let v_weak = weak_update v && not force in
    let a,v_cp = if v_weak then
        let v_cp = Temp ("weaklv_" ^ string_of_mvar v,0, ty_mvar v) in
        (expand a v [v_cp], v_cp)
      else (a, v) in

    (* If v is not in the environment, we add it *)
    let env = env_add_mvar (Abstract1.env a) v_cp in
    let a = Abstract1.change_environment man a env false in

    let int = Coeff.Interval (bound_texpr a e) in
    let eint = Texpr1.cst env int in

    let a = Abstract1.assign_texpr man a (avar_of_mvar v_cp) eint None in

    (* We fold back v, if needed *)
    if v_weak then fold a [v; v_cp] else a

  let e_complex e =
    (is_relational ()) && (Mtexpr.contains_mod Mtexpr.(e.mexpr))

  let es_complex es = List.exists e_complex es

  (* If the domain is relational, and if e contains a modulo, then we just
     return the interval of variations of e (i.e. we forget all relations
     between v_cp and the other variables). *)
  let assign_expr_aux force a v e =
    if e_complex e then
      assign_expr_norel force a v e
    else assign_expr_rel force a v e


  (* Return the j-th term of the expression e seen in base b = 2^8:
     ((e - (e mod b^j)) / b^j) mod b *)
  let get_block e j =
    let bj = mpq_pow (8 * j) |> Mpqf.of_mpq |> cst_of_mpqf Mtexpr.(e.env)
    and b = mpq_pow 8 |> Mpqf.of_mpq |> cst_of_mpqf Mtexpr.(e.env) in
    (* e - (e mod b^j) *)
    let e1 = Mtexpr.binop Texpr1.Sub e (Mtexpr.binop Texpr1.Mod e bj ) in
    (* e1 / b^j) mod b *)
    Mtexpr.binop Texpr1.Mod ( Mtexpr.binop Texpr1.Div e1 bj) b

  (* If force is true then we do a forced strong update on v. *)
  let assign_expr ?force:(force=false) a v e = match v with
    | Mvalue (AarrayEl (gv,ws,i)) ->
      let offset = (int_of_ws ws) / 8 * i in
      List.fold_left (fun a j ->
          let p = offset + j in
          let mvj = Mvalue (AarrayEl (gv, U8, p)) in
          let mej = get_block e j in
          assign_expr_aux force a mvj mej)
        a (List.init ((int_of_ws ws) / 8) (fun j -> j))

    | _ -> assign_expr_aux force a v e

  let print : ?full:bool -> Format.formatter -> t -> unit =
    fun ?full:(full=false) fmt a ->
      if full && (is_relational ()) then
        Format.fprintf fmt "@[<v 0>@[%a@]@;@]" Abstract1.print a;

      let (arr_vars, _) = Environment.vars (Abstract1.env a) in
      let vars = Array.to_list arr_vars in

      let pp_abs fmt v =
        let vi = Abstract1.bound_variable man a v in
        Format.fprintf fmt "@[%s: %a@]"
          (Var.to_string v)
          Interval.print vi in

      let pp_sep fmt () = Format.fprintf fmt "@;" in

      let vars_p = List.filter (fun v ->
          (not Aparam.ignore_unconstrained ||
           (not !Aparam.nrel_no_print || is_relational ()) &&
           not (Abstract1.is_variable_unconstrained man a v)) &&
          not (variables_ignore v)) vars in

      if vars_p <> [] then
        Format.fprintf fmt "@[<v 0>%a@]" (pp_list ~sep:pp_sep pp_abs) vars_p
      else ()


  let to_box1 : 'a Abstract1.t -> Abstract1.box1 = fun a ->
    Abstract1.to_box man a

  let box1_to_box : Abstract1.box1 -> Box.t Abstract1.t = fun box ->
    let env = box.box1_env in
    let vars,_ = Environment.vars env in
    let bman = BoxManager.man in
    Abstract1.of_box bman env vars Abstract1.(box.interval_array)

  let to_box :  t -> Box.t Abstract1.t = fun a ->
    to_box1 a |> box1_to_box

  let of_box1 (box : Abstract1.box1) =
    let env = box.box1_env in
    let vars,_ = Environment.vars env in
    Abstract1.of_box man env vars Abstract1.(box.interval_array)

  let of_box : Box.t Abstract1.t -> t = fun a ->
    let bman = BoxManager.man in
    Abstract1.to_box bman a |> of_box1

  let trivially_false man a c =
    let int = bound_texpr_man man a (Mtcons.get_expr c) in
    let oi = interval_to_int int in

    Utils.omap_dfl (fun i -> match Mtcons.get_typ c with
        | Tcons0.DISEQ -> i = 0
        | Tcons0.EQ -> i <> 0
        | Tcons0.SUP -> i <= 0
        | Tcons0.SUPEQ -> i < 0
        | Tcons0.EQMOD n -> match scalar_to_int n with
          | None -> false
          | Some n -> (i mod n) <> 0
      ) false oi

  let meet_constr_man man a cs =
    let cs = List.filter (fun c -> not (trivially_false man a c)) cs in
    if cs = [] then bottom_man man a
    else
      let map,cs = List.fold_left (fun (map, acc) c ->
          let e = Mtcons.get_expr c in

          (* We use a different variable for each occurrence of weak variables *)
          let map,mexpr = Mtexpr.weak_transf map e.mexpr in

          (* We prepare the expression *)
          let ae = Mtexpr.to_aexpr { Mtexpr.mexpr = mexpr;
                                     Mtexpr.env = Abstract1.env a } in
          let c = Tcons1.make ae (Mtcons.get_typ c) in
          (map, c :: acc)
        ) (Mm.empty,[]) cs in

      let a = add_weak_cp_man man a map in
      let env = List.map Tcons1.get_env cs |> env_lce in

      (* We evaluate the constraint *)
      let c_array = Tcons1.array_make env (List.length cs) in
      List.iteri (fun i c -> Tcons1.array_set c_array i c) cs;

      let a = Abstract1.meet_tcons_array man a c_array in

      (* We fold back the added variables *)
      rem_weak_cp_man man a map

  let meet_constr_norel a cs =
    let bman = BoxManager.man in
    let ac = meet_constr_man bman (to_box a) cs
             |> of_box in
    meet a ac

  let meet_constr_list a cs =
    let es = List.map Mtcons.get_expr cs in
    if es_complex es then meet_constr_norel a cs
    else meet_constr_man man a cs

  let meet_constr a c = meet_constr_list a [c]

  let unify a a' = Abstract1.unify man a a'

  let change_environment a mvars =
    let env_vars = u8_blast_vars mvars
                   |> List.map avar_of_mvar
                   |> Array.of_list
    and empty_var_array = Array.make 0 (Var.of_string "") in
    let new_env = Environment.make env_vars empty_var_array in
    Abstract1.change_environment man a new_env false

  let remove_vars a mvars =
    let vars = Environment.vars (Abstract1.env a)
               |> fst
               |> Array.to_list
    and rem_vars = u8_blast_vars mvars
                   |> List.map avar_of_mvar  in

    let nvars = List.filter (fun x -> not (List.mem x rem_vars)) vars
                |> Array.of_list
    and empty_var_array = Array.make 0 (Var.of_string "") in

    let new_env = Environment.make nvars empty_var_array in
    Abstract1.change_environment man a new_env false

  let get_env a = Abstract1.env a

end


(*******************)
(* Domains Product *)
(*******************)

type v_dom = Nrd of int | Ppl of int

let string_of_dom = function
  | Nrd i -> "Nrd" ^ string_of_int i
  | Ppl i -> "Ppl" ^ string_of_int i

module Mdom = Map.Make(struct
    type t = v_dom

    let compare = Pervasives.compare
    let equal u v = u = v
  end)

let is_prefix u v =
  if String.length u <= String.length v then
    String.sub v 0 (String.length u) = u
  else false

type analyzer_param = { relationals : string list option;
                        pointers : string list option }

module type ProgWrap = sig
  val main : unit Prog.func
  val prog : unit Prog.prog
  val param : analyzer_param
end

module type VDomWrap = sig
  (* Associate a domain (ppl or non-relational to every variable *)
  val vdom : mvar -> v_dom
end

module DomNR : VDomWrap = struct
  let vdom _ = Nrd 0
end

(* Fix-point computation *)
let rec fpt f eq x =
  let x' = f x in
  if (eq x x') then
    x
  else
    fpt f eq x'

module Scmp = struct
  type t = string
  let compare = compare
end

module Ms = Map.Make(Scmp)

(* For now we fixed the domains, and we use only two of them, one non-relational
   and on Ppl. Still, we generalized to n different domains whenever possible
   to help future possible extentions. *)
module AbsNumProd (VDW : VDomWrap) (NonRel : AbsNumType) (PplDom : AbsNumType)
  : AbsNumType = struct

  type t = { nrd : NonRel.t Mdom.t;
             ppl : PplDom.t Mdom.t }

  let nrddoms = [Nrd 0]
  let ppldoms = [Ppl 0]

  (* We need log the result of VDW.vdom for the of_box function. This is not
     clean, but I do not see a simpler way. *)
  let log_index = Hashtbl.create ~random:false 16
  let log = Hashtbl.create ~random:false 16

  let vdom v =
    let r = VDW.vdom v in
    let vs = avar_of_mvar v |> Var.to_string in
    if not (Hashtbl.mem log_index vs) then begin
      Hashtbl.add log_index vs ();
      Hashtbl.add log r vs
    end;
    r

  let pp_dom fmt = function
    | Ppl i -> Format.fprintf fmt "Ppl %d" i
    | Nrd i -> Format.fprintf fmt "Nrd %d" i

  let pp_log fmt () =
    Format.fprintf fmt "@[<v 0>";
    Hashtbl.iter (fun dom v ->
        Format.fprintf fmt "%s --> %a@;" v pp_dom dom)
      log;
    Format.fprintf fmt "@;@]@.";;

  let expr_doms e =
    let rec aux acc = function
      | Mtexpr.Mcst _ -> acc
      | Mtexpr.Mvar v ->
        if List.mem (vdom v) acc then acc else (vdom v) :: acc
      | Mtexpr.Munop (_, e1, _, _) -> aux acc e1
      | Mtexpr.Mbinop (_, e1, e2, _, _) -> aux (aux acc e1) e2 in

    aux [] e

  (* Replace all variables not in domain d by an interval *)
  let proj_expr a d (e : Mtexpr.t) =
    let env = e.env in
    let m_make e = Mtexpr.({ mexpr = e; env = env }) in

    let rec proj_mexpr (e : Mtexpr.mexpr) = match expr_doms e with
      | [] -> m_make e
      | [d'] ->
        if d = d' then m_make e
        else
          let int = match d' with
            | Nrd _ -> NonRel.bound_texpr (Mdom.find d' a.nrd) (m_make e)
            | Ppl _ -> PplDom.bound_texpr (Mdom.find d' a.ppl) (m_make e) in
          Mtexpr.cst env (Coeff.Interval int)

      | _ -> match e with
        | Mtexpr.Munop (op, e1, _, _) -> Mtexpr.unop op (proj_mexpr e1)
        | Mtexpr.Mbinop (op, e1, e2, _, _) ->
          Mtexpr.binop op (proj_mexpr e1) (proj_mexpr e2)
        | _ -> assert false in

    proj_mexpr e.mexpr

  let proj_constr a d (c : Mtcons.t) =
    Mtcons.make (proj_expr a d (Mtcons.get_expr c)) (Mtcons.get_typ c)

  let split_doms l =
    let rec aux (ores,pres) = function
      | [] -> (ores, pres)
      | v :: tail ->
        let res' = match vdom v with
          | Ppl _ as d ->
            if List.mem_assoc d pres then
              (ores, assoc_up d (fun x -> v :: x) pres)
            else
              (ores, (d,[v]) :: pres)

          | Nrd _ as d ->
            if List.mem_assoc d ores then
              (assoc_up d (fun x -> v :: x) ores, pres)
            else
              ((d,[v]) :: ores, pres) in

        aux res' tail in

    aux (List.map (fun d -> (d,[])) nrddoms,
         List.map (fun d -> (d,[])) ppldoms) l

  let make l =
    let (ores,pres) = split_doms l in
    let a = { nrd = Mdom.empty; ppl = Mdom.empty } in

    let a = List.fold_left (fun a (d,lvs) ->
        { a with nrd = Mdom.add d (NonRel.make lvs) a.nrd })
        a ores in

    List.fold_left (fun a (d,lvs) ->
        { a with ppl = Mdom.add d (PplDom.make lvs) a.ppl })
      a pres

  let un_app fnrd fppl a =
    { nrd = Mdom.mapi fnrd a.nrd;
      ppl = Mdom.mapi fppl a.ppl }

  let bin_app fnrd fppl a a' =
    let f_opt f k u v = match u,v with
      | None, _ | _, None ->
        let s = Printf.sprintf
            "bin_app: Domain %s does not exist" (string_of_dom k) in
        raise (Aint_error s)
      | Some x, Some y -> Some (f x y) in

    { nrd = Mdom.merge (f_opt fnrd) a.nrd a'.nrd;
      ppl = Mdom.merge (f_opt fppl) a.ppl a'.ppl }

  let list_app fnrd fppl (l : t list) =
    match l with
    | [] -> raise (Aint_error "list_app of an empty list");
    | a :: _ ->

      { nrd = Mdom.mapi (fun k _ ->
            let els = List.map (fun x -> Mdom.find k x.nrd) l in
            fnrd els) a.nrd;
        ppl = Mdom.mapi (fun k _ ->
            let els = List.map (fun x -> Mdom.find k x.ppl) l in
            fppl els) a.ppl}

  let meet = bin_app NonRel.meet PplDom.meet

  let meet_list = list_app NonRel.meet_list PplDom.meet_list

  let join = bin_app NonRel.join PplDom.join

  let join_list = list_app NonRel.join_list PplDom.join_list

  let widening oc a a' =
    let fp d = omap_dfl (fun c -> proj_constr a' d c |> some) None oc in
    let nroc  = fp (Nrd 0)
    and pploc = fp (Ppl 0) in
    bin_app (NonRel.widening nroc) (PplDom.widening pploc) a a'

  let forget_list a l =
    let f1 _ x = NonRel.forget_list x l
    and f2 _ x = PplDom.forget_list x l in
    un_app f1 f2 a

  let is_included a a' =
    (Mdom.for_all (fun d t -> NonRel.is_included t (Mdom.find d a'.nrd)) a.nrd)
    &&
    (Mdom.for_all (fun d t -> PplDom.is_included t (Mdom.find d a'.ppl)) a.ppl)

  let is_bottom a =
    assert ((Mdom.cardinal a.nrd) + (Mdom.cardinal a.nrd) <> 0);
    (Mdom.exists (fun _ t -> NonRel.is_bottom t) a.nrd)
    || (Mdom.exists (fun _ t -> PplDom.is_bottom t) a.ppl)

  let bottom a =
    let f1 _ x = NonRel.bottom x
    and f2 _ x = PplDom.bottom x in
    un_app f1 f2 a

  let expand a v v_list =
    let f1 d x = if vdom v = d then NonRel.expand x v v_list else x
    and f2 d x = if vdom v = d then PplDom.expand x v v_list else x in
    un_app f1 f2 a

  let fold a v_list = match v_list with
    | [] -> raise (Aint_error "fold of an empty list")
    | v :: _ ->
      let f1 d x = if vdom v = d then NonRel.fold x v_list else x
      and f2 d x = if vdom v = d then PplDom.fold x v_list else x in
      un_app f1 f2 a

  let bound_variable a v = match vdom v with
    | Nrd _ -> NonRel.bound_variable (Mdom.find (vdom v) a.nrd) v
    | Ppl _ -> PplDom.bound_variable (Mdom.find (vdom v) a.ppl) v


  (* This works only if there is only one Ppl domain (Ppl 0). *)
  let bound_texpr a (e : Mtexpr.t) =
    let p_e = proj_expr a (Ppl 0) e in
    PplDom.bound_texpr (Mdom.find (Ppl 0) a.ppl) p_e

  (* If force is true then we do a forced strong update on v. *)
  let assign_expr ?force:(force=false) a v (e : Mtexpr.t) =
    let d = vdom v in
    let p_e = proj_expr a d e in
    match d with
    | Nrd _ ->
      let d_a = Mdom.find d a.nrd in
      let d_a' = NonRel.assign_expr ~force:force d_a v p_e in
      { a with nrd = Mdom.add d d_a' a.nrd }

    | Ppl _ ->
      let d_a = Mdom.find d a.ppl in
      let d_a' = PplDom.assign_expr ~force:force d_a v p_e in
      { a with ppl = Mdom.add d d_a' a.ppl }


  let meet_constr_list a cs =
    let f1 d x = NonRel.meet_constr_list x (List.map (proj_constr a d) cs)
    and f2 d x = PplDom.meet_constr_list x (List.map (proj_constr a d) cs) in
    un_app f1 f2 a

  let meet_constr a c =
    let f1 d x = NonRel.meet_constr x (proj_constr a d c)
    and f2 d x = PplDom.meet_constr x (proj_constr a d c) in
    un_app f1 f2 a

  let unify = bin_app NonRel.unify PplDom.unify

  let print : ?full:bool -> Format.formatter -> t -> unit =
    fun ?full:(full=false) fmt a ->
      let pp_map pp_el fmt l =
        pp_list pp_el fmt (List.map snd (Mdom.bindings l)) in

      if Mdom.cardinal a.nrd = 0 || !only_rel_print then
        Format.fprintf fmt "@[<v 0>* Rel:@;%a@]"
          (pp_map (PplDom.print ~full:full)) a.ppl
      else
        Format.fprintf fmt "@[<v 0>* NonRel:@;%a* Rel:@;%a@]"
          (pp_map (NonRel.print ~full:full)) a.nrd
          (pp_map (PplDom.print ~full:full)) a.ppl

  let change_environment a mvars =
    let (ores,pres) = split_doms mvars in

    let f1 d x = NonRel.change_environment x (List.assoc d ores)
    and f2 d x = PplDom.change_environment x (List.assoc d pres) in
    un_app f1 f2 a

  let remove_vars a mvars =
    let (ores,pres) = split_doms mvars in

    let f1 d x = NonRel.remove_vars x (List.assoc d ores)
    and f2 d x = PplDom.remove_vars x (List.assoc d pres) in
    un_app f1 f2 a

  let get_env a =
    let l =
      Mdom.fold (fun _ a l ->
          let vars,_ = NonRel.get_env a |> Environment.vars in
          Array.to_list vars @ l) a.nrd []
      |> Mdom.fold (fun _ a l ->
          let vars,_ = PplDom.get_env a |> Environment.vars in
          Array.to_list vars @ l) a.ppl in

    let env_vars = Array.of_list l
    and empty_var_array = Array.make 0 (Var.of_string "") in
    Environment.make env_vars empty_var_array


  let to_box a =
    let env = get_env a in
    let bman = Box.manager_alloc () in
    let l =
      Mdom.fold (fun _ a acc ->
          Abstract1.change_environment bman (NonRel.to_box a) env false
          :: acc
        ) a.nrd []
      |> Mdom.fold (fun _ a acc ->
          Abstract1.change_environment bman (PplDom.to_box a) env false
          :: acc
        ) a.ppl in

    Abstract1.meet_array bman (Array.of_list l)

  (* This is messy because we have to use the log to inverse avar_of_mvar *)
  let of_box (box : Box.t Abstract1.t) =
    let vars = Environment.vars (Abstract1.env box)
               |> fst
               |> Array.to_list
               |> List.map Var.to_string in
    let bman = Box.manager_alloc () in

    let denv dom =
      let dvars = Hashtbl.find_all log dom
                  |> List.filter (fun x -> List.mem x vars)
                  |> List.map Var.of_string
                  |> Array.of_list
      and empty_var_array = Array.make 0 (Var.of_string "") in
      Environment.make dvars empty_var_array in

    let res = List.fold_left (fun a dom ->
        let penv = denv dom in
        let av = Abstract1.change_environment bman box penv false
                 |> NonRel.of_box in
        { a with nrd = Mdom.add dom av a.nrd }
      ) (make []) nrddoms in

    List.fold_left (fun a dom ->
        let penv = denv dom in
        let av = Abstract1.change_environment bman box penv false
                 |> PplDom.of_box in
        { a with ppl = Mdom.add dom av a.ppl }
      ) res ppldoms

end



(***************************************)
(* Boolean combination of constraints. *)
(***************************************)

type btcons =
  | BLeaf of Mtcons.t
  | BVar of string * bool
  | BAnd of btcons * btcons
  | BOr of btcons * btcons

let rec pp_btcons ppf = function
  | BLeaf t -> Mtcons.print ppf t

  | BVar (s,b) ->
    if b then Format.fprintf ppf "%s" s
    else Format.fprintf ppf "NOT %s" s

  | BAnd (bl,br) ->
    Format.fprintf ppf "(%a@ AND@ %a)"
      pp_btcons bl pp_btcons br

  | BOr (bl,br) ->
    Format.fprintf ppf "(%a@ OR@ %a)"
      pp_btcons bl pp_btcons br

let true_tcons1 env =
  let zero_t = Coeff.s_of_int 0 in
  Mtcons.make (Mtexpr.cst env zero_t) Tcons1.EQ

let false_tcons1 env =
  let zero_t = Coeff.s_of_int 0 in
  Mtcons.make (Mtexpr.cst env zero_t) Tcons1.DISEQ

let bvar_name v neg =
  if neg then "f_" ^ v else "t_" ^ v

(* Return the negation of c, except for EQMOD.
   For EQMOD, we return a constraint that always hold. *)
let flip_constr c =
  let t = Mtcons.get_expr c in
  match Mtcons.get_typ c with
  | Tcons1.EQ -> Mtcons.make t Tcons1.DISEQ |> some
  | Tcons1.DISEQ -> Mtcons.make t Tcons1.EQ |> some
  | Tcons1.SUPEQ ->
    let mt = Mtexpr.unop Texpr1.Neg t in
    Mtcons.make mt Tcons1.SUP |> some

  | Tcons1.SUP ->
    let mt = Mtexpr.unop Texpr1.Neg t in
    Mtcons.make mt Tcons1.SUPEQ |> some

  | Tcons1.EQMOD _ -> None (* Remark: For small i, we could do something *)


exception Bop_not_supported

let rec flip_btcons : btcons -> btcons option = fun c ->
  let rec flip_btcons_aux = function
    | BLeaf c -> begin match flip_constr c with
        | Some fc -> BLeaf fc
        | None -> raise Bop_not_supported end
    | BVar (s,bool) -> BVar (s, true <> bool)
    | BAnd (bl,br) -> BOr (flip_btcons_aux bl, flip_btcons_aux br)
    | BOr (bl,br) -> BAnd (flip_btcons_aux bl, flip_btcons_aux br) in

  try Some (flip_btcons_aux c) with Bop_not_supported -> None


(* Type of expression that have been split to remove IfThenElse *)
type s_expr = (btcons list * Mtexpr.t option) list

let sexpr_from_simple_expr : Mtexpr.t -> s_expr = fun expr ->
  [([], Some expr)]

let pp_s_expr fmt (e : s_expr) =
  let pp_el fmt (l,t_opt) =
    Format.fprintf fmt "@[<v 0>%d constraints:@;@[<v 1>%a@]@;term: @[%a@]@]"
      (List.length l)
      (pp_list pp_btcons) l
      (pp_opt Mtexpr.print_mexpr) ((omap (fun x -> Mtexpr.(x.mexpr))) t_opt) in

  Format.fprintf fmt "@[<v 0>%a@]"
    (pp_list pp_el) e


(*************************)
(* Partition Tree Domain *)
(*************************)

type cnstr = { mtcons : Mtcons.t;
               cpt_uniq : int;
               loc : L.t }

let pp_cnstr fmt c =
  Format.fprintf fmt "(%d) %a: %a"
    (c.cpt_uniq)
    L.pp_sloc c.loc
    Mtcons.print c.mtcons

let pp_cnstrs fmt =
  Format.fprintf fmt "[%a]"
    (pp_list ~sep:(fun fmt () -> Format.fprintf fmt ";@ ") pp_cnstr)

let pp_cnstrss fmt =
  Format.fprintf fmt "@[<v 0>%a@]"
    (pp_list ~sep:(fun fmt () -> Format.fprintf fmt "@;") pp_cnstrs)

module Ptree = struct
  type 'a t =
    | Node of cnstr * 'a t * 'a t
    | Leaf of 'a


  let rec pp_ptree pp_leaf fmt = function
    | Leaf x -> pp_leaf fmt x
    | Node (c,Leaf x,Leaf r) ->
      Format.fprintf fmt "@[<v 0>@[<v 2># @[%a@] :@;\
                          @[%a@]@]@;\
                          @[<v 2># :@;\
                          @[%a@]@]@]"
        pp_cnstr c
        pp_leaf x
        pp_leaf r

    | Node (c,l,r) ->
      Format.fprintf fmt "@[<v 0>\
                          @[<v 2># @[%a@] :@;\
                          @[%a@]@]@;\
                          @[<v 2># :@;\
                          @[%a@]@]@]"
        pp_cnstr c
        (pp_ptree pp_leaf) l
        (pp_ptree pp_leaf) r

  let flip c = flip_constr c |> otolist

  let rec same_shape t1 t2 = match t1, t2 with
    | Node (c1,l1,r1), Node (c2,l2,r2) when c1 = c2 ->
      (same_shape l1 l2) && (same_shape r1 r2)
    | Leaf _, Leaf _ -> true
    | _ -> false

  let apply (f : Mtcons.t list -> 'a -> 'b) (t : 'a t) =
    let rec aux cs t = match t with
      | Node (c,l,r) -> Node (c,
                              aux (c.mtcons :: cs) l,
                              aux (flip c.mtcons @ cs ) r)
      | Leaf x -> Leaf (f cs x) in
    aux [] t

  let apply2_merge (fmerge : 'a t -> 'b t -> ('a t * 'b t))
      (f : Mtcons.t list -> 'a -> 'b -> 'c) t1 t2 =
    let rec aux cs t1 t2 = match t1,t2 with
      | Node (c1,l1,r1), Node (c2,l2,r2) when c1 = c2 ->
        Node (c1,
              aux (c1.mtcons :: cs) l1 l2,
              aux (flip c1.mtcons @ cs) r1 r2)
      | Leaf x1, Leaf x2 -> Leaf (f cs x1 x2)
      | _ -> raise (Aint_error "Ptree: Shape do not match") in

    let t1, t2 = if same_shape t1 t2 then t1,t2 else fmerge t1 t2 in

    aux [] t1 t2

  let apply_list (f : Mtcons.t list -> 'a list -> 'b) ts =
    let rec aux cs ts = match ts with
      | [] -> raise (Aint_error "Ptree: apply_l empty list")
      | Node (c,_,_) :: _ -> aux_node c cs ts [] []
      | Leaf _ :: _ -> aux_leaf cs ts []

    and aux_node c cs ts lts rts = match ts with
      | Node (c',l,r) :: ts' when c = c' ->
        aux_node c cs ts' (l :: lts) (r :: rts)
      | [] -> Node (c,
                    aux (c.mtcons :: cs) lts,
                    aux (flip c.mtcons @ cs ) rts)
      | _ -> raise (Aint_error "Ptree: aux_node bad shape")

    and aux_leaf cs ts xts = match ts with
      | Leaf x :: ts' -> aux_leaf cs ts' (x :: xts)
      | [] -> Leaf (f cs xts)
      | _ -> raise (Aint_error "Ptree: aux_leaf bad shape") in

    aux [] ts

  let eval (fn : cnstr -> 'a -> 'a -> 'a)
      (fl : Mtcons.t list -> 'b -> 'a)
      (t : 'b t) =
    let rec aux cs = function
      | Node (c,l,r) ->
        fn c (aux (c.mtcons :: cs) l) (aux (flip c.mtcons @ cs) r)
      | Leaf x -> fl cs x in
    aux [] t

  let eval2_merge (fmerge : 'b t -> 'c t -> ('b t * 'c t))
      (fn : Mtcons.t list -> 'a -> 'a -> 'a)
      (fl : Mtcons.t list -> 'b -> 'c -> 'a)
      (t1 : 'b t) (t2 : 'c t) =
    let rec aux cs t1 t2 = match t1,t2 with
      | Node (c1,l1,r1), Node (c2,l2,r2) when c1 = c2 ->
        fn cs (aux (c1.mtcons :: cs) l1 l2) (aux (flip c1.mtcons @ cs) r1 r2)
      | Leaf x1, Leaf x2 -> fl cs x1 x2
      | _ -> raise (Aint_error "Ptree: eval2 : shape do not match") in

    let t1, t2 = if same_shape t1 t2 then t1,t2 else fmerge t1 t2 in

    aux [] t1 t2

  let ptree_size = eval (fun _ a b -> a + b) (fun _ _ -> 1)
end


module type AbsDisjType = sig
  include AbsNumType

  (* of_box uses an already existing disjunctive value to get its shape. *)
  val of_box : Box.t Abstract1.t -> t -> t

  (* Adds a block of constraints for the disjunctive domain *)
  val new_cnstr_blck : t -> t

  (* Add a constraint to the top-most block *)
  val add_cnstr : t -> Mtcons.t -> L.t -> t * t

  (* Pop the top-most block of constraints in the disjunctive domain *)
  val pop_cnstr_blck : t -> t
end

(* Disjunctive domain. Leaves are already constrained under the branch
   conditions. *)
module AbsDisj (A : AbsNumType) : AbsDisjType = struct

  type t = { tree : A.t Ptree.t;
             cnstrs : cnstr list list }

  let _uniq = ref 0

  let make_cnstr c i =
    incr _uniq;
    { mtcons = c; cpt_uniq = !_uniq; loc = i }

  let same_shape t t' = t.cnstrs = t'.cnstrs

  let compare c c' = Pervasives.compare c.cpt_uniq c'.cpt_uniq

  let equal c c' = compare c c' = 0

  let cnstrs_list l = List.rev l |> List.flatten

  let rec merge_blck mcs t t' = match mcs, t, t' with
    | [], Ptree.Leaf _, Ptree.Leaf _ -> t, t'
    | c0 :: mcs', Ptree.Node (c, tl, tr), Ptree.Node (c',tl',tr') ->
      if equal c c' && equal c c0 then
        let mtl,mtl' = merge_blck mcs' tl tl'
        and mtr,mtr' = merge_blck mcs' tr tr' in
        ( Ptree.Node (c, mtl, mtr), Ptree.Node (c,mtl', mtr') )
      else if equal c c0 then merge_blck mcs t (Ptree.Node (c,t', t'))
      else if equal c' c0 then merge_blck mcs (Ptree.Node (c,t, t)) t'
      else raise (Aint_error "merge_blck: bad shape")

    | c0 :: _, Ptree.Node (c, _,_), Ptree.Leaf _ ->
      assert (equal c0 c);
      merge_blck mcs t (Ptree.Node (c,t', t'))

    | c0 :: _, Ptree.Leaf _, Ptree.Node (c', _,_) ->
      assert (equal c0 c');
      merge_blck mcs (Ptree.Node (c',t, t)) t'

    | _ -> raise (Aint_error "merge_blck: bad shape")

  let rec merge_last_blck mcs t t' l = match l with
    | [] -> merge_blck mcs t t'
    | c0 :: l' ->
      match t,t' with
      | Ptree.Node (c,tl,tr), Ptree.Node (c',tl',tr')
        when equal c c' && equal c c0 ->
        let mtl,mtl' = merge_last_blck mcs tl tl' l'
        and mtr,mtr' = merge_last_blck mcs tr tr' l' in
        Ptree.Node (c, mtl, mtr), Ptree.Node (c,mtl', mtr')
      | _ -> assert false

  let tmerge t t' =
    if same_shape t t' then t, t'
    else match t.cnstrs, t'.cnstrs with
      | [], [] -> t,t'
      | cs :: l, cs' :: l' ->
        assert (l = l');
        let mcs = List.sort_uniq compare (cs @ cs') in
        let mt, mt' = merge_last_blck mcs t.tree t'.tree (cnstrs_list l) in
        ( { tree = mt; cnstrs = mcs :: l }, { tree = mt'; cnstrs = mcs :: l } )
      | _ -> assert false

  let apply f t = { t with tree = Ptree.apply f t.tree }

  let eval fn fl t = Ptree.eval fn fl t.tree

  let apply2 f t t' =
    let t,t' = tmerge t t' in
    { tree = Ptree.apply2_merge (fun _ _ -> assert false) f t.tree t'.tree;
      cnstrs = t.cnstrs }

  let eval2 fn fl t t' =
    let t,t' = tmerge t t' in
    Ptree.eval2_merge (fun _ _ -> assert false) fn fl t.tree t'.tree

  let merge_list l = match l with
    | [] -> []
    | t :: l' ->
      let t_lce = List.fold_left (fun acc x -> tmerge acc x |> snd) t l' in
      t_lce :: (List.map (fun x -> tmerge t_lce x |> snd) l')

  let apply_list f ts =
    match merge_list ts with
    | [] -> raise (Aint_error "apply_list: empty list")
    | t :: _ as ts ->
      let tts = List.map (fun x -> x.tree) ts in
      { tree = Ptree.apply_list f tts;
        cnstrs = t.cnstrs }

  let new_cnstr_blck : t -> t = fun t -> { t with cnstrs = [] :: t.cnstrs }

  let tbottom a = Ptree.apply (fun _ x -> A.bottom x) a

  (* Insert the constraint in the current block at the correct place *)
  let rec add_cnstr_blck c t = match t with
    | Ptree.Leaf a ->
      let ra = match flip_constr c.mtcons with
        | None -> a
        | Some nc -> A.meet_constr a nc in

      ( Ptree.Node (c,
                    Ptree.Leaf (A.meet_constr a c.mtcons),
                    Ptree.Leaf (A.bottom a)),
        Ptree.Node (c,
                    Ptree.Leaf (A.bottom a),
                    Ptree.Leaf ra) )

    | Ptree.Node (c', tl, tr) ->
      let cc = compare c c' in
      if cc = -1 then
        let tl' = Ptree.apply (fun _ a -> A.meet_constr a c.mtcons) t
        and tr' = Ptree.apply (fun _ a -> match flip_constr c.mtcons with
            | None -> a
            | Some nc -> A.meet_constr a nc) t in
        ( Ptree.Node (c, tl', tbottom t), Ptree.Node (c, tbottom t, tr') )

      else if cc = 1 then
        let fn c (mtl,mtl') (mtr,mtr') = ( Ptree.Node (c, mtl, mtr),
                                           Ptree.Node (c, mtl', mtr') ) in
        fn c' (add_cnstr_blck c tl) (add_cnstr_blck c tr)

      else raise (Aint_error "add_cnstr_blck: bad shape")

  (* Go down to the last block in t and apply f, then inductively combine the
     results using fn *)
  let rec apply_last_blck fn f t l = match l,t with
    | [], _ -> f t
    | c0 :: l', Ptree.Node (c, tl, tr) when equal c c0 ->
      let mtl = apply_last_blck fn f tl l'
      and mtr = apply_last_blck fn f tr l' in
      fn c mtl mtr

    | _ -> raise (Aint_error "apply_last_blck: bad shape err3")

  let add_cnstr : t -> Mtcons.t -> L.t -> t * t = fun t c loc ->
    match t.cnstrs with
    | cs :: l ->
      let cnstr = make_cnstr c loc in
      let f x = add_cnstr_blck cnstr x
      and fn c (mtl,mtl') (mtr,mtr') = ( Ptree.Node (c, mtl, mtr),
                                         Ptree.Node (c, mtl', mtr') ) in

      let ncs = (List.sort_uniq compare (cnstr :: cs)) :: l in
      let tl,tr = apply_last_blck fn f t.tree (cnstrs_list l) in
      ( { tree = tl; cnstrs = ncs }, { tree = tr; cnstrs = ncs } )

    | _ -> raise (Aint_error "add_cnstr: empty list")

  let pop_cnstr_blck : t -> t = fun t -> match t.cnstrs with
    | _ :: l ->
      let f x =
        let tree = Ptree.eval (fun _ a b -> A.join a b) (fun _ a -> a) x in
        Ptree.Leaf tree
      and fn c mtl mtr = Ptree.Node (c, mtl, mtr) in

      { tree =  apply_last_blck fn f t.tree (cnstrs_list l);
        cnstrs =  l }
    | _ -> raise (Aint_error "pop_cnstr_blck: empty list")

  let meet_constr_ne (a : A.t) l =
    let l_f = List.filter (fun c ->
        let cmp = Environment.compare (Mtcons.get_expr c).env (A.get_env a) in
        cmp = -1 || cmp = 0) l in

    match l_f with
    | [] -> a
    | _ :: _ -> A.meet_constr_list a l_f

  (* All leaves should have the same environment *)
  let get_env t =
    let rec aux = function
      | Ptree.Node (_,l,_) -> aux l
      | Ptree.Leaf x -> A.get_env x in
    aux t.tree

  (* Make a top value defined on the given variables *)
  let make l = { tree = Leaf (A.make l);
                 cnstrs = [[]] }

  let meet = apply2 (fun _ -> A.meet)
  let meet_list = apply_list (fun _ -> A.meet_list)

  let join = apply2 (fun _ -> A.join)
  let join_list = apply_list (fun _ -> A.join_list)

  let widening oc = apply2 (fun _ -> A.widening oc)

  let forget_list t l = apply (fun _ x -> A.forget_list x l) t

  let is_included = eval2 (fun _ l b -> l && b) (fun _ -> A.is_included)
  let is_bottom = eval (fun _ l b -> l && b) (fun _ -> A.is_bottom)

  let bottom a = apply (fun _ x -> A.bottom x) a

  let expand t v l = apply (fun _ x -> A.expand x v l) t

  let fold t l = apply (fun _ x -> A.fold x l) t

  let bman : Box.t Manager.t = BoxManager.man
  let box_of_int int = Abstract0.of_box bman 1 0 (Array.init 1 (fun _ -> int))
  let box_join b1 b2 = Abstract0.join bman b1 b2
  let int_of_box b = Abstract0.bound_dimension bman b 0

  (* Interval does not support joins, so we go through level 0 boxes. *)
  let bound_variable t v =
    eval (fun _ -> box_join) (fun _ x -> A.bound_variable x v |> box_of_int ) t
    |> int_of_box

  let bound_texpr t e =
    eval (fun _ -> box_join) (fun _ x -> A.bound_texpr x e |> box_of_int ) t
    |> int_of_box

  let assign_expr ?force:(force=false) (t : t) (v : mvar) (e : Mtexpr.t) =
    apply (fun _ x -> A.assign_expr ~force:force x v e) t

  let meet_constr t c = apply (fun _ x -> A.meet_constr x c) t
  let meet_constr_list t cs = apply (fun _ x -> A.meet_constr_list x cs) t

  let unify = apply2 (fun _ -> A.unify)

  let change_environment t l = apply (fun _ x -> A.change_environment x l) t

  let remove_vars t l = apply (fun _ x -> A.remove_vars x l) t

  let to_box = eval (fun _ -> Abstract1.join bman) (fun _ -> A.to_box)
  let of_box _ = raise (Aint_error "not supported by disjunctive domain")


  let of_box bt tshape = apply (fun _ _ -> A.of_box bt) tshape

  let shrt_tree t =
    let fn c l r = match l, r with
      | Ptree.Leaf la, Ptree.Leaf lr ->
        if A.is_bottom la && A.is_bottom lr then Ptree.Leaf la
        else Ptree.Node (c, l, r)
      | _ -> Ptree.Node (c, l, r) in

    let fl _ a = Ptree.Leaf a in

    eval fn fl t

  let print ?full:(full=false) fmt t =
    Ptree.pp_ptree (fun fmt a ->
        if A.is_bottom a then Format.fprintf fmt "Bottom"
        else A.print ~full:full fmt a) fmt (shrt_tree t)
end


module Lift (A : AbsNumType) : AbsDisjType = struct
  include A

  let of_box bt _ = A.of_box bt

  let new_cnstr_blck t = t

  let add_cnstr t c _ =
    (A.meet_constr t c,
     match flip_constr c with
     | Some nc -> A.meet_constr t nc
     | None -> t)

  let pop_cnstr_blck t = t
end

(**************************************)
(* Building of the partition skeleton *)
(**************************************)

let ty_gvar_of_mvar = function
  | Mvalue (Avar v) -> Some v
  | _ -> None

let swap_op2 op e1 e2 =
  match op with
  | E.Ogt   _ -> e2, e1
  | E.Oge   _ -> e2, e1
  | _         -> e1, e2

let opk_of_cmpk = function
  | E.Cmp_int -> E.Op_int
  | E.Cmp_w (_,ws) -> E.Op_w ws

let mtexpr_of_bigint env z =
  let mpq_z = Mpq.init_set_str (B.to_string z) ~base:10 in
  Mtexpr.cst env (Coeff.s_of_mpq mpq_z)

module PIMake (PW : ProgWrap) : VDomWrap = struct

  (* We compute the dependency heuristic graph *)
  let pa_res = Pa.pa_make PW.main PW.prog

  (* We compute the reflexive and transitive cloture of dp *)
  let f (dp : Pa.dp) =
    Mv.map (fun sv ->
        Sv.fold (fun v' s ->
            Sv.union s (Pa.dp_v dp v'))
          sv sv) dp

  let dp = fpt f (Mv.equal Sv.equal) pa_res.pa_dp

  let add_flow sv_ini =
    Mv.fold (fun v sv v_rel ->
        if Sv.disjoint sv sv_ini then v_rel
        else Sv.add v v_rel
      ) dp sv_ini

  (* We are relational on a variable v iff:
     - there is a direct flow from the intersection of PW.main.f_args and
     Glob_options.relational to v.
     - the variable appears in while loops conditions. *)
  let sv_ini =
    match PW.param.relationals with
    | None -> PW.main.f_args |> Sv.of_list
    | Some v_rel ->
      List.filter (fun v -> List.mem v.v_name v_rel) PW.main.f_args
      |> Sv.of_list

  let v_rel : Sv.t =
    let v_rel = add_flow sv_ini in
    Sv.union v_rel pa_res.while_vars

  (* v is a pointer variable iff there is a direct flow from the intersection
     of PW.main.f_args and Glob_options.pointers to v. *)
  let pt_ini =
    match PW.param.pointers with
    | None -> PW.main.f_args |> Sv.of_list
    | Some v_pt ->
      List.filter (fun v -> List.mem v.v_name v_pt) PW.main.f_args
      |> Sv.of_list

  let v_pt : Sv.t = add_flow pt_ini

  let pp_rel_vars fmt rel =
    (pp_list (Printer.pp_var ~debug:true)) fmt
      (List.sort (fun v v' -> Pervasives.compare v.v_name v'.v_name)
         (Sv.elements rel))

  let () = debug(fun () ->
      Format.eprintf "@[<hov 2>%d relational variables:@ @,%a@]@;\
                      @[<hov 2>%d pointers:@ @,%a@]@;@."
        (Sv.cardinal v_rel)
        pp_rel_vars v_rel
        (Sv.cardinal v_pt)
        pp_rel_vars v_pt)

  let vdom = function
    | Temp _ | WTemp _ -> assert false

    | MNumInv _ -> Ppl 0        (* Numerical invariant must be relational *)

    | Mvalue (Avar v) | MinValue v ->
      if Sv.mem v v_rel then Ppl 0 else Nrd 0

    | MvarOffset v
    | MmemRange (MemLoc v) ->
      if Sv.mem v v_pt then Ppl 0 else Nrd 0

    | Mvalue (AarrayEl _)
    | Mvalue (Aarray _) -> Nrd 0
end


(***********************************)
(* Numerical Domain With Profiling *)
(***********************************)

module type NumWrap = sig
  val prefix : string
  module Num : AbsNumType
end

module MakeAbsNumProf (A : NumWrap) : AbsNumType with type t = A.Num.t = struct
  include A.Num

  let record s = Prof.record (A.prefix^s)
  let call s = Prof.call (A.prefix^s)

  let () = record "make"
  let make x =
    let t = Sys.time () in
    let r = A.Num.make x in
    let () = call "make" (Sys.time () -. t) in
    r

  let () = record "is_bottom"
  let is_bottom x =
    let t = Sys.time () in
    let r = A.Num.is_bottom x in
    let () = call "is_bottom" (Sys.time () -. t) in
    r

  let () = record "bottom"
  let bottom x =
    let t = Sys.time () in
    let r = A.Num.bottom x in
    let () = call "bottom" (Sys.time () -. t) in
    r

  let () = record "meet_list"
  let meet_list x =
    let t = Sys.time () in
    let r = A.Num.meet_list x in
    let () = call "meet_list" (Sys.time () -. t) in
    r

  let () = record "join_list"
  let join_list x =
    let t = Sys.time () in
    let r = A.Num.join_list x in
    let () = call "join_list" (Sys.time () -. t) in
    r

  let () = record "meet"
  let meet x y =
    let t = Sys.time () in
    let r = A.Num.meet x y in
    let () = call "meet" (Sys.time () -. t) in
    r

  let () = record "join"
  let join x y =
    let t = Sys.time () in
    let r = A.Num.join x y in
    let () = call "join" (Sys.time () -. t) in
    r

  let () = record "widening"
  let widening x y =
    let t = Sys.time () in
    let r = A.Num.widening x y in
    let () = call "widening" (Sys.time () -. t) in
    r

  let () = record "is_included"
  let is_included x y =
    let t = Sys.time () in
    let r = A.Num.is_included x y in
    let () = call "is_included" (Sys.time () -. t) in
    r

  let () = record "forget_list"
  let forget_list x y =
    let t = Sys.time () in
    let r = A.Num.forget_list x y in
    let () = call "forget_list" (Sys.time () -. t) in
    r

  let () = record "fold"
  let fold x y =
    let t = Sys.time () in
    let r = A.Num.fold x y in
    let () = call "fold" (Sys.time () -. t) in
    r

  let () = record "bound_variable"
  let bound_variable x y =
    let t = Sys.time () in
    let r = A.Num.bound_variable x y in
    let () = call "bound_variable" (Sys.time () -. t) in
    r

  let () = record "bound_texpr"
  let bound_texpr x y =
    let t = Sys.time () in
    let r = A.Num.bound_texpr x y in
    let () = call "bound_texpr" (Sys.time () -. t) in
    r

  let () = record "meet_constr"
  let meet_constr x y =
    let t = Sys.time () in
    let r = A.Num.meet_constr x y in
    let () = call "meet_constr" (Sys.time () -. t) in
    r

  let () = record "unify"
  let unify x y =
    let t = Sys.time () in
    let r = A.Num.unify x y in
    let () = call "unify" (Sys.time () -. t) in
    r

  let () = record "expand"
  let expand x y z =
    let t = Sys.time () in
    let r = A.Num.expand x y z in
    let () = call "expand" (Sys.time () -. t) in
    r

  let () = record "assign_expr"
  let assign_expr ?force:(force=false) x y z =
    let t = Sys.time () in
    let r = A.Num.assign_expr ~force:force x y z in
    let () = call "assign_expr" (Sys.time () -. t) in
    r

  let () = record "to_box"
  let to_box x =
    let t = Sys.time () in
    let r = A.Num.to_box x in
    let () = call "to_box" (Sys.time () -. t) in
    r

  let () = record "of_box"
  let of_box x =
    let t = Sys.time () in
    let r = A.Num.of_box x in
    let () = call "of_box" (Sys.time () -. t) in
    r

end

module type DisjWrap = sig
  val prefix : string
  module Num : AbsDisjType
end

module MakeAbsDisjProf (A : DisjWrap) : AbsDisjType = struct
  include MakeAbsNumProf (struct
      let prefix = A.prefix
      module Num = struct
        include A.Num
        let of_box _ = assert false
      end
    end)

  let of_box = A.Num.of_box
  let new_cnstr_blck = A.Num.new_cnstr_blck
  let add_cnstr = A.Num.add_cnstr
  let pop_cnstr_blck = A.Num.pop_cnstr_blck
end


(*************************************************)
(* Numerical Domain with Two Levels of Precision *)
(*************************************************)

module type AbsNumT = sig
  module R : AbsDisjType
  module NR : AbsNumType

  val downgrade : R.t -> NR.t
  (* The second argument is used as a shape *)
  val upgrade : NR.t -> R.t -> R.t
end

module AbsNumTMake (PW : ProgWrap) : AbsNumT = struct
  module VDW = PIMake (PW)

  module RProd = AbsNumProd (VDW) (AbsNumI(BoxManager)) (AbsNumI(PplManager))

  module RNum = AbsDisj (RProd)

  module R = MakeAbsDisjProf (struct
      module Num = RNum
      let prefix = "R."
    end)

  module NRNum = AbsNumI(BoxManager)

  module NR = MakeAbsNumProf (struct
      module Num = NRNum
      let prefix = "NR."
    end)


  let downgrade a = NR.of_box (R.to_box a)

  let upgrade a tshape = R.of_box (NR.to_box a) tshape
end


(*****************************)
(* Points-to Abstract Domain *)
(*****************************)

(* Pointer expressions *)
type ptr_expr = PtVars of mvar list | PtTopExpr

(* Symbolic pointers *)
type ptrs = Ptrs of mem_loc list | TopPtr

let pp_memloc fmt = function MemLoc v -> Format.fprintf fmt "%s" v.v_name

let pp_memlocs fmt l =
  pp_list ~sep:(fun fmt () -> Format.fprintf fmt "@ ") pp_memloc fmt l

let pp_ptr fmt = function
  | Ptrs m -> Format.fprintf fmt "%a" pp_memlocs m
  | TopPtr -> Format.fprintf fmt "#TopPtr"


module type PointsTo = sig
  type t

  (* make takes as input the set of memory locations of the program *)
  val make : mem_loc list -> t

  val meet : t -> t -> t
  val join : t -> t -> t

  val widening : t -> t -> t

  val forget_list : t -> mvar list -> t
  val is_included : t -> t -> bool

  (* val top_mem_loc : t -> mem_loc list *)

  val expand : t -> mvar -> mvar list -> t
  val fold : t -> mvar list -> t

  val var_points_to : t -> mvar -> ptrs
  val assign_ptr_expr : t -> mvar -> ptr_expr -> t

  val unify : t -> t -> t

  val print : Format.formatter -> t -> unit
end

module PointsToImpl : PointsTo = struct
  (* Points-to abstract value *)
  type t = { pts : mem_loc list Ms.t }
             (* top : mem_loc list } *)

  let make mls =
    let string_of_var v = match v.v_ty with
      | Arr _ -> raise (Aint_error "Array(s) in export function's inputs")
      | Bty _ -> string_of_mvar (Mvalue (Avar v)) in

    let pts = List.fold_left (fun pts x -> match x with
        | MemLoc v -> Ms.add (string_of_var v) [x] pts)
        Ms.empty mls in
    { pts = pts }
    (* { pts = pts ; top = mls } *)

  let meet : t -> t -> t = fun t t' ->
    let pts'' =
      Ms.merge (fun _ aop bop -> match aop,bop with
          | None, x | x, None -> x (* None corresponds to TopPtr *)

          | Some l, Some l' ->
            let l_inter = List.filter (fun x -> List.mem x l') l in
            Some (List.sort_uniq Pervasives.compare l_inter )
        ) t.pts t'.pts in

    { t with pts = pts'' }

  let join : t -> t -> t = fun t t' ->
    let pts'' =
      Ms.merge (fun _ aop bop -> match aop,bop with
          | None, _ | _, None -> None (* None corresponds to TopPtr *)

          | Some l, Some l' ->
            Some (List.sort_uniq Pervasives.compare (l @ l'))
        ) t.pts t'.pts in

    { t with pts = pts'' }

  let widening t t' = join t t'

  let svar_points_to : t -> string -> ptrs = fun t s_var ->
    if Ms.mem s_var t.pts then Ptrs (Ms.find s_var t.pts)
    else TopPtr

  let var_points_to : t -> mvar -> ptrs = fun t var ->
    svar_points_to t (string_of_mvar var)

  let forget_list : t -> mvar list -> t = fun t l_rem ->
    let vl_rem = List.map string_of_mvar l_rem in
    { t with pts = Ms.filter (fun v _ -> not (List.mem v vl_rem)) t.pts }

  let is_included : t -> t -> bool = fun t t' ->
    Ms.for_all (fun v l ->
        if Ms.mem v t'.pts then true
        else
          let l' = Ms.find v t'.pts in
          List.for_all (fun x -> List.mem x l') l
      ) t.pts

  (* let top_mem_loc : t -> mem_loc list = fun t -> t.top *)

  let join_ptrs_list ptrss =
    let rec aux acc = function
      | [] -> Ptrs (List.sort_uniq Pervasives.compare acc)
      | TopPtr :: _ -> TopPtr
      | Ptrs l :: tail -> aux (l @ acc) tail in

    aux [] ptrss

  let pt_assign : t -> string -> ptrs -> t = fun t v ptrs -> match ptrs with
    | Ptrs vpts -> { t with pts = Ms.add v vpts t.pts }
    | TopPtr -> { t with pts = Ms.remove v t.pts }

  let assign_ptr_expr : t -> mvar -> ptr_expr -> t = fun t v e -> match e with
    | PtTopExpr -> { t with pts = Ms.remove (string_of_mvar v) t.pts }
    | PtVars el ->
      let v_pts =
        List.fold_left (fun acc var ->
            var_points_to t var :: acc) [] el
        |> join_ptrs_list in

      pt_assign t (string_of_mvar v) v_pts

  let unify : t -> t -> t = meet

  let expand : t -> mvar -> mvar list -> t = fun t v l ->
    let v_pts = var_points_to t v in
    List.fold_left (fun t v' -> pt_assign t (string_of_mvar v') v_pts ) t l

  let fold : t -> mvar list -> t = fun t l -> match l with
    | [] -> assert false
    | v :: tail ->
      let t' = assign_ptr_expr t v (PtVars l) in
      forget_list t' tail

  let print ppf t =
    Format.fprintf ppf "@[<hov 4>* Points-to:@ %a@]@;"
      (pp_list ~sep:(fun _ _ -> ()) (fun ppf (k,l) ->
           if l <> [] then
             Format.fprintf ppf "%s: %a;@,"
               k pp_memlocs l;))
      (List.filter (fun (x,_) -> not (svariables_ignore x)) (Ms.bindings t.pts))

end


(*****************************************)
(* Maps with Equivalence Classes of Keys *)
(*****************************************)

module type Ordered = sig
  type t
  val compare : t -> t -> int
end

module Mc = Map.Int

module Map2 (M : Map.S) = struct
  let map2 : ('a -> 'b -> 'c) -> 'a M.t -> 'b M.t -> 'c M.t =
    fun f map_a map_b ->
      M.mapi (fun k a ->
          let b = M.find k map_b in
          f a b)
        map_a

  let merge2 : (unit -> 'a) -> (unit -> 'b) -> 'a M.t -> 'b M.t -> ('a M.t * 'b M.t)=
    fun fa fb mapa mapb ->
      (M.merge (fun _ aopt _ -> match aopt with
           | None -> fa () |> some
           | Some a -> Some a)
          mapa mapb,
       M.merge (fun _ _ bopt -> match bopt with
           | None -> fb () |> some
           | Some b -> Some b)
         mapa mapb)
end

module type EqMap = sig
  type key
  type 'a t

  val empty : 'a t

  val mem: key -> 'a t -> bool

  val find: key -> 'a t -> 'a

  val adds: key list -> 'a -> 'a t -> 'a t

  val removes: key list -> 'a t -> 'a t

  val map: ('a -> 'b) -> 'a t -> 'b t

  val map2 : ('a -> 'a -> 'c) -> 'a t -> 'a t -> 'c t

  val kfilter : (key -> bool) -> 'a t -> 'a t

  val vmerge:
    ('a option -> 'a option -> 'b option) -> 'a t -> 'a t -> 'b t
end

module MakeEqMap (K : Ordered) : EqMap with type key = K.t = struct
  type key = K.t

  module Mk = Map.Make(K)

  type 'a t = { ktoc : int Mk.t;
                ctov : 'a Mc.t;
                _cpt : int }

  let empty = { ktoc = Mk.empty;
                ctov = Mc.empty;
                _cpt = 0 }

  let newc t = ({ t with _cpt = t._cpt + 1 }, t._cpt)

  let mem k t = try Mc.mem (Mk.find k t.ktoc) t.ctov with Not_found -> false

  let find k t = Mc.find (Mk.find k t.ktoc) t.ctov

  let adds ks a t =
    let t,i = newc t in
    let ktoc =
      List.fold_left (fun ktoc k -> Mk.add k i ktoc) t.ktoc ks in
    { t with ktoc = ktoc; ctov = Mc.add i a t.ctov }

  let map f t = { t with ctov = Mc.map f t.ctov }

  (* This function unifies the equivalence classes of t and t' *)
  let unify_classes : 'a t -> 'b t -> int * int Mk.t * 'a Mc.t * 'b Mc.t =
    fun t t' ->
      let open Utils in
      let module Sk = Set.Make(K) in
      (* This function groupe keys in the same equivalence class *)
      let rec grp l = match l with
        | [] | _ :: [] -> l
        | (x1,l1) :: (x2,l2) :: l' ->
          if x1 = x2 then grp ((x1,Sk.union l1 l2) :: l')
          else (x1,l1) :: grp ((x2,l2) :: l') in

      let s_binds x =
        Mk.bindings x.ktoc
        |> List.stable_sort (fun (_,i) (_,i') -> Pervasives.compare i i')
        |> List.map (fun (x,y) -> (y,Sk.singleton x))
        |> grp in

      let lt,lt' = s_binds t,s_binds t' in
      let ltk = List.fold_left (fun sk (_,sk') ->
          Sk.union sk sk') Sk.empty lt in
      let ltk' = List.fold_left (fun sk (_,sk') ->
          Sk.union sk sk') Sk.empty lt' in

      (* Tedious *)
      let rec merge_ne f_next lt lt' cpt mk mc mc' t t' ltk ltk' = match lt with
        (* We inverse the arguments ! *)
        | [] -> f_next lt' lt cpt mk mc' mc t' t ltk' ltk

        | (i,l) :: r ->
          let k = Sk.any l in
          let oi' = try Some (Mk.find k t'.ktoc) with Not_found -> None in
          let l' = match obind (fun i' -> List.assoc_opt i' lt') oi' with
            | Some s -> s
            | None -> Sk.empty in
          let join =
            Sk.union
              (Sk.inter l l')
              (Sk.union
                 (Sk.diff l ltk')
                 (Sk.diff l' ltk)) in
          let mk = Sk.fold (fun k mk -> Mk.add k cpt mk) join mk in
          let mc = Mc.add cpt (Mc.find i t.ctov) mc in
          let mc' = match oi' with
            | None -> mc'
            | Some i' -> Mc.add cpt (Mc.find i' t'.ctov) mc' in

          let nl, nl' = Sk.diff l join, Sk.diff l' join in
          let nlt = if Sk.is_empty nl then r else (i,nl) :: r in
          let nlt' = match oi' with
            | None -> lt'
            | Some i' ->
              if Sk.is_empty nl' then List.remove_assoc i' lt'
              else assoc_up i' (fun _ -> nl') lt' in

          merge_ne f_next nlt nlt' (cpt + 1) mk mc mc' t t' ltk ltk' in

      merge_ne (merge_ne (fun _ _ cpt mk mc mc' _ _ _ _ -> (cpt,mk,mc,mc')))
        lt lt' 0 Mk.empty Mc.empty Mc.empty t t' ltk ltk'

  let map2 f t t' =
    let cpt,mk,mc,mc' = unify_classes t t' in
    let module M2 = Map2(Mc) in
    { ktoc = mk;
      ctov = M2.map2 f mc mc';
      _cpt = cpt }

  let kfilter (f : key -> bool) (t : 'a t) =
    let module Si = Set.Int in
    let ktoc = Mk.filter (fun k _ -> f k) t.ktoc in
    let si = Mk.fold (fun _ i sk -> Si.add i sk) ktoc Si.empty in
    let ctov = Mc.filter (fun i _ -> Si.mem i si) t.ctov in
    { t with ctov = ctov; ktoc = ktoc }

  let removes (ks : key list) (t : 'a t) =
    kfilter (fun k -> not (List.mem k ks)) t

  let vmerge f t t' =
    let cpt,mk,mc,mc' = unify_classes t t' in
    let mr = Mk.fold (fun _ i mr ->
        if Mc.mem i mr then mr
        else
          let ov = Mc.Exceptionless.find i mc
          and ov' = Mc.Exceptionless.find i mc' in
          match f ov ov' with
          | None -> mr
          | Some rv -> Mc.add i rv mr)
        mk Mc.empty in
    let mk = Mk.filter (fun _ i -> Mc.mem i mr) mk in
    { ktoc = mk; ctov = mr; _cpt = cpt }
end

module EMs = MakeEqMap(Scmp)


(************************************************)
(* Abstraction of numerical and boolean values. *)
(************************************************)

(* Extends a numerical domain to include boolean variable abstractions and
   keep track of initialized variables and points-to information *)
module type AbsNumBoolType = sig
  type t

  (* Make a top value defined on the given variables *)
  val make : mvar list -> mem_loc list -> t

  val meet : t -> t -> t
  val join : t -> t -> t
  val widening : Mtcons.t option -> t -> t -> t

  val forget_list : t -> mvar list -> t
  val forget_bvar : t -> string -> t

  val is_included : t -> t -> bool
  val is_bottom : t -> bool

  (* val top_mem_loc : t -> mem_loc list *)

  val expand : t -> mvar -> mvar list -> t
  val fold : t -> mvar list -> t

  val bound_variable : t -> mvar -> Interval.t
  val bound_texpr : t -> Mtexpr.t -> Interval.t

  (* Does not change the points-to information *)
  val assign_sexpr : ?force:bool -> t -> mvar -> s_expr -> t
  val assign_bexpr : t -> string -> btcons -> t

  val var_points_to : t -> mvar -> ptrs
  val assign_ptr_expr : t -> mvar -> ptr_expr -> t

  val meet_btcons : t -> btcons -> t

  (* Unify the two abstract values on their least common environment. *)
  val unify : t -> t -> t

  (* Variables that are removed are first existentially quantified, and
     variables that are introduced are unconstrained. *)
  val change_environment : t -> mvar list -> t
  val remove_vars : t -> mvar list -> t

  val clear_init : t -> atype list -> t
  val is_init : t -> atype -> t
  val check_init : t -> atype -> bool

  val get_env : t -> Environment.t

  val print : ?full:bool -> Format.formatter -> t -> unit

  val new_cnstr_blck : t -> t
  val add_cnstr : t -> Mtcons.t -> L.t -> t * t
  val pop_cnstr_blck : t -> t
end


module AbsBoolNoRel (AbsNum : AbsNumT) (Pt : PointsTo)
  : AbsNumBoolType = struct

  (* <Ms.find s init> is an over-approximation of the program state where s
     is *not* initialized.
     Remark: we lazily populate init and bool*)
  type t = { bool : AbsNum.NR.t Ms.t;
             init : AbsNum.NR.t EMs.t;
             num : AbsNum.R.t;
             points_to : Pt.t }

  module Ms2 = Map2(Ms)

  let merge_bool_dom t t' =
    let eb,eb' = Ms2.merge2
        (fun () -> AbsNum.downgrade t.num)
        (fun () -> AbsNum.downgrade t'.num)
        t.bool t'.bool in
    ({ t with bool = eb }, { t' with bool = eb' })

  let merge_init_dom t t' =
    let eb = EMs.vmerge (fun x _ -> match x with
        | None -> Some (AbsNum.downgrade t.num)
        | Some _ -> x) t.init t'.init
    and eb' = EMs.vmerge (fun x _ -> match x with
        | None -> Some (AbsNum.downgrade t'.num)
        | Some _ -> x) t'.init t.init in
    ({ t with init = eb }, { t' with init = eb' })

  let apply f df fpt t = { bool = Ms.map df t.bool;
                           init = EMs.map df t.init;
                           num = f t.num;
                           points_to = fpt t.points_to }

  (* Since init and bool are lazily populated, we merge the domains before applying f *)
  let apply2 f df fpt t t' =
    let t, t' = merge_init_dom t t' in
    let t, t' = merge_bool_dom t t' in
    { bool = Ms2.map2 df t.bool t'.bool;
      init = EMs.map2 df t.init t'.init;
      num = f t.num t'.num;
      points_to = fpt t.points_to t'.points_to }

  let for_all2 : ('a -> 'b -> 'c) -> 'a Ms.t -> 'b Ms.t -> bool =
    fun f map_a map_b ->
      Ms.for_all (fun k a ->
          let b = Ms.find k map_b in
          f a b)
        map_a

  let rec bool_vars = function
    | [] -> []
    | h :: t ->
      if ty_mvar h = Bty Bool then
        let vh = string_of_mvar h in
        (bvar_name vh true) :: (bvar_name vh false) :: bool_vars t
      else bool_vars t

  let rec init_vars = function
    | [] -> []
    | Mvalue at :: t -> string_of_mvar (Mvalue at) :: init_vars t
    | _ :: t -> init_vars t

  let make : mvar list -> mem_loc list -> t = fun l mls ->
    let b_vars = bool_vars l in
    let abs = AbsNum.R.make l in
    let dabs = AbsNum.downgrade abs in

    let bmap = List.fold_left (fun bmap bv ->
        Ms.add bv dabs bmap) Ms.empty b_vars in
    { bool = bmap;
      init = EMs.empty;
      num = abs;
      points_to = Pt.make mls }

  let unify_map : AbsNum.NR.t Ms.t -> AbsNum.NR.t Ms.t -> AbsNum.NR.t Ms.t =
    fun b b' ->
      let eb = Ms.merge (fun _ x y -> match x with
          | None -> y
          | Some _ -> x) b b'
      and eb' = Ms.merge (fun _ x y -> match x with
          | None -> y
          | Some _ -> x) b' b in
      Ms2.map2 AbsNum.NR.unify eb eb'


  let eunify_map : AbsNum.NR.t EMs.t -> AbsNum.NR.t EMs.t -> AbsNum.NR.t EMs.t =
    fun b b' ->
      let eb = EMs.vmerge (fun x y -> match x with
          | None -> y
          | Some _ -> x) b b'
      and eb' = EMs.vmerge (fun x y -> match x with
          | None -> y
          | Some _ -> x) b' b in
      EMs.map2 AbsNum.NR.unify eb eb'

  let meet : t -> t -> t = fun t t' ->
    let t,t' = merge_bool_dom t t' in
    { bool = Ms2.map2 AbsNum.NR.meet t.bool t'.bool;
      init = eunify_map t.init t'.init;
      num = AbsNum.R.meet t.num t'.num;
      points_to = Pt.meet t.points_to t'.points_to }

  let join : t -> t -> t = apply2 AbsNum.R.join AbsNum.NR.join Pt.join

  let widening : Mtcons.t option -> t -> t -> t = fun oc ->
    apply2 (AbsNum.R.widening oc) (AbsNum.NR.widening oc) Pt.widening

  let forget_list : t -> mvar list -> t = fun t l ->
    let f x = AbsNum.R.forget_list x l
    and df x = AbsNum.NR.forget_list x l
    and f_pts x = Pt.forget_list x l in
    apply f df f_pts t

  let forget_bvar : t -> string -> t  = fun t s ->
    let dnum = AbsNum.downgrade t.num in
    { t with bool = Ms.add s dnum t.bool }

  (* No need to check anything on t.init and t'.init. *)
  let is_included : t -> t -> bool = fun t t' ->
    (AbsNum.R.is_included t.num t'.num)
    && (for_all2 AbsNum.NR.is_included t.bool t'.bool)
    && (Pt.is_included t.points_to t'.points_to)

  (* let top_mem_loc : t -> mem_loc list = fun t -> Pt.top_mem_loc t.points_to *)

  let is_bottom : t -> bool = fun t -> AbsNum.R.is_bottom t.num

  let bound_variable : t -> mvar -> Interval.t = fun t v ->
    AbsNum.R.bound_variable t.num v

  let bound_texpr : t -> Mtexpr.t -> Interval.t = fun t e ->
    AbsNum.R.bound_texpr t.num e

  let expand : t -> mvar -> mvar list -> t = fun t v vl ->
    let f x = AbsNum.R.expand x v vl
    and df x = AbsNum.NR.expand x v vl
    and f_pts x = Pt.expand x v vl in
    apply f df f_pts t

  let fold : t -> mvar list -> t = fun t vl ->
    let f x = AbsNum.R.fold x vl
    and df x = AbsNum.NR.fold x vl in
    let f_pts x = Pt.fold x vl in
    apply f df f_pts t

  (* abs_beval t bexpr : evaluate bexpr in t.
     We split disequalities in two cases to improve precision. *)
  let rec abs_eval_btcons : t -> btcons -> AbsNum.R.t = fun t bexpr ->
    match bexpr with
    | BLeaf c -> begin match Mtcons.get_typ c with
        | Tcons0.DISEQ ->
          let bexpr_pos = BLeaf (Mtcons.make (Mtcons.get_expr c) Tcons0.SUP) in

          let minus_expr = Mtexpr.unop Texpr0.Neg (Mtcons.get_expr c) in
          let bexpr_neg = BLeaf (Mtcons.make minus_expr Tcons0.SUP) in

          abs_eval_btcons t (BOr (bexpr_pos,bexpr_neg))
        | _ -> AbsNum.R.meet_constr t.num c end

    | BVar (v,neg) ->
      begin try
          let ab = Ms.find (bvar_name v neg) t.bool in
          AbsNum.upgrade ab t.num with
      | Not_found -> t.num end

    | BOr (l_bexpr, r_bexpr) ->
      AbsNum.R.join
        (abs_eval_btcons t l_bexpr)
        (abs_eval_btcons t r_bexpr)

    | BAnd (l_bexpr, r_bexpr) ->
      AbsNum.R.meet
        (abs_eval_btcons t l_bexpr)
        (abs_eval_btcons t r_bexpr)

  let abs_eval_neg_btcons t bexpr = match flip_btcons bexpr with
    | None -> t.num
    | Some c -> abs_eval_btcons t c

  (* Assign an expression given by a list of constrained expressions.
     We do not touch init and points_to there, this has to be done by manualy
     by the caller.
     We unpopulate init to be faster. This is sound if the evaluation of an
     expression neither modifies init not depend on it. *)
  let assign_sexpr : ?force:bool -> t -> mvar -> s_expr -> t =
    fun ?force:(force=false) t v s_expr ->
      let s_init = t.init in
      let points_to_init = t.points_to in
      let t = { t with init = EMs.empty } in

      let n_env = AbsNum.R.get_env t.num in
      let constr_expr_list =
        List.map (fun (bexpr_list, expr) ->
            match bexpr_list with
            | [] -> (None,expr)
            | _ ->
              let constr = List.map (abs_eval_btcons t) bexpr_list
                           |> AbsNum.R.meet_list  in
              (Some constr,expr))
          s_expr in

      let t_list =
        List.map (fun (constr,expr) -> match expr with
            | Some e ->
              let e = Mtexpr.extend_environment e n_env in
              let t' = match constr with
                | None -> t
                | Some c ->
                  let dc = AbsNum.downgrade c in
                  apply (AbsNum.R.meet c) (AbsNum.NR.meet dc) (fun x -> x) t in
              apply
                (fun x -> AbsNum.R.assign_expr ~force:force x v e)
                (fun x -> AbsNum.NR.assign_expr ~force:force x v e)
                (fun x -> x) t'

            | None -> match constr with
              | None -> t
              | Some c ->
                let dc = AbsNum.downgrade c in
                apply (AbsNum.R.meet c) (AbsNum.NR.meet dc) (fun x -> x) t)
          constr_expr_list in

      (* We compute the join of all the assignments *)
      let join_map b_list = match b_list with
        | [] -> assert false
        | h :: l ->
          Ms.mapi (fun key x ->
              let elems = x :: List.map (Ms.find key) l in
              AbsNum.NR.join_list elems) h in

      let b_list,n_list = List.map (fun x -> x.bool) t_list,
                          List.map (fun x -> x.num) t_list in

      { bool = join_map b_list;
        init = s_init;
        num = AbsNum.R.join_list n_list;
        points_to = points_to_init }

  (* Assign a boolean expression.
     As we did in assign_sexpr, we unpopulate init *)
  let assign_bexpr t vb bexpr =
    let s_init = t.init in
    let points_to_init = t.points_to in

    let t = { t with init = EMs.empty } in

    let t_vb, f_vb = bvar_name vb true,
                     bvar_name vb false in

    let new_b =
      Ms.add t_vb (abs_eval_btcons t bexpr |> AbsNum.downgrade) t.bool
      |> Ms.add f_vb (abs_eval_neg_btcons t bexpr |> AbsNum.downgrade) in

    { bool = new_b;
      init = s_init;
      num = t.num;
      points_to = points_to_init }

  let var_points_to t v = Pt.var_points_to t.points_to v

  let assign_ptr_expr t v pt_e =
    { t with points_to = Pt.assign_ptr_expr t.points_to v pt_e }

  let meet_btcons : t -> btcons -> t = fun t c ->
    let cn = abs_eval_btcons t c in
    let dcn = AbsNum.downgrade cn in

    apply (AbsNum.R.meet cn) (AbsNum.NR.meet dcn) (fun x -> x) t

  let unify : t -> t -> t = fun t t' ->
    { bool = unify_map t.bool t'.bool;
      init = eunify_map t.init t'.init;
      num = AbsNum.R.unify t.num t'.num;
      points_to = Pt.unify t.points_to t'.points_to }

  let change_environment : t -> mvar list -> t = fun t l ->
    let bvars = bool_vars l
    and ivars = init_vars l in
    (* We remove the variables that are not in l *)
    let b = Ms.filter (fun s _ -> List.mem s bvars) t.bool
    and init = EMs.kfilter (fun s -> List.mem s ivars) t.init in

    (* We add the variables that are in l but not in t.bool's domain.
       We do not need to do it for t.init, since it is lazily populated *)
    let b = List.fold_left (fun b s ->
        if Ms.mem s b then b
        else Ms.add s (AbsNum.downgrade t.num) b) b bvars in

    (* We change the environment of the underlying numerical domain *)
    let f x = AbsNum.R.change_environment x l
    and df x = AbsNum.NR.change_environment x l in
    apply f df (fun x -> x) { t with bool = b; init = init }

  let remove_vars : t -> mvar list -> t = fun t l ->
    let bvars = bool_vars l
    and ivars = init_vars l in
    (* We remove the variables in l *)
    let b = Ms.filter (fun s _ -> not (List.mem s bvars)) t.bool
    and init = EMs.kfilter (fun s -> not (List.mem s ivars)) t.init in

    (* We change the environment of the underlying numerical domain *)
    let f x = AbsNum.R.remove_vars x l
    and df x = AbsNum.NR.remove_vars x l
    and ptf x = Pt.forget_list x l in
    apply f df ptf { t with bool = b; init = init }


  let clear_init : t -> atype list -> t = fun t l ->
    let l_ext = u8_blast_ats l |> List.map string_of_mvar in
    let init = EMs.removes l_ext t.init in
    { t with init = init }

  let is_init : t -> atype -> t = fun t at ->
    let vats = u8_blast_at at |> List.map string_of_mvar in
    { t with
      init = EMs.adds vats (AbsNum.R.bottom t.num |> AbsNum.downgrade) t.init }

  let check_init : t -> atype -> bool = fun t at ->
    let vats = u8_blast_at at |> List.map string_of_mvar in
    let dnum = AbsNum.downgrade t.num in

    let check x =
      try AbsNum.NR.meet dnum (EMs.find x t.init) |> AbsNum.NR.is_bottom with
      | Not_found -> AbsNum.R.is_bottom t.num in
    List.for_all check vats

  let get_env : t -> Environment.t = fun t -> AbsNum.R.get_env t.num

  let print : ?full:bool -> Format.formatter -> t -> unit =
    fun ?full:(full=false) fmt t ->
      if !only_rel_print then
        Format.fprintf fmt "@[<v 0>%a@]"
          (AbsNum.R.print ~full:full) t.num
      else
        Format.fprintf fmt "@[<v 0>@[<v 0>%a@]@;%a@]"
          (AbsNum.R.print ~full:full) t.num
          Pt.print t.points_to

  let new_cnstr_blck t = { t with num = AbsNum.R.new_cnstr_blck t.num }

  let add_cnstr t c i =
    let tl, tr = AbsNum.R.add_cnstr t.num c i in
    ( { t with num = tl }, { t with num = tr } )

  let pop_cnstr_blck t = { t with num = AbsNum.R.pop_cnstr_blck t.num }
end


module AbsDomMake (PW : ProgWrap) =
  AbsBoolNoRel (AbsNumTMake (PW)) (PointsToImpl)


(**********************)
(* Typing Environment *)
(**********************)

module Ss = Set.Make(Scmp)

module Tcmp = struct
  type t = ty
  let compare = compare
end

module Mty = Map.Make (Tcmp)

type s_env = { m_globs : mvar list; m_locs : mem_loc list }

(*
let add_glob env x ws =
  let ty = Bty (U ws) in
  { env with s_glob = Ms.add x (x,Conv.cty_of_ty ty) env.s_glob }


let add_glob_var s v =
  let uv = L.unloc v in
  match uv.v_kind, uv.v_ty with
  | Global, Bty (U _) -> Ms.add uv.v_name (uv.v_name, Conv.cty_of_ty uv.v_ty) s
  | _ -> s

let rec add_glob_expr s = function
  | Pconst _ | Pbool _ | Parr_init _ -> s
  | Pglobal (sw,x) ->
    let ty = Bty (U sw) in
    Ms.add x (x,Conv.cty_of_ty ty) s
  | Pvar x         -> add_glob_var s x
  | Pget(_,x,e)      -> add_glob_expr (add_glob_var s x) e
  | Pload(_,x,e)   -> add_glob_expr (add_glob_var s x) e
  | Papp1(_, e)    -> add_glob_expr s e
  | Papp2(_,e1,e2) -> add_glob_expr (add_glob_expr s e1) e2
  | PappN (_,es) -> List.fold_left add_glob_expr s es
  | Pif(_,e,e1,e2)   -> add_glob_expr
                        (add_glob_expr
                           (add_glob_expr s e) e1) e2

let add_glob_exprs s es = List.fold_left add_glob_expr s es

let rec add_glob_lv s = function
  | Lnone _      -> s
  | Lvar x       -> add_glob_var s x
  | Lmem (_,x,e)
  | Laset (_,x,e)  -> add_glob_expr (add_glob_var s x) e

let add_glob_lvs s lvs = List.fold_left add_glob_lv s lvs

let rec add_glob_instr s i =
  match i.i_desc with
  | Cassgn(x, _, _, e) -> add_glob_expr (add_glob_lv s x) e
  | Copn(x,_,_,e) -> add_glob_exprs (add_glob_lvs s x) e
  | Cif(e,c1,c2) -> add_glob_body (add_glob_body (add_glob_expr s e) c1) c2
  | Cfor(x,(_,e1,e2), c) ->
    add_glob_body (add_glob_expr (add_glob_expr (add_glob_var s x) e1) e2) c
  | Cwhile(_,c,e,c')    -> add_glob_body (add_glob_expr (add_glob_body s c') e) c
  | Ccall(_,x,_,e) -> add_glob_exprs (add_glob_lvs s x) e

and add_glob_body s c =  List.fold_left add_glob_instr s c
 *)
let get_wsize = function
  | Type.Coq_sword sz -> sz
  | _ -> raise (Aint_error "Not a Coq_sword")



(*********************)
(* Safety conditions *)
(*********************)

type safe_cond =
  | Initv of var
  | Initai of var * wsize * expr
  | Inita of var * int
  | InBound of int * wsize * expr
  | Valid of wsize * var * expr
  | NotZero of wsize * expr
  | Termination

let pp_var = Printer.pp_var ~debug:false
let pp_expr = Printer.pp_expr ~debug:false
let pp_ws fmt ws = Format.fprintf fmt "%i" (int_of_ws ws)

let pp_safety_cond fmt = function
  | Initv x -> Format.fprintf fmt "is_init %a" pp_var x
  | Initai(x,ws,e) ->
    Format.fprintf fmt "is_init (w%d)%a.[%a]" (int_of_ws ws) pp_var x pp_expr e
  | Inita(x,n) -> Format.fprintf fmt "is_init[%i] %a" n pp_var x
  | NotZero(sz,e) -> Format.fprintf fmt "%a <>%a zero" pp_expr e pp_ws sz
  | InBound(n,ws,e)  ->
    Format.fprintf fmt "in_bound: %a-th block of (U%d) words in array of \
                        length %i U8"
      pp_expr e (int_of_ws ws) n
  | Valid (sz, x, e) ->
    Format.fprintf fmt "is_valid %s + %a W%a" x.v_name pp_expr e pp_ws sz
  | Termination -> Format.fprintf fmt "termination"

type violation_loc =
  | InProg of Prog.L.t
  | InReturn of funname

type violation = violation_loc * safe_cond

let pp_violation_loc fmt = function
  | InProg loc -> Format.fprintf fmt "%a" L.pp_sloc loc
  | InReturn fn -> Format.fprintf fmt "%s return" fn.fn_name

let pp_violation fmt (loc,cond) =
  Format.fprintf fmt "%a: %a"
    pp_violation_loc loc
    pp_safety_cond cond

let pp_violations fmt violations =
  if violations = [] then
    Format.fprintf fmt "@[<v>*** No Safety Violation@;@]"
  else
    Format.fprintf fmt "@[<v 2>*** Safety Violation(s):@;@[<v>%a@]@;@]"
      (pp_list pp_violation) violations

let vloc_compare v v' = match v, v' with
  | InReturn fn, InReturn fn' -> Pervasives.compare fn fn'
  | InProg _, InReturn _ -> 1
  | InReturn _, InProg _ -> -1
  | InProg l, InProg l' ->
    Pervasives.compare (fst l.loc_start) (fst l'.loc_start)

let v_compare v v' =
  let c = vloc_compare (fst v) (fst v') in
  if c <> 0 then c
  else Pervasives.compare (snd v) (snd v')

let add64 x e = Papp2 (E.Oadd ( E.Op_w Wsize.U64), Pvar x, e)

let in_bound x ws e =
  match (L.unloc x).v_ty with
  | Arr(ws',n) -> InBound(n * int_of_ws ws' / 8, ws, e)
  | _ -> assert false

let safe_op2 e2 = function
  | E.Oand | E.Oor | E.Oadd _ | E.Omul _ | E.Osub _
  | E.Oland _ | E.Olor _ | E.Olxor _
  | E.Olsr _ | E.Olsl _ | E.Oasr _
  | E.Oeq _ | E.Oneq _ | E.Olt _ | E.Ole _ | E.Ogt _ | E.Oge _ -> []

  | E.Odiv E.Cmp_int -> []
  | E.Omod Cmp_int  -> []
  | E.Odiv (E.Cmp_w(_, s)) -> [NotZero (s, e2)]
  | E.Omod (E.Cmp_w(_, s)) -> [NotZero (s, e2)]

  | E.Ovadd _ | E.Ovsub _ | E.Ovmul _
  | E.Ovlsr _ | E.Ovlsl _ | E.Ovasr _ -> []

let safe_var x = match (L.unloc x).v_ty with
  | Arr(_,n) -> Inita (L.unloc x, n)
  | _ -> Initv(L.unloc x)

let rec safe_e_rec safe = function
  | Pconst _ | Pbool _ | Parr_init _ -> safe
  | Pvar x -> 
    if is_gkvar x then safe_var x.gv :: safe
    else safe
  | Pload (ws,x,e) -> Valid (ws, L.unloc x, e) :: safe_e_rec safe e
  | Pget (aa, ws, x, e) -> 
    assert (aa = Warray_.AAscale); (* NOT IMPLEMENTED *)
    let safe = 
      if is_gkvar x then 
        Initai(L.unloc x.gv, ws, e) :: safe
      else safe  in
    in_bound x.gv ws e :: safe
  | Psub _ -> assert false (* NOT IMPLEMENTED *)
  | Papp1 (_, e) -> safe_e_rec safe e
  | Papp2 (op, e1, e2) -> safe_op2 e2 op @ safe_e_rec (safe_e_rec safe e1) e2
  | PappN (E.Opack _,_) -> safe

  | Pif  (_,e1, e2, e3) ->
    (* We do not check "is_defined e1 && is_defined e2" since
        (safe_e_rec (safe_e_rec safe e1) e2) implies it *)
    safe_e_rec (safe_e_rec (safe_e_rec safe e1) e2) e3

let safe_e = safe_e_rec []

let safe_es = List.fold_left safe_e_rec []

let safe_lval = function
  | Lnone _ | Lvar _ -> []
  | Lmem(ws, x, e) -> Valid (ws, L.unloc x, e) :: safe_e_rec [] e
  | Laset(aa,ws,x,e) -> 
    assert (aa = Warray_.AAscale); (* NOT IMPLEMENTED *)
    in_bound x ws e :: safe_e_rec [] e
  | Lasub _ -> assert false (* NOT IMPLEMENTED *)

let safe_lvals = List.fold_left (fun safe x -> safe_lval x @ safe) []

let safe_opn safe opn es = 
  let id = Expr.get_instr opn in
  List.map (fun c ->
      match c with
      | X86_decl.NotZero(sz, i) ->
        NotZero(sz, List.nth es (Conv.int_of_nat i))) id.i_safe @ safe

let safe_instr ginstr = match ginstr.i_desc with
  | Cassgn (lv, _, _, e) -> safe_e_rec (safe_lval lv) e
  | Copn (lvs,_,opn,es) -> safe_opn (safe_lvals lvs @ safe_es es) opn es
  | Cif(e, _, _) -> safe_e e
  | Cwhile(_,_, _, _) -> []       (* We check the while condition later. *)
  | Ccall(_, lvs, _, es) -> safe_lvals lvs @ safe_es es
  | Cfor (_, (_, e1, e2), _) -> safe_es [e1;e2]

let safe_return main_decl =
  List.fold_left (fun acc v -> safe_var v :: acc) [] main_decl.f_ret


(*********)
(* Utils *)
(*********)

let pcast ws e = match Conv.ty_of_cty (Conv.cty_of_ty (ty_expr e)) with
  | Bty Int -> Papp1 (E.Oword_of_int ws, e)
  | Bty (U ws') ->
    assert (int_of_ws ws' <= int_of_ws ws);
    if ws = ws' then e
    else Papp1 (E.Ozeroext (ws,ws'), e)

  | Bty Bool | Arr _ -> assert false


let obind2 f x y = match x, y with
  | Some u, Some v -> f u v
  | _ -> None

let mvar_of_var v = match v.v_ty with
  | Bty _ -> Mvalue (Avar v)
  | Arr _ -> Mvalue (Aarray v)

let wsize_of_ty ty = match ty with
  | Bty Bool -> assert false
  | Bty Int -> -1
  | Bty (U sz) -> int_of_ws sz
  | Arr (sz, _) -> int_of_ws sz

let rec combine3 l1 l2 l3 = match l1,l2,l3 with
  | h1 :: t1, h2 :: t2, h3 :: t3 -> (h1,h2,h3) :: combine3 t1 t2 t3
  | [], [], [] -> []
  | _ -> raise (Invalid_argument "combine3")

let rec add_offsets assigns = match assigns with
  | [] -> []
  | (Mvalue (Avar v)) :: tail ->
    (Mvalue (Avar v)) :: (MvarOffset v) :: add_offsets tail
  | u :: tail -> u :: add_offsets tail

let rec add_offsets3 assigns = match assigns with
  | [] -> []
  | (ty, Mvalue (Avar v),es) :: tail ->
    (ty, Mvalue (Avar v),es)
    :: (ty, MvarOffset v,es)
    :: add_offsets3 tail
  | u :: tail -> u :: add_offsets3 tail

let fun_locals f_decl =
  let locals = Sv.elements (locals f_decl) in
  List.map mvar_of_var locals
  |> expand_arr_vars
  |> add_offsets

let fun_args_no_offset f_decl = List.map mvar_of_var f_decl.f_args
                                |> expand_arr_vars

let fun_args f_decl = fun_args_no_offset f_decl |> add_offsets

let in_cp_var v = match v with
  | Mvalue (Avar v) -> Some (MinValue v)
  | _ -> None

let fun_in_args_no_offset f_decl =
  fun_args_no_offset f_decl |> List.map in_cp_var

let fun_rets_no_offsets f_decl =
  List.map (fun x -> L.unloc x |> mvar_of_var) f_decl.f_ret
  |> expand_arr_vars

let get_mem_range env = List.map (fun x -> MmemRange x) env.m_locs

let prog_globals env = env.m_globs
(*  List.map (fun (_,(s,ty)) -> Mglobal (s, Conv.ty_of_cty ty))
    (Ms.bindings env.s_glob)
  @ get_mem_range env
  |> expand_arr_vars
  |> add_offsets *)

let fun_vars f_decl env =
  fun_args f_decl
  @ prog_globals env
  @ fun_locals f_decl


(****************************)
(* Expression Linearization *)
(****************************)

(* TODO: careful with signed words. Look at jasmin_word.ec *)
let op1_to_abs_unop op1 = match op1 with
  | E.Oneg _   -> Some Texpr1.Neg
  | E.Oword_of_int _ | E.Oint_of_word _ | E.Ozeroext _ -> assert false
  | _ -> None


let op2_to_abs_binop op2 = match op2 with
  | E.Oadd _ -> Some Texpr1.Add
  | E.Omul _ -> Some Texpr1.Mul
  | E.Osub _ -> Some Texpr1.Sub
  | E.Omod _ -> Some Texpr1.Mod

  | E.Odiv _ -> Some Texpr1.Div

  | E.Oand | E.Oor
  | E.Oland _ | E.Olor _ | E.Olxor _ (* bit-wise boolean connectives *)
  | E.Olsr _ | E.Olsl _ | E.Oasr _
  | E.Oeq _ | E.Oneq _ | E.Olt _ | E.Ole _ | E.Ogt _ | E.Oge _ -> None

  | E.Ovadd (_, _) | E.Ovsub (_, _) | E.Ovmul (_, _)
  | E.Ovlsr (_, _) | E.Ovlsl (_, _) | E.Ovasr (_, _) -> None


(* Return lin_expr mod 2^n *)
let expr_pow_mod apr_env n lin_expr =
  let mod_expr = cst_pow_minus apr_env n 0 in
  Mtexpr.binop Texpr1.Mod lin_expr mod_expr

let word_interval signed ws =
  if signed then
    (* TODO: add signed words *)
    assert false
  else
    let up_mpq = mpq_pow_minus ws 1 in
    Interval.of_mpqf (Mpqf.of_int 0) up_mpq

(* We wrap lin_expr as an out_i word.
   On unsigned word, we do: ((lin_expr % 2^n) + 2^n) % 2^n) *)
(* TODO: this is correct only on unsigned words *)
let wrap_lin_expr n lin_expr =
  let env = Mtexpr.(lin_expr.env) in
  let expr = expr_pow_mod env n lin_expr in

  let pow_expr = cst_pow_minus env n 0 in
  let expr' = Mtexpr.binop Texpr1.Add expr pow_expr in

  expr_pow_mod env n expr'



let print_not_word_expr e =
  Format.eprintf "@[<v>Should be a word expression:@;\
                  @[%a@]@;Type:@;@[%a@]@]@."
    (Printer.pp_expr ~debug:(!Glob_options.debug)) e
    (Printer.pp_ty) (Conv.ty_of_cty (Conv.cty_of_ty (ty_expr e)))

let check_is_int v = match v.v_ty with
  | Bty Int -> ()
  | _ ->
    Format.eprintf "%s should be an int but is a %a"
      v.v_name Printer.pp_ty v.v_ty;
    raise (Aint_error "Bad type")

let check_is_word v = match v.v_ty with
  | Bty (U _) -> ()
  | _ ->
    Format.eprintf "%s should be a word but is a %a"
      v.v_name Printer.pp_ty v.v_ty;
    raise (Aint_error "Bad type")


(*********************)
(* Abstract Iterator *)
(*********************)

(* Locations of the abstract iterator *)
type it_loc =
  | ItFunIn of funname * L.t   (* call-site sensitive function call *)

module ItKey = struct
  type t = it_loc

  let compare = Pervasives.compare
end

module ItMap = Map.Make(ItKey)


(************************)
(* Abstract Interpreter *)
(************************)

module AbsInterpreter (PW : ProgWrap) : sig
  val analyze : unit -> violation list
                        * (Format.formatter -> unit -> unit)
                        * (Format.formatter -> mvar -> unit)
end = struct

  (* We ensure that all variable names are unique *)
  let main_decl,prog = MkUniq.mk_uniq PW.main PW.prog;;

  Prof.reset_all ();;

  module AbsDom = AbsDomMake (struct
      let main = main_decl
      let prog = prog
      let param = PW.param
    end)


  type astate = { it : (AbsDom.t * AbsDom.t) ItMap.t;
                  abs : AbsDom.t;
                  cstack : funname list;
                  env : s_env;
                  prog : unit prog;
                  s_effects : mem_loc list;
                  violations : violation list }

  (* Return true iff the linear expression overflows *)
  let linexpr_overflow abs lin_expr signed ws =
    let int = AbsDom.bound_texpr abs lin_expr in
    let ws_int = word_interval signed ws in

    not (Interval.is_leq int ws_int)

  (* TODO: signed words *)
  let wrap_if_overflow abs e _ ws =
    if linexpr_overflow abs e false ws then
      wrap_lin_expr ws e
    else e

  (* Casting: lin_expr is a in_i word, and we cast it as an out_i word. *)
  (* TODO: signed words *)
  let cast_if_overflows abs out_i in_i lin_expr =
    assert ((out_i <> -1)  && (in_i <> -1));
    if out_i <= in_i then
      wrap_if_overflow abs lin_expr false out_i
    else
      wrap_if_overflow abs lin_expr false in_i

  let aeval_cst_var abs x =
    let int = AbsDom.bound_variable abs (mvar_of_var (L.unloc x)) in
    interval_to_int int

  (* Try to evaluate e to a constant expression in abs *)
  let rec aeval_cst_int abs e = match e with
    | Pvar x -> begin match (L.unloc x.gv).v_ty with
        | Bty Int -> aeval_cst_var abs x.gv
        | Bty (U ws) ->
          let env = AbsDom.get_env abs in
          let line = Mtexpr.var env (mvar_of_var (L.unloc x.gv)) in
          if linexpr_overflow abs line false (int_of_ws ws) then None
          else aeval_cst_var abs x.gv
        | _ -> raise (Aint_error "type error in aeval_cst_int") end

    | Pconst c -> Some (B.to_int c)

    | Papp1 (E.Oneg Op_int, e) ->
      obind (fun x -> Some (- x)) (aeval_cst_int abs e)

    | Papp1 (E.Oint_of_word _, e) ->
      obind (fun x -> Some x) (aeval_cst_int abs e)
    (* No need to check for overflows because we do not allow word operations. *)

    | Papp2 (Oadd Op_int, e1, e2) ->
      obind2 (fun x y -> Some (x + y))
        (aeval_cst_int abs e1) (aeval_cst_int abs e2)

    | Papp2 (Osub Op_int, e1, e2) ->
      obind2 (fun x y -> Some (x - y))
        (aeval_cst_int abs e1) (aeval_cst_int abs e2)

    | Papp2 (Omul Op_int, e1, e2) ->
      obind2 (fun x y -> Some (x * y))
        (aeval_cst_int abs e1) (aeval_cst_int abs e2)

    | _ -> None


  let arr_full_range x =
    List.init
      ((arr_range x) * (arr_size x |> size_of_ws))
      (fun i -> AarrayEl (x, U8, i))

  let abs_arr_range abs x ws ei = match aeval_cst_int abs ei with
    | Some i -> [AarrayEl (x, ws, i)]
    | None -> arr_full_range x

  (* Collect all variables appearing in e. *)
  let ptr_expr_of_expr abs e =
    let exception Expr_contain_load in
    let rec aux acc e = match e with
      | Pbool _ | Parr_init _ | Pconst _ -> acc

      | Pvar x -> mvar_of_var (L.unloc x.gv) :: acc
      | Pget(aa,ws,x,ei) ->
        assert (aa = Warray_.AAscale); (* NOT IMPLEMENTED *)
        (abs_arr_range abs (L.unloc x.gv) ws ei
         |> List.map (fun x -> Mvalue x))
        @ acc
      | Psub _ -> assert false (* NOT IMPLEMENTED *)
      | Papp1 (_, e1) -> aux acc e1
      | PappN (_, es) -> List.fold_left aux acc es

      | Pload _ -> raise Expr_contain_load

      | Pif (_,_,e1,e2) | Papp2 (_, e1, e2) -> aux (aux acc e1) e2 in

    try PtVars (aux [] e) with Expr_contain_load -> PtTopExpr

  exception Unop_not_supported of E.sop1

  exception Binop_not_supported of E.sop2

  exception If_not_supported

  let top_linexpr abs ws_e =
    let lin = Mtexpr.cst (AbsDom.get_env abs) (Coeff.Interval Interval.top) in
    wrap_if_overflow abs lin false (int_of_ws ws_e)

  let rec linearize_iexpr abs (e : expr) =
    let apr_env = AbsDom.get_env abs in
    match e with
    | Pconst z -> mtexpr_of_bigint apr_env z

    | Pvar x ->
      check_is_int (L.unloc x.gv);
      Mtexpr.var apr_env (Mvalue (Avar (L.unloc x.gv)))

    | Papp1(E.Oint_of_word sz,e1) ->
      assert (ty_expr e1 = tu sz);
      let abs_expr1 = linearize_wexpr abs e1 in
      wrap_if_overflow abs abs_expr1 false (int_of_ws sz)

    | Papp1 (op1, e1) ->
      begin match op1_to_abs_unop op1 with
        | Some absop ->
          Mtexpr.unop absop (linearize_iexpr abs e1)

        | None -> raise (Unop_not_supported op1) end

    | Papp2 (op2, e1, e2) ->
      begin match op2_to_abs_binop op2 with
        | Some absop ->
          Mtexpr.(binop absop
                    (linearize_iexpr abs e1)
                    (linearize_iexpr abs e2))

        | None -> raise (Binop_not_supported op2) end

    | Pif _ -> raise If_not_supported

    | _ -> assert false

  and linearize_wexpr abs (e : expr) =
    let apr_env = AbsDom.get_env abs in
    let ws_e = ws_of_ty (ty_expr e) in

    match e with
    | Pvar x ->
      check_is_word (L.unloc x.gv);
      let lin = Mtexpr.var apr_env (Mvalue (Avar (L.unloc x.gv))) in
      wrap_if_overflow abs lin false (int_of_ws ws_e)

    | Papp1(E.Oword_of_int sz,e1) ->
      assert (ty_expr e1 = tint);
      let abs_expr1 = linearize_iexpr abs e1 in
      wrap_if_overflow abs abs_expr1 false (int_of_ws sz)

    | Papp1(E.Ozeroext (osz,isz),e1) ->
      assert (ty_expr e1 = tu isz);
      let abs_expr1 = linearize_wexpr abs e1 in
      cast_if_overflows abs (int_of_ws osz) (int_of_ws isz) abs_expr1

    | Papp1 (op1, e1) ->
      begin match op1_to_abs_unop op1 with
        | Some absop ->
          let lin = Mtexpr.unop absop (linearize_wexpr abs e1) in
          wrap_if_overflow abs lin false (int_of_ws ws_e)

        | None -> raise (Unop_not_supported op1) end

    | Papp2 (op2, e1, e2) ->
      begin match op2_to_abs_binop op2 with
        | Some Texpr1.Mod -> begin match op2 with
            | E.Omod (Cmp_w (_,_))  ->
              (* TODO: signed words *)
              let l_e1 = linearize_wexpr abs e1 in
              let l_e2 = linearize_wexpr abs e2 in

              let lin = Mtexpr.(binop Texpr1.Mod l_e1 l_e2) in
              wrap_if_overflow abs lin false (int_of_ws ws_e)

            | _ ->
              raise (Aint_error "linearize_wexpr : Papp2 : bad type") end

        | Some Texpr1.Add | Some Texpr1.Mul | Some Texpr1.Sub as absop->
          let lin = Mtexpr.(binop (oget absop)
                              (linearize_wexpr abs e1)
                              (linearize_wexpr abs e2)) in
          wrap_if_overflow abs lin false (int_of_ws ws_e)

        | Some Texpr1.Div | Some Texpr1.Pow | None ->
          raise (Binop_not_supported op2) end

    | Pget(aa,ws,x,ei) ->
      assert (aa = Warray_.AAscale); (* NOT IMPLEMENTED *)
      begin match abs_arr_range abs (L.unloc x.gv) ws ei with
        | [] -> assert false
        | [at] ->
          let lin = Mtexpr.var apr_env (Mvalue at) in
          wrap_if_overflow abs lin false (int_of_ws ws_e)
        | _ -> top_linexpr abs ws_e end

    (* We return top on loads and Opack *)
    | PappN (E.Opack _, _) | Pload _ -> top_linexpr abs ws_e

    | _ -> print_not_word_expr e;
      assert false

  let map_f f e_opt = match e_opt with
    | None -> None
    | Some (ty,b,el,er) -> Some (ty, b, f el, f er)

  let rec remove_if_expr_aux : expr ->
    (ty * expr * expr * expr) option = function
    | Pif (ty,e1,et,ef) -> Some (ty,e1,et,ef)

    | Pconst _  | Pbool _ | Parr_init _ | Pvar _ -> None

    | Pget(aa,ws,x,e1) ->
      remove_if_expr_aux e1
      |> map_f (fun ex -> Pget(aa,ws,x,ex))
    | Psub _ -> assert false (* NOT IMPLEMENTED *)
    | Pload (sz, x, e1) ->
      remove_if_expr_aux e1
      |> map_f (fun ex -> Pload (sz,x,ex))

    | Papp1 (op1, e1) ->
      remove_if_expr_aux e1
      |> map_f (fun ex -> Papp1 (op1,ex))

    | Papp2 (op2, e1, e2) ->
      begin match remove_if_expr_aux e1 with
        | Some _ as e_opt -> map_f (fun ex -> Papp2 (op2, ex, e2)) e_opt
        | None -> remove_if_expr_aux e2
                  |> map_f (fun ex -> Papp2 (op2, e1, ex)) end

    | PappN (opn, es) ->
      let rec f_expl i es = match es with
        | [] -> (-1,None)
        | e :: r_es -> match remove_if_expr_aux e with
          | None -> f_expl (i + 1) r_es
          | Some _ as r -> (i,r) in

      match f_expl 0 es with
      | _,None -> None
      | i,Some (ty, b, el, er) ->
        let repi ex = List.mapi (fun j x -> if j = i then ex else x) es in
        Some (ty, b, PappN (opn, repi el), PappN (opn, repi er))


  let rec remove_if_expr (e : expr) = match remove_if_expr_aux e with
    | Some (_,b,el,er) ->
      List.map (fun (l_bool,expr) ->
          (b :: l_bool,expr))
        (remove_if_expr el)
      @ (List.map (fun (l_bool,expr) ->
          ((Papp1 (E.Onot,b)) :: l_bool,expr))
          (remove_if_expr er))
    | None -> [([],e)]


  (* TODO: unsound on signed operations *)
  let op2_to_typ op2 = match op2 with
    | E.Oand | E.Oor | E.Oadd _ | E.Omul _ | E.Osub _
    | E.Odiv _ | E.Omod _ | E.Oland _ | E.Olor _
    | E.Olxor _ | E.Olsr _ | E.Olsl _ | E.Oasr _ -> assert false

    | E.Oeq k -> (Tcons1.EQ, k)
    | E.Oneq k -> (Tcons1.DISEQ, k)
    | E.Olt k -> (Tcons1.SUP, opk_of_cmpk k)
    | E.Ole k -> (Tcons1.SUPEQ, opk_of_cmpk k)
    | E.Ogt k -> (Tcons1.SUP, opk_of_cmpk k)
    | E.Oge k -> (Tcons1.SUPEQ, opk_of_cmpk k)

    | Ovadd (_, _) | Ovsub (_, _) | Ovmul (_, _)
    | Ovlsr (_, _) | Ovlsl (_, _) | Ovasr (_, _) -> assert false

  let rec bexpr_to_btcons_aux : AbsDom.t -> 'a Prog.gexpr -> btcons =
    fun abs e ->
      let aux = bexpr_to_btcons_aux abs in
      match e with
      | Pbool b ->
        let cons =
          if b then true_tcons1 (AbsDom.get_env abs)
          else false_tcons1 (AbsDom.get_env abs) in
        BLeaf cons

      | Pvar x -> BVar (string_of_mvar (Mvalue (Avar (L.unloc x.gv))), true)

      | Pif(_,e1,et,ef) ->
        let bet, bef, be1 = aux et, aux ef, aux e1 in
        let be1_f = match flip_btcons be1 with
          | Some c -> c
          | None -> raise Bop_not_supported in

        BOr ( BAnd(be1,bet), BAnd(be1_f,bef) )

      | Papp1 (op1, e1) -> begin match op1 with
          | E.Onot ->
            let be1 = aux e1 in
            begin match flip_btcons be1 with
              | Some c -> c
              | None -> raise Bop_not_supported end
          | _ -> assert false end

      | Papp2 (op2, e1, e2) -> begin match op2 with
          | E.Oadd _ | E.Omul _ | E.Osub _
          | E.Odiv _ | E.Omod _ | E.Oland _ | E.Olor _
          | E.Olxor _ | E.Olsr _ | E.Olsl _ | E.Oasr _ -> assert false

          | Ovadd (_, _) | Ovsub (_, _) | Ovmul (_, _)
          | Ovlsr (_, _) | Ovlsl (_, _) | Ovasr (_, _) -> assert false

          | E.Oand -> BAnd ( aux e1, aux e2 )

          | E.Oor -> BOr ( aux e1, aux e2 )

          (* TODO: this is unsound on signed words *)
          | E.Oeq _ | E.Oneq _ | E.Olt _ | E.Ole _ | E.Ogt _ | E.Oge _ ->
            match remove_if_expr_aux e with
            | Some (ty,eb,el,er)  -> aux (Pif (ty,eb,el,er))
            | None -> flat_bexpr_to_btcons abs op2 e1 e2 end

      | _ -> assert false

  and flat_bexpr_to_btcons abs op2 e1 e2 =
    let e1',e2' = swap_op2 op2 e1 e2 in
    let lincons, kind = op2_to_typ op2 in

    try let expr = match kind with
        | E.Op_int ->
          let lin1 = linearize_iexpr abs e1'
          and lin2 = linearize_iexpr abs e2' in

          Mtexpr.(binop Sub lin2 lin1)

        | E.Op_w ws ->
          let lin1 = match ty_expr e1' with
            | Bty Int   -> linearize_iexpr abs e1'
            | Bty (U _) -> linearize_wexpr abs e1'
            | _ -> assert false
          and lin2 = match ty_expr e2' with
            | Bty Int   -> linearize_iexpr abs e2'
            | Bty (U _) -> linearize_wexpr abs e2'
            | _ -> assert false in

          (* TODO: signed words *)
          let lin1 = wrap_if_overflow abs lin1 false (int_of_ws ws)
          and lin2 = wrap_if_overflow abs lin2 false (int_of_ws ws) in
          Mtexpr.(binop Sub lin2 lin1) in

      BLeaf (Mtcons.make expr lincons)
    with Unop_not_supported _ | Binop_not_supported _ ->
      raise Bop_not_supported


  let bexpr_to_btcons : 'a Prog.gexpr -> AbsDom.t -> btcons option =
    fun e abs -> try Some (bexpr_to_btcons_aux abs e) with
        Bop_not_supported -> None


  let linearize_if_iexpr : 'a Prog.gexpr -> AbsDom.t -> s_expr =
    fun e abs ->
      List.map (fun (bexpr_list, expr) ->
          let f x = bexpr_to_btcons x abs in
          let b_list = List.map f bexpr_list in

          let b_list =
            if List.exists (fun x -> x = None) b_list then []
            else List.map oget b_list in

          let lin_expr = try Some (linearize_iexpr abs expr) with
            | Unop_not_supported _ | Binop_not_supported _ -> None in

          (b_list, lin_expr))
        (remove_if_expr e)

  let linearize_if_wexpr : int -> expr -> AbsDom.t -> s_expr =
    fun out_sw e abs ->
      List.map (fun (bexpr_list, expr) ->
          let f x = bexpr_to_btcons x abs in
          let b_list = List.map f bexpr_list in

          let b_list =
            if List.exists (fun x -> x = None) b_list then []
            else List.map oget b_list in

          let in_sw = ws_of_ty (ty_expr e) in

          let lin_expr =
            try linearize_wexpr abs expr
                |> cast_if_overflows abs out_sw (int_of_ws in_sw)
                |> some
            with | Unop_not_supported _ | Binop_not_supported _ -> None in

          (b_list, lin_expr))
        (remove_if_expr e)

  let rec linearize_if_expr : int -> 'a Prog.gexpr -> AbsDom.t -> s_expr =
    fun out_ws e abs ->
      match ty_expr e with
      | Bty Int ->
        assert (out_ws = -1);
        linearize_if_iexpr e abs

      | Bty (U _) -> linearize_if_wexpr out_ws e abs

      | Bty Bool -> assert false
      | Arr _ -> assert false


  let init_env : 'info prog -> mem_loc list -> s_env =
    fun (glob_decls, _fun_decls) mem_locs ->
      let m_globs = 
        let gl = List.map fst glob_decls in
        List.map mvar_of_var gl
        |> expand_arr_vars
        |> add_offsets in
      { m_globs; m_locs = mem_locs }

  let init_args f_args state =
    List.fold_left (fun state v -> match v with
        | Mvalue at -> { state with abs = AbsDom.is_init state.abs at }
        | _ -> state )
      state f_args

  let set_zeros f_args abs =
    List.fold_left (fun abs v -> match v with
        | MvarOffset _ | MmemRange _ ->
          let env = AbsDom.get_env abs in
          let z_expr = Mtexpr.cst env (Coeff.s_of_int 0) in
          let z_sexpr = sexpr_from_simple_expr z_expr in

          AbsDom.assign_sexpr ~force:true abs v z_sexpr
        | _ -> abs)
      abs f_args


  let set_bounds f_args abs =
    List.fold_left (fun abs v ->
        let ws = match v with
          | Mvalue (AarrayEl (_,ws,_)) -> Some ws
          | Mvalue (Avar gv) -> begin match gv.v_ty with
              | Bty (U ws) -> Some ws
              | _ -> None end
          | _ -> None in

        (* TODO: for signed words, set the correct bounds here *)
        if ws <> None then
          let int = word_interval false (oget ws |> int_of_ws)
          and env = AbsDom.get_env abs in
          let z_sexpr = Mtexpr.cst env (Coeff.Interval int)
                        |> sexpr_from_simple_expr in

          AbsDom.assign_sexpr abs v z_sexpr
        else abs)
      abs f_args


  let apply_glob globs abs =
    List.fold_left (fun abs (x,e) ->
      match e with
      | Global.Gword (ws, w) -> 
        let i = Conv.bi_of_word ws w in
        let env = AbsDom.get_env abs in
        let sexpr = mtexpr_of_bigint env i |> sexpr_from_simple_expr in
        AbsDom.assign_sexpr abs (Mvalue (Avar x)) sexpr
      | Global.Garr(p,t) -> 
        let ws, es = Conv.to_array x.v_ty p t in
        let add abs i e =
          let env = AbsDom.get_env abs in
          let sexpr = mtexpr_of_bigint env e |> sexpr_from_simple_expr in
          AbsDom.assign_sexpr abs (Mvalue(AarrayEl(x,ws,i))) sexpr in
        List.fold_lefti add abs (Array.to_list es)) 
      abs globs

  let init_state : unit func -> unit prog -> astate =
    fun main_decl (glob_decls, fun_decls) ->
      let mem_locs = List.map (fun x -> MemLoc x) main_decl.f_args in
      let env = init_env (glob_decls, fun_decls) mem_locs in
      let it = ItMap.empty in

      (* We add the initial variables *)
      let f_args = fun_args main_decl in
      (* If f_args is empty, we add a dummy variable to avoid having an
         empty relational abstraction *)
      let f_args = if f_args = [] then [dummy_mvar] else f_args in

      let f_in_args = List.map in_cp_var f_args
      and m_locs = List.map (fun mloc -> MmemRange mloc ) env.m_locs in


      (* We set the offsets and ranges to zero, and bound the variables using
         their types. E.g. register of type U 64 is in [0;2^64]. *)
      let abs = AbsDom.make (f_args @ m_locs) mem_locs
                |> set_zeros (f_args @ m_locs)
                |> set_bounds f_args in

      (* We apply the global declarations *)
      let abs = apply_glob glob_decls abs in

      (* We extend the environment to its local variables *)
      let f_vars = (List.map otolist f_in_args |> List.flatten)
                   @ fun_vars main_decl env in

      let abs = AbsDom.change_environment abs f_vars in

      (* We keep track of the initial values. *)
      let abs = List.fold_left2 (fun abs x oy -> match oy with
          | None -> abs
          | Some y ->
            let sexpr = Mtexpr.var (AbsDom.get_env abs) x
                        |> sexpr_from_simple_expr in
            AbsDom.assign_sexpr abs y sexpr)
          abs f_args f_in_args in

      { it = it;
        abs = abs;
        cstack = [main_decl.f_name];
        env = env;
        prog = (glob_decls, fun_decls);
        s_effects = [];
        violations = [] }

      |> init_args (fun_args main_decl)

  (* Checks that all safety conditions hold, except for valid memory access. *)
  let rec is_safe state = function
    | Initv v -> begin match mvar_of_var v with
        | Mvalue at -> AbsDom.check_init state.abs at
        | _ -> assert false end

    | Inita (v,i) -> begin match mvar_of_var v with
        | Mvalue (Aarray v) ->
          let ws = arr_size v in
          let vels = List.init i (fun n -> AarrayEl (v,ws,n)) in

          List.for_all (AbsDom.check_init state.abs) vels
        | _ -> assert false end

    | Initai (v,ws,e) -> begin match mvar_of_var v with
        | Mvalue (Aarray v) ->
          let is = abs_arr_range state.abs v ws e in
          List.for_all (AbsDom.check_init state.abs) is
        | _ -> assert false end

    | InBound (i,ws,e) ->
      (* We check that (e + 1) * ws/8 is no larger than i *)
      let epp = Papp2 (E.Oadd E.Op_int,
                       e,
                       Pconst (B.of_int 1)) in
      let wse = Papp2 (E.Omul E.Op_int,
                       epp,
                       Pconst (B.of_int ((int_of_ws ws) / 8))) in
      let be = Papp2 (E.Ogt E.Cmp_int, wse, Pconst (B.of_int i)) in

      begin match bexpr_to_btcons be state.abs with
        | None -> false
        | Some c -> AbsDom.is_bottom (AbsDom.meet_btcons state.abs c) end

    | NotZero (ws,e) ->
      (* We check that e is never 0 *)
      let be = Papp2 (E.Oeq (E.Op_w ws), e, pcast ws (Pconst (B.of_int 0))) in
      begin match bexpr_to_btcons be state.abs with
        | None -> false
        | Some c -> AbsDom.is_bottom (AbsDom.meet_btcons state.abs c) end

    | Valid _ | Termination -> true (* These are checked elsewhere *)

  (* Update abs with the abstract memory range for memory accesses. *)
  let rec mem_safety_apply (abs, violations, s_effect) = function
    | Valid (ws,x,e) as pv ->
      begin match AbsDom.var_points_to abs (mvar_of_var x) with
        | Ptrs pts ->
          if List.length pts = 1 then
            let pt = List.hd pts in
            let x_o = Mtexpr.var (AbsDom.get_env abs) (MvarOffset x) in
            let lin_e = linearize_wexpr abs e in
            let c_ws =
              ((int_of_ws ws) / 8)
              |> Coeff.s_of_int
              |> Mtexpr.cst (AbsDom.get_env abs) in
            let ws_plus_e = Mtexpr.binop Texpr1.Add c_ws lin_e in
            let sexpr = Mtexpr.binop Texpr1.Add x_o ws_plus_e
                        |> sexpr_from_simple_expr in

            ( AbsDom.assign_sexpr abs (MmemRange pt) sexpr,
              violations,
              if List.mem pt s_effect then s_effect else pt :: s_effect)
          else (abs, pv :: violations, s_effect)
        | TopPtr -> (abs, pv :: violations, s_effect) end

    | _ -> (abs, violations, s_effect)

  let rec check_safety_rec state unsafe = function
    | [] -> unsafe
    | c :: t ->
      if is_safe state c then check_safety_rec state unsafe t
      else check_safety_rec state (c :: unsafe) t

  let rec mem_safety_rec a = function
    | [] -> a
    | c :: t -> mem_safety_rec (mem_safety_apply a c) t


  let add_violations : astate -> violation list -> astate = fun state ls ->
    { state with violations = List.sort_uniq v_compare (ls @ state.violations) }

  let rec check_safety state loc conds =
    let vsc = check_safety_rec state [] conds in
    let abs, mvsc, s_effects =
      mem_safety_rec (state.abs, [], state.s_effects) conds in
    let state = { state with abs = abs; s_effects = s_effects } in
    let unsafe = vsc @ mvsc |> List.map (fun x -> (loc,x)) in
    if unsafe <> [] then Format.eprintf "%a@." pp_violations unsafe;
    add_violations state unsafe

  type mlvar = MLnone | MLvar of mvar | MLvars of mvar list

  let pp_mlvar fmt = function
    | MLnone -> Format.fprintf fmt "MLnone"
    | MLvar mv -> Format.fprintf fmt "MLvar %a" pp_mvar mv
    | MLvars mvs ->
      Format.fprintf fmt "MLvars @[<hov 2>%a@]"
        (pp_list pp_mvar) mvs

  (* Return te mvar where the abstract assignment takes place. For now, no
     abstraction of the memory. *)
  let mvar_of_lvar abs lv = match lv with
    | Lnone _ -> MLnone
    | Lmem _ -> MLnone
    | Lvar x  ->
      let ux = L.unloc x in
      begin match ux.v_ty with
        | Bty _ -> MLvar (Mvalue (Avar ux))
        | Arr _ -> MLvar (Mvalue (Aarray ux)) end

    | Laset (aa,ws, x, ei) ->
      assert (aa = Warray_.AAscale); (* NOT IMPLEMENTED *)
      begin match abs_arr_range abs (L.unloc x) ws ei
            |> List.map (fun v -> Mvalue v) with
      | [] -> assert false
      | [mv] -> MLvar (mv)
      | _ as mvs -> MLvars mvs
      end
    | Lasub _ -> assert false (* NOT IMPLEMENTED *)
      

  let apply_offset_expr abs outmv inv offset_expr =
    match ty_gvar_of_mvar outmv with
    | None -> abs
    | Some outv ->
      let env = AbsDom.get_env abs in
      let inv_os = Mtexpr.var env (MvarOffset inv) in

      let off_e = linearize_wexpr abs offset_expr
      and e_ws = ws_of_ty (ty_expr offset_expr) in
      let wrap_off_e = wrap_if_overflow abs off_e false (int_of_ws e_ws) in

      let sexpr =
        Mtexpr.binop Texpr1.Add inv_os wrap_off_e
        |> sexpr_from_simple_expr in

      AbsDom.assign_sexpr abs (MvarOffset outv) sexpr

  let aeval_top_offset abs outmv = match ty_gvar_of_mvar outmv with
    | Some outv -> AbsDom.forget_list abs [MvarOffset outv]
    | None -> abs

  let valid_offset_var abs ws_o y =
    if ws_o = Bty (U (U64)) then
      match AbsDom.var_points_to abs (mvar_of_var (L.unloc y)) with
      | TopPtr -> false
      | Ptrs ypts -> List.length ypts = 1
    else false

  (* Evaluate the offset abstraction *)
  let aeval_offset abs ws_o outmv e = match e with
    | Pvar y ->
      let y = y.gv in
      if valid_offset_var abs ws_o y then
        apply_offset_expr abs outmv (L.unloc y) (pcast U64 (Pconst(B.of_int 0)))
      else aeval_top_offset abs outmv

    | Papp2 (op2,el,er) -> begin match op2,el with
        | E.Oadd ( E.Op_w U64), Pvar y ->
          let y = y.gv in
          if valid_offset_var abs ws_o y then
            apply_offset_expr abs outmv (L.unloc y) er
          else aeval_top_offset abs outmv

        | _ -> aeval_top_offset abs outmv end

    | _ -> aeval_top_offset abs outmv

  (* Array assignment. Does the numerical and points-to assignments. *)
  let assign_arr_expr a v e = match v with
    | Mvalue (Aarray gv) -> begin match Mtexpr.(e.mexpr) with
        | Mtexpr.Mvar (Mvalue (Aarray ge)) ->
          let n = arr_range gv in
          let ws = arr_size gv in
          assert (n = arr_range ge);
          assert (ws = arr_size ge);
          List.fold_left (fun a i ->
              let vi = Mvalue (AarrayEl (gv,ws,i))  in
              let eiv = Mvalue (AarrayEl (ge,ws,i)) in
              let ei = Mtexpr.var (AbsDom.get_env a) eiv
                       |> sexpr_from_simple_expr in

              (* Numerical abstraction *)
              let a = AbsDom.assign_sexpr a vi ei in
              (* Points-to abstraction *)
              AbsDom.assign_ptr_expr a vi (PtVars [eiv]))
            a (List.init n (fun i -> i))

        | _ -> assert false end
    | _ -> assert false

  let omvar_is_offset = function
    | MLvar (MvarOffset _) -> true
    | _ -> false

  (* Abstract evaluation of an assignment *)
  let abs_assign : astate -> ty -> mlvar -> expr -> astate =
    fun state out_ty out_mvar e ->
      assert (not (omvar_is_offset out_mvar));
      match ty_expr e, out_mvar with
      | _, MLnone -> state

      | _, MLvars vs -> { state with abs = AbsDom.forget_list state.abs vs }

      | Bty Int, MLvar mvar | Bty (U _), MLvar mvar ->
        (* Numerical abstraction *)
        let lv_s = wsize_of_ty out_ty in
        let s_expr = linearize_if_expr lv_s e state.abs in
        let abs = AbsDom.assign_sexpr state.abs mvar s_expr in

        (* Points-to abstraction *)
        let ptr_expr = ptr_expr_of_expr state.abs e in
        let abs = AbsDom.assign_ptr_expr abs mvar ptr_expr in

        (* Offset abstraction *)
        let abs = aeval_offset abs out_ty mvar e in

        { state with abs = abs }

      | Bty Bool, MLvar mvar ->
        begin let svar = string_of_mvar mvar in
          match bexpr_to_btcons e state.abs with
          | None -> { state with abs = AbsDom.forget_bvar state.abs svar }
          | Some btcons ->
            let abs' = AbsDom.assign_bexpr state.abs svar btcons in
            { state with abs = abs' } end

      | Arr _, MLvar mvar ->
        match e with
        | Pvar x ->
          let x = x.gv in
          let apr_env = AbsDom.get_env state.abs in
          let se = Mtexpr.var apr_env (Mvalue (Aarray (L.unloc x))) in
          begin match mvar with
            | Mvalue (Aarray _) | Temp _ ->
              { state with abs = assign_arr_expr state.abs mvar se }
            | _ -> assert false end

        | Parr_init _ -> state

        | _ ->
          Format.eprintf "@[%a@]@." (Printer.pp_expr ~debug:true) e;
          assert false

  let init_lv lv state = match mvar_of_lvar state.abs lv with
    |  MLvar (Mvalue at) -> { state with abs = AbsDom.is_init state.abs at }
    | _ -> state

  let init_lvs lvs s = List.fold_left (fun s lv -> init_lv lv s) s lvs

  let offsets_of_mvars l = List.map ty_gvar_of_mvar l
                           |> List.filter (fun x -> x <> None)
                           |> List.map (fun x -> MvarOffset (oget x))

  let rec add_offsets_lv assigns = match assigns with
    | [] -> []
    | (ty, Mvalue (Avar v), (lvty, MLvar (Mvalue (Avar vr)))) :: tail ->
      (ty, Mvalue (Avar v), (lvty, MLvar (Mvalue (Avar vr))))
      :: (ty, MvarOffset v, (lvty, MLvar (MvarOffset vr)))
      :: add_offsets_lv tail
    | u :: tail -> u :: add_offsets_lv tail

  (* Prepare the caller for a function call. Returns the state with the
     arguments es evaluated in f input variables. *)
  let aeval_f_args f es state =
    let f_decl = get_fun_def state.prog f |> oget in

    let f_args = fun_args_no_offset f_decl
    and exp_es = expand_arr_exprs es
    and exp_in_tys = f_decl.f_tyin |> expand_arr_tys in

    let assigns = combine3 exp_in_tys f_args exp_es
                  |> List.map (fun (x,y,z) -> (x, MLvar y, z)) in

    let state = List.fold_left (fun state (in_ty, mvar, e) ->
        abs_assign state in_ty mvar e)
        state assigns in

    (f_args,state)

  let aeval_f_return abs ret_assigns =
    List.fold_left (fun abs (out_ty,rvar,(lv,mlvo)) ->
        match mlvo with
        | MLnone -> abs

        | MLvars mlvs -> AbsDom.forget_list abs mlvs

        | MLvar mlv -> match ty_mvar mlv with
          | Bty Bool ->
            let smlv = string_of_mvar mlv in
            let rconstr = BVar (string_of_mvar rvar, true) in
            AbsDom.assign_bexpr abs smlv rconstr

          | _ ->
            let mret = Mtexpr.var (AbsDom.get_env abs) rvar in

            let lv_size = wsize_of_ty (ty_lval lv)
            and ret_size = wsize_of_ty out_ty in

            (* Numerical abstraction *)
            let expr = match ty_mvar mlv, ty_mvar rvar with
              | Bty Int, Bty Int -> mret
              | Bty (U _), Bty Int ->
                (* TODO: Signed *)
                wrap_if_overflow abs mret Unsigned lv_size
              | Bty (U _), Bty (U _) ->
                cast_if_overflows abs lv_size ret_size mret
              | _, _ -> assert false in

            let s_expr = sexpr_from_simple_expr expr in
            let abs = AbsDom.assign_sexpr abs mlv s_expr in

            (* Points-to abstraction *)
            let ptr_expr = PtVars [rvar] in
            let abs = AbsDom.assign_ptr_expr abs mlv ptr_expr in

            (* Offset abstraction *)
            match ty_gvar_of_mvar rvar with
            | None -> abs
            | Some rv ->
              let lrv = L.mk_loc L._dummy rv in
              aeval_offset abs out_ty mlv (Pvar (gkvar lrv)))
      abs ret_assigns


  let forget_f_vars f state =
    let f_decl = get_fun_def state.prog f |> oget in
    let f_vs =  fun_args f_decl @ fun_locals f_decl in

    (* We remove f variables *)
    { state with abs = AbsDom.remove_vars state.abs f_vs }

  let forget_stack_vars state = match state.cstack with
    | [_] | [] -> state
    | _ :: cf :: _ -> forget_f_vars cf state


  (* Forget the values of all variables with have been modified by side-effect
     during a function call.
     Remark: we only log side effects on memory locations, hence we always
     forget global variables. *)
  let forget_side_effect state s_effects =
    let vs_globs = prog_globals state.env
                   |> List.filter (function
                       | MmemRange pt -> List.mem pt s_effects
                       | _ -> true) in
    {state with abs = AbsDom.forget_list state.abs vs_globs }

  (* Forget the values of memory locations that have *not* been modified. *)
  let forget_no_side_effect fstate s_effects =
    let nse_vs = get_mem_range fstate.env
                 |> List.filter (function
                     | MmemRange pt -> not (List.mem pt s_effects)
                     | _ -> true) in
    { fstate with abs = AbsDom.forget_list fstate.abs nse_vs }

  (* Prepare a function call. Returns the state where:
     - The arguments of f have been evaluated.
     - The variables of the caller's caller have been *removed*.
     - s_effects is empty. *)
  let prepare_call state f es =
    let (assign_vars,state) = aeval_f_args f es state in

    let state = init_args assign_vars state
                |> forget_stack_vars in

    let state = { state with abs = AbsDom.new_cnstr_blck state.abs } in

    { state with cstack = f :: state.cstack;
                 s_effects = [] }


  let get_ret_assgns state f_decl lvs =
    let f_map (x,y) = match y with
      | MLnone | MLvars _ -> [x,y]
      | MLvar u ->
        let eu = expand_arr_vars [u] in
        List.map (fun z -> (x, MLvar z)) eu in

    let f_rets_no_offsets = fun_rets_no_offsets f_decl
    and out_tys = f_decl.f_tyout |> expand_arr_tys
    and mlvs = List.map (fun x -> (x, mvar_of_lvar state.abs x)) lvs
               |> List.map f_map
               |> List.flatten in

    combine3 out_tys f_rets_no_offsets mlvs
    |> add_offsets_lv


  let return_call state fstate lvs =
    (* We forget side effects of f in the caller *)
    let state = forget_side_effect state fstate.s_effects in

    (* We pop the top-most block of constraints in the callee *)
    let fstate = { fstate with abs = AbsDom.pop_cnstr_blck fstate.abs } in

    (* We forget variables untouched by f in the callee *)
    let fstate = forget_no_side_effect fstate fstate.s_effects in
    let fname = List.hd fstate.cstack in

    debug(fun () ->
        Format.eprintf "@[<v 0>Side effects of %s: @[<hov 2>%a@]@]@."
          fname.fn_name
          (pp_list pp_mvar) (List.map (fun x -> MmemRange x) fstate.s_effects));

    let state = { abs = AbsDom.meet state.abs fstate.abs;
                  it = fstate.it;
                  env = state.env;
                  prog = state.prog;
                  s_effects = List.unique (state.s_effects @ fstate.s_effects);
                  cstack = state.cstack;
                  violations = List.sort_uniq v_compare
                      (state.violations @ fstate.violations) } in

    (* Finally, we assign the returned values in the corresponding lvalues *)
    let f_decl = get_fun_def fstate.prog fname |> oget in
    let r_assgns = get_ret_assgns state f_decl lvs in
    let state = { state with abs = aeval_f_return state.abs r_assgns } in

    (* We forget the variables of f to get a smaller abstract element,
       and we know that variables in lvs are initialized *)
    forget_f_vars fname state
    |> init_lvs lvs

  let simpl_obtcons = function
    | Some (BLeaf c) -> Some c
    | _ -> None

  let dec_num_of_mtcons c =
    let sc = simpl_obtcons c in
    match omap Mtcons.get_typ sc with
    | Some Lincons0.SUPEQ | Some Lincons0.SUP -> omap Mtcons.get_expr sc
    | _ -> None

  let split_opn n opn es = match opn with
    | E.Oset0 ws -> [None;None;None;None;None;
                     Some (pcast ws (Pconst (B.of_int 0)))]

    | E.Ox86 (X86_instr_decl.CMP ws) ->
      (* Input types: ws, ws *)
      (* Return flags in order: of, cf, sf, ?, zf *)
      let el,er = match es with [el;er] -> el,er | _ -> assert false in
      let of_f = None
      and cf = None
      and sf = None
      and unknown = None
      and zf = Some (Papp2 (E.Oeq (E.Op_w ws),
                            Papp2 (E.Osub (E.Op_w ws),
                                   el,
                                   er),
                            Pconst (B.of_int 0))) in
      [of_f;cf;sf;unknown;zf]

    | _ -> List.init n (fun _ -> None)

  let num_instr_evaluated = ref 0

  let print_ginstr ginstr abs () =
    Format.eprintf "@[<v>@[<v>%a@]@;*** %d Instr: %a %a@;@]%!"
      (AbsDom.print ~full:true) abs
      (let a = !num_instr_evaluated in incr num_instr_evaluated; a)
      L.pp_sloc (fst ginstr.i_loc)
      (Printer.pp_instr ~debug:false) ginstr

  let print_binop fmt (cpt_instr,abs1,abs2,abs3) =
    Format.fprintf fmt "@[<v 2>Of %d:@;%a@]@;\
                        @[<v 2>And %d:@;%a@]@;\
                        @[<v 2>Yield:@;%a@]"
      cpt_instr
      (AbsDom.print ~full:true) abs1
      (!num_instr_evaluated - 1)
      (AbsDom.print ~full:true) abs2
      (AbsDom.print ~full:true) abs3

  let print_if_join cpt_instr ginstr labs rabs abs_r () =
    Format.eprintf "@;@[<v 2>If join %a for Instr:@;%a @;@;%a@]@."
      L.pp_sloc (fst ginstr.i_loc)
      (Printer.pp_instr ~debug:false) ginstr
      print_binop (cpt_instr,
                   labs,
                   rabs,
                   abs_r)

  let print_while_join cpt_instr abs abs_o abs_r () =
    Format.eprintf "@;@[<v 2>While Join:@;%a@]@."
      print_binop (cpt_instr,
                   abs,
                   abs_o,
                   abs_r)

  let print_while_widening cpt_instr abs abs' abs_r () =
    Format.eprintf "@;@[<v 2>While Widening:@;%a@]"
      print_binop (cpt_instr,
                   abs,
                   abs',
                   abs_r)

  let print_return ginstr fabs fname () =
    Format.eprintf "@[<v>@[<v>%a@]Returning %s (called line %a):@;@]%!"
      (AbsDom.print ~full:true) fabs
      fname
      L.pp_sloc (fst ginstr.i_loc)


  let rec aeval_ginstr : 'info instr -> astate -> astate =
    fun ginstr state ->
      debug (print_ginstr ginstr state.abs);

      (* We stop if the abstract state is bottom *)
      if AbsDom.is_bottom state.abs then state
      else
        (* We check the safety conditions *)
        let conds = safe_instr ginstr in
        let state = check_safety state (InProg (fst ginstr.i_loc)) conds in
        aeval_ginstr_aux ginstr state

  and aeval_ginstr_aux : 'info instr -> astate -> astate =
    fun ginstr state -> match ginstr.i_desc with
      | Cassgn (lv, _, _, e) ->
        abs_assign state (ty_lval lv) (mvar_of_lvar state.abs lv) e
        |> init_lv lv

      | Copn (lvs,_,opn,es) ->
        let assgns = split_opn (List.length lvs) opn es in
        let state, mlvs_forget =
          List.fold_left2 (fun (state, mlvs_forget) lv e_opt ->
              match mvar_of_lvar state.abs lv, e_opt with
              | MLnone,_ -> (state, mlvs_forget)

              | MLvar mlv, None -> (state, mlv :: mlvs_forget)
              | MLvar mlv, Some e ->
                (abs_assign state (ty_lval lv) (MLvar mlv) e, mlvs_forget)

              | MLvars mlvs, _ -> (state, mlvs @ mlvs_forget))
            (state,[]) lvs assgns in

        let mlvs_forget = List.sort_uniq Pervasives.compare mlvs_forget in

        { state with abs = AbsDom.forget_list state.abs mlvs_forget }
        |> init_lvs lvs

      | Cif(e,c1,c2) ->
        let eval_cond state = function
          | Some ec -> AbsDom.meet_btcons state.abs ec
          | None -> state.abs in
        let oec = bexpr_to_btcons e state.abs in

        let labs, rabs =
          if Aparam.if_disj && is_some (simpl_obtcons oec) then
            let ec = simpl_obtcons oec |> oget in
            AbsDom.add_cnstr state.abs ec (fst ginstr.i_loc)
          else
            let noec = obind flip_btcons oec in
            ( eval_cond state oec, eval_cond state noec ) in

        let lstate = aeval_gstmt c1 { state with abs = labs } in

        let cpt_instr = !num_instr_evaluated - 1 in

        (* We abstractly evaluate the right branch
           Be careful the start from lstate, as we need to use the
           updated abstract iterator. *)
        let rstate = aeval_gstmt c2 { lstate with abs = rabs } in

        let abs_res = AbsDom.join lstate.abs rstate.abs in
        debug (print_if_join cpt_instr ginstr lstate.abs rstate.abs abs_res);
        { rstate with abs = abs_res }

      | Cwhile(_,c1, e, c2) ->
        let cpt = ref 0 in
        let state = aeval_gstmt c1 state in

        (* We now check that e is safe *)
        let conds = safe_e e in
        let state = check_safety state (InProg (fst ginstr.i_loc)) conds in

        let oec = bexpr_to_btcons e state.abs in

        let eval_body state_i state =
          let cpt_instr = !num_instr_evaluated - 1 in

          let ni_e = dec_num_of_mtcons oec in
          (* We evaluate a quantity that we try to prove is decreasing. *)
          Format.eprintf "@[<v>Candidate decreasing numerical quantity:@;\
                          @[%a@]@;@;@]"
            (pp_opt Mtexpr.print) ni_e;

          let mvar_ni = MNumInv (fst ginstr.i_loc) in
          let state_i = match ni_e with
            | None -> state_i
            | Some nie ->
              { state_i with abs = AbsDom.assign_sexpr state_i.abs
                                 mvar_ni
                                 (sexpr_from_simple_expr nie) } in

          (* We add a disjunctive constraint block *)
          let state_i = { state_i with
                          abs = AbsDom.new_cnstr_blck state_i.abs } in

          let state_o = aeval_gstmt (c2 @ c1) state_i in

          (* We check that ni_e decreased by at least one *)
          let state_o = match ni_e with
            | None -> (* Here, we cannot prove termination *)
              let violation = (InProg (fst ginstr.i_loc), Termination) in
              add_violations state_o [violation]

            | Some nie ->
              let env = AbsDom.get_env state_o.abs in
              let nie = Mtexpr.extend_environment nie env in

              (* (initial nie) - nie - 1 *)
              let e = Mtexpr.(binop Sub
                                (var env mvar_ni) nie) in

              let int = AbsDom.bound_texpr state_o.abs e
              and zint = AbsDom.bound_variable state_o.abs mvar_ni
              and test_intz =
                Interval.of_scalar (Scalar.of_int 0) (Scalar.of_infty 1)
              and test_into =
                Interval.of_scalar (Scalar.of_int 1) (Scalar.of_infty 1) in

              Format.eprintf "@[<v>@;Numerical quantity decreasing by:@;\
                              @[%a@]@;\
                              Initial numerical quantity in interval:@;\
                              @[%a@]@;@]"
                Interval.print int
                Interval.print zint;

              if (Interval.is_leq int test_into) &&
                 (Interval.is_leq zint test_intz) then state_o
              else
                let violation = (InProg (fst ginstr.i_loc), Termination) in
                add_violations state_o [violation] in

          (* We pop the disjunctive constraint block *)
          let state_o = { state_o with
                          abs = AbsDom.pop_cnstr_blck state_o.abs } in

          let abs_r = AbsDom.join state.abs state_o.abs in
          debug (print_while_join cpt_instr state.abs state_o.abs abs_r);
          { state_o with abs = abs_r } in

        let enter_loop state =
          debug (fun () -> Format.eprintf "Loop %d@;" !cpt);
          cpt := !cpt + 1;
          match oec with
          | Some ec ->
            debug (fun () -> Format.eprintf "Meet with %a@;" pp_btcons ec);
            { state with abs = AbsDom.meet_btcons state.abs ec }
          | None ->
            debug (fun () -> Format.eprintf "No meet");
            state in

        (* Unroll one time the loop. *)
        let unroll_once state = eval_body (enter_loop state) state in

        let rec unroll_times i state pre_state =
          if i = 0 then (state,pre_state)
          else unroll_times (i - 1) (unroll_once state) (Some state) in

        let is_stable state pre_state =
          (pre_state <> None) &&
          (AbsDom.is_included state.abs (oget pre_state).abs) in

        let exit_loop state =
          debug (fun () -> Format.eprintf "Exit loop@;");
          match obind flip_btcons oec with
          | Some neg_ec ->
            { state with abs = AbsDom.meet_btcons state.abs neg_ec }
          | None -> state in

        let rec stabilize state pre_state =
          if is_stable state pre_state then exit_loop state
          else
            let cpt_instr = !num_instr_evaluated - 1 in
            let state' = unroll_once state in
            let w_abs =
              AbsDom.widening (simpl_obtcons oec) state.abs state'.abs in
            debug(print_while_widening cpt_instr state.abs state'.abs w_abs);
            stabilize { state' with abs = w_abs } (Some state) in

        let rec stabilize_b state_i pre_state =
          let cpt_i = !num_instr_evaluated - 1 in
          let state = eval_body state_i pre_state in

          if is_stable state (Some pre_state) then exit_loop state
          else
            let state_i' = enter_loop state in

            let w_abs =
              AbsDom.widening (simpl_obtcons oec) state_i.abs state_i'.abs in
            debug(print_while_widening cpt_i state_i.abs state_i'.abs w_abs);
            stabilize_b { state_i' with abs = w_abs } state in

        (* We first unroll the loop k_unroll times. We then stabilize the
           abstraction (in finite time) using AbsDom.widening.
           (k_unroll is a parameter of the analysis). *)
        let state, pre_state = unroll_times Aparam.k_unroll state None in

        if Aparam.widening_out then stabilize state pre_state
        else stabilize_b (enter_loop state) state


      | Ccall(_, lvs, f, es) ->
        let f_decl = get_fun_def state.prog f |> oget in
        let fn = f_decl.f_name in

        debug (fun () -> Format.eprintf "@[<v>Call %s:@;@]" fn.fn_name);

        let fstate = match Aparam.abs_call_strategy with
          | CallDirect -> aeval_call f es state

          | CallWidening ->
            let callsite,_ = ginstr.i_loc in
            aeval_call_widening f es callsite state in

        (* We check the safety conditions of the return *)
        let conds = safe_return f_decl in
        let fstate = check_safety fstate (InReturn fn) conds in

        debug(print_return ginstr fstate.abs fn.fn_name);

        return_call state fstate lvs

      | Cfor(i, (d,e1,e2), c) ->
        match aeval_cst_int state.abs e1, aeval_cst_int state.abs e2 with
        | Some z1, Some z2 ->
          if z1 = z2 then state else
            let init_i, final_i, op = match d with
              | UpTo -> assert (z1 < z2); (z1, z2 - 1, fun x -> x + 1)
              | DownTo -> assert (z1 < z2); (z2, z1 + 1, fun x -> x - 1) in

            let rec mk_range i f op =
              if i = f then [i] else i :: mk_range (op i) f op in

            let range = mk_range init_i final_i op
            and mvari = Mvalue (Avar (L.unloc i))
            and apr_env = AbsDom.get_env state.abs in

            List.fold_left ( fun state ci ->
                (* We add a disjunctive constraint block *)
                let state =
                  { state with abs = AbsDom.new_cnstr_blck state.abs } in

                (* We set the integer variable i to ci. *)
                let expr_ci = Mtexpr.cst apr_env (Coeff.s_of_int ci)
                              |> sexpr_from_simple_expr in
                let abs = AbsDom.assign_sexpr state.abs mvari expr_ci in
                let state =
                  { state with abs = AbsDom.is_init abs (Avar (L.unloc i)) }
                  |> aeval_gstmt c in

                (* We pop the disjunctive constraint block *)
                { state with abs = AbsDom.pop_cnstr_blck state.abs }
              ) state range

        | _ ->
          Format.eprintf "@[<v>For loop: \
                          I was expecting a constant integer expression.@;\
                          Expr1:@[%a@]@;Expr2:@[%a@]@;@."
            (Printer.pp_expr ~debug:true) e1
            (Printer.pp_expr ~debug:true) e2;
          assert false

  and aeval_call : funname -> exprs -> astate -> astate =
    fun f es state ->
      let f_decl = get_fun_def state.prog f |> oget in

      let state = prepare_call state f es in

      aeval_gstmt f_decl.f_body state


  and aeval_call_widening : funname -> exprs -> L.t -> astate -> astate =
    fun f es callsite state ->
      let itk = ItFunIn (f,callsite) in
      if ItMap.mem itk state.it then
        (* f has been abstractly evaluated before *)
        let (in_abs,out_abs) = ItMap.find itk state.it in
        if AbsDom.is_included state.abs in_abs then
          (* We meet with f output over-abstraction, taking care of
             forgetting all variables that may be modified through side
             effects during f evaluation. *)
          let state = forget_side_effect state state.env.m_locs in
          { state with abs = AbsDom.meet state.abs out_abs }
        else
          (* We do a widening to accelerate convergence *)
          let n_in_abs =
            AbsDom.widening None in_abs (AbsDom.join in_abs state.abs) in
          let state = { state with abs = n_in_abs }
                      |> aeval_call f es in
          { state with
            it = ItMap.add itk (n_in_abs,state.abs) state.it }

      else
        (* We abstractly evaluate f for the first time *)
        let in_abs = state.abs in
        let state = aeval_call f es state in
        { state with it = ItMap.add itk (in_abs,state.abs) state.it }

  and aeval_gstmt : 'info stmt -> astate -> astate =
    fun gstmt state ->
      let state = List.fold_left (fun state ginstr ->
          aeval_ginstr ginstr state)
          state gstmt in
      let () = debug (fun () ->
          if gstmt <> [] then
            Format.eprintf "%a%!"
              (AbsDom.print ~full:true) state.abs) in
      state

  let print_mem_ranges state =
    debug(fun () -> Format.eprintf
             "@[<v 0>@;Final offsets full abstract value:@;@[%a@]@]@."
             (AbsDom.print ~full:true) state.abs)

  let print_var_interval state fmt mvar =
    let int = AbsDom.bound_variable state.abs mvar in
    Format.fprintf fmt "@[%a: %a@]"
      pp_mvar mvar
      Interval.print int

  let mem_ranges_printer state f_decl fmt () =
    let in_vars = fun_in_args_no_offset f_decl
                  |> List.map otolist
                  |> List.flatten in
    let vars_to_keep = in_vars @ get_mem_range state.env in
    let vars = in_vars @ fun_vars f_decl state.env in
    let rem_vars = List.fold_left (fun acc v ->
        if (List.mem v vars_to_keep) then acc else v :: acc )
        [] vars in

    let abs_proj = AbsDom.forget_list state.abs rem_vars
                   |> AbsDom.pop_cnstr_blck in

    let sb = !only_rel_print in (* Not very clean *)
    only_rel_print := true;
    Format.fprintf fmt "@[%a@]"
      (AbsDom.print ~full:true) abs_proj;
    only_rel_print := sb


  let analyze () =
    (* Stats *)
    let exception UserInterupt in

    let t_start = Sys.time () in
    let print_stats _ =
      Format.eprintf "@[<v 0>Duration: %1f@;%a@]"
        (Sys.time () -. t_start)
        Prof.print () in

    try
      (* We print stats before exciting *)
      let hndl = Sys.Signal_handle (fun _ -> print_stats (); raise UserInterupt) in
      let old_handler = Sys.signal Sys.sigint hndl in

      let state = init_state main_decl prog in

      (* We abstractly evaluate the main function *)
      let final_st = aeval_gstmt main_decl.f_body state in

      (* We check the safety conditions of the return *)
      let conds = safe_return main_decl in
      let final_st = check_safety final_st (InReturn main_decl.f_name) conds in

      debug(fun () -> Format.eprintf "%a" pp_violations final_st.violations);
      print_mem_ranges final_st;

      let () = debug (fun () -> print_stats ()) in
      let () = Sys.set_signal Sys.sigint old_handler in

      ( final_st.violations,
        mem_ranges_printer final_st main_decl,
        print_var_interval final_st )
    with
    | Manager.Error _ as e -> hndl_apr_exc e
end


module type ExportWrap = sig
  val main : unit Prog.func
  val prog : unit Prog.prog
end

module AbsAnalyzer (EW : ExportWrap) = struct
  let parse_pt_rel s = match String.split_on_char ';' s with
    | [pts;rels] -> { relationals = String.split_on_char ',' rels |> some;
                      pointers = String.split_on_char ',' pts |> some }
    | [_] ->
      raise (Failure "-safetyparam ill-formed (maybe you forgot a ';' ?)")
    | _ ->
      raise (Failure "-safetyparam ill-formed (too many ';' ?)")

  let parse_pt_rels s = String.split_on_char ':' s |> List.map parse_pt_rel

  let parse_params : string -> (string option * analyzer_param list) list =
    fun s ->
      String.split_on_char '|' s
      |> List.map (fun s -> match String.split_on_char '>' s with
          | [fn;ps] -> (Some fn, parse_pt_rels ps)
          | [ps] -> (None, parse_pt_rels ps)
          | _ -> raise (Failure "-safetyparam ill-formed (too many '>' ?)"))

  let analyze () =
    let ps_assoc = omap_dfl (fun s_p -> parse_params s_p)
        [ None, [ { relationals = None; pointers = None } ]]
        !Glob_options.safety_param in

    let ps = try List.assoc (Some EW.main.f_name.fn_name) ps_assoc with
      | Not_found -> try List.assoc None ps_assoc with
        | Not_found -> [ { relationals = None; pointers = None } ] in

    let pt_vars =
      List.fold_left (fun acc p -> match p.pointers with
          | None -> acc
          | Some l -> l @ acc) [] ps
      |> List.sort_uniq Pervasives.compare
      |> List.map (fun pt ->
          try List.find (fun x -> x.v_name = pt) EW.main.f_args with
          | Not_found ->
            raise (Failure ("-safetyparam ill-formed (" ^ pt ^ " unknown)"))) in

    let npt = List.filter (fun x -> not (List.mem x pt_vars)) EW.main.f_args
              |> List.map (fun x -> MmemRange (MemLoc x)) in

    let l_res = List.map (fun p ->
        let module AbsInt = AbsInterpreter (struct
            include EW
            let param = p
          end) in
        AbsInt.analyze ()) ps in

    match l_res with
    | [] -> raise (Failure "-safetyparam ill-formed (empty list of params)")
    | (violations, _, print_mvar_interval) :: _->
      Format.eprintf "@.@[<v>%a@;@;\
                      @[<v 2>Memory ranges:@;%a@]@;\
                      %a@]@."
        pp_violations violations
        (pp_list print_mvar_interval) npt
        (pp_list (fun fmt (_,f,_) -> f fmt ())) l_res;

      if violations <> [] then begin
        Format.eprintf "@[<v>Program is not safe!@;@]@.";
        exit(2)
      end;
end
