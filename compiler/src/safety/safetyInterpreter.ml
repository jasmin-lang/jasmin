open Utils
open Prog
open Apron
open ToEC
open Wsize

open SafetyProf
open SafetyPreanalysis
open SafetyInterfaces
open SafetyUtils
open SafetyExpr
open SafetyVar
open SafetyConstr
open SafetySymEq
open SafetyPointsTo
open SafetyBoolean
    
module Config = SafetyConfig
  
(*------------------------------------------------------------*)
(* REM *)
(* Printexc.record_backtrace true *)

let hndl_apr_exc e = match e with
  | Manager.Error exclog as e ->
    Printexc.print_backtrace stderr;
    Format.eprintf "@[<v>Apron error message:@;@[%a@]@;@]@."
      Manager.print_exclog exclog;
    raise e
  | _ as e -> raise e



(**********************)
(* Typing Environment *)
(**********************)

module Ss = Set.Make(Scmp)

module Tcmp = struct
  type t = ty
  let compare = compare
end

module Mty = Map.Make (Tcmp)

type s_env = { s_glob : (string * Type.stype) Ms.t;
               m_locs : mem_loc list }

let pp_s_env fmt env =
  Format.printf fmt "@[<v>global variables:@;%a@]"
    (pp_list (fun fmt (_,(x,sw)) ->
         Format.fprintf fmt "@[%s: %a@]@,"
           x Printer.pp_ty (Conv.ty_of_cty sw)))
    (Ms.bindings env.s_glob)
    (pp_list (fun fmt i -> Format.fprintf fmt "%d" i))

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

let get_wsize = function
  | Type.Coq_sword sz -> sz
  | _ -> raise (Aint_error "Not a Coq_sword")



(*********************)
(* Safety conditions *)
(*********************)

type safe_cond =
  | Initv of var
  | Initai of var * wsize * expr
  | InBound of int * wsize * expr
  | Valid of wsize * ty gvar * expr
  | NotZero of wsize * expr
  | Termination

let pp_var = Printer.pp_var ~debug:false
let pp_expr = Printer.pp_expr ~debug:false
let pp_ws fmt ws = Format.fprintf fmt "%i" (int_of_ws ws)

let pp_safety_cond fmt = function
  | Initv x -> Format.fprintf fmt "is_init %a" pp_var x
  | Initai(x,ws,e) ->
    Format.fprintf fmt "is_init (w%d)%a.[%a]" (int_of_ws ws) pp_var x pp_expr e
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
    Format.fprintf fmt "@[<v 2>*** Safety Violation(s):@;@[<v>%a@]@]"
      (pp_list pp_violation) violations

let vloc_compare v v' = match v, v' with
  | InReturn fn, InReturn fn' -> Stdlib.compare fn fn'
  | InProg _, InReturn _ -> 1
  | InReturn _, InProg _ -> -1
  | InProg l, InProg l' ->
    Stdlib.compare (fst l.loc_start) (fst l'.loc_start)

let rec lex f = match f with
  | f_cmp :: f_t ->
    let c = f_cmp () in
    if c = 0
    then lex f_t
    else c
  | _ -> 0

let v_compare (loc,c) (loc',c') =
  lex [(fun () -> vloc_compare loc loc');
       (fun () ->  Stdlib.compare c c')]

let add64 x e = Papp2 (E.Oadd ( E.Op_w U64), Pvar x, e)

let in_bound x ws e =
  match (L.unloc x).v_ty with
  | Arr(ws',n) -> [InBound(n * int_of_ws ws' / 8, ws, e)]
  | Bty (U _)-> []                   (* TODO: check this *)
  | _ -> assert false


let init_get x ws e =
  match (L.unloc x).v_ty with
  | Arr _ -> [Initai(L.unloc x, ws, e)]
  | Bty (U _)-> [Initv (L.unloc x)] (* TODO: check this *)
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
  | Arr _ -> []
  | _ -> [Initv(L.unloc x)]

let rec safe_e_rec safe = function
  | Pconst _ | Pbool _ | Parr_init _ | Pglobal _ -> safe
  | Pvar x -> safe_var x @ safe

  | Pload (ws,x,e) -> Valid (ws, L.unloc x, e) :: safe_e_rec safe e
  | Pget (ws, x, e) -> (in_bound x ws e) @ (init_get x ws e) @ safe
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
  | Laset(ws,x,e) -> (in_bound x ws e) @ safe_e_rec [] e

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
  List.fold_left (fun acc v -> safe_var v @ acc) [] main_decl.f_ret


(*********)
(* Utils *)
(*********)

let pcast ws e = match ty_expr e with
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
  | (Mvalue (Avar v)) :: tail when v.v_ty <> Bty (Prog.Bool) ->       
    (Mvalue (Avar v)) :: (MvarOffset v) :: add_offsets tail
  | u :: tail -> u :: add_offsets tail

let rec add_offsets3 assigns = match assigns with
  | [] -> []
  | (ty, Mvalue (Avar v),es) :: tail when v.v_ty <> Bty (Prog.Bool) ->
    (ty, Mvalue (Avar v),es)
    :: (ty, MvarOffset v,es)
    :: add_offsets3 tail
  | u :: tail -> u :: add_offsets3 tail

let fun_locals ~expand_arrays f_decl =
  let locals = Sv.elements (locals f_decl) in
  let vars =
    List.map mvar_of_var locals
    |> add_offsets in

  if expand_arrays
  then expand_arr_vars vars
  else vars


let fun_args_no_offset f_decl = List.map mvar_of_var f_decl.f_args

let fun_args ~expand_arrays f_decl =
  let args = fun_args_no_offset f_decl
             |> add_offsets in
  if expand_arrays
  then expand_arr_vars args
  else args

let in_cp_var v = match v with
  | Mvalue (Avar v) -> Some (MinValue v)
  | _ -> None

let fun_in_args_no_offset f_decl =
  fun_args_no_offset f_decl |> List.map in_cp_var

let fun_rets_no_offsets f_decl =
  List.map (fun x -> L.unloc x |> mvar_of_var) f_decl.f_ret

let get_mem_range env = List.map (fun x -> MmemRange x) env.m_locs

let prog_globals ~expand_arrays env =
  let vars =
    List.map (fun (_,(s,ty)) -> Mglobal (s, Conv.ty_of_cty ty))
      (Ms.bindings env.s_glob)
    @ get_mem_range env
    |> add_offsets in

  if expand_arrays
  then expand_arr_vars vars
  else vars

let fun_vars ~expand_arrays f_decl env =
  fun_args ~expand_arrays:expand_arrays f_decl
  @ prog_globals ~expand_arrays:expand_arrays env
  @ fun_locals ~expand_arrays:expand_arrays f_decl


(****************************)
(* Expression Linearization *)
(****************************)

let op1_to_abs_unop op1 = match op1 with
  | E.Oneg _   -> Some Texpr1.Neg
  | E.Oword_of_int _ | E.Oint_of_word _ | E.Ozeroext _ -> assert false
  | _ -> None


type abs_binop =
  | AB_Unknown
  | AB_Arith of Apron.Texpr1.binop
  | AB_Shift of [`Unsigned_left | `Unsigned_right | `Signed_right ]
  (* Remark: signed left is a synonymous for unsigned left *)               

let abget = function AB_Arith a -> a | _ -> assert false
  
let op2_to_abs_binop op2 = match op2 with
  | E.Oadd _ -> AB_Arith Texpr1.Add
  | E.Omul _ -> AB_Arith Texpr1.Mul                  
  | E.Osub _ -> AB_Arith Texpr1.Sub

  | E.Omod (Cmp_w (Signed, _)) -> AB_Unknown
  | E.Omod _ -> AB_Arith Texpr1.Mod

  | E.Odiv (Cmp_w (Signed, _)) -> AB_Unknown
  | E.Odiv _ -> AB_Arith Texpr1.Div

  | E.Olsr _ -> AB_Shift `Unsigned_right
  | E.Olsl _ -> AB_Shift `Unsigned_left
  | E.Oasr _ -> AB_Shift `Signed_right
      
  | E.Oand | E.Oor
  | E.Oland _ | E.Olor _ | E.Olxor _ (* bit-wise boolean connectives *)
  | E.Oeq _ | E.Oneq _ | E.Olt _ | E.Ole _ | E.Ogt _ | E.Oge _ -> AB_Unknown

  | E.Ovadd (_, _) | E.Ovsub (_, _) | E.Ovmul (_, _)
  | E.Ovlsr (_, _) | E.Ovlsl (_, _) | E.Ovasr (_, _) -> AB_Unknown


(* Return lin_expr mod 2^n *)
let expr_pow_mod apr_env n lin_expr =
  let mod_expr = cst_pow_minus apr_env n 0 in
  Mtexpr.binop Texpr1.Mod lin_expr mod_expr

let word_interval sign ws = match sign with
  | Signed ->
    let pow_m_1 = mpq_pow (ws - 1) in
    let up_mpq = Mpqf.sub pow_m_1 (Mpqf.of_int 1)         
    and down_mpq = Mpqf.neg pow_m_1 in
    Interval.of_mpqf down_mpq up_mpq 

  | Unsigned ->
    let up_mpq = mpq_pow_minus ws 1 in
    Interval.of_mpqf (Mpqf.of_int 0) up_mpq

(* We wrap expr as an out_i word.
   On signed words: ((((lin_expr - 2^(n-1)) % 2^n) + 2^n) % 2^n) - 2^(n-1)
   On unsigned word:  ((lin_expr            % 2^n) + 2^n) % 2^n)             
*)
let wrap_lin_expr sign n expr =
  let env = Mtexpr.(expr.env) in
  match sign with
  | Signed -> 
    let pow_n = cst_pow_minus env n 0 in
    let pow_n_minus_1 = cst_pow_minus env (n - 1) 0 in

    let expr = Mtexpr.binop Texpr1.Sub expr pow_n_minus_1 in
    let expr = expr_pow_mod env n expr in
    let expr = Mtexpr.binop Texpr1.Add expr pow_n in
    let expr = expr_pow_mod env n expr in
    Mtexpr.binop Texpr1.Sub expr pow_n_minus_1 

  | Unsigned ->
    let pow_n = cst_pow_minus env n 0 in
    
    let expr = expr_pow_mod env n expr in
    let expr = Mtexpr.binop Texpr1.Add expr pow_n in
    expr_pow_mod env n expr

let print_not_word_expr e =
  Format.eprintf "@[<v>Should be a word expression:@;\
                  @[%a@]@;Type:@;@[%a@]@]@."
    (Printer.pp_expr ~debug:(!Glob_options.debug)) e
    (Printer.pp_ty) (Conv.ty_of_cty (Conv.cty_of_ty (ty_expr e)))

let check_is_int v = match v.v_ty with
  | Bty Int -> ()
  | _ ->
    Format.eprintf "%s should be an int but is a %a@."
      v.v_name Printer.pp_ty v.v_ty;
    raise (Aint_error "Bad type")

let check_is_word v = match v.v_ty with
  | Bty (U _) -> ()
  | _ ->
    Format.eprintf "%s should be a word but is a %a@."
      v.v_name Printer.pp_ty v.v_ty;
    raise (Aint_error "Bad type")


(***************)
(* Left Values *)
(***************)

type mlvar =
  | MLnone
  | MLvar  of minfo * mvar
  | MLvars of minfo * mvar list (* If there is uncertainty on the lvalue where 
                                   the assignement takes place. *)
 
let pp_mlvar fmt = function
  | MLnone -> Format.fprintf fmt "MLnone"
  | MLvar (info, mv) ->
    Format.fprintf fmt "MLvar (%d) %a" info.i_instr_number pp_mvar mv
  | MLvars (info, mvs) ->
    Format.fprintf fmt "MLvars (%d) @[<hov 2>%a@]"
      info.i_instr_number
      (pp_list pp_mvar) mvs

let mvar_of_lvar_no_array loc lv = match lv with
  | Lnone _ -> MLnone
  | Lmem _ -> MLnone
  | Lvar x  ->
    let ux = L.unloc x in
    begin match ux.v_kind, ux.v_ty with
      | Global,_ -> assert false (* this case should not be possible *)
      (* MLvar (Mglobal (ux.v_name,ux.v_ty)) *)
      | _, Bty _ -> MLvar (loc, Mvalue (Avar ux))
      | _, Arr _ -> MLvar (loc, Mvalue (Aarray ux)) end
  | Laset _ -> assert false



(*********************)
(* Abstract Iterator *)
(*********************)

(* Locations of the abstract iterator *)
type it_loc =
  | ItFunIn of funname * L.t   (* call-site sensitive function call *)

module ItKey = struct
  type t = it_loc

  let compare it it' = match it, it' with
    | ItFunIn (fn,l), ItFunIn (fn',l') ->
      match Prog.F.compare fn fn' with
      | 0 -> Stdlib.compare l l'
      | _ as res -> res
end

module ItMap = Map.Make(ItKey)


(***********************************)
(* Abstract Expression Interpreter *)
(***********************************)

let string_of_sign = function
  | Unsigned -> "Unsigned"
  | Signed -> "Signed"
  
(* Builds and check properties of expressions for the abstract domain [AbsDom]. *)
module AbsExpr (AbsDom : AbsNumBoolType) = struct
  (* Return true iff the linear expression overflows *)
  let linexpr_overflow abs lin_expr sign ws =
    let int = AbsDom.bound_texpr abs lin_expr in
    let ws_int = word_interval sign ws in

    not (Interval.is_leq int ws_int)

  let wrap_if_overflow abs e sign ws =
    if linexpr_overflow abs e sign ws then
      let () = debug (fun () ->
          Format.eprintf "@[<hv 0>Warning: (sub-)expression@ @[%a@]@ \
                          overflowed U%d (as %s)@]@."
            Mtexpr.print_mexpr e.Mtexpr.mexpr
            ws
            (string_of_sign sign)) in
      wrap_lin_expr sign ws e
    else e

  (* Casting: lin_expr is a in_i word, and we cast it as an out_i word. *)
  let cast_if_overflows abs out_i in_i lin_expr =
    assert ((out_i <> -1)  && (in_i <> -1));
    if out_i <= in_i then
      wrap_if_overflow abs lin_expr Unsigned out_i
    else
      wrap_if_overflow abs lin_expr Unsigned in_i

  let aeval_cst_var abs x =
    let int = AbsDom.bound_variable abs (mvar_of_var (L.unloc x)) in
    interval_to_int int

  (* Try to evaluate e to a constant expression in abs *)
  let rec aeval_cst_int abs e = match e with
    | Pvar x -> begin match (L.unloc x).v_ty with
        | Bty Int -> aeval_cst_var abs x
        | Bty (U ws) ->
          let env = AbsDom.get_env abs in
          let line = Mtexpr.var env (mvar_of_var (L.unloc x)) in
          if linexpr_overflow abs line Unsigned (int_of_ws ws) then None
          else aeval_cst_var abs x
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

  (* Try to evaluate e to a constant expression (of type word) in abs.
     Superficial checks only. *)
  let rec aeval_cst_w abs e = match e with
    | Pvar x -> begin match (L.unloc x).v_ty with
        | Bty (U ws) ->
          let env = AbsDom.get_env abs in
          let line = Mtexpr.var env (mvar_of_var (L.unloc x)) in
          if linexpr_overflow abs line Unsigned (int_of_ws ws) then None
          else aeval_cst_var abs x
        | _ -> raise (Aint_error "type error in aeval_cst_w") end

    | Papp1 (E.Oword_of_int ws, e) ->
      let c_e = aeval_cst_int abs e in
      let pws = BatInt.pow 2 (int_of_ws ws) in
      omap (fun c_e -> ((c_e mod pws) + pws) mod pws) c_e

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

      | Pvar x -> mvar_of_var (L.unloc x) :: acc
      | Pglobal (ws,x) -> Mglobal (x,Bty (U ws)) :: acc
      | Pget(ws,x,ei) ->
        (abs_arr_range abs (L.unloc x) ws ei
         |> List.map (fun x -> Mvalue x))
        @ acc

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
    wrap_if_overflow abs lin Unsigned (int_of_ws ws_e)

  let rec linearize_iexpr abs (e : expr) =
    let apr_env = AbsDom.get_env abs in
    match e with
    | Pconst z -> mtexpr_of_bigint apr_env z

    | Pvar x ->
      check_is_int (L.unloc x);
      Mtexpr.var apr_env (Mvalue (Avar (L.unloc x)))

    | Papp1(E.Oint_of_word sz,e1) ->
      let abs_expr1 = linearize_wexpr abs e1 in
      wrap_if_overflow abs abs_expr1 Unsigned (int_of_ws sz)

    | Papp1 (op1, e1) ->
      begin match op1_to_abs_unop op1 with
        | Some absop ->
          Mtexpr.unop absop (linearize_iexpr abs e1)

        | None -> raise (Unop_not_supported op1) end

    | Papp2 (op2, e1, e2) ->
      begin match op2_to_abs_binop op2 with
        | AB_Arith absop ->
          Mtexpr.(binop absop
                    (linearize_iexpr abs e1)
                    (linearize_iexpr abs e2))

        | AB_Unknown -> raise (Binop_not_supported op2)
        | AB_Shift _ -> assert false (* shift only makes sense on bit-vectors *)
      end

    | Pif _ -> raise If_not_supported

    | _ -> assert false

  and linearize_wexpr abs (e : ty gexpr) =
    let apr_env = AbsDom.get_env abs in
    let ws_e = ws_of_ty (ty_expr e) in

    match e with
    | Pvar x ->
      check_is_word (L.unloc x);
      let lin = Mtexpr.var apr_env (Mvalue (Avar (L.unloc x))) in
      wrap_if_overflow abs lin Unsigned (int_of_ws ws_e)

    | Pglobal(ws, x) ->
      let lin = Mtexpr.var apr_env (Mglobal (x,Bty (U ws))) in
      wrap_if_overflow abs lin Unsigned (int_of_ws ws)

    | Papp1(E.Oword_of_int sz,e1) ->
      assert (ty_expr e1 = tint);
      let abs_expr1 = linearize_iexpr abs e1 in
      wrap_if_overflow abs abs_expr1 Unsigned (int_of_ws sz)

    | Papp1(E.Ozeroext (osz,isz),e1) ->
      assert (ty_expr e1 = tu isz);
      let abs_expr1 = linearize_wexpr abs e1 in
      cast_if_overflows abs (int_of_ws osz) (int_of_ws isz) abs_expr1

    | Papp1 (op1, e1) ->
      begin match op1_to_abs_unop op1 with
        | Some absop ->
          let lin = Mtexpr.unop absop (linearize_wexpr abs e1) in
          wrap_if_overflow abs lin Unsigned (int_of_ws ws_e)

        | None -> raise (Unop_not_supported op1) end

    | Papp2 (op2, e1, e2) ->
      begin match op2_to_abs_binop op2 with
        | AB_Arith Texpr1.Mod
        | AB_Arith Texpr1.Mul as absop->
          let lin = Mtexpr.(binop (abget absop)
                              (linearize_wexpr abs e1)
                              (linearize_wexpr abs e2)) in
          wrap_if_overflow abs lin Unsigned (int_of_ws ws_e)

        | AB_Arith Texpr1.Add
        | AB_Arith Texpr1.Sub as absop ->
          let ws_out = int_of_ws ws_e in
          let lin1, lin2 = linearize_wexpr abs e1, linearize_wexpr abs e2 in
          let lin = Mtexpr.(binop (abget absop) lin1 lin2) in
          
          (* If the expression overflows, we try to rewrite differently *)
          if linexpr_overflow abs lin Unsigned ws_out then
            let alt_lin = match e2 with
              | Papp1(E.Oword_of_int sz, Pconst z) ->
                let z = mpqf_of_bigint z in
                let mz = Mpqf.add (Mpqf.neg z) (mpq_pow (int_of_ws sz)) in
                (* We check that [mz] is in [0; 2^{ws_out - 1}] *)
                if (Mpqf.cmp (mpq_pow ws_out) mz > 0) &&
                   (Mpqf.cmp (Mpqf.of_int 0) mz <= 0) then
                  let c' = Mtexpr.cst apr_env (Coeff.s_of_mpqf mz) in
                  let alt_absop = match absop with
                    | AB_Arith Texpr1.Add -> Texpr1.Sub
                    | AB_Arith Texpr1.Sub -> Texpr1.Add
                    | _ -> assert false in
                  Some Mtexpr.(binop alt_absop lin1 c')
                else None
                  
              | _ -> None
            in
            
            if alt_lin <> None &&
               not (linexpr_overflow abs (oget alt_lin) Unsigned ws_out) 
            then
              let () = debug (fun () ->
                  Format.eprintf "@[<hov 0>Replaced the expression@   \
                                  %a@ by %a@]@."
                    Mtexpr.print_mexpr lin.mexpr
                    Mtexpr.print_mexpr (oget alt_lin).mexpr) in
              oget alt_lin
            else wrap_lin_expr Unsigned ws_out lin
          else lin

        | AB_Shift `Signed_right
        | AB_Arith Texpr1.Div
        | AB_Arith Texpr1.Pow
        | AB_Unknown ->
          raise (Binop_not_supported op2)

        | AB_Shift stype  -> match aeval_cst_w abs e2 with
          | Some i when i <= int_of_ws ws_e ->
            let absop = match stype with
              | `Unsigned_right -> Texpr1.Div
              | `Unsigned_left -> Texpr1.Mul
              | _ -> assert false in
            let lin = Mtexpr.(binop absop
                                (linearize_wexpr abs e1)
                                (cst_pow_minus apr_env i 0)) in

            wrap_if_overflow abs lin Unsigned (int_of_ws ws_e)

          | _ ->
            raise (Binop_not_supported op2)
      end

    | Pget(ws,x,ei) ->
      begin match abs_arr_range abs (L.unloc x) ws ei with
        | [] -> assert false
        | [at] ->
          let lin = Mtexpr.var apr_env (Mvalue at) in
          wrap_if_overflow abs lin Unsigned (int_of_ws ws_e)
        | _ -> top_linexpr abs ws_e end

    (* We return top on loads and Opack *)
    | PappN (E.Opack _, _) | Pload _ -> top_linexpr abs ws_e

    | _ -> print_not_word_expr e;
      assert false

  let map_f f e_opt = match e_opt with
    | None -> None
    | Some (ty,b,el,er) -> Some (ty, b, f el, f er)

  let rec remove_if_expr_aux : 'a Prog.gexpr ->
    ('a * 'a Prog.gexpr * 'a Prog.gexpr * 'a Prog.gexpr) option = function
    | Pif (ty,e1,et,ef) -> Some (ty,e1,et,ef)

    | Pconst _  | Pbool _ | Parr_init _ | Pvar _ | Pglobal _ -> None

    | Pget(ws,x,e1) ->
      remove_if_expr_aux e1
      |> map_f (fun ex -> Pget(ws,x,ex))

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


  let rec remove_if_expr (e : 'a Prog.gexpr) = match remove_if_expr_aux e with
    | Some (_,b,el,er) ->
      List.map (fun (l_bool,expr) ->
          (b :: l_bool,expr))
        (remove_if_expr el)
      @ (List.map (fun (l_bool,expr) ->
          ((Papp1 (E.Onot,b)) :: l_bool,expr))
          (remove_if_expr er))
    | None -> [([],e)]

  let op2_to_typ op2 =
    let to_cmp_kind = function
      | E.Op_int -> E.Cmp_int
      | E.Op_w ws -> E.Cmp_w (Unsigned, ws) in

    match op2 with
    | E.Oand | E.Oor | E.Oadd _ | E.Omul _ | E.Osub _
    | E.Odiv _ | E.Omod _ | E.Oland _ | E.Olor _
    | E.Olxor _ | E.Olsr _ | E.Olsl _ | E.Oasr _ -> assert false

    | E.Oeq k -> (Tcons1.EQ, to_cmp_kind k)
    | E.Oneq k -> (Tcons1.DISEQ, to_cmp_kind k)
    | E.Olt k -> (Tcons1.SUP, k)
    | E.Ole k -> (Tcons1.SUPEQ, k)
    | E.Ogt k -> (Tcons1.SUP, k)
    | E.Oge k -> (Tcons1.SUPEQ, k)

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

    | Pvar x -> BVar (Bvar.make (Mvalue (Avar (L.unloc x))) true)

    | Pglobal _ -> assert false (* Global variables are of type word *)

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

        | E.Oeq _ | E.Oneq _ | E.Olt _ | E.Ole _ | E.Ogt _ | E.Oge _ ->
          match remove_if_expr_aux e with
          | Some (ty,eb,el,er)  -> aux (Pif (ty,eb,el,er))
          | None -> flat_bexpr_to_btcons abs op2 e1 e2 end

    | _ -> assert false

  and flat_bexpr_to_btcons abs op2 e1 e2 =
    let e1',e2' = swap_op2 op2 e1 e2 in
    let lincons, cmp_kind = op2_to_typ op2 in

    (* (Sub lin2 lin1) lincos 0  *)
    try let lin2,lin1 = match cmp_kind with
        | E.Cmp_int ->
          let lin1 = linearize_iexpr abs e1'
          and lin2 = linearize_iexpr abs e2' in
          lin2, lin1
        (* Mtexpr.(binop Sub lin2 lin1) *)

        | E.Cmp_w (sign, ws) ->
          let lin1 = match ty_expr e1' with
            | Bty Int   -> linearize_iexpr abs e1'
            | Bty (U _) -> linearize_wexpr abs e1'
            | _ -> assert false
          and lin2 = match ty_expr e2' with
            | Bty Int   -> linearize_iexpr abs e2'
            | Bty (U _) -> linearize_wexpr abs e2'
            | _ -> assert false in

          let lin1 = wrap_if_overflow abs lin1 sign (int_of_ws ws)
          and lin2 = wrap_if_overflow abs lin2 sign (int_of_ws ws) in
          (* Mtexpr.(binop Sub lin2 lin1)  *)
          lin2, lin1
      in

      (* We do some basic simplifications.
         [expr lincons 0] must be equivalent to [(Sub lin2 lin1) lincos 0] *)
      let expr = match lincons, lin2, lin1 with
        | (Tcons1.EQ | Tcons1.DISEQ), { mexpr = Mtexpr.Mcst cst }, lin
        | (Tcons1.EQ | Tcons1.DISEQ), lin, { mexpr = Mtexpr.Mcst cst } ->      
          if Coeff.equal_int cst 0
          then lin
          else Mtexpr.(binop Sub lin2 lin1) 
        | _ -> Mtexpr.(binop Sub lin2 lin1) 
      in
      BLeaf (Mtcons.make expr lincons)

    with Unop_not_supported _ | Binop_not_supported _ ->
      raise Bop_not_supported


  let bexpr_to_btcons : 'a Prog.gexpr -> AbsDom.t -> btcons option =
    fun e abs ->
    try let c = bexpr_to_btcons_aux abs e in
      (* We substitute variables in [bexpr] using known symbolic 
         equalities in [t.sym] *)
      Some (AbsDom.subst_btcons abs c)
    with Bop_not_supported -> None


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

  let linearize_if_wexpr : int -> ty gexpr -> AbsDom.t -> s_expr =
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


  let set_zeros f_args abs =
    List.fold_left (fun abs v -> match v with
        | MvarOffset _ | MmemRange _ ->
          let env = AbsDom.get_env abs in
          let z_expr = Mtexpr.cst env (Coeff.s_of_int 0) in
          let z_sexpr = sexpr_from_simple_expr z_expr in

          AbsDom.assign_sexpr ~force:true abs v None z_sexpr
        | _ -> abs)
      abs f_args


  let bound_warning gv ws fmt =
    Format.fprintf fmt
      "We assume, as in the source program, that only the lower %d \
       bits of [%a] are initially set"
      (int_of_ws ws) (Printer.pp_var ~debug:false) gv 

  let bound_warning_user gv min max fmt =
    Format.fprintf fmt
      "Input variable [%a] assumed to be initially in [%a; %a]"
      (Printer.pp_var ~debug:false) gv
      Mpqf.print min Mpqf.print max
    
  let input_range_bound gv ws =
    let open Config in
    let ranges = sc_input_ranges () in
    try
      let ir = List.find (fun x -> gv.v_name = x.ir_name) ranges in
      let min, max = Mpqf.of_string ir.ir_min, Mpqf.of_string ir.ir_max in
      let ws_max = Mpqf.sub (mpq_pow (ws - 1)) (Mpqf.of_int 1) in

      if Mpqf.cmp (Mpqf.of_int 0) min = 1 
      then begin
        Format.eprintf "Input range bound for [%s]: \"min\" must \
                        be positive" gv.v_name ;
        exit 1 end;

      if Mpqf.cmp max ws_max = 1 
      then begin
        Format.eprintf "Input range bound for [%s]: \"max\" must \
                        be below %a" gv.v_name Mpqf.print ws_max;
        exit 1 end;
      
      Some (Interval.of_mpqf min max, bound_warning_user gv min max)
    with Not_found -> None
  
  (* We set bounds for the arguments, according to the register sizes
     in the source program. E.g., if a U32 register variable is
     allocated to a U64 register, then we assume that it contains a
     value in [0; 2^32 - 1].  We print a warning at the end of the
     analysis, to make this assumption clear. *)
  let set_bounds f_args source_f_args abs =
    assert (List.length f_args = List.length source_f_args);
    let abs, warns =
      List.fold_left2 (fun (abs, warns) v source_v ->
          let gv_ws, warn = match v, source_v with
            | Mvalue (AarrayEl (_,_ws,_)), _ ->
              (* Export function cannot have arrays as input. *)
              assert false (* Some ws *)

            | Mvalue (Avar gv), Mvalue (Avar source_gv) ->
              begin match gv.v_ty, source_gv.v_ty with
                | Bty (U ws), Bty (U ws') ->
                  if ws = ws'
                  then Some (gv, ws), None
                  else
                    let () = assert (int_of_ws ws > int_of_ws ws') in
                    Some (gv, ws'), Some (bound_warning gv ws')

                | _ -> None, None end
            | _ -> None, None in          
          
          if gv_ws <> None then
            let gv, ws = oget gv_ws in
            let ws_i = int_of_ws ws in
            let int, warn = match input_range_bound gv ws_i with
              | None -> word_interval Unsigned ws_i, warn

              (* overwrites the previous warning *)
              | Some (int, warn) -> int, Some warn
            in
            let env = AbsDom.get_env abs in
            let z_sexpr = Mtexpr.cst env (Coeff.Interval int)
                          |> sexpr_from_simple_expr in

            let warns = match warn with
              | None -> warns
              | Some warn -> warn :: warns in

            (AbsDom.assign_sexpr abs v None z_sexpr, warns)
          else (abs, warns))
        (abs, []) f_args source_f_args
    in
    abs, warns


  let apply_glob globs abs =
    List.fold_left (fun abs (ws,n,i) ->
        let env = AbsDom.get_env abs in
        let sexpr = mtexpr_of_bigint env i |> sexpr_from_simple_expr in
        AbsDom.assign_sexpr abs (Mglobal (n, Bty (U ws))) None sexpr)
      abs globs


  (*-------------------------------------------------------------------------*)
  (* Return te mvar where the abstract assignment takes place. For now, no
     abstraction of the memory. *)
  let mvar_of_lvar abs loc lv = match lv with
    | Lnone _ | Lmem _ | Lvar _ -> mvar_of_lvar_no_array loc lv

    | Laset (ws, x, ei) ->
      match abs_arr_range abs (L.unloc x) ws ei
            |> List.map (fun v -> Mvalue v) with
      | [] -> assert false
      | [mv] -> MLvar (loc, mv)
      | _ as mvs -> MLvars (loc, mvs)

  let apply_offset_expr abs outmv info inv offset_expr =
    match ty_gvar_of_mvar outmv with
    | None -> abs
    | Some outv ->
      let env = AbsDom.get_env abs in
      let inv_os = Mtexpr.var env (MvarOffset inv) in

      let off_e = linearize_wexpr abs offset_expr
      and e_ws = ws_of_ty (ty_expr offset_expr) in
      let wrap_off_e = wrap_if_overflow abs off_e Unsigned (int_of_ws e_ws) in

      let sexpr =
        Mtexpr.binop Texpr1.Add inv_os wrap_off_e
        |> sexpr_from_simple_expr in

      AbsDom.assign_sexpr abs (MvarOffset outv) info sexpr

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
  let aeval_offset abs ws_o outmv info e = match e with
    | Pvar y ->
      if valid_offset_var abs ws_o y then
        let o = pcast U64 (Pconst(B.of_int 0)) in
        apply_offset_expr abs outmv info (L.unloc y) o
      else aeval_top_offset abs outmv

    | Papp2 (op2,el,er) -> begin match op2,el with
        | E.Oadd ( E.Op_w U64), Pvar y ->
          if valid_offset_var abs ws_o y then
            apply_offset_expr abs outmv info (L.unloc y) er
          else aeval_top_offset abs outmv

        | _ -> aeval_top_offset abs outmv end

    | _ -> aeval_top_offset abs outmv

  (* Initialize variable or array elements. *)
  let a_init_mv_no_array mv abs = match mv with
    |  Mvalue (AarrayEl _ as at) |  Mvalue (Avar _ as at) ->
      AbsDom.is_init abs at
    | _ -> assert false

  (* Initialize variable or array elements lvalues. *)
  let a_init_mlv_no_array mlv abs = match mlv with
    | MLvar (_,mv) -> a_init_mv_no_array mv abs
    | _ -> assert false

  (* Array assignment. Does the numerical assignments.
     Remark: array elements do not need to be tracked in the point-to
     abstraction. *)
  let assign_arr_expr a v e =
    match v with
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
              let a = AbsDom.assign_sexpr a vi None ei in

              (* Initialization *)
              List.fold_left2 (fun a vi eiv ->
                  AbsDom.copy_init a vi eiv)
                a
                (u8_blast_var ~blast_arrays:true vi)
                (u8_blast_var ~blast_arrays:true eiv))

            a (List.init n (fun i -> i))

        | _ -> assert false end
    | _ -> assert false


  let omvar_is_offset = function
    | MLvar (_, MvarOffset _) -> true
    | _ -> false

  (* Abstract evaluation of an assignment. 
     Also handles variable initialization. *)
  let abs_assign : AbsDom.t -> 'a gty -> mlvar -> ty gexpr -> AbsDom.t =
    fun abs out_ty out_mvar e ->
      assert (not (omvar_is_offset out_mvar));
      match ty_expr e, out_mvar with
      | _, MLnone -> abs

      (* Here, we have no information on which elements are initialized. *)
      | _, MLvars (_, vs) -> AbsDom.forget_list abs vs 

      | Bty Int, MLvar (loc, mvar) | Bty (U _), MLvar (loc, mvar) ->
        (* Numerical abstraction *)
        let lv_s = wsize_of_ty out_ty in
        let s_expr = linearize_if_expr lv_s e abs in
        let abs0 = abs in
        let abs = AbsDom.assign_sexpr abs mvar (Some loc) s_expr in

        (* Points-to abstraction *)
        let ptr_expr = ptr_expr_of_expr abs0 e in
        let abs = AbsDom.assign_ptr_expr abs mvar ptr_expr in

        (* Offset abstraction *)
        let abs = aeval_offset abs out_ty mvar (Some loc) e in
        
        a_init_mlv_no_array out_mvar abs

      | Bty Bool, MLvar (_, mvar) ->
        begin
          let abs = match bexpr_to_btcons e abs with
            | None -> AbsDom.forget_bvar abs mvar 
            | Some btcons -> AbsDom.assign_bexpr abs mvar btcons in
          a_init_mlv_no_array out_mvar abs
        end

      | Arr _, MLvar (_, mvar) ->
        match e with
        | Pvar x ->
          let apr_env = AbsDom.get_env abs in
          let se = Mtexpr.var apr_env (Mvalue (Aarray (L.unloc x))) in
          begin match mvar with
            | Mvalue (Aarray _) -> assign_arr_expr abs mvar se 
            | Temp _ -> assert false (* this case should not be possible *)
            | _ -> assert false end

        | Parr_init _ -> abs

        | _ ->
          Format.eprintf "@[%a@]@." (Printer.pp_expr ~debug:true) e;
          assert false

  let abs_assign_opn abs loc lvs assgns =
    let abs, mlvs_forget =
      List.fold_left2 (fun (abs, mlvs_forget) lv e_opt ->
          match mvar_of_lvar abs loc lv, e_opt with
          | MLnone, _ -> (abs, mlvs_forget)

          | MLvar (_,mlv) as cmlv, None ->
            (* Remark: n-ary operation cannot return arrays. *)
            let abs = a_init_mlv_no_array cmlv abs in
            (abs, mlv :: mlvs_forget)
          | MLvar _ as mlv, Some e ->
            (abs_assign abs (ty_lval lv) mlv e, mlvs_forget)

          | MLvars (_, mlvs), _ -> (abs, mlvs @ mlvs_forget))
        (abs,[]) lvs assgns in

    let mlvs_forget = List.sort_uniq Stdlib.compare mlvs_forget in

    AbsDom.forget_list abs mlvs_forget 

end


(************************)
(* Abstract Interpreter *)
(************************)

type warnings = (Format.formatter -> unit) list
    
type analyse_res =
  { violations : violation list;
    print_var_interval : (Format.formatter -> mvar -> unit);
    mem_ranges_printer : (Format.formatter -> unit -> unit);
    warnings : warnings; }
                     
module AbsInterpreter (PW : ProgWrap) : sig
  val analyze : unit -> analyse_res
end = struct

  let source_main_decl = PW.main_source
  let main_decl,prog = PW.main, PW.prog

  let () = Prof.reset_all ()

  (*---------------------------------------------------------------*)
  module AbsDom = AbsBoolNoRel (AbsNumTMake (PW)) (PointsToImpl) (SymExprImpl)

  module AbsExpr = AbsExpr (AbsDom)

  (*---------------------------------------------------------------*)
  type side_effects = mem_loc list

  (* Function abstraction.
     This is a bit messy because the same function abstraction can be used
     with different call-stacks, but the underlying disjunctive domain we 
     use is sensitive to the call-stack. *)
  module FAbs : sig
    type t

    (* [make abs_in abs_out f_effects] *)
    val make    : AbsDom.t -> AbsDom.t -> side_effects -> t

    (* [ apply in fabs = (f_in, f_out, effects) ]:
       Return the abstraction of the initial states that was used, the
       abstract final state, and the side-effects of the function (if the
       abstraction applies in state [in]).
       Remarks: 
       - the final state abstraction [f_out] uses the disjunctions of [in]. *)
    val apply : AbsDom.t -> t -> (AbsDom.t * side_effects) option

    val get_in : t -> AbsDom.t
  end = struct
    (* Sound over-approximation of a function 'f' behavior:
       for any initial state in [it_in], the state after executing the function
       'f' is over-approximated by [it_out], the function's side-effects are at
       most [it_s_effects]. *)
    type t = { fa_in        : AbsDom.t;
               fa_out       : AbsDom.t;
               fa_s_effects : mem_loc list; }

    let make abs_in abs_out f_effects =
      { fa_in        = AbsDom.remove_disj abs_in;
        fa_out       = AbsDom.remove_disj abs_out;
        fa_s_effects = f_effects; }

    let apply abs_in fabs =
      if AbsDom.is_included abs_in (AbsDom.to_shape fabs.fa_in abs_in) 
      then begin
        debug (fun () -> 
            Format.eprintf "Reusing previous analysis of the body ...@.@.");
        Some (AbsDom.to_shape fabs.fa_out abs_in, fabs.fa_s_effects)
      end
      else None

    let get_in t = t.fa_in
  end


  (*---------------------------------------------------------------*)
  type astate = { it : FAbs.t ItMap.t;
                  abs : AbsDom.t; 
                  cstack : funname list;
                  env : s_env;
                  prog : minfo prog;
                  s_effects : side_effects;
                  violations : violation list }

  let init_state_init_args f_args state =
    List.fold_left (fun state v -> match v with
        | Mvalue at ->
          { state with abs = AbsDom.is_init state.abs at; }
        | _ -> state )
      state f_args

  let init_env : 'info prog -> mem_loc list -> s_env =
    fun (glob_decls, fun_decls) mem_locs ->
    let env = { s_glob = Ms.empty; m_locs = mem_locs } in
    let env =
      List.fold_left (fun env (ws, x, _) -> add_glob env x ws)
        env glob_decls in

    List.fold_left (fun env f_decl ->
        { env with s_glob = List.fold_left (fun s_glob ginstr ->
              add_glob_instr s_glob ginstr)
              env.s_glob f_decl.f_body })
      env fun_decls

  let init_state : unit func -> minfo func -> minfo prog -> astate * warnings =
    fun main_source main_decl (glob_decls, fun_decls) ->
      let mem_locs = List.map (fun x -> MemLoc x) main_decl.f_args in
      let env = init_env (glob_decls, fun_decls) mem_locs in
      let it = ItMap.empty in

      (* We add the initial variables *)
      let comp_f_args decl =
        let f_args = fun_args ~expand_arrays:true decl in
        (* If f_args is empty, we add a dummy variable to avoid having an
           empty relational abstraction *)
        if f_args = [] then [dummy_mvar] else f_args
      in
      let f_args        = comp_f_args main_decl in
      let source_f_args = comp_f_args main_source in
      
      let f_in_args = List.map in_cp_var f_args
      and m_locs = List.map (fun mloc -> MmemRange mloc ) env.m_locs in

      (* We set the offsets and ranges to zero, and bound the variables using
         their types. E.g. register of type U 64 is in [0;2^64]. *)
      let abs, warns = AbsDom.make (f_args @ m_locs) mem_locs
                |> AbsExpr.set_zeros (f_args @ m_locs)
                (* We use the function location as location of the initial 
                   assignment of the main procedure's arguments. *)
                |> AbsExpr.set_bounds f_args source_f_args in

      (* We apply the global declarations *)
      let abs = AbsExpr.apply_glob glob_decls abs in

      (* We extend the environment to its local variables *)
      let f_vars = (List.map otolist f_in_args |> List.flatten)
                   @ fun_vars ~expand_arrays:true main_decl env in

      let abs = AbsDom.change_environment abs f_vars in

      (* We keep track of the initial values. *)
      let abs = List.fold_left2 (fun abs x oy -> match oy with
          | None -> abs
          | Some y ->
            let sexpr = Mtexpr.var (AbsDom.get_env abs) x
                        |> sexpr_from_simple_expr in
            AbsDom.assign_sexpr abs y None sexpr)
          abs f_args f_in_args in

      let state = { it = it;
                    abs = abs;
                    cstack = [main_decl.f_name];
                    env = env;
                    prog = (glob_decls, fun_decls);
                    s_effects = [];
                    violations = []; } in

      (* We initialize the arguments. Note that for exported function, we 
         know that input arrays are initialized. *)
      ( init_state_init_args (fun_args ~expand_arrays:true main_decl) state,
        warns )


  (*-------------------------------------------------------------------------*)
  (* Checks that all safety conditions hold, except for valid memory access. *)
  let is_safe state = function
    | Initv v -> begin match mvar_of_var v with
        | Mvalue at -> AbsDom.check_init state.abs at
        | _ -> assert false end

    | Initai (v,ws,e) -> begin match mvar_of_var v with
        | Mvalue (Aarray v) ->
          let is = AbsExpr.abs_arr_range state.abs v ws e in
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

      begin match AbsExpr.bexpr_to_btcons be state.abs with
        | None -> false
        | Some c -> 
          AbsDom.is_bottom (AbsDom.meet_btcons state.abs c) end

    | NotZero (ws,e) ->
      (* We check that e is never 0 *)
      let be = Papp2 (E.Oeq (E.Op_w ws), e, pcast ws (Pconst (B.of_int 0))) in
      begin match AbsExpr.bexpr_to_btcons be state.abs with
        | None -> false
        | Some c -> 
          AbsDom.is_bottom (AbsDom.meet_btcons state.abs c) end

    | Valid _ | Termination -> true (* These are checked elsewhere *)

  (* Update abs with the abstract memory range for memory accesses. *)
  let mem_safety_apply (abs, violations, s_effect) = function
    | Valid (ws,x,e) as pv ->
      begin match AbsDom.var_points_to abs (mvar_of_var x) with
        | Ptrs pts ->
          if List.length pts = 1 then
            let pt = List.hd pts in
            let x_o = Mtexpr.var (AbsDom.get_env abs) (MvarOffset x) in
            let lin_e = AbsExpr.linearize_wexpr abs e in
            let c_ws =
              ((int_of_ws ws) / 8)
              |> Coeff.s_of_int
              |> Mtexpr.cst (AbsDom.get_env abs) in
            let ws_plus_e = Mtexpr.binop Texpr1.Add c_ws lin_e in
            let sexpr = Mtexpr.binop Texpr1.Add x_o ws_plus_e
                        |> sexpr_from_simple_expr in

            ( AbsDom.assign_sexpr abs (MmemRange pt) None sexpr,
              violations,
              if List.mem pt s_effect then s_effect else pt :: s_effect)
          else (abs, pv :: violations, s_effect)
        | TopPtr -> (abs, pv :: violations, s_effect) end

    | _ -> (abs, violations, s_effect)


  (*-------------------------------------------------------------------------*)
  let rec check_safety_rec state unsafe = function
    | [] -> unsafe
    | c :: t ->
      let unsafe = if is_safe state c then unsafe else c :: unsafe in
      check_safety_rec state unsafe t 
        
  let rec mem_safety_rec a = function
    | [] -> a
    | c :: t ->       
      mem_safety_rec (mem_safety_apply a c) t

  let add_violations : astate -> violation list -> astate = fun state ls ->
    if ls <> [] then Format.eprintf "%a@." pp_violations ls;
    { state with violations = List.sort_uniq v_compare (ls @ state.violations) }
    
  let rec check_safety state loc conds =
    let vsc = check_safety_rec state [] conds in
    let abs, mvsc, s_effects =
      mem_safety_rec (state.abs, [], state.s_effects) conds in
    
    let state = { state with abs = abs;
                             s_effects = s_effects } in
    
    let unsafe = vsc @ mvsc
                 |> List.map (fun x -> (loc,x)) in
    add_violations state unsafe

      
  (*-------------------------------------------------------------------------*)
  (* Initialize variable or array elements lvalues. *)
  let init_mlv_no_array mlv state = 
    { state with abs = AbsExpr.a_init_mlv_no_array mlv state.abs; }
      

  let offsets_of_mvars l = List.map ty_gvar_of_mvar l
                           |> List.filter (fun x -> x <> None)
                           |> List.map (fun x -> MvarOffset (oget x))

  (* Prepare the caller for a function call. Returns the state with the
     arguments es evaluated in f input variables. *)
  let aeval_f_args f es state =
    let f_decl = get_fun_def state.prog f |> oget in

    let f_args = fun_args_no_offset f_decl
    and exp_in_tys = f_decl.f_tyin in

    let assigns = combine3 exp_in_tys f_args es
                  |> List.map (fun (x,y,z) ->
                      (* The info on the [mlval] does not matter here,
                         since the flow-sensitive packing heuristic we use 
                         only makes sense for fully inlined Jasmin programs *)
                      let y = MLvar ({ i_instr_number = -1 }, y) in
                      (x, y, z)) in

    let abs = List.fold_left (fun abs (in_ty, mvar, e) ->
        AbsExpr.abs_assign abs in_ty mvar e ) 
        state.abs assigns in

    { state with abs = abs }

  (* Remark: handles variable initialization. *)
  let aeval_f_return abs ret_assigns =
    List.fold_left (fun abs (out_ty,rvar,(lv,mlvo)) ->
        match mlvo with
        | MLnone -> abs

        | MLvars (_, mlvs) ->
          (* Here, we have no information on which elements are initialized. *)
          AbsDom.forget_list abs mlvs

        | MLvar (_, mlv) -> match ty_mvar mlv with
          | Bty Bool ->
            let rconstr = BVar (Bvar.make rvar true) in
            AbsDom.assign_bexpr abs mlv rconstr
            |> AbsExpr.a_init_mlv_no_array mlvo

          | Bty _ ->
            let mret = Mtexpr.var (AbsDom.get_env abs) rvar in

            let lv_size = wsize_of_ty (ty_lval lv)
            and ret_size = wsize_of_ty out_ty in

            (* Numerical abstraction *)
            let expr = match ty_mvar mlv, ty_mvar rvar with
              | Bty Int, Bty Int -> mret
              | Bty (U _), Bty Int ->
                AbsExpr.wrap_if_overflow abs mret Unsigned lv_size
              | Bty (U _), Bty (U _) ->
                AbsExpr.cast_if_overflows abs lv_size ret_size mret
              | _, _ -> assert false in

            let s_expr = sexpr_from_simple_expr expr in
            (* We use [None] as minfo here, since the flow-sensitive
               packing heuristic we use only makes sense for fully
               inlined Jasmin programs *)
            let abs = AbsDom.assign_sexpr abs mlv None s_expr in

            (* Points-to abstraction *)
            let ptr_expr = PtVars [rvar] in
            let abs = AbsDom.assign_ptr_expr abs mlv ptr_expr in

            (* Offset abstraction *)
            let abs = match ty_gvar_of_mvar rvar with
              | None -> abs
              | Some rv ->
                let lrv = L.mk_loc L._dummy rv in
                (* We use [None] as minfo here, since the flow-sensitive
                   packing heuristic we use only makes sense for fully
                   inlined Jasmin programs *)
                AbsExpr.aeval_offset abs out_ty mlv None (Pvar lrv) in

            AbsExpr.a_init_mlv_no_array mlvo abs

          | Arr _ ->
            let mret = Mtexpr.var (AbsDom.get_env abs) rvar in

            let lv_size = wsize_of_ty (ty_lval lv)
            and ret_size = wsize_of_ty out_ty in
            assert (lv_size = ret_size); (* may not be necessary *)

            (* Numerical abstractions only.
               Points-to and offset abstraction are not needed for array and 
               array elements *)
            AbsExpr.assign_arr_expr abs mlv mret)
      
      abs ret_assigns

  let forget_f_vars f state =
    let f_decl = get_fun_def state.prog f |> oget in
    let f_vs = fun_args ~expand_arrays:true f_decl
               @ fun_locals ~expand_arrays:true f_decl in

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
    let vs_globs = prog_globals ~expand_arrays:true state.env
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
  let prepare_call state callsite f es =
    debug (fun () -> Format.eprintf "evaluating arguments ...@.");
    let state = aeval_f_args f es state in

    debug (fun () -> Format.eprintf "forgetting variables ...@.");
    let state = forget_stack_vars state in

    let state = { state with 
                  abs = AbsDom.new_cnstr_blck state.abs callsite; } in

    { state with cstack = f :: state.cstack;
                 s_effects = [] }


  (* Profiling *)
  let () = Prof.record "prepare_call"
  let prepare_call abs callsite f es =
    let t = Sys.time () in
    let r = prepare_call abs callsite f es in
    let t' = Sys.time () in
    let sf = "prepare_call_" ^ f.fn_name in
    let () = 
      if Prof.is_recorded sf
      then ()
      else Prof.record sf in
    let () = Prof.call "prepare_call" (t' -. t) in
    let () = Prof.call sf (t' -. t) in
    r

  let get_ret_assgns abs f_decl lvs =
    let f_rets_no_offsets = fun_rets_no_offsets f_decl
    and out_tys = f_decl.f_tyout
    and mlvs = List.map (fun x ->
        (* The info of [mlv] does not matter here,
           since the flow-sensitive packing heuristic we use 
           only makes sense for fully inlined Jasmin programs *)
        (x, AbsExpr.mvar_of_lvar abs { i_instr_number = -1 }  x)) lvs in

    combine3 out_tys f_rets_no_offsets mlvs


  let return_call state callsite fstate lvs =
    (* We forget side effects of f in the caller *)
    let state = forget_side_effect state fstate.s_effects in

    (* We pop the top-most block of constraints in the callee *)
    let fabs = AbsDom.pop_cnstr_blck fstate.abs callsite in
    let fstate = { fstate with abs = fabs; } in

    (* We forget variables untouched by f in the callee *)
    let fstate = forget_no_side_effect fstate fstate.s_effects in
    let fname = List.hd fstate.cstack in

    debug(fun () ->
        Format.eprintf "@[<v 0>side effects of %s: @[<hov 2>%a@]@]@."
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

    debug(fun () -> Format.eprintf "evaluating returned values ...@.");
    (* Finally, we assign the returned values in the corresponding lvalues *)
    let f_decl = get_fun_def fstate.prog fname |> oget in
    let r_assgns = get_ret_assgns state.abs f_decl lvs in      
    
    let state = { state with abs = aeval_f_return state.abs r_assgns } in

    debug(fun () -> 
        Format.eprintf "forgetting %s local variables ...@.@." fname.fn_name);
    (* We forget the variables of f to get a smaller abstract element. *)
    forget_f_vars fname state

  let simpl_obtcons = function
    | Some (BLeaf c) -> Some c
    | _ -> None


  (* -------------------------------------------------------------------- *)
  (* Return flags for the different operations.
     This covers a subset of the x86 flags, as described in the Coq
     semantics (x86_instr_decl.v). *)

  (* Carry flag is true if [w] and [vu] are not equal. *)
  let cf_of_word sz w vu =
    Some (Papp2 (E.Oneq (E.Op_int),
                 Papp1(E.Oint_of_word sz,w),
                 vu))

  (* FIXME *)
  let sf_of_word _sz _w = None
  (* msb w. *)

  (* FIXME *)
  let pf_of_word _sz _w = None
  (* lsb w. *) 

  let zf_of_word sz w =
    Some (Papp2 (E.Oeq (E.Op_w sz),
                 w,
                 pcast sz (Pconst (B.of_int 0))))

  let rflags_of_aluop sz w vu _vs = 
    let of_f = None               (* FIXME *)
    and cf   = cf_of_word sz w vu 
    and sf   = sf_of_word sz w
    and pf   = pf_of_word sz w
    and zf   = zf_of_word sz w in
    [of_f;cf;sf;pf;zf]

  (* For the SUB (without carry) and CMP operation, we manually set
     the flags to have simpler and more precise expressions for the 
     carry and zero flags. *)
  let rflags_of_sub sz w1 w2 =
    let sub = Papp2 (E.Osub (E.Op_w sz), w1, w2) in 
    let of_f = None               (* FIXME *)
    and cf   = Some (Papp2 (E.Olt (E.Cmp_w (Unsigned, sz)), w1,w2))
    and sf   = sf_of_word sz sub
    and pf   = pf_of_word sz sub
    and zf   = Some (Papp2 (E.Oeq (E.Op_w sz), w1,w2))
    in
    [of_f;cf;sf;pf;zf]

  let rflags_of_bwop sz w =
    let of_f = Some (Pbool false)
    and cf   = Some (Pbool false)
    and sf   = sf_of_word sz w
    and pf   = pf_of_word sz w
    and zf   = zf_of_word sz w in
    [of_f;cf;sf;pf;zf]

  let rflags_of_neg sz w _vs = 
    let of_f = None               (* FIXME, same than for rflags_of_aluop *)
    and cf   = None               (* FIXME, must be (w != 0)*)
    and sf   = sf_of_word sz w
    and pf   = pf_of_word sz w
    and zf   = zf_of_word sz w in
    [of_f;cf;sf;pf;zf]

  let rflags_of_mul (ov : bool option) =
    (*  OF; CF; SF; PF; ZF *)
    [Some ov; Some ov; None; None; None]

  let rflags_unknwon =
    (*  OF; CF; SF; PF; ZF *)
    [None; None; None; None; None]

  let rflags_of_div =
    (*  OF; CF; SF; PF; ZF *)
    rflags_unknwon

  let rflags_of_andn sz w =
    let of_f = Some (Pbool false)
    and cf   = Some (Pbool false)
    and sf   = sf_of_word sz w
    and pf   = None
    and zf   = zf_of_word sz w in
    [of_f;cf;sf;pf;zf]

  (* Remove the carry flag *)
  let nocf = function
    | [of_f;_;sf;pf;zf] -> [of_f;sf;pf;zf]
    | _ -> assert false

  let opn_dflt n = List.init n (fun _ -> None)

  let opn_bin_gen f_flags ws op op_int es =
    let el,er = as_seq2 es in
    let w = Papp2 (op, el, er) in
    let vu = Papp2 (op_int,
                    Papp1(E.Oint_of_word ws,el),
                    Papp1(E.Oint_of_word ws,er)) in
    let vs = () in              (* FIXME *)
    let rflags = f_flags ws w vu vs in
    rflags @ [Some w]

  let opn_bin_alu = opn_bin_gen rflags_of_aluop

  let opn_sub sz es =
    let el,er = as_seq2 es in
    let w = Papp2 (E.Osub (E.Op_w sz), el, er) in
    let rflags = rflags_of_sub sz el er in
    rflags @ [Some w]

  (* -------------------------------------------------------------------- *)
  (* FIXME: redo using the generic flags definition above *)
  let mk_addcarry ws es =
    let el,er,eb = as_seq3 es in    
    let w_no_carry = Papp2 (E.Oadd (E.Op_w ws), el, er) in
    let w_carry = Papp2 (E.Oadd (E.Op_w ws),
                         w_no_carry,
                         pcast ws (Pconst (B.of_int 1))) in

    let eli = Papp1 (E.Oint_of_word ws, el)    (* (int)el *)
    and eri = Papp1 (E.Oint_of_word ws, er) in (* (int)er *)
    let w_i =
      Papp2 (E.Oadd E.Op_int, eli, eri) in (* (int)el + (int)er *)
    let pow_ws = Pconst (B.pow (B.of_int 2) (int_of_ws ws)) in (* 2^ws *)

    (* cf_no_carry is true <=> 2^ws <= el + er      (addition without modulo) *)
    let cf_no_carry = Papp2 (E.Ole E.Cmp_int, pow_ws, w_i ) in
    (* cf_carry    is true <=> 2^ws <= el + er + 1  (addition without modulo) *)
    let cf_carry = Papp2 (E.Ole E.Cmp_int,
                          pow_ws,
                          Papp2 (E.Oadd E.Op_int,
                                 w_i,
                                 Pconst (B.of_int 1))) in

    match eb with
    | Pbool false ->         (* No carry *)
      [Some cf_no_carry; Some w_no_carry] 

    | Pbool true ->          (* Carry *)
      [Some cf_carry; Some w_carry] 

    | _ ->                   (* General case, potential carry *)
      let _w = Pif (Bty (U ws), eb, w_carry, w_no_carry) in
      let _cf = Pif (Bty Bool, eb, cf_carry, cf_no_carry) in

      (* FIXME: make this optional ?*)
      [None; None]
      (* [Some cf; Some w]  *)

  (* FIXME: idem *)
  let mk_subcarry ws es =
    let el,er,eb = as_seq3 es in    
    let w_no_carry = Papp2 (E.Osub (E.Op_w ws), el, er) in
    let w_carry = Papp2 (E.Osub (E.Op_w ws),
                         w_no_carry,
                         pcast ws (Pconst (B.of_int 1))) in

    let eli = Papp1 (E.Oint_of_word ws, el)    (* (int)el *)
    and eri = Papp1 (E.Oint_of_word ws, er) in (* (int)er *)

    (* cf_no_carry is true <=> el < er *)
    let cf_no_carry = Papp2 (E.Olt E.Cmp_int, eli, eri ) in
    (* cf_carry    is true <=> el < er + 1  (sub without modulo) *)
    let cf_carry = Papp2 (E.Ole E.Cmp_int,
                          eli,
                          Papp2 (E.Oadd E.Op_int, eri, Pconst (B.of_int 1))) in

    match eb with
    | Pbool false ->         (* No carry *)
      [Some cf_no_carry; Some w_no_carry] 

    | Pbool true ->          (* Carry *)
      [Some cf_carry; Some w_carry] 

    | _ ->                   (* General case, potential carry *)
      let _w = Pif (Bty (U ws), eb, w_carry, w_no_carry) in
      let _cf = Pif (Bty Bool, eb, cf_carry, cf_no_carry) in

      (* FIXME: make this optional ?*)
      [None; None]
      (* [Some cf; Some w]  *)

  
  (* -------------------------------------------------------------------- *)
  (* Remark: the assignments must be done in the correct order.
     Bitwise operators are ignored for now (result is soundly set to top).
     See x86_instr_decl.v for a desciption of the operators. *)
  let split_opn n opn es = match opn with
    | E.Oset0 ws -> [None;None;None;None;None;
                     Some (pcast ws (Pconst (B.of_int 0)))]

    | E.Osubcarry ws -> mk_subcarry ws es
      
    | E.Oaddcarry ws -> mk_addcarry ws es

    | E.Ox86MOVZX32 ->
      let e = as_seq1 es in
      (* Cast [e], seen as an U32, to an integer, and then back to an U64. *)
      [Some (Papp1(E.Oword_of_int U64, Papp1(E.Oint_of_word U32, e)))]

    (* Idem than Ox86MOVZX32, but with different sizes. *)      
    | E.Ox86 (X86_instr_decl.MOVZX (sz_o, sz_i)) ->
      assert (int_of_ws sz_o >= int_of_ws sz_i);
      let e = as_seq1 es in
      [Some (Papp1(E.Oword_of_int sz_o, Papp1(E.Oint_of_word sz_i, e)))]

    (* CMP flags are identical to SUB flags. *)
    | E.Ox86 (X86_instr_decl.CMP ws) ->
      (* Input types: ws, ws *)
      let el,er = as_seq2 es in
      rflags_of_sub ws el er

    (* add unsigned / signed *)
    | E.Ox86 (X86_instr_decl.ADD ws) ->
      opn_bin_alu ws (E.Oadd (E.Op_w ws)) (E.Oadd E.Op_int) es

    (* sub unsigned / signed *)
    | E.Ox86 (X86_instr_decl.SUB ws) ->
      opn_sub ws es

    (* mul unsigned *)
    | E.Ox86 (X86_instr_decl.MUL ws) ->
      let el,er = as_seq2 es in
      let w = Papp2 (E.Omul (E.Op_w ws), el, er) in
      (* FIXME: overflow bit to have the precise flags *)
      (* let ov = ?? in
       * let rflags = rflags_of_mul ov in *)
      let rflags = [None; None; None; None; None] in
      rflags @ [None; Some w]

    (* div unsigned *)
    | E.Ox86 (X86_instr_decl.DIV ws) ->
      let el,er = as_seq2 es in
      let w = Papp2 (E.Odiv (E.Cmp_w (Unsigned, ws)), el, er) in
      let rflags = rflags_of_div in
      rflags @ [None; Some w]

    (* div signed *)
    | E.Ox86 (X86_instr_decl.IDIV ws) ->
      let el,er = as_seq2 es in
      let w = Papp2 (E.Odiv (E.Cmp_w (Signed, ws)), el, er) in
      let rflags = rflags_of_div in
      rflags @ [None; Some w]

    (* increment *)
    | E.Ox86 (X86_instr_decl.INC ws) ->
      let e = as_seq1 es in
      let w = Papp2 (E.Oadd (E.Op_w ws), e,
                     Papp1(E.Oword_of_int ws, Pconst (B.of_int 1))) in
      let vu = Papp2 (E.Oadd E.Op_int,
                      Papp1(E.Oint_of_word ws,e),
                      Pconst (B.of_int 1)) in
      let vs = () in
      let rflags = nocf (rflags_of_aluop ws w vu vs) in
      rflags @ [Some w]

    (* decrement *)
    | E.Ox86 (X86_instr_decl.DEC ws) ->
      let e = as_seq1 es in
      let w = Papp2 (E.Osub (E.Op_w ws), e,
                     Papp1(E.Oword_of_int ws,Pconst (B.of_int 1))) in
      let vu = Papp2 (E.Osub E.Op_int,
                      Papp1(E.Oint_of_word ws,e),
                      Pconst (B.of_int 1)) in
      let vs = () in
      let rflags = nocf (rflags_of_aluop ws w vu vs) in
      rflags @ [Some w]

    (* negation *)
    | E.Ox86 (X86_instr_decl.NEG ws) ->
      let e = as_seq1 es in
      let w = Papp1 (E.Oneg (E.Op_w ws), e) in
      let vs = () in
      let rflags = rflags_of_neg ws w vs in
      rflags @ [Some w]

    (* copy *)
    | E.Ox86 (X86_instr_decl.MOV _) ->
      let e = as_seq1 es in 
      [Some e]

    (* shift, unsigned / left  *)
    | E.Ox86 (X86_instr_decl.SHL ws) ->
      let e1, e2 = as_seq2 es in
      let e = Papp2 (E.Olsl ws, e1, e2) in
      rflags_unknwon @ [Some e]

    (* shift, unsigned / right  *)
    | E.Ox86 (X86_instr_decl.SHR ws) ->
      let e1, e2 = as_seq2 es in
      let e = Papp2 (E.Olsr ws, e1, e2) in
      rflags_unknwon @ [Some e]

    (* shift, signed / right  *)
    | E.Ox86 (X86_instr_decl.SAR ws) ->
      let e1, e2 = as_seq2 es in
      let e = Papp2 (E.Oasr ws, e1, e2) in
      rflags_unknwon @ [Some e]
  
    (* FIXME: adding bit shift with flags *)
    (* 
    | ROR    of wsize    (* rotation / right *)
    | ROL    of wsize    (* rotation / left  *)
    | RCR    of wsize    (* rotation / right with carry *)
    | RCL    of wsize    (* rotation / left  with carry *)
    | SHL    of wsize    (* unsigned / left  *)
    | SHR    of wsize    (* unsigned / right *)
    | SAL    of wsize    (*   signed / left; synonym of SHL *)
    | SAR    of wsize    (*   signed / right *)
    | SHLD   of wsize    (* unsigned (double) / left *)
    | SHRD   of wsize    (* unsigned (double) / right *)
    | MULX    of wsize  (* mul unsigned, doesn't affect arithmetic flags *)
    | ADCX    of wsize  (* add with carry flag, only writes carry flag *)
    | ADOX    of wsize  (* add with overflow flag, only writes overflow flag *)
    *)

    (* conditional copy *)
    | E.Ox86 (X86_instr_decl.CMOVcc sz) ->
      let c,el,er = as_seq3 es in
      let e = Pif (Bty (U sz), c, el, er) in
      [Some e] 

    (* bitwise operators *)
    | E.Ox86 (X86_instr_decl.TEST _)
    | E.Ox86 (X86_instr_decl.AND  _)
    | E.Ox86 (X86_instr_decl.ANDN _)
    | E.Ox86 (X86_instr_decl.OR   _)
    | E.Ox86 (X86_instr_decl.NOT  _)        
    | E.Ox86 (X86_instr_decl.XOR  _)

    (* mul signed with truncation *)
    | E.Ox86 (X86_instr_decl.IMUL _)
    | E.Ox86 (X86_instr_decl.IMULr _)
    | E.Ox86 (X86_instr_decl.IMULri _) 

    | _ ->
      debug (fun () ->
          Format.eprintf "Warning: unknown opn %s, default to ⊤.@."
            (Printer.pp_opn opn));
      opn_dflt n


  (* -------------------------------------------------------------------- *)
  (* Ugly handling of flags to build. 
     When adding new flags, update [find_heur]. *)
  type flags_heur = { fh_zf : Mtexpr.t option;
                      fh_cf : Mtexpr.t option; }

  let pp_flags_heur fmt fh =
    let to_me = omap (fun x -> x.Mtexpr.mexpr) in
    Format.fprintf fmt "@[<hv 0>zf: %a;@ cf %a@]"
      (pp_opt Mtexpr.print_mexpr) (to_me fh.fh_zf)
      (pp_opt Mtexpr.print_mexpr) (to_me fh.fh_cf)
  
  
  (* [v] is the variable receiving the assignment. *)
  let opn_heur apr_env opn v es =
    match opn with 
    (* sub carry *) 
    | E.Osubcarry _ ->
      (* FIXME: improve precision by allowing decrement by something else 
         than 1 here. *)
      Some { fh_zf = None;
             fh_cf = Some (Mtexpr.binop Texpr1.Add
                             (Mtexpr.var apr_env v)
                             (Mtexpr.cst apr_env (Coeff.s_of_int 1))); }
        
    (* decrement *) 
    | E.Ox86 (X86_instr_decl.DEC _) ->
      Some { fh_zf = Some (Mtexpr.var apr_env v);
             fh_cf = Some (Mtexpr.binop Texpr1.Add
                             (Mtexpr.var apr_env v)
                             (Mtexpr.cst apr_env (Coeff.s_of_int 1))); }

    (* compare *)
    | E.Ox86 (X86_instr_decl.CMP _) ->
      let exception Opn_heur_failed in
      let rec to_mvar = function
        | Pvar x ->
          check_is_word (L.unloc x);
          Mtexpr.var apr_env (Mvalue (Avar (L.unloc x)))
        | Papp1 (E.Oword_of_int _, e) -> to_mvar e
        | Papp1 (E.Oint_of_word _, e) -> to_mvar e 
        | _ -> raise Opn_heur_failed in
      let el, er = as_seq2 es in
      begin try
        let el, er = to_mvar el, to_mvar er in
        Some { fh_zf = Some (Mtexpr.binop Texpr1.Sub el er);
               fh_cf = Some (Mtexpr.binop Texpr1.Sub el er); }
        with Opn_heur_failed -> None end
      
    (* (\* sub with borrow *\)
     * | E.Ox86 (X86_instr_decl.SBB _) *)
    | _ ->
      debug (fun () ->
          Format.eprintf "No heuristic for the return flags of %s@."
            (Printer.pp_opn opn));
      None

  exception Heuristic_failed

  (* Ugly, just tries to match the string name to a flag name. *)
  let find_heur bv = function
    | None -> raise Heuristic_failed
    | Some heur ->     
      let s = Bvar.var_name bv in
      let s = String.lowercase s in
      if String.starts_with s "v_cf"
      then Utils.oget ~exn:Heuristic_failed heur.fh_cf
      else if String.starts_with s "v_zf"
      then Utils.oget ~exn:Heuristic_failed heur.fh_zf
      else raise Heuristic_failed

  (* Heuristic for the (candidate) decreasing quantity to prove while
     loop termination. *)  
  let dec_qnty_heuristic abs loop_body loop_cond =
    let heur_leaf leaf = match Mtcons.get_typ leaf with
      | Lincons0.SUPEQ | Lincons0.SUP -> Mtcons.get_expr leaf

      (* We handle the exit condition "x <> 0" as if it was "x > 0" *)
      | Lincons0.DISEQ -> Mtcons.get_expr leaf

      | _ -> raise Heuristic_failed in

    match loop_cond with
    (* If the exit condition is a constraint (i.e. a leaf boolean term),
       then we try to retrieve the expression inside. *)
    | Some (BLeaf sc) -> heur_leaf sc

    (* For boolean variables, we look whether it is a return flag. If that is
       the case, we look for the instruction that set the flag, and use a
       heuristic depending on the operation. *)
    | Some (BVar bv) ->
      let brev = List.rev loop_body in 
      begin try
          List.find_map (fun ginstr -> match ginstr.i_desc with 
              | Copn(lvs,_,opn,es) ->
                List.find_map_opt (fun lv ->
                    match lv with
                    | Lvar x -> 
                      let x_mv = Mvalue (Avar (L.unloc x)) in
                      if Bvar.make x_mv true = Bvar.positive bv 
                      (* We found the assignment where the flag is set *)
                      then
                        (* Register for which the flags are computed. *)
                        let reg_assgn = match List.last lvs with
                          | Lvar r -> Mvalue (Avar (L.unloc r))
                          | Lnone _ -> raise Heuristic_failed
                          | _ -> assert false in

                        let apr_env = AbsDom.get_env abs in
                        let heur = opn_heur apr_env opn reg_assgn es in
                        Some (find_heur bv heur)
                      else None
                    | _ -> None) lvs

              | _ -> None                
            ) brev
        with Not_found -> raise Heuristic_failed
      end

    | _ -> raise Heuristic_failed


  (* -------------------------------------------------------------------- *)
  (* Check that there are no memory stores and loads. *)
  let check_memory_access_aux f_decl = 

    (* vs_for: integer variable from for loops, which will be inlined to
       a constant integer value. *)
    let rec nm_i vs_for i = match i.i_desc with
      | Cassgn (lv, _, _, e)    -> nm_lv vs_for lv && nm_e vs_for e
      | Copn (lvs, _, _, es)    -> nm_lvs vs_for lvs && nm_es vs_for es
      | Cif (e, st, st')        -> 
        nm_e vs_for e && nm_stmt vs_for st && nm_stmt vs_for st'
      | Cfor (i, _, st)         -> nm_stmt (i :: vs_for) st
      | Cwhile (_, st1, e, st2) -> 
        nm_e vs_for e && nm_stmt vs_for st1 && nm_stmt vs_for st2
      | Ccall (_, lvs, fn, es)  -> 
        let f' = get_fun_def prog fn |> oget in
        nm_lvs vs_for lvs && nm_es vs_for es && nm_fdecl f'

    and nm_fdecl f = nm_stmt [] f.f_body

    and nm_stmt vs_for stmt = List.for_all (nm_i vs_for) stmt

    and nm_e vs_for = function
      | Pconst _ | Pbool _ | Parr_init _ | Pglobal _ | Pvar _ -> true
      | Pget (_, _, e)     -> know_offset vs_for e && nm_e vs_for e
      | Pload _            -> false
      | Papp1 (_, e)       -> nm_e vs_for e
      | Papp2 (_, e1, e2)  -> nm_es vs_for [e1; e2]
      | PappN (_,es)       -> nm_es vs_for es
      | Pif (_, e, el, er) -> nm_es vs_for [e; el; er]

    and nm_es vs_for es = List.for_all (nm_e vs_for) es

    and nm_lv vs_for = function
      | Lnone _ | Lvar _ -> true
      | Laset (_,_,e) -> know_offset vs_for e
      | Lmem _ -> false

    and nm_lvs vs_for lvs = List.for_all (nm_lv vs_for) lvs 

    and know_offset vs_for = function
      | Pconst _ -> true
      | Pvar v -> List.mem v vs_for
      | Papp1 (E.Oneg Op_int, e) -> know_offset vs_for e

      | Papp2 ((Osub Op_int | Omul Op_int | Oadd Op_int), e1, e2) ->
        know_offset vs_for e1 && know_offset vs_for e2

      | _ -> false
    in

    nm_fdecl f_decl 


  (* Memoisation *)
  let nm_memo = Hf.create 16
  let check_memory_access f_decl =
    try Hf.find nm_memo f_decl.f_name with Not_found ->
      let res = check_memory_access_aux f_decl in
      Hf.add nm_memo f_decl.f_name res;
      res

  
  (* The function must not use memory loads/stores, array accesses must be 
     fixed, and arrays in arguments must be fully initialized
     (i.e. cells must be initialized). *)
  let check_valid_call_top st f_decl = 
    let cells_init = 
      List.for_all (fun v -> match mvar_of_var v with
          | Mvalue (Aarray _) as mv -> 
            let vs = u8_blast_var ~blast_arrays:true mv in
            List.for_all (function 
                | Mvalue at -> AbsDom.check_init st.abs at
                | _ -> assert false (* initialization of other arguments
                                       should already have been checked
                                       by the analyzer. *)
              ) vs
          | _ -> true
        ) f_decl.f_args in

    cells_init && check_memory_access f_decl


  (* -------------------------------------------------------------------- *)
  let num_instr_evaluated = ref 0

  let print_ginstr ginstr abs_vals =
    Format.eprintf "@[<v>@[<v>%a@]@;*** %d Instr: nb %d, %a %a@;@;@]%!"
      (AbsDom.print ~full:true) abs_vals
      (let a = !num_instr_evaluated in incr num_instr_evaluated; a)
      ginstr.i_info.i_instr_number
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

  let print_if_join cpt_instr ginstr labs rabs abs_r =
    Format.eprintf "@;@[<v 2>If join %a for Instr:@;%a @;@;%a@]@."
      L.pp_sloc (fst ginstr.i_loc)
      (Printer.pp_instr ~debug:false) ginstr
      (print_binop) (cpt_instr,
                     labs,
                     rabs,
                     abs_r)

  let print_while_join cpt_instr abs abs_o abs_r =
    Format.eprintf "@;@[<v 2>While Join:@;%a@]@."
      (print_binop) (cpt_instr,
                             abs,
                             abs_o,
                             abs_r)

  let print_while_widening cpt_instr abs abs' abs_r =
    Format.eprintf "@;@[<v 2>While Widening:@;%a@]@."
      (print_binop) (cpt_instr,
                             abs,
                             abs',
                             abs_r)

  let print_return ginstr fabs fname =
    Format.eprintf "@[<v>@[<v>%a@]Returning %s (called line %a):@;@]%!"
      (AbsDom.print ~full:true) fabs
      fname
      L.pp_sloc (fst ginstr.i_loc)

  let rec aeval_ginstr : ('ty,minfo) ginstr -> astate -> astate =
    fun ginstr state ->
      debug (fun () ->
        print_ginstr ginstr state.abs);

      (* We stop if the abstract state is bottom *)
      if AbsDom.is_bottom state.abs
      then state
      else
        (* We check the safety conditions *)
        let conds = safe_instr ginstr in
        let state = check_safety state (InProg (fst ginstr.i_loc)) conds in
        aeval_ginstr_aux ginstr state

  and aeval_ginstr_aux : ('ty,minfo) ginstr -> astate -> astate =
    fun ginstr state ->
    match ginstr.i_desc with 
      | Cassgn (lv,tag,ty1, Pif (ty2, c, el, er))
        when Config.sc_pif_movecc_as_if () ->
        assert (ty1 = ty2);
        let cl = { ginstr with i_desc = Cassgn (lv, tag, ty1, el) } in
        let cr = { ginstr with i_desc = Cassgn (lv, tag, ty2, er) } in
        aeval_if ginstr c [cl] [cr] state

      | Copn (lvs,tag,E.Ox86 (X86_instr_decl.CMOVcc sz),es)
        when Config.sc_pif_movecc_as_if () ->
        let c,el,er = as_seq3 es in
        let lv = as_seq1 lvs in
        let cl = { ginstr with i_desc = Cassgn (lv, tag, Bty (U sz), el) } in
        let cr = { ginstr with i_desc = Cassgn (lv, tag, Bty (U sz), er) } in
        aeval_if ginstr c [cl] [cr] state

      | Cassgn (lv, _, _, e) ->
        let abs = AbsExpr.abs_assign
            state.abs 
            (ty_lval lv)
            (AbsExpr.mvar_of_lvar state.abs ginstr.i_info lv) 
            e in
        { state with abs = abs; }

      | Copn (lvs,_,opn,es) ->
        (* Remark: the assignments must be done in the correct order. *)
        let assgns = split_opn (List.length lvs) opn es in
        let abs = AbsExpr.abs_assign_opn state.abs ginstr.i_info lvs assgns in

        { state with abs = abs; }

      | Cif(e,c1,c2) ->
        aeval_if ginstr e c1 c2 state

      | Cwhile(_,c1, e, c2) ->
        let prog_pt = fst ginstr.i_loc in

        (* We add a disjunctive constraint block. *)
        let abs = AbsDom.new_cnstr_blck state.abs prog_pt in
        let state = { state with abs = abs; } in

        let cpt = ref 0 in
        let state = aeval_gstmt c1 state in

        (* We now check that e is safe *)
        let conds = safe_e e in
        let state = check_safety state (InProg prog_pt) conds in

        (* Given an abstract state, compute the loop condition expression. *)
        let oec abs = AbsExpr.bexpr_to_btcons e abs in

        (* Candidate decreasing quantity *)
        let ni_e =
          try Some (dec_qnty_heuristic 
                      state.abs (c2 @ c1) 
                      (oec state.abs))
          with Heuristic_failed -> None in
        (* Variable where we store its value before executing the loop body. *)
        let mvar_ni = MNumInv prog_pt in

        (* We check that if the loop does not exit, then ni_e decreased by
             at least one. *)
        let check_ni_dec state = 
          if AbsDom.is_bottom state.abs then state
          else
            match ni_e with
            | None -> (* Here, we cannot prove termination *)
              let violation = (InProg prog_pt, Termination) in
              add_violations state [violation]

            | Some nie ->
              let env = AbsDom.get_env state.abs in
              let nie = Mtexpr.extend_environment nie env in

              (* (initial nie) - nie *)
              let e = Mtexpr.(binop Sub (var env mvar_ni) nie) in

              (* We assume the loop does not exit, and check whether the 
                 candidate decreasing quantity indeed decreased. *)
              let state_in = match oec state.abs with
                | Some ec -> 
                  { state with 
                    abs = AbsDom.meet_btcons state.abs ec }
                | None -> state in

              debug(fun () -> 
                  Format.eprintf "@[<v 2>Checking the numerical quantity in:@;\
                                  %a@]@."
                    (AbsDom.print ~full:true)
                    state_in.abs);

              let int = AbsDom.bound_texpr state_in.abs e
              and zint = AbsDom.bound_variable state_in.abs mvar_ni
              and test_intz =
                Interval.of_scalar (Scalar.of_int 0) (Scalar.of_infty 1)
              and test_into =
                Interval.of_scalar (Scalar.of_int 1) (Scalar.of_infty 1) in

              debug(fun () ->
                  Format.eprintf "@[<v>@;Candidate decreasing numerical \
                                  quantity:@;\
                                  @[%a@]@;\
                                  Numerical quantity decreasing by:@;\
                                  @[%a@]@;\
                                  Initial numerical quantity in interval:@;\
                                  @[%a@]@;@]"
                    (pp_opt Mtexpr.print) ni_e
                    Interval.print int
                    Interval.print zint;);

              if (Interval.is_leq int test_into) &&
                 (Interval.is_leq zint test_intz) then state
              else
                let violation = (InProg prog_pt, Termination) in
                add_violations state [violation] in


        (* ⟦body⟧state_i ∪ state *)
        let eval_body state_i state =
          let cpt_instr = !num_instr_evaluated - 1 in

          let state_o = aeval_gstmt (c2 @ c1) state_i in

          (* We check that if the loop does not exit, then ni_e decreased by
             at least one *)
          let state_o = check_ni_dec state_o in

          (* We forget the variable storing the initial value of the 
             candidate decreasing quantity. *)
          let state_o = { state_o with 
                          abs = AbsDom.forget_list state_o.abs [mvar_ni] } in

          let abs_r = AbsDom.join state.abs state_o.abs in
          debug (fun () ->
              print_while_join cpt_instr state.abs state_o.abs abs_r);
          { state_o with abs = abs_r; } in

        let enter_loop state =
          debug (fun () -> Format.eprintf "Loop %d@;" !cpt);
          cpt := !cpt + 1;
          let state = match oec state.abs with
            | Some ec ->
              debug (fun () -> Format.eprintf "Meet with %a@;" pp_btcons ec);
              { state with abs = AbsDom.meet_btcons state.abs ec }
            | None ->
              debug (fun () -> Format.eprintf "No meet");
              state in

          (* We evaluate a quantity that we try to prove is decreasing. *)
          debug (fun () ->
              Format.eprintf "@[<v>Candidate decreasing numerical quantity:@;\
                              @[%a@]@;@;@]"
                (pp_opt Mtexpr.print) ni_e);

          (* We evaluate the initial value of the candidate decreasing
             quantity. *)
          match ni_e with
            | None -> state
            | Some nie ->
              { state with 
                abs = AbsDom.assign_sexpr state.abs
                                 mvar_ni None
                                 (sexpr_from_simple_expr nie) } in

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
          match obind flip_btcons (oec state.abs) with
          | Some neg_ec ->
            debug (fun () -> Format.eprintf "Meet with %a@;" pp_btcons neg_ec);
            { state with abs = AbsDom.meet_btcons state.abs neg_ec }
          | None -> state in

        (* Simple heuristic for the widening threshold.
           Basically, if the loop condition is a return flag, we use the 
           candidate decreasing numerical quantity to make the threshold. *)
        let smpl_thrs abs = match simpl_obtcons (oec abs) with
          | Some _ as constr -> constr
          | None -> omap (fun e -> Mtcons.make e Lincons1.SUP) ni_e in
            
        let rec stabilize state pre_state =
          if is_stable state pre_state then exit_loop state
          else
            let cpt_instr = !num_instr_evaluated - 1 in
            let state' = unroll_once state in
            let w_abs =
              AbsDom.widening
                (smpl_thrs state.abs) (* this is used as a threshold *)
                state.abs state'.abs in

            debug(fun () ->
                print_while_widening
                  cpt_instr state.abs state'.abs w_abs);
            stabilize { state' with abs = w_abs; } (Some state) in

        let rec stabilize_b state_i pre_state =
          let cpt_i = !num_instr_evaluated - 1 in
          let state = eval_body state_i pre_state in

          if is_stable state (Some pre_state) then exit_loop state
          else
            let state_i' = enter_loop state in

            let w_abs =
              AbsDom.widening
                (smpl_thrs state_i.abs) (* this is used as a threshold *)
                state_i.abs state_i'.abs in
            debug(fun () ->
                print_while_widening cpt_i
                  state_i.abs state_i'.abs w_abs);
            stabilize_b { state_i' with abs = w_abs; } state in

        (* We first unroll the loop k_unroll times. 
           (k_unroll is a parameter of the analysis) *)
        let state, pre_state = unroll_times (Config.sc_k_unroll ()) state None in

        (* We stabilize the abstraction (in finite time) using widening. *)
        let state =
          if Config.sc_widening_out ()
          then stabilize state pre_state
          else stabilize_b (enter_loop state) state in

        (* We pop the disjunctive constraint block *)
        let abs = AbsDom.pop_cnstr_blck state.abs prog_pt in
        { state with abs = abs; } 


      | Ccall(_, lvs, f, es) ->
        let f_decl = get_fun_def state.prog f |> oget in
        let fn = f_decl.f_name in

        debug (fun () -> Format.eprintf "@[<v>Call %s:@;@]%!" fn.fn_name);
        let callsite,_ = ginstr.i_loc in

        let state_i = prepare_call state callsite f es in

        let fstate = aeval_call f f_decl callsite state_i in

        (* We check the safety conditions of the return *)
        let conds = safe_return f_decl in
        let fstate = check_safety fstate (InReturn fn) conds in

        debug(fun () ->
            print_return ginstr fstate.abs fn.fn_name);

        return_call state callsite fstate lvs

      | Cfor(i, (d,e1,e2), c) ->
        let prog_pt = fst ginstr.i_loc in
        match AbsExpr.aeval_cst_int state.abs e1, 
              AbsExpr.aeval_cst_int state.abs e2 with
        | Some z1, Some z2 ->
          if z1 = z2 then state else
            let init_i, final_i, op = match d with
              | UpTo -> assert (z1 < z2); (z1, z2 - 1, fun x -> x + 1)
              | DownTo -> assert (z1 < z2); (z2, z1 + 1, fun x -> x - 1) in

            let rec mk_range i f op =
              if i = f then [i] else i :: mk_range (op i) f op in

            let range = mk_range init_i final_i op
            and mvari = Mvalue (Avar (L.unloc i)) in
            let apr_env = AbsDom.get_env state.abs in 

            List.fold_left ( fun state ci ->
                (* We add a disjunctive constraint block. *)
                let std = AbsDom.new_cnstr_blck state.abs prog_pt in
                let state = { state with abs = std; } in

                (* We set the integer variable i to ci. *)
                let expr_ci = Mtexpr.cst apr_env (Coeff.s_of_int ci)
                                  |> sexpr_from_simple_expr in
                let abs = 
                  AbsDom.assign_sexpr
                    state.abs mvari (Some ginstr.i_info) expr_ci in

                let state =
                  { state with
                    abs = AbsDom.is_init abs (Avar (L.unloc i)); }
                  |> aeval_gstmt c in

                (* We pop the disjunctive constraint block. *)
                let abs = AbsDom.pop_cnstr_blck state.abs prog_pt in
                { state with abs = abs; } 
              ) state range

        | _ ->
          Format.eprintf "@[<v>For loop: \
                          I was expecting a constant integer expression.@;\
                          Expr1:@[%a@]@;Expr2:@[%a@]@;@."
            (Printer.pp_expr ~debug:true) e1
            (Printer.pp_expr ~debug:true) e2;
          assert false

  and aeval_call : funname -> minfo func -> L.t -> astate -> astate =
    fun f f_decl callsite st_in ->
    let itk = ItFunIn (f,callsite) in

    match aeval_call_strategy callsite f_decl st_in with 
    | Config.Call_Direct -> aeval_body f_decl.f_body st_in

    (* Precond: [check_valid_call_top st_in] must hold:
       the function must not use memory loads/stores, array accesses must be 
       fixed, and arrays in arguments must be fully initialized
       (i.e. cells must be initialized). *)
    | Config.Call_TopByCallSite ->
      (* f has been abstractly evaluated at this callsite before *)
      if ItMap.mem itk st_in.it then 
        let fabs = ItMap.find itk st_in.it in
        match FAbs.apply st_in.abs fabs with
        | Some (f_abs_out, f_effects) ->
          { st_in with abs = f_abs_out;
                       s_effects = f_effects; } 

        | None -> assert false    (* that should not be possible *)

      (* We abstractly evaluate f for the first time *)
      else
        (* Set the abstract state to top (and remove all disjunction).
             Moreover, all arguments of [f_decl] are assumed
             initialized (including array cells). *)
        let st_in_ndisj = 
          let mvars = List.map mvar_of_var f_decl.f_args
                      |> u8_blast_vars ~blast_arrays:true in
          let abs = AbsDom.top_ni st_in.abs in
          let abs = List.fold_left (fun abs mv -> match mv with
              | Mvalue at -> AbsDom.is_init abs at
              | _ -> assert false
            ) abs mvars in
          
          { st_in with abs = abs } 
        in

        let st_out_ndisj = aeval_body f_decl.f_body st_in_ndisj in

        (* We make a new function abstraction for f. Roughly, it is of the form:
           input |--> (output,effects) *)
        let fabs = FAbs.make 
            st_in_ndisj.abs
            st_out_ndisj.abs
            st_out_ndisj.s_effects in

        let st_out_ndisj = { st_out_ndisj with
                             it = ItMap.add itk fabs st_out_ndisj.it } in

        (* It remains to add the disjunctions of the call_site to st_out *)
        { st_out_ndisj with 
          abs = AbsDom.to_shape st_out_ndisj.abs st_in.abs }
        
  and aeval_if ginstr e c1 c2 state =
    let eval_cond state = function
      | Some ec -> AbsDom.meet_btcons state.abs ec
      | None -> state.abs in
    let oec = AbsExpr.bexpr_to_btcons e state.abs in

    let labs, rabs =
      if Config.sc_if_disj () && is_some (simpl_obtcons oec) then
        let ec = simpl_obtcons oec |> oget in
        AbsDom.add_cnstr state.abs ~meet:true ec (fst ginstr.i_loc)
      else
        (* FIXME: check that the fact that we do not introduce a 
           disjunction node does not create issues. *)
        let noec = obind flip_btcons oec in
        ( eval_cond state oec, eval_cond state noec ) in

    (* Branches evaluation *)
    let lstate = aeval_gstmt c1 { state with abs = labs; } in

    let cpt_instr = !num_instr_evaluated - 1 in

    (* We abstractly evaluate the right branch
       Be careful the start from lstate, as we need to use the
       updated abstract iterator. *)
    let rstate = aeval_gstmt c2 { lstate with abs = rabs; } in

    let abs_res = AbsDom.join lstate.abs rstate.abs in
    debug (fun () ->
        print_if_join cpt_instr ginstr lstate.abs rstate.abs abs_res);
    { rstate with abs = abs_res; }

  and aeval_body f_body state =
    debug (fun () -> Format.eprintf "Evaluating the body ...@.@.");
    aeval_gstmt f_body state

  and aeval_gstmt : ('ty,'i) gstmt -> astate -> astate =
    fun gstmt state ->
    let state = List.fold_left (fun state ginstr ->
        aeval_ginstr ginstr state)
        state gstmt in
    let () = debug (fun () ->
        if gstmt <> [] then
          Format.eprintf "%a%!" (AbsDom.print ~full:true) state.abs) in
    state

  (* Select the call strategy for [f_decl] in [st_in] *)
  and aeval_call_strategy callsite f_decl st_in =
    let strat = match Config.sc_call_policy () with
    | Config.CallDirectAll -> Config.Call_Direct
    (* | CallWideningAll -> Call_WideningByCallSite *)
    | Config.CallTopHeuristic ->
      if check_valid_call_top st_in f_decl
      then Config.Call_TopByCallSite 
      else Config.Call_Direct in

    debug(fun () -> Format.eprintf "Call strategy for %s at %a: %a@." 
             f_decl.f_name.fn_name
             L.pp_sloc callsite
             pp_call_strategy strat);
    strat
  
  (*------------------------------------------------------------------------*)
  let print_mem_ranges state =
    debug(fun () -> Format.eprintf
             "@[<v 0>@;Final offsets full abstract value:@;@[%a@]@]@."
             (AbsDom.print ~full:true)
             state.abs)

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
    let vars = in_vars @ fun_vars ~expand_arrays:false f_decl state.env in
    let rem_vars = List.fold_left (fun acc v ->
        if (List.mem v vars_to_keep) then acc else v :: acc )
        [] vars in

    let abs_proj = 
      AbsDom.pop_cnstr_blck
        (AbsDom.forget_list state.abs rem_vars) 
        L._dummy                (* We use L._dummy for the initial block *)
    in

    let sb = !only_rel_print in (* Not very clean *)
    only_rel_print := true;
    Format.fprintf fmt "@[%a@]" (AbsDom.print ~full:true) abs_proj;
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

      let state, warnings = init_state source_main_decl main_decl prog in

      (* We abstractly evaluate the main function *)
      let final_st = aeval_gstmt main_decl.f_body state in

      (* We check the safety conditions of the return *)
      let conds = safe_return main_decl in
      let final_st = check_safety final_st (InReturn main_decl.f_name) conds in

      debug(fun () -> Format.eprintf "%a" pp_violations final_st.violations);
      print_mem_ranges final_st;

      let () = debug (fun () -> print_stats ()) in
      let () = Sys.set_signal Sys.sigint old_handler in

      { violations = final_st.violations;
        mem_ranges_printer = mem_ranges_printer final_st main_decl;
        print_var_interval = print_var_interval final_st;
        warnings = warnings; }
    with
    | Manager.Error _ as e -> hndl_apr_exc e
end


module type ExportWrap = sig
  (* main function, before any compilation pass *)
  val main_source : unit Prog.func
      
  val main : unit Prog.func
  val prog : unit Prog.prog
end

module AbsAnalyzer (EW : ExportWrap) = struct
  
  module EW = struct
    let main_source = EW.main_source
    
    (* We ensure that all variable names are unique *)
    let main,prog = MkUniq.mk_uniq EW.main EW.prog
  end

  let parse_pt_rel s = match String.split_on_char ';' s with
    | [pts;rels] ->
      let relationals =
        if rels = ""
        then Some []
        else String.split_on_char ',' rels |> some in
      let pointers =
        if pts = ""
        then Some []
        else String.split_on_char ',' pts |> some in
      { relationals = relationals;
        pointers = pointers; }
      
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
    try     
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
      |> List.sort_uniq Stdlib.compare
      |> List.map (fun pt ->
          try List.find (fun x -> x.v_name = pt) EW.main.f_args with
          | Not_found ->
            raise (Failure ("-safetyparam ill-formed (" ^ pt ^ " unknown)"))) in

    let npt = List.filter (fun x -> not (List.mem x pt_vars)) EW.main.f_args
              |> List.map (fun x -> MmemRange (MemLoc x)) in

    let () = Config.pp_current_config_diff () in
    
    let l_res = List.map (fun p ->
        let module AbsInt = AbsInterpreter (struct
            include EW
            let param = p
          end) in
        AbsInt.analyze ()) ps in

    match l_res with
    | [] -> raise (Failure "-safetyparam ill-formed (empty list of params)")
    | res :: _->
      let pp_mem_range fmt = match npt with
        | [] -> Format.fprintf fmt ""
        | _ ->          
          Format.eprintf "@[<v 2>Memory ranges:@;%a@]@;"
            (pp_list res.print_var_interval) npt in

      let pp_warnings fmt warns =
        if warns <> [] then
          Format.fprintf fmt "@[<v 2>Warnings:@;%a@]@;"
            (pp_list (fun fmt x -> x fmt)) warns in
      
      Format.eprintf "@.@[<v>%a@;\
                      %a@;\
                      %t\
                      %a@]@."
        pp_warnings res.warnings
        pp_violations res.violations
        pp_mem_range
        (pp_list (fun fmt res -> res.mem_ranges_printer fmt ())) l_res;

      if res.violations <> [] then begin
        Format.eprintf "@[<v>Program is not safe!@;@]@.";
        exit(2)
      end;
    with | Manager.Error _ as e -> hndl_apr_exc e
end
