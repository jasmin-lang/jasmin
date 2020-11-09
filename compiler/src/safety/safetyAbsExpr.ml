open Utils
open Prog
open Apron
open ToEC
open Wsize

open SafetyPreanalysis
open SafetyInterfaces
open SafetyUtils
open SafetyExpr
open SafetyVar
open SafetyConstr
    

let get_wsize = function
  | Type.Coq_sword sz -> sz
  | _ -> raise (Aint_error "Not a Coq_sword")

let pcast ws e = match ToEC.ty_expr e with
  | Bty Int -> Papp1 (E.Oword_of_int ws, e)
  | Bty (U ws') ->
    assert (int_of_ws ws' <= int_of_ws ws);
    if ws = ws' then e
    else Papp1 (E.Ozeroext (ws,ws'), e)

  | Bty Bool | Arr _ -> assert false

let wsize_of_ty ty = match ty with
  | Bty Bool -> assert false
  | Bty Int -> -1
  | Bty (U sz) -> int_of_ws sz
  | Arr (sz, _) -> int_of_ws sz


(****************************)
(* Expression Linearization *)
(****************************)

let op1_to_abs_unop op1 = match op1 with
  | E.Oneg _   -> Some Texpr1.Neg
  | E.Oword_of_int _ | E.Oint_of_word _ | E.Ozeroext _ -> assert false
  | _ -> None

type word_op =
  | Wand                        (* supported only for padding with 2^n - 1 *)
  | Wor                         (* currently not-supported *)
  | Wxor                        (* currently not-supported *)
    
  | Wshift of [`Unsigned_left | `Unsigned_right | `Signed_right ]
  (* Remarks: 
     - signed left is a synonymous for unsigned left.
     - currently, shift-right is not supported. *)
              
type abs_binop =
  | AB_Unknown
  | AB_Wop   of word_op
  | AB_Arith of Apron.Texpr1.binop

let abget = function AB_Arith a -> a | _ -> assert false
  
let op2_to_abs_binop op2 = match op2 with
  | E.Oadd _ -> AB_Arith Texpr1.Add
  | E.Omul _ -> AB_Arith Texpr1.Mul                  
  | E.Osub _ -> AB_Arith Texpr1.Sub

  | E.Omod (Cmp_w (Signed, _)) -> AB_Unknown
  | E.Omod _ -> AB_Arith Texpr1.Mod

  | E.Odiv (Cmp_w (Signed, _)) -> AB_Unknown
  | E.Odiv _ -> AB_Arith Texpr1.Div

  | E.Olsr _ -> AB_Wop (Wshift `Unsigned_right)
  | E.Olsl _ -> AB_Wop (Wshift `Unsigned_left)
  | E.Oasr _ -> AB_Wop (Wshift `Signed_right)
      
  | E.Oand | E.Oor                   (* boolean connectives *)
  | E.Oeq _ | E.Oneq _ | E.Olt _ | E.Ole _ | E.Ogt _ | E.Oge _ -> AB_Unknown

  (* bit-wise boolean connectives *)
  | E.Oland _ -> AB_Wop Wand
  | E.Olor _  -> AB_Wop Wor
  | E.Olxor _ -> AB_Wop Wxor
      
  | E.Ovadd (_, _) | E.Ovsub (_, _) | E.Ovmul (_, _)
  | E.Ovlsr (_, _) | E.Ovlsl (_, _) | E.Ovasr (_, _) -> AB_Unknown


(* Return lin_expr mod 2^n *)
let expr_pow_mod n lin_expr =
  let mod_expr = cst_pow_minus n 0 in
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
  match sign with
  | Signed -> 
    let pow_n = cst_pow_minus n 0 in
    let pow_n_minus_1 = cst_pow_minus (n - 1) 0 in

    let expr = Mtexpr.binop Texpr1.Sub expr pow_n_minus_1 in
    let expr = expr_pow_mod n expr in
    let expr = Mtexpr.binop Texpr1.Add expr pow_n in
    let expr = expr_pow_mod n expr in
    Mtexpr.binop Texpr1.Sub expr pow_n_minus_1 

  | Unsigned ->
    let pow_n = cst_pow_minus n 0 in
    
    let expr = expr_pow_mod n expr in
    let expr = Mtexpr.binop Texpr1.Add expr pow_n in
    expr_pow_mod n expr

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
            Mtexpr.print e
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
    interval_to_zint int

  (* Try to evaluate e to a constant expression in abs *)
  let rec aeval_cst_zint abs e = match e with
    | Pvar x -> begin match (L.unloc x).v_ty with
        | Bty Int -> aeval_cst_var abs x
        | Bty (U ws) ->
          let line = Mtexpr.var (mvar_of_var (L.unloc x)) in
          if linexpr_overflow abs line Unsigned (int_of_ws ws) then None
          else aeval_cst_var abs x
        | _ -> raise (Aint_error "type error in aeval_cst_int") end

    | Pconst c -> Some (Z.of_string (B.to_string c))

    | Papp1 (E.Oneg Op_int, e) ->
      obind (fun x -> Some (Z.neg x)) (aeval_cst_zint abs e)

    | Papp1 (E.Oint_of_word _, e) ->
      obind (fun x -> Some x) (aeval_cst_zint abs e)
    (* No need to check for overflows because we do not allow word operations. *)

    | Papp2 (Oadd Op_int, e1, e2) ->
      obind2 (fun x y -> Some (Z.add x y))
        (aeval_cst_zint abs e1) (aeval_cst_zint abs e2)

    | Papp2 (Osub Op_int, e1, e2) ->
      obind2 (fun x y -> Some (Z.sub x y))
        (aeval_cst_zint abs e1) (aeval_cst_zint abs e2)

    | Papp2 (Omul Op_int, e1, e2) ->
      obind2 (fun x y -> Some (Z.mul x y))
        (aeval_cst_zint abs e1) (aeval_cst_zint abs e2)

    | _ -> None

  (* Try to evaluate e to a constant expression (of type word) in abs.
     Superficial checks only. *)
  let rec aeval_cst_w abs e = match e with
    | Pvar x -> begin match (L.unloc x).v_ty with
        | Bty (U ws) ->
          let line = Mtexpr.var (mvar_of_var (L.unloc x)) in
          if linexpr_overflow abs line Unsigned (int_of_ws ws) then None
          else aeval_cst_var abs x
        | _ -> raise (Aint_error "type error in aeval_cst_w") end

    | Papp1 (E.Oword_of_int ws, e) ->
      let c_e = aeval_cst_zint abs e in
      let pws = Z.pow (Z.of_int 2) (int_of_ws ws) in
      omap (fun c_e ->
          let x = Z.add Z.(c_e mod pws) pws in
          Z.(x mod pws)) c_e

    | _ -> None

  let rec aeval_cst_w_i abs e =
    try omap Z.to_int (aeval_cst_w abs e) with
    | Z.Overflow -> None

  let aeval_cst_int abs e =
    try omap Z.to_int (aeval_cst_zint abs e) with
    | Z.Overflow -> None
  
  (*-------------------------------------------------------------------------*)
  let arr_full_range x =
    List.init
      ((arr_range x) * (arr_size x |> size_of_ws))
      (fun i -> AarrayEl (x, U8, i))

  let abs_arr_range abs x ws ei =
    match omap Z.to_int (aeval_cst_zint abs ei) with
    | Some i -> [AarrayEl (x, ws, i)]
    | None -> arr_full_range x
    | exception Z.Overflow -> arr_full_range x

  (*-------------------------------------------------------------------------*)
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
    let lin = Mtexpr.cst (Coeff.Interval Interval.top) in
    wrap_if_overflow abs lin Unsigned (int_of_ws ws_e)

  let rec linearize_iexpr abs (e : expr) =
    match e with
    | Pconst z -> mtexpr_of_bigint z

    | Pvar x ->
      check_is_int (L.unloc x);
      Mtexpr.var (Mvalue (Avar (L.unloc x)))

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
        | AB_Wop _ -> assert false (* word operations only makes sense on bit-vectors *)
      end

    | Pif _ -> raise If_not_supported

    | _ -> assert false

  and linearize_wexpr abs (e : ty gexpr) =
    let ws_e = ws_of_ty (ty_expr e) in

    match e with
    | Pvar x ->
      check_is_word (L.unloc x);
      let lin = Mtexpr.var (Mvalue (Avar (L.unloc x))) in
      wrap_if_overflow abs lin Unsigned (int_of_ws ws_e)

    | Pglobal(ws, x) ->
      let lin = Mtexpr.var (Mglobal (x,Bty (U ws))) in
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
                  let c' = Mtexpr.cst (Coeff.s_of_mpqf mz) in
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
                    Mtexpr.print lin
                    Mtexpr.print (oget alt_lin)) in
              oget alt_lin
            else wrap_lin_expr Unsigned ws_out lin
          else lin

        | AB_Wop (Wshift `Signed_right)
        | AB_Arith Texpr1.Div
        | AB_Arith Texpr1.Pow
        | AB_Unknown ->
          raise (Binop_not_supported op2)

        | AB_Wop (Wshift stype) ->
          begin
            match aeval_cst_w_i abs e2 with
            | Some i when i <= int_of_ws ws_e ->
              let absop = match stype with
                | `Unsigned_right -> Texpr1.Div
                | `Unsigned_left -> Texpr1.Mul
                | _ -> assert false in
              let lin = Mtexpr.(binop absop
                                  (linearize_wexpr abs e1)
                                  (cst_pow_minus i 0)) in

              wrap_if_overflow abs lin Unsigned (int_of_ws ws_e)
                
            | _ -> raise (Binop_not_supported op2)
          end

        (* Padding. *)
        | AB_Wop Wand ->
          let e', i = match aeval_cst_w abs e2 with
            | Some i -> e1, i
            | None -> match aeval_cst_w abs e1 with
              | Some i -> e2, i
              | None -> raise (Binop_not_supported op2) in

          let log_i = Z.log2up i in
          let log_i = Mtexpr.cst (Coeff.s_of_mpqf (Mpqf.of_int log_i)) in
                        
          let lin_e' = linearize_wexpr abs e' in
                    
          let lin = Mtexpr.(binop Texpr1.Mod lin_e' log_i) in
          wrap_if_overflow abs lin Unsigned (int_of_ws ws_e)

            | _ -> raise (Binop_not_supported op2)
      end

    | Pget(ws,x,ei) ->
      begin match abs_arr_range abs (L.unloc x) ws ei with
        | [] -> assert false
        | [at] ->
          let lin = Mtexpr.var (Mvalue at) in
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

  let swap_op2 op e1 e2 =
    match op with
    | E.Ogt   _ -> e2, e1
    | E.Oge   _ -> e2, e1
    | _         -> e1, e2

  let rec bexpr_to_btcons_aux : AbsDom.t -> 'a Prog.gexpr -> btcons =
    fun abs e ->
    let aux = bexpr_to_btcons_aux abs in
    match e with
    | Pbool b ->
      let cons =
        if b then true_tcons1
        else false_tcons1 in
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
        | (Tcons1.EQ | Tcons1.DISEQ), (Mtexpr.Mcst cst), lin
        | (Tcons1.EQ | Tcons1.DISEQ), lin, (Mtexpr.Mcst cst) ->      
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
          let z_expr = Mtexpr.cst (Coeff.s_of_int 0) in
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
            let z_sexpr = Mtexpr.cst (Coeff.Interval int)
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
        let sexpr = mtexpr_of_bigint i |> sexpr_from_simple_expr in
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
      let inv_os = Mtexpr.var (MvarOffset inv) in

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
    | Mvalue (Aarray gv) -> begin match e with
        | Mtexpr.Mvar (Mvalue (Aarray ge)) ->
          let n = arr_range gv in
          let ws = arr_size gv in
          assert (n = arr_range ge);
          assert (ws = arr_size ge);
          List.fold_left (fun a i ->
              let vi = Mvalue (AarrayEl (gv,ws,i))  in
              let eiv = Mvalue (AarrayEl (ge,ws,i)) in
              let ei = Mtexpr.var eiv
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
          let se = Mtexpr.var (Mvalue (Aarray (L.unloc x))) in
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

