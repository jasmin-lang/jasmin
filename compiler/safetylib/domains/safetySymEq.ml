open Jasmin
open Utils
open Apron
    
open SafetyUtils
open SafetyVar
open SafetyExpr 
open SafetyConstr
open SafetyInterfaces



(************************************)
(* Simple Rewriting and Decompiling *)
(************************************)

exception Rewrite_failed
let neg_e e =
  let open Mtexpr in
  let rec neg_e = function
    | Munop (Texpr1.Neg, e', _, _) -> e'
    | Mbinop (Texpr1.Add, e1, e2, _, _) ->
      binop Texpr1.Add (neg_e e1) (neg_e e2)
    | Mbinop (Texpr1.Sub, e1, e2, _, _) ->
      binop Texpr1.Add (neg_e e1) e2
    | Mbinop (Texpr1.Mul, e1, e2, _, _) ->
      binop Texpr1.Mul (neg_e e1) e2
    | Mcst c -> cst (Coeff.neg c)
    | Mvar _ as e -> unop Texpr1.Neg e
    | _ -> raise Rewrite_failed
  in
  neg_e e

let is_var = function Mtexpr.Mvar _ -> true | _ -> false
let is_cst = function Mtexpr.Mcst _ -> true | _ -> false

(* Tries to do trivial rewritings. *)
let rec rewrite_e e =
  let open Mtexpr in
  match e with
  | Munop (Texpr1.Neg, e', _, _) when not (is_var e') ->
    begin
      try rewrite_e (neg_e e') with Rewrite_failed -> e
    end

  | Mbinop (Texpr1.Add, Mcst i, e', _, _) when Coeff.equal_int i 0 ->
    rewrite_e e'

  | Mbinop (Texpr1.Add, e', Mcst i, _, _)
  | Mbinop (Texpr1.Sub, e', Mcst i, _, _) when Coeff.equal_int i 0 ->
    rewrite_e e'

  | Mbinop (Texpr1.Sub, Mcst i, e', _, _) when Coeff.equal_int i 0 ->
    rewrite_e (unop Texpr1.Neg e')

  | Mbinop (Texpr1.Sub, e1, e2, _, _) ->
    begin
      try
        let e2 = neg_e e2 in
        binop Texpr1.Add e1 e2
      with Rewrite_failed ->
        let e1, e2 = rewrite_e e1, rewrite_e e2 in
        binop Texpr1.Sub e1 e2
    end

  | Mbinop (op, e1, e2, _, _) ->
    let e1, e2 = rewrite_e e1, rewrite_e e2 in
    binop op e1 e2
  | Munop (op, e', _, _) ->
    let e' = rewrite_e e' in
    unop op e'

  | Mcst _ | Mvar _ -> e

let rewrite_c bt =
  Mtcons.make (rewrite_e (Mtcons.get_expr bt)) (Mtcons.get_typ bt)

(* Tries to rewrite [bt] into [a + b ⋄ 0] where ⋄ ∈ {≥, >, ≠, =} *)
let cmp_cst bt =
  let open Mtexpr in
  let e = Mtcons.get_expr bt in
  match e with
  | Mbinop (Texpr1.Add, a, b, _, _) -> Some (a, b, Mtcons.get_typ bt)
  | Mvar _ as e' ->
    Some (e', cst (Coeff.s_of_int 0), Mtcons.get_typ bt)
  | _ -> None

(* FIXME: this is quite ad-hoc.*)
let rec rewrite bt = match bt with
  | BAnd (BLeaf bt1, BLeaf bt2) ->
    let bt1, bt2 = rewrite_c bt1, rewrite_c bt2 in
    begin
      let swap (c1,c2) = match c1, c2 with
        | Some (_,_,Tcons1.SUPEQ), Some (_,_,Tcons1.DISEQ) -> c1, c2
        | Some (_,_,Tcons1.DISEQ), Some (_,_,Tcons1.SUPEQ) -> c2, c1
        | _ -> None, None in
      match swap (cmp_cst bt1, cmp_cst bt2) with      

      | None, _ | _, None -> bt
      (*     a + b >= 0                  a' + b' <> 0 *)
      | Some (a, b, Tcons1.SUPEQ), Some (a', b', Tcons1.DISEQ) ->
        let ma = rewrite_e (Mtexpr.unop Texpr1.Neg a) in
        let mb = rewrite_e (Mtexpr.unop Texpr1.Neg b) in
        if (Mtexpr.equal_mexpr a a' && Mtexpr.equal_mexpr b b') ||
           (Mtexpr.equal_mexpr a b' && Mtexpr.equal_mexpr b a') ||
           (Mtexpr.equal_mexpr ma a' && Mtexpr.equal_mexpr mb b') ||
           (Mtexpr.equal_mexpr ma b' && Mtexpr.equal_mexpr mb a')
        then
          (* (a + b <> 0 /\ a + b >= 0) <=> a + b > 0
             or:
             (-a + -b <> 0 /\ a + b >= 0) <=> a + b > 0 *)
          BLeaf (Mtcons.make
                   (Mtexpr.binop Texpr1.Add a b)
                   Tcons1.SUP)
        else bt
      | _ -> bt
    end

  | BAnd (b1,b2) -> BAnd ( rewrite b1, rewrite b2 )
  | BOr (b1,b2)  -> BOr  ( rewrite b1, rewrite b2 ) 
  | BVar _ | BLeaf _ -> bt
    
(*------------------------------------------------------------*)
module SymExprImpl : SymExpr = struct
  (* γ(x ↦ e)    = { m | 〚x〛(m) = 〚e〛(m) }
     γ(x ↦ e, t) = γ(x ↦ e) ∩ γ(t)
     γ(ε)        = ⊤        
     
     Remarks:
     - there is not bottom
     - we do not care about the environments in [vsym] and [bsym] *)
  type t = { vsym : Mtexpr.t Mm.t;
             bsym : Mtcons.t Mbv.t; }

  let make () = { vsym = Mm.empty; bsym = Mbv.empty; }

  let print ppf t =
    Format.fprintf ppf "@[<v 0>\
                        @[<hv 0>Sym (vars):%a@]@;\
                        @[<hv 0>Sym (bool) Expr:%a@]@]"
      (pp_list (fun ppf (v,e) ->
           Format.fprintf ppf "(%a ↦ %a)"
             pp_mvar v
             Mtexpr.print e))
      (Mm.bindings t.vsym)
      (pp_list (fun ppf (v,be) ->
           Format.fprintf ppf "(%a ↦ %a)"
             Bvar.print v
             Mtcons.print be))
      (Mbv.bindings t.bsym)

  let apply f g t    = { vsym = f t.vsym; 
                         bsym = g t.bsym; }

  let map f g t      = apply (Mm.map f) (Mbv.map g) t

  let merge f g t t' = { vsym = Mm.merge f t.vsym t'.vsym;
                         bsym = Mbv.merge g t.bsym t'.bsym; }
    
  let meet =
    let f _ e e' = match e, e' with
      | Some e, Some e' -> if Mtexpr.equal_mexpr e e' then Some e else None
      | Some e, None | None, Some e -> Some e
      | _ -> assert false
    and g _ b b' = match b, b' with
      | Some b, Some b' -> if Mtcons.equal_tcons b b' then Some b else None
      | Some b, None | None, Some b -> Some b
      | _ -> assert false in
    merge f g

  let join =
    let f _ e e' = match e, e' with
      | Some e, Some e' -> if Mtexpr.equal_mexpr e e' then Some e else None
      | Some _, None | None, Some _ -> None
      | _ -> assert false
    and g _ b b' = match b, b' with
      | Some b, Some b' -> if Mtcons.equal_tcons b b' then Some b else None
      | Some _, None | None, Some _ -> None
      | _ -> assert false in
    merge f g

  let widening = join
    
  let b_remove t v =
    let bv_p, bv_n = Bvar.make v true, Bvar.make v false in
    { t with bsym = Mbv.remove bv_p (Mbv.remove bv_n t.bsym); }
    
  (* Remove any entry in [t] using variable [v] *)
  let v_clear t v =
    let f = Mm.filter (fun _ e ->
        not (List.mem v (Mtexpr.get_var e)))
    and g = Mbv.filter (fun _ be ->
        let e = Mtcons.get_expr be in
        not (List.mem v (Mtexpr.get_var e))) in
    let t = apply f g t in

    let t = b_remove t v in
    { t with vsym = Mm.remove v t.vsym }
      
  let assign_expr_one force t (v,e) =
    let t = v_clear t v in
    if weak_update v && not force
    then t

    (* We add the binding [v ↦ e] *)
    else { t with vsym = Mm.add v e t.vsym }

  let assign_expr ?force:(force=false) t ves =
    let ves = List.filter (fun (v,_) -> match v with
        | Mlocal (AarraySlice _) -> false (* FIXME: add an option *)
        | Mglobal _ -> false
        | _ -> true
      ) ves in
    List.fold_left (assign_expr_one force) t ves
    
  let assign_bexpr t v btcons =
    let t = v_clear t v in
    match btcons with
    | BLeaf tcons ->
      let bv_p, bv_n = Bvar.make v true, Bvar.make v false in

      (* Add the positive variable symbolic expression *)
      let bsym = Mbv.add bv_p tcons t.bsym in

      (* Add the negative variable symbolic expression *)
      let n_btcons = flip_constr tcons in
      let bsym = Option.map_default (fun c -> Mbv.add bv_n c bsym) bsym n_btcons in
      { t with bsym = bsym }
      
    | BVar _bv -> t               (* FIXME: we could use [_bv] 
                                     symbolic expression here. *)
    | BAnd _ | BOr _ -> t


  (* FIXME: we are not changing the environments here. 
     Check that this is ok. *)
  let change_environment t vs =
    let f = Mm.filter (fun v e ->
        let vars = Mtexpr.get_var e in 
        List.mem v vs &&
        List.for_all (fun v' -> List.mem v' vs) vars)
    and g = Mbv.filter (fun bv be ->
        let e = Mtcons.get_expr be in
        let vars = Mtexpr.get_var e in
        List.mem (Bvar.get_mv bv) vs &&
        List.for_all (fun v' -> List.mem v' vs) vars) in
    apply f g t     


  (* Implement if needed. *)
  (* let subst_expr : t -> Mtexpr.t -> Mtexpr.t = fun t e -> assert false *)

  (* This substitute boolean flags by an equivalent constraint.
     Also, tries to decompile what [lowering.v] did. *)
  let subst_btcons t bt =
    let rec subst_btcons = function
    | BVar bv ->
      begin
        try BLeaf (Mbv.find bv t.bsym)
        with Not_found -> BVar bv
      end
    | BLeaf _ as bt -> bt       (* we could substitute in [bt] if needed. *)
    | BAnd (b1,b2) -> BAnd (subst_btcons b1, subst_btcons b2)
    | BOr (b1,b2)  -> BOr  (subst_btcons b1, subst_btcons b2) in

    (* We try to simplify [bt] after the substitution. *)
    let bt' = rewrite (subst_btcons bt) in
    if Config.sc_print_symb_subst () && not (equal_btcons bt bt') then
      debug (fun () ->
          Format.eprintf "@[<hov 0>Substituted@,   %a@ by %a@]@;"
            pp_btcons bt pp_btcons bt'
        );
    bt'

  
  let forget_list = List.fold_left v_clear
      
  let support t = ( List.map fst (Mm.bindings t.vsym),
                    List.map fst (Mbv.bindings t.bsym) )      
end
