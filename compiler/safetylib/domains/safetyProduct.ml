open Jasmin
open Utils
open Apron
open Prog
    
open SafetyUtils
open SafetyPreanalysis
open SafetyVar
open SafetyExpr 
open SafetyConstr
open SafetyInterfaces
    
(*------------------------------------------------------------*)
(* Domains Product *)

type v_dom = Nrd of int | Ppl of int

let pp_dom fmt = function
  | Ppl 0 -> Format.fprintf fmt "Rel"
  | Nrd 0 -> Format.fprintf fmt "NonRel"
  | _ -> assert false

(* let pp_dom fmt = function
 *   | Ppl i -> Format.fprintf fmt "Ppl %d" i
 *   | Nrd i -> Format.fprintf fmt "Nrd %d" i *)

let string_of_dom = function
  | Nrd i -> "Nrd" ^ string_of_int i
  | Ppl i -> "Ppl" ^ string_of_int i

module Mdom = Map.Make(struct
    type t = v_dom

    let compare = Stdlib.compare
    let equal u v = u = v
  end)


type dom_st = v_dom Mm.t
    
module type VDomWrap = sig
  (* Associate a domain (ppl or non-relational) to every variable.
     An array element must have the same domain that its blasted component. 
     The second argument is a state, which allows to change a variable domain
     during the analysis. 
     Only [Mlocal (Avar _)] and [MvarOffset _] can change domain. *)
  val vdom : mvar -> dom_st -> v_dom

  (* Initial state. *)
  val dom_st_init : dom_st

  (* [dom_st_update dom_st xs info] updates the packing partition to prepare for
     the assignments of variables [xs]. *)
  val dom_st_update : dom_st -> mvar list -> minfo -> dom_st

  val merge_dom : dom_st -> dom_st -> dom_st
  val fold_dom_st : (mvar -> v_dom -> 'a -> 'a) -> dom_st -> 'a -> 'a
end


(*---------------------------------------------------------------*)

(* For now we fixed the domains, and we use only two of them, one non-relational
   and one Ppl. Still, we generalized to n different domains whenever possible
   to help future possible extentions. *)
module AbsNumProd (VDW : VDomWrap) (NonRel : AbsNumType) (PplDom : AbsNumType)
  : AbsNumProdT = struct

  type t = { nrd : NonRel.t Mdom.t;
             ppl : PplDom.t Mdom.t;
             dom_st : dom_st; }

  let nrddoms = [Nrd 0]
  let ppldoms = [Ppl 0]

  
  let vdom v dom_st =
    if v = dummy_mvar then Ppl 0 
    else VDW.vdom v dom_st 
      
  let is_in_dom_ppl v d t =
    let a = Mdom.find d t.ppl in
    let av = avar_of_mvar v in
    Environment.mem_var (PplDom.get_env a) av

  let is_in_dom_nrd v d t =
    let a = Mdom.find d t.nrd in
    let av = avar_of_mvar v in
    Environment.mem_var (NonRel.get_env a) av
      
  (* This assumes that we only use [Nrd 0] and [Ppl 0]. *)
  let set_rel t v =
    match vdom v t.dom_st with
    | Ppl 0 -> t

    | Nrd 0 ->
      (* We change dynamically the packing only for local variables and
         offsets. *)
      assert (is_local_var v || is_offset v);
      assert (not (is_in_dom_ppl v (Ppl 0) t)); 
      let anrd = Mdom.find (Nrd 0) t.nrd in

      (* The environment does not matter. *)
      let int = NonRel.bound_variable anrd v in
      let e = Mtexpr.cst (Coeff.Interval int) in

      let appl = Mdom.find (Ppl 0) t.ppl in
      let appl = PplDom.assign_expr appl [v, e] in

      let anrd = NonRel.remove_vars anrd [v] in
      
      { t with ppl = Mdom.add (Ppl 0) appl t.ppl;
               nrd = Mdom.add (Nrd 0) anrd t.nrd; }

    | _ -> assert false

  (* This assumes that we only use [Nrd 0] and [Ppl 0]. *)
  let set_unrel t v =
    match vdom v t.dom_st with
    | Nrd 0 -> t

    | Ppl 0 ->
      (* We change dynamically the packing only for local variables
         and offsets. *)
      assert (is_local_var v || is_offset v);
      assert (not (is_in_dom_nrd v (Nrd 0) t)); 
      let appl = Mdom.find (Ppl 0) t.ppl in

      (* The environment does not matter. *)
      let int = PplDom.bound_variable appl v in
      let e = Mtexpr.cst (Coeff.Interval int) in

      let anrd = Mdom.find (Nrd 0) t.nrd in
      let anrd = NonRel.assign_expr anrd [v,e] in

      let appl = PplDom.remove_vars appl [v] in

      { t with ppl = Mdom.add (Ppl 0) appl t.ppl;
               nrd = Mdom.add (Nrd 0) anrd t.nrd; }

    | _ -> assert false
      
  let expr_doms e dom_st =
    let rec aux acc = function
      | Mtexpr.Mcst _ -> acc
      | Mtexpr.Mvar v ->
        if List.mem (vdom v dom_st) acc then acc else (vdom v dom_st) :: acc
      | Mtexpr.Munop (_, e1, _, _) -> aux acc e1
      | Mtexpr.Mbinop (_, e1, e2, _, _) -> aux (aux acc e1) e2 in

    aux [] e

  (* Replace all variables not in domain d by an interval *)
  let proj_expr a d (e : Mtexpr.t) =
    let rec proj_mexpr (e : Mtexpr.t) = match expr_doms e a.dom_st with
      | [] -> e
      | [d'] ->
        if d = d' then e
        else
          let int = match d' with
            | Nrd _ -> NonRel.bound_texpr (Mdom.find d' a.nrd) e
            | Ppl _ -> PplDom.bound_texpr (Mdom.find d' a.ppl) e in
          Mtexpr.cst (Coeff.Interval int)

      | _ -> match e with
        | Mtexpr.Munop (op, e1, _, _) -> Mtexpr.unop op (proj_mexpr e1)
        | Mtexpr.Mbinop (op, e1, e2, _, _) ->
          Mtexpr.binop op (proj_mexpr e1) (proj_mexpr e2)
        | _ -> assert false in

    proj_mexpr e

  let proj_constr a d (c : Mtcons.t) =
    Mtcons.make (proj_expr a d (Mtcons.get_expr c)) (Mtcons.get_typ c)

  let split_doms l dom_st =
    let rec aux (ores,pres) = function
      | [] -> (ores, pres)
      | v :: tail ->
        let res' = match vdom v dom_st with
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
    let (ores,pres) = split_doms l VDW.dom_st_init in
    let a = { nrd = Mdom.empty; ppl = Mdom.empty; dom_st = VDW.dom_st_init; } in

    let a = List.fold_left (fun a (d,lvs) ->
        (* let dom_st = List.fold_left (fun dom_st lv ->
         *     Mm.add lv d dom_st) a.dom_st lvs in *)
        { a with nrd = Mdom.add d (NonRel.make lvs) a.nrd; })
        a ores in

    List.fold_left (fun a (d,lvs) ->
        (* let dom_st = List.fold_left (fun dom_st lv ->
         *     Mm.add lv d dom_st) a.dom_st lvs in *)
        { a with ppl = Mdom.add d (PplDom.make lvs) a.ppl; })
      a pres

  let un_app fnrd fppl a =
    { nrd = Mdom.mapi fnrd a.nrd;
      ppl = Mdom.mapi fppl a.ppl;
      dom_st = a.dom_st; }

  (* Repack [a] according to the domain state [dom_st]. *)
  let repack a dom_st =
    let a = VDW.fold_dom_st (fun v d a -> match d with
        | Ppl 0 -> set_rel a v
        | Nrd 0 -> set_unrel a v
        | _ -> assert false
      ) dom_st a in
    { a with dom_st = dom_st }

  let dom_st_update t vs info =
    let dom_st = VDW.dom_st_update t.dom_st vs info in
    repack t dom_st

  (* Unify two abstract values with maybe different domain states. *)
  let unify_dom_st a a' =
    let dom_st = VDW.merge_dom a.dom_st a'.dom_st in
    repack a dom_st, repack a' dom_st

  (* Unify a list of abstract values with maybe different domain states. *)
  let unify_dom_sts = function
    | [] -> raise (Aint_error "unify_dom_sts of an empty list")
    | (a :: l) as alist ->
      let dom_st = List.fold_left (fun dom_st x ->
          VDW.merge_dom dom_st x.dom_st) a.dom_st l in
      List.map (fun x -> repack x dom_st) alist    
    
  let bin_app fnrd fppl a a' =
    let a, a' = unify_dom_st a a' in   
    let f_opt f k u v = match u,v with
      | None, _ | _, None ->
        let s = Printf.sprintf
            "bin_app: Domain %s does not exist" (string_of_dom k) in
        raise (Aint_error s)
      | Some x, Some y -> Some (f x y) in

    { nrd = Mdom.merge (f_opt fnrd) a.nrd a'.nrd;
      ppl = Mdom.merge (f_opt fppl) a.ppl a'.ppl;
      dom_st = a.dom_st; }

  let list_app fnrd fppl (l : t list) =
    let l = unify_dom_sts l in
    match l with
    | [] -> raise (Aint_error "list_app of an empty list");
    | a :: _ ->

      { nrd = Mdom.mapi (fun k _ ->
            let els = List.map (fun x -> Mdom.find k x.nrd) l in
            fnrd els) a.nrd;
        ppl = Mdom.mapi (fun k _ ->
            let els = List.map (fun x -> Mdom.find k x.ppl) l in
            fppl els) a.ppl;
        dom_st = a.dom_st; }

  let meet = bin_app NonRel.meet PplDom.meet

  let meet_list = list_app NonRel.meet_list PplDom.meet_list

  let join = bin_app NonRel.join PplDom.join

  let join_list = list_app NonRel.join_list PplDom.join_list

  let widening oc a a' =
    let fp d = Option.map (proj_constr a' d) oc in
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
    assert ((Mdom.cardinal a.nrd) + (Mdom.cardinal a.ppl) <> 0);
    (Mdom.exists (fun _ t -> NonRel.is_bottom t) a.nrd)
    || (Mdom.exists (fun _ t -> PplDom.is_bottom t) a.ppl)

  let bottom a =
    let f1 _ x = NonRel.bottom x
    and f2 _ x = PplDom.bottom x in
    un_app f1 f2 a

  let top a =
    let f1 _ x = NonRel.top x
    and f2 _ x = PplDom.top x in
    un_app f1 f2 a

  let expand a v v_list =
    let f1 d x = if vdom v a.dom_st = d then NonRel.expand x v v_list else x
    and f2 d x = if vdom v a.dom_st = d then PplDom.expand x v v_list else x in
    un_app f1 f2 a

  let fold a v_list = match v_list with
    | [] -> raise (Aint_error "fold of an empty list")
    | v :: _ ->
      let f1 d x = if vdom v a.dom_st = d then NonRel.fold x v_list else x
      and f2 d x = if vdom v a.dom_st = d then PplDom.fold x v_list else x in
      un_app f1 f2 a

  let bound_variable a v =
    let d = vdom v a.dom_st in 
    match d with
    | Nrd _ -> NonRel.bound_variable (Mdom.find d a.nrd) v
    | Ppl _ -> PplDom.bound_variable (Mdom.find d a.ppl) v


  (* This works only if there is only one Ppl domain (Ppl 0). *)
  let bound_texpr a (e : Mtexpr.t) =
    let p_e = proj_expr a (Ppl 0) e in
    PplDom.bound_texpr (Mdom.find (Ppl 0) a.ppl) p_e

  (* If force is true then we do a forced strong update on v. *)
  let assign_expr ?force:(force=false) a (ves : (mvar * Mtexpr.t) list) =
    (* We split the assignments according to the domain. *)
    let part = List.fold_left (fun part (v,e) ->
        let d = vdom v a.dom_st in
        let p_e = proj_expr a d e in
        let class_d = Mdom.find_default [] d part in
        Mdom.add d ((v,p_e) :: class_d) part
      ) Mdom.empty ves in

    Mdom.fold (fun d ves a -> match d with
        | Nrd _ ->
          let d_a = Mdom.find d a.nrd in
          let d_a = NonRel.assign_expr ~force:force d_a ves in
          { a with nrd = Mdom.add d d_a a.nrd }

        | Ppl _ ->
          let d_a = Mdom.find d a.ppl in
          let d_a = PplDom.assign_expr ~force:force d_a ves in
          { a with ppl = Mdom.add d d_a a.ppl }
      ) part a

  let meet_constr_list a cs =
    let f1 d x = NonRel.meet_constr_list x (List.map (proj_constr a d) cs)
    and f2 d x = PplDom.meet_constr_list x (List.map (proj_constr a d) cs) in
    un_app f1 f2 a

  let meet_constr a c =
    let f1 d x = NonRel.meet_constr x (proj_constr a d c)
    and f2 d x = PplDom.meet_constr x (proj_constr a d c) in
    un_app f1 f2 a

  let sat_constr a c =
    (Mdom.for_all (fun d t -> NonRel.sat_constr t (proj_constr a d c)) a.nrd)
    &&
    (Mdom.for_all (fun d t -> PplDom.sat_constr t (proj_constr a d c)) a.ppl)
    
  let unify = bin_app NonRel.unify PplDom.unify

  let print : ?full:bool -> Format.formatter -> t -> unit =
    fun ?full:(full=false) fmt a ->
      let pp_map pp_el fmt l =
        pp_list pp_el fmt (List.map snd (Mdom.bindings l)) in
      
      if Mdom.cardinal a.nrd = 0 || !only_rel_print then
        Format.fprintf fmt "@[<v 0>* Rel:@;%a@]"
          (pp_map (PplDom.print ~full:full)) a.ppl
      else
        let nrd_size = Mdom.fold (fun _ nrd size ->
            size + Environment.size (NonRel.get_env nrd)
          ) a.nrd 0 in
        let ppl_size = Mdom.fold (fun _ nrd size ->
            size + Environment.size (PplDom.get_env nrd)
          ) a.ppl 0 in

        Format.fprintf fmt "@[<v 0>\
                            * NonRel (%d vars.):@;%a\
                            * Rel (%d vars.):@;%a@]"
          nrd_size
          (pp_map (NonRel.print ~full:full)) a.nrd
          ppl_size
          (pp_map (PplDom.print ~full:full)) a.ppl

  let change_environment a mvars =
    let (ores,pres) = split_doms mvars a.dom_st in

    let f1 d x = NonRel.change_environment x (List.assoc d ores)
    and f2 d x = PplDom.change_environment x (List.assoc d pres) in
    un_app f1 f2 a

  let remove_vars a mvars =
    let (ores,pres) = split_doms mvars a.dom_st in

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

    env_of_list l


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

  (* This is messy because we have to use the log to inverse avar_of_mvar. *)
  let of_box (box : Box.t Abstract1.t) shape =
    let vars = Environment.vars (Abstract1.env box)
               |> fst
               |> Array.to_list in
    let bman = Box.manager_alloc () in

    let denv dom =
      let dvars = List.filter (fun v ->
          let mv = mvar_of_avar v in
          vdom mv shape.dom_st = dom) vars in
      env_of_list dvars
    in

    (* let denv dom =
     *   let dvars = Hashtbl.find_all log dom
     *               |> List.filter (fun x -> List.mem x vars)
     *               |> List.map Var.of_string
     *   env_of_list dvars *)

    let res = List.fold_left (fun a dom ->
        let penv = denv dom in
        let av = Abstract1.change_environment bman box penv false
                 |> NonRel.of_box in
        { a with nrd = Mdom.add dom av a.nrd }
      ) (make []) nrddoms in

    let res = List.fold_left (fun a dom ->
        let penv = denv dom in
        let av = Abstract1.change_environment bman box penv false
                 |> PplDom.of_box in
        { a with ppl = Mdom.add dom av a.ppl }
      ) res ppldoms in

    { res with dom_st = shape.dom_st }

end


(*---------------------------------------------------------------*)
(* Statique Packing *)
module PIMake (PW : ProgWrap) : VDomWrap = struct 
  (* We do not use the state in this heuristic *)
  let dom_st_init = Mm.empty
  let dom_st_update dom_st _ _ = dom_st
  let merge_dom dom_st _ = dom_st
  let fold_dom_st _ _ a = a
    
  (* We compute the dependency heuristic graph *)
  let pa_res = Pa.pa_make PW.main (Some PW.prog)

  (* We compute the reflexive and transitive closure of dp *)
  let dp = trans_closure pa_res.pa_dp

  (* We are relational on a variable v iff:
     - there is a direct flow from the intersection of PW.main.f_args and
     Glob_options.relational to v.
     - the variable appears in a while loops conditions,
     or is modified by a while loop condition variable. *)
  let sv_ini =
    match PW.param.relationals with
    | None -> PW.main.f_args |> Sv.of_list
    | Some v_rel ->
      List.filter (fun v -> List.mem v.v_name v_rel) PW.main.f_args
      |> Sv.of_list

  let v_rel : Sv.t =
    let v_rel = flow_to dp sv_ini in
    let v_while = flow_to dp pa_res.while_vars in
    (* let v_while = pa_res.while_vars in *)
    Sv.union v_rel v_while

  (* v is a pointer variable iff there is a direct flow from the intersection
     of PW.main.f_args and Glob_options.pointers to v. *)
  let pt_ini =
    match PW.param.pointers with
    | None -> PW.main.f_args |> Sv.of_list
    | Some v_pt ->
      List.filter (fun v -> List.mem v.v_name v_pt) PW.main.f_args
      |> Sv.of_list

  let v_pt : Sv.t = flow_to dp pt_ini

  let pp_rel_vars fmt rel =
    (pp_list (Printer.pp_var ~debug:false)) fmt
      (List.sort (fun v v' -> Stdlib.compare v.v_name v'.v_name)
         (Sv.elements rel))

  let () = debug(fun () ->
      Format.eprintf "@[<v 0>@[<hov 2>%d relational variables:@ @,%a@]@;\
                      @[<hov 2>%d pointers:@ @,%a@]@]@."
        (Sv.cardinal v_rel)
        pp_rel_vars v_rel
        (Sv.cardinal v_pt)
        pp_rel_vars v_pt)

  (* Arrays and array elements must always be non-relational. 
     We do not use the state in this heuristic *)
  let vdom v _ = match v with
    | Temp _ | WTemp _ -> assert false

    | MNumInv _ -> Ppl 0        (* Numerical invariant must be relational *)

    | Mlocal (Avar v) | MinLocal v ->
      if Sv.mem v v_rel then Ppl 0 else Nrd 0

    | MvarOffset v
    | MmemRange (MemLoc v) ->
      if Sv.mem v v_pt then Ppl 0 else Nrd 0

    | Mglobal _
    | Mlocal (AarraySlice _)
    | Mlocal (Aarray _) -> Nrd 0
end

(* Dynamic Packing *)
module PIDynMake (PW : ProgWrap) : VDomWrap = struct
  let merge_dom dom_st dom_st' =
    Mm.merge (fun v d1 d2 -> match d1, d2 with
        | Some d, None | None, Some d -> Some d

        | Some (Nrd 0), Some (Ppl 0)
        | Some (Ppl 0), Some (Nrd 0) ->
          debug (fun () -> Format.eprintf "Dynamic partitioning: \
                                           lowered %a's precision@."
                    pp_mvar v);         
          (* We change dynamically the packing only for local variables 
             and offsets. *)
          assert (is_local_var v || is_offset v);
          (* We default to the less precise abstraction. *)
          Some (Nrd 0)

        | Some d1, Some d2 when d1 = d2 -> Some d1
        | _, _ -> assert false) dom_st dom_st'

  let fold_dom_st = Mm.fold
                      
  (* We compute the dependency heuristic graph on the SSA transform of main.
     Precondition: [PW.main] must not contain function calls, and variables 
     must be uniquely characterized by their names. *)
  let ssa_main, pa_res =
    (* FIXME: code duplication! dirty hack *)
    let asmOp = Arch_extra.asm_opI X86_arch_full.X86_core.asm_e in
    FSPa.fs_pa_make X86_decl.x86_decl.reg_size asmOp PW.main

  (* We compute the reflexive and transitive clojure of dp *)
  let dp = trans_closure pa_res.pa_dp

  (* We are relational on a SSA variable [v] iff:
     - there is a direct flow from the intersection of [ssa_main.f_args] and
     [Glob_options.relational] to [v].
     - the variable appears in a while loops conditions,
     or is modified by a while loop condition variable. *)
  let ssa_sv_ini =
    match PW.param.relationals with
    | None -> ssa_main.f_args |> Sv.of_list
    | Some v_rel ->
      List.filter (fun v -> List.mem v.v_name v_rel) ssa_main.f_args
      |> Sv.of_list

  let sv_ini =
    match PW.param.relationals with
    | None -> PW.main.f_args |> Sv.of_list
    | Some v_rel ->
      List.filter (fun v -> List.mem v.v_name v_rel) PW.main.f_args
      |> Sv.of_list

  let ssa_v_rel : Sv.t =
    let v_rel = flow_to dp ssa_sv_ini in
    let v_while = flow_to dp pa_res.while_vars in
    (* let v_while = pa_res.while_vars in *)
    Sv.union v_rel v_while

  
  (* [v] is a SSA pointer variable iff there is a direct flow from the intersection
     of [PW.main.f_args] and [Glob_options.pointers] to [v]. *)
  let ssa_pt_ini =
    match PW.param.pointers with
    | None -> ssa_main.f_args |> Sv.of_list
    | Some v_pt ->
      List.filter (fun v -> List.mem v.v_name v_pt) ssa_main.f_args
      |> Sv.of_list

  let pt_ini =
    match PW.param.pointers with
    | None -> PW.main.f_args |> Sv.of_list
    | Some v_pt ->
      List.filter (fun v -> List.mem v.v_name v_pt) PW.main.f_args
      |> Sv.of_list

  let ssa_v_pt : Sv.t = flow_to dp ssa_pt_ini
      
  let dom_st_init = List.fold_left2 (fun dom_st v ssa_v ->
      (* Value entry *)
      let dom_st = if Sv.mem ssa_v ssa_v_rel then
          let mv = Mlocal (Avar v) in
          Mm.add mv (Ppl 0) dom_st
        else
          let mv = Mlocal (Avar v) in
          Mm.add mv (Nrd 0) dom_st
      in
      (* Pointer (offset) entry *)
      if Sv.mem ssa_v ssa_v_pt then
          let mv = MvarOffset v in
          Mm.add mv (Ppl 0) dom_st
        else
          let mv = MvarOffset v in
          Mm.add mv (Nrd 0) dom_st
    ) Mm.empty PW.main.f_args ssa_main.f_args    

  (* We build a mapping from locations (where assignments take place) to
     pairs of [v,dom] where [v] is the left value, and [dom] states
     whether [v] must be handled precisely or not. *)
  let build_map_lv info lmap lv ssa_lv =
    match lv, ssa_lv with
    | _, Lnone _ | _, Lmem _ | _, Laset _ -> lmap
    | Lvar v, Lvar ssa_v ->
      let v, ssa_v = L.unloc v, L.unloc ssa_v in
      assert (v.v_name = ssa_v.v_name);
      (* We raise the value of [v] if needed *)
      let mv = Mlocal (Avar v) in
      let rel =
        if Sv.mem ssa_v ssa_v_rel then [mv, Ppl 0] else [mv, Nrd 0]  in

      (* We raise the offset of [v] if needed *)
      let mv_pt = MvarOffset v in
      let pt =
        if Sv.mem ssa_v ssa_v_pt then [mv_pt, Ppl 0] else [mv_pt, Nrd 0] in

      Mint.add info.i_instr_number (rel @ pt) lmap

    | _ -> assert false

  let rec build_lmap_i lmap i ssa_i = match i.i_desc, ssa_i.i_desc with
    | Copn (lvs,_,_,_), Copn (ssa_lvs,_,_,_) ->
      List.fold_left2 (build_map_lv i.i_info) lmap lvs ssa_lvs
        
    | Cassgn (lv,_,_,_), Cassgn (ssa_lv,_,_,_) ->
      build_map_lv i.i_info lmap lv ssa_lv

    | Cwhile (_, is1, _, is2), Cwhile (_, ssa_is1, _, ssa_is2)         
    | Cif (_, is1, is2), Cif (_, ssa_is1, ssa_is2) ->
      let lmap = build_lmap lmap is1 ssa_is1 in
      build_lmap lmap is2 ssa_is2

    | Cfor (_, _, is), Cif (_, _, ssa_is) ->
      build_lmap lmap is ssa_is

    | Ccall _, _ | _, Ccall _ -> assert false
      
    | _, _ -> lmap

  and build_lmap lmap is ssa_is = match is, ssa_is with
    | _, { i_desc = Cassgn (_,AT_phinode,_,_) } :: ssa_is ->
      build_lmap lmap is ssa_is
    | i :: is, ssa_i :: ssa_is ->
      let lmap = build_lmap_i lmap i ssa_i in
      build_lmap lmap is ssa_is
    | [], [] -> lmap
    | _ -> assert false

  let lmap = build_lmap Mint.empty PW.main.f_body ssa_main.f_body


  let print_update v dom dom_st =    
    debug (fun () -> match Mm.find v dom_st with 
        | exception Not_found ->
          Format.eprintf "Dynamic partitioning: set %a to %a@;"
            pp_mvar v pp_dom dom                 
        | old_dom ->
          if old_dom <> dom then
            Format.eprintf "Dynamic partitioning: change %a from %a to %a@;"
              pp_mvar v
              pp_dom old_dom
              pp_dom dom)

  let dom_st_update_one dom_st v info =
    try
      match v with
      | MvarOffset _ | Mlocal (Avar _) ->
        let entries = Mint.find info.i_instr_number lmap in
        begin
          try
            let dom = List.assoc v entries in
            let () = print_update v dom dom_st in          
            Mm.add v dom dom_st
          with Not_found -> dom_st
        end
      | _ -> dom_st
    with Not_found -> dom_st

  let dom_st_update dom_st vs info =
    List.fold_left (fun dom_st v ->
        dom_st_update_one dom_st v info
      ) dom_st vs
    
  (* Arrays and array elements must always be non-relational. 
     We do not use the state in this heuristic *)
  let vdom (v : mvar) (dom_st : dom_st) = match v with
    | Temp _ | WTemp _ -> assert false

    | MNumInv _ -> Ppl 0        (* Numerical invariant must be relational *)

    | MvarOffset _
    | Mlocal (Avar _) ->
      begin
        try Mm.find v dom_st
        with Not_found -> Nrd 0
      end

    | MinLocal v ->
      if Sv.mem v sv_ini then Ppl 0 else Nrd 0
      
    | MmemRange (MemLoc v) ->
      if Sv.mem v pt_ini then Ppl 0 else Nrd 0

    | Mglobal _
    | Mlocal (AarraySlice _)
    | Mlocal (Aarray _) -> Nrd 0

  let print_lmap fmt lmap =
    let pp_one fmt (v,d) =
      Format.fprintf fmt "set %a to %a"
        pp_mvar v
        pp_dom d in

    (* Ordering for printing. *)
    let my_compare (_,l) (_,l') =
      let nrd_l  = List.for_all (fun (_,d) -> d = Nrd 0) l
      and nrd_l' = List.for_all (fun (_,d) -> d = Nrd 0) l' in
      if nrd_l && not nrd_l' then -1
      else if not nrd_l && nrd_l' then 1
      else 0 in
    let bindings = List.sort my_compare (Mint.bindings lmap) in
    Format.fprintf fmt "@[<v 2>Dynamic packing table (%d entries):@;%a@]"
      (Mint.cardinal lmap)
      (pp_list
         (fun fmt (i_nb, l) ->
            Format.fprintf fmt "instr nb %d -> @[<v 0>%a@]"
              i_nb
              (pp_list pp_one) l))
      bindings

  let pp_rel_vars fmt rel =
    (pp_list (Printer.pp_var ~debug:true)) fmt
      (List.sort (fun v v' -> Stdlib.compare v.v_name v'.v_name)
         (Sv.elements rel))
  
  let () = debug(fun () ->
      Format.eprintf "@[<v 0>\
                      @[<hov 2>%d relational variables (initially):@ @,%a@]@;\
                      @[<hov 2>%d pointers (initially):@ @,%a@]@;\
                      %a@]@."
        (Sv.cardinal sv_ini)
        pp_rel_vars sv_ini
        (Sv.cardinal pt_ini)
        pp_rel_vars pt_ini
        print_lmap lmap)
end


(*------------------------------------------------------------*)
(* Reduced Product *)

module type RProdParam = sig
  module A : AbsDisjType
  module B : AbsDisjType
  val print : ?full:bool -> Format.formatter -> (A.t * B.t) -> unit
  val reduce : (A.t * B.t) -> (A.t * B.t)
end

(* Asymmetric reduced product.   
   Careful, to_box, of_box are only using the left abstract values. *)
module ReducedProd (P : RProdParam) : AbsDisjType = struct  
  module A = P.A
  module B = P.B

  type t = A.t * B.t
  
  let reduce = P.reduce
  
  let app  fa fb (a,b)           = reduce (fa a, fb b)
  let app2 fa fb (a1,b1) (a2,b2) = reduce (fa a1 a2, fb b1 b2)
  let appl fa fb l =
    let la, lb = List.split l in
    reduce (fa la, fb lb)
    
  let make vs = reduce (A.make vs, B.make vs)
    
  let meet      = app2 A.meet      B.meet
  let meet_list = appl A.meet_list B.meet_list  
  
  let join      = app2 A.join      B.join
  let join_list = appl A.join_list B.join_list

  let widening c = app2 (A.widening c) (B.widening c)
  
  let forget_list t l =
    app (fun x -> A.forget_list x l) (fun x -> B.forget_list x l) t

  let is_bottom (a,b) = (A.is_bottom a) || (B.is_bottom b)

  let is_included (a1,b1) (a2,b2) =
    if is_bottom (a2,b2)
    then is_bottom (a1,b1)
    else A.is_included a1 a2 && B.is_included b1 b2
      
  let bottom = app A.bottom B.bottom
  let top    = app A.top B.top
  
  let expand t v l = app (fun x -> A.expand x v l) (fun x -> B.expand x v l) t
      
  let fold t l = app (fun x -> A.fold x l) (fun x -> B.fold x l) t
      
  let bound_variable (a,b) v =
    let i1, i2 = A.bound_variable a v, B.bound_variable b v in
    interval_meet i1 i2
    
  let bound_texpr (a,b) e =
    let i1, i2 = A.bound_texpr a e, B.bound_texpr b e in
    interval_meet i1 i2
  
  let assign_expr ?force:(force=false) t ves =
    app (fun x -> A.assign_expr ~force:force x ves)
        (fun x -> B.assign_expr ~force:force x ves) t
      
  let meet_constr t c =
    app (fun x -> A.meet_constr x c)
        (fun x -> B.meet_constr x c) t
  
  let meet_constr_list t cs =
    app (fun x -> A.meet_constr_list x cs)
        (fun x -> B.meet_constr_list x cs) t

  let sat_constr (a,b) c = A.sat_constr a c || B.sat_constr b c
    
  let unify = app2 A.unify B.unify
  
  let change_environment t vs =
    app (fun x -> A.change_environment x vs)
        (fun x -> B.change_environment x vs) t
     
  let remove_vars t vs =
    app (fun x -> A.remove_vars x vs)
        (fun x -> B.remove_vars x vs) t

  let to_box (a,_) = A.to_box a

  (* We put a top value for the right element *)
  let of_box box (a,_) =
    (A.of_box box a, B.make [dummy_mvar])

  let get_env (a,b) = 
    Environment.lce (A.get_env a) (B.get_env b)
  
  let print = P.print

  let set_rel t v =
    app (fun x -> A.set_rel x v)
        (fun x -> B.set_rel x v) t
  
  let set_unrel t v =
    app (fun x -> A.set_unrel x v)
        (fun x -> B.set_unrel x v) t

  let dom_st_update t v minfo =
    app (fun x -> A.dom_st_update x v minfo)
        (fun x -> B.dom_st_update x v minfo) t

  let top_no_disj = app A.top_no_disj B.top_no_disj

  let to_shape = app2 A.to_shape B.to_shape 

  let remove_disj = app A.remove_disj B.remove_disj

  (* Adds a block of constraints for the disjunctive domain *)
  let new_cnstr_blck t l = 
    app (fun x -> A.new_cnstr_blck x l)
        (fun x -> B.new_cnstr_blck x l) t

  let add_cnstr (a,b) ~meet c l =
    let a1,a2 = A.add_cnstr a ~meet c l
    and b1,b2 = B.add_cnstr b ~meet c l in
    (a1,b1), (a2,b2)

  (* Pop the top-most block of constraints in the disjunctive domain *)
  let pop_cnstr_blck t l =
    app (fun x -> A.pop_cnstr_blck x l)
        (fun x -> B.pop_cnstr_blck x l) t

  let pop_all_blcks = app A.pop_all_blcks B.pop_all_blcks
end
