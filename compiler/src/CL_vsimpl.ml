open ToCL
open CoreIdent

module Counter = struct
  let cpt = ref 0
  let next () = incr cpt ; !cpt
  let get () = !cpt
end

module Cfg = struct

  type node =
    { mutable nkind : CL.Instr.instr;
      mutable succs : node list;
      mutable preds: node list;
      id: int
    }

  and program = node list

  let mk_node nkind =
    let preds = [] in
    let succs = [] in
    let id = Counter.next() in
    { nkind ; succs; preds; id }

  (** Compute CFG:
      Requires to first compute all nodes, by maintaining the order of the stmt
      in the list.
  *)

  let rec update_succ node succ =
    let addSucc n  =
      node.succs <- n :: node.succs;
      n.preds <- node :: n.preds
    in
    let addOptionSucc (n: node option) =
      match n with
      | None -> ()
      | Some n' -> addSucc n'
    in
    addOptionSucc succ

  let rec cfg_node nodes next =
    match nodes with
    | [] -> assert false
    | [h] -> update_succ h next
    | h :: q ->
      update_succ h (Some (List.hd q));
      cfg_node q next

  let compute_cfg program = cfg_node program None

  let cfg_of_prog prog =
    let cfg = List.map mk_node prog in
    compute_cfg cfg;
    List.hd cfg

  let cfg_of_prog_rev prog =
    let prog_rev = List.rev prog in
    let cfg = List.map mk_node prog_rev in
    compute_cfg cfg;
    List.hd cfg

  let prog_of_cfg cfg =
    let rec aux node acc =
      match node.succs with
      | [] -> node.nkind::acc
      | [h] -> aux h (node.nkind::acc)
      | _ -> assert false
    in
    aux cfg []

  let prog_of_cfg_rev cfg =
    let rec aux node acc =
      match node.succs with
      | [] -> node.nkind::acc
      | [h] -> aux h (node.nkind::acc)
      | _ -> assert false
    in
    let prog_rev = aux cfg [] in
    List.rev prog_rev

end

(* type vector = *)
(*   | U16x16 *)

(* let unfold_vector formals = *)
(*   let aux ((formal,ty) as v) = *)
(*     let mk_vector = Annot.filter_string_list None ["u16x16", U16x16] in *)
(*     match Annot.ensure_uniq1 "vect" mk_vector (formal.v_annot) with *)
(*     | None -> [v],[] *)
(*     | Some U16x16 -> *)
(*       let rec aux i acc = *)
(*         match i with *)
(*         | 0 -> acc *)
(*         | n -> *)
(*           let name = String.concat "_" [formal.v_name; "v" ; string_of_int i] in *)
(*           let v = O.I.mk_tmp_lval ~name u16 in *)
(*           aux ( n - 1) (v :: acc) *)
(*       in *)
(*       let v = aux 16 [] in *)
(*       let va = List.map (fun v -> CL.Instr.Avar v) v in *)
(*       let a = CL.Instr.Avatome va in *)
(*       let l = O.I.var_to_tyvar ~vector:(16,16) formal in *)
(*       v,[CL.Instr.Op1.mov l a] *)
(*   in *)
(*   List.fold_left (fun (acc1,acc2) v -> *)
(*       let fs,is = aux v in *)
(*       fs @ acc1,is @ acc2) *)
(*     ([],[]) formals *)

module SimplVector = struct
  open Cfg
  open CL.Instr

  let rec int_of_ty = function
    | CL.Uint n -> n
    | Sint n -> n
    | Bit -> assert false
    | Vector (i,t) -> i * int_of_ty t

  let int_of_tyvar (tyv: CL.tyvar) =
    let (_,ty) = tyv in
    int_of_ty ty

  let getNextI n' =
    match n'.preds with
    | h :: _ -> Some h
    | _ -> None

  let getPrevI n' =
      match n'.succs with
      | h :: _ -> Some h
      | _ -> None

  let rec is_unsigned (ty: CL.ty) =
    match ty with
    | Uint _ -> true
    | Sint _ -> false
    | Bit -> true
    | Vector (_, ty') -> is_unsigned ty'

  let rec is_equiv_type (ty: CL.ty) (ty': CL.ty) =
    match (ty, ty') with
    | (Uint i, Uint i') -> i == i'
    | (Uint i, Sint i') -> false
    | (Uint i, Bit) -> assert false
    | (Uint i, Vector (i', ty'')) ->
      i == (i' * int_of_ty ty'') && (is_unsigned ty'')
    | (Sint i, Bit) -> assert false
    | (Sint i, Vector (i', ty'')) ->
      i == (i' * int_of_ty ty'') && not(is_unsigned ty'')
    | (Bit, Vector (_, _)) -> assert false
    | Vector (i, ty''), Vector (i', ty''') ->
      (i * int_of_ty ty'' == i' * int_of_ty ty''') && ((is_unsigned ty'') == (is_unsigned ty'''))
    | _ -> is_equiv_type ty' ty (* use recursivity to check the commutative pair *)

  let rec find_vect_lval v n  =
      let (v, ty) = v in
      let aux v' n' =
        let nI = getPrevI n' in
        match nI with
        | Some i -> find_vect_lval v' i
        | None -> None
      in
    match n.nkind with
    | {iname = "cast"; iargs = [Lval (v', ty'); Atom (Avar (v'', ty''))]} ->
      if v == v' && is_equiv_type ty' ty'' then
        aux (v'',ty'') n
      else
        aux (v, ty) n
    | {iname = "mov"; iargs = [Lval (v', ty') ; Atom (Avecta ((v'', ty''), j))]} ->
      if v == v' && j == 0 && is_equiv_type ty' ty'' then (* do we care if j != 0 ? *)
        aux (v'',ty'') n
      else
        aux (v, ty) n
    | {iname = "mov"; iargs = [Lval (v', ty'); Atom (Avatome [Avar (v'', ty'')])]} ->
      if v == v' && is_equiv_type ty' ty'' then
        aux (v'', ty'') n
      else
        aux (v, ty) n
    | {iname = "adds"; iargs = [_; Lval (v', ty'); Atom (Avar (_, ty'')); Atom (Avar (_, ty'''))]} ->
      if v == v' && (is_equiv_type ty' ty'' || is_equiv_type ty' ty''') then
        Some (v', ty')
      else
        aux (v, ty) n
    | {iname = "add"; iargs = [Lval (v', ty');  Atom (Avar (_, ty'')); Atom (Avar (_, ty'''))]} ->
      if v == v' && (is_equiv_type ty' ty'' || is_equiv_type ty' ty''') then
        Some (v', ty')
      else
        aux (v, ty) n
    | {iname = "mull"; iargs = [Lval (vh', tyh'); Lval (vl', tyl'); Atom (Avar (_, ty'')); Atom (Avar (_, ty'''))]} ->
      if v == vl' &&  (is_equiv_type  tyl' ty'' || is_equiv_type tyl' ty''') then
        Some (vl', tyl')
      else if v == vh' &&  (is_equiv_type  tyh' ty'' || is_equiv_type tyh' ty''') then
        Some (vh', tyh')
      else
        aux (v, ty) n
    | {iname = "subb"; iargs = [_; Lval (v', ty'); Atom (Avar (_, ty'')); Atom (Avar (_, ty'''))]} ->
        if v == v' &&  (is_equiv_type  ty' ty'' || is_equiv_type ty' ty''') then
          Some (v', ty')
        else
          aux (v, ty) n
    | _ -> aux (v, ty) n (* Keep searching *)

    let sr_lval node pred = (* Search for the source of the argument in lval of another instruction *)
      let rec update_arg args v i =
        begin
          match args with
          | [] -> assert false
          | h::q ->
            if i == 0 then v::q
            else h::(update_arg q v (i-1))
        end
      in
      let replace_arg v' i =
        let arg' = (Atom (Avar v')) in
        let iargs' = update_arg node.nkind.iargs arg' i in
        node.nkind <- { iname = node.nkind.iname; iargs = iargs' }
      in
      let aux v idx =
        let l = find_vect_lval v pred in
          begin
            match l with
            | Some v' -> replace_arg v' idx
            | None -> ()
          end
      in
      match node.nkind with
      | {iname = "adds"; iargs = [_; _; Atom (Avar (v, Vector (i, ty))); Atom (Avar (v', Vector (i', ty')))]} -> 
        aux (v, Vector (i, ty)) 2;
        aux (v', Vector (i', ty')) 3;
      | {iname = "mull"; iargs = [_; _; Atom (Avar (v, Vector (i, ty))); Atom (Avar (v', Vector (i', ty')))]} -> 
        aux (v, Vector (i, ty)) 2;
        aux (v', Vector (i', ty')) 3;
      | {iname = "subb"; iargs = [_; _; Atom (Avar (v, Vector (i, ty))); Atom (Avar (v', Vector (i', ty')))]} -> 
        aux (v, Vector (i, ty)) 2;
        aux (v', Vector (i', ty')) 3;
      | _ -> ()

    let rec sr_lvals node =
      match node.succs with
      | [] -> ()
      | h::_ ->
        sr_lval node h;
        sr_lvals h

  let rec unused_lval v nI = (* Checks if lval is used in any subsequent instruction *)
    let rec var_in_vatome v' l =
      match l with
        | h :: t ->
          begin
            match h with
            | Avar v' -> (v' == v) || (var_in_vatome v t)
            | Avecta (v', _) -> (v' == v) || (var_in_vatome v t)
            | Avatome l' -> (var_in_vatome v t) || (var_in_vatome v l')  (* is this valid CL? should we assert false ?? *)
            | _ -> (var_in_vatome v t)
          end
        | [] -> false
    in
    let aux v' n' =
      let i = getNextI n' in
      unused_lval v' i
    in
    match nI with
    | None -> true
    | Some n ->
      begin
        match n.nkind with
        | {iname = "mov"; iargs = [_; Atom (Avar v')]} -> (v' != v) && (aux v n)
        | {iname = "mov"; iargs = [_; Atom (Avecta (v', _))]} -> (v' != v) && (aux v n)
        | {iname = "mov"; iargs = [_; Atom (Aconst _)]} -> aux v n
        | {iname = "mov"; iargs = [_; Atom (Avatome l)]} -> not(var_in_vatome v l) && (aux v n)
        | {iname = "cast"; iargs = [_; Atom (Avar v')]} -> (v' != v) && (aux v n)
        | {iname = "cast"; iargs = [_; Atom (Avecta (v', _))]} -> (v' != v) && (aux v n)
        | {iname = "cast"; iargs = [_; Atom (Aconst _)]} -> aux v n
        | {iname = "cast"; iargs = [_; Atom (Avatome l)]} -> not(var_in_vatome v l) && (aux v n)
        | {iname = "adds"; iargs = [_; _; Atom (Avar v'); Atom (Avar v'')]} -> (v' != v) && (v'' != v) && (aux v n)
        | {iname = "adds"; iargs = [_; _; Atom (Avecta (v', _)); Atom (Avecta (v'', _))]} -> (v' != v) && (v'' != v) && (aux v n)
        | {iname = "add"; iargs = [_; Atom (Avar v'); Atom (Avar v'')]} -> (v' != v) && (v'' != v) && (aux v n)
        | {iname = "add"; iargs = [_; Atom (Avecta (v', _)); Atom (Avecta (v'', _))]} -> (v' != v) && (v'' != v) && (aux v n)
        | {iname = "subb"; iargs = [_; _; Atom (Avar v'); Atom (Avar v'')]} -> (v' != v) && (v'' != v) && (aux v n)
        | {iname = "subb"; iargs = [_; _; Atom (Avecta (v', _)); Atom (Avecta (v'', _))]} -> (v' != v) && (v'' != v) && (aux v n)
        | {iname = "sub"; iargs = [_; Atom (Avar v'); Atom (Avar v'')]} -> (v' != v) && (v'' != v) && (aux v n)
        | {iname = "sub"; iargs = [_; Atom (Avecta (v', _)); Atom (Avecta (v'', _))]} -> (v' != v) && (v'' != v) && (aux v n)
        | {iname = "mull"; iargs = [_; _; Atom (Avar v'); Atom (Avar v'')]} -> (v' != v) && (v'' != v) && (aux v n)
        | {iname = "mull"; iargs = [_; _; Atom (Avecta (v', _)); Atom (Avecta (v'', _))]} -> (v' != v) && (v'' != v) && (aux v n)
        | _ -> aux v n
      end

  let rec nop_uinst cfg node =
    let nI = getNextI node in
    match node.nkind with
      | {iname = "cast"; iargs = [Lval v; _]}  ->
        if unused_lval v nI then
          node.nkind <- { iname = "nop"; iargs = [] }
        else ()
      | {iname = "mov"; iargs = [Lval v; _]}  ->
        if unused_lval v nI then
          node.nkind <- { iname = "nop"; iargs = [] }
        else ()
      | _ -> ()

  let rec nop_uinsts cfg node =
    nop_uinst cfg node;
    let nI = getPrevI node in
    match nI with
    | None -> ()
    | Some i -> nop_uinsts cfg i

  let rec remove_nops l =
    match l with
    | [] -> []
    | h::t ->
      begin
      match h with
      | { iname = "nop" } -> remove_nops t
      | _ -> h :: remove_nops t
      end

  let rec simpl_cfg cfg =
    sr_lvals cfg;
    let nI = getPrevI cfg in
    match nI with
    | None -> cfg
    | Some i ->
      begin
        nop_uinsts cfg i;
        let cfg' = cfg_of_prog (remove_nops (prog_of_cfg_rev cfg)) in
        cfg'
      end
end
