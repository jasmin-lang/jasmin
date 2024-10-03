open ToCL
open CoreIdent

(*
TODO:
1: load constants into vector registers: we should unpack instead of loading full value
2: shuffle functions don't have an effect?
*)

module Counter = struct
  let cpt = ref 0
  let next () = incr cpt ; !cpt
  let get () = !cpt
end

let rec is_eq_type (ty: CL.ty) (ty': CL.ty) =
  match (ty, ty') with
  | (Uint i, Uint i') -> i == i'
  | (Uint i, Sint i') -> false
  | (Uint i, Bit) -> false
  | (Uint i, Vector (i', ty'')) -> false
  | (Sint i, Sint i') -> i == i'
  | (Sint i, Bit) -> false
  | (Sint i, Vector (i', ty'')) -> false
  | (Bit, Bit) -> true
  | (Bit, Vector (_, _)) -> false
  | Vector (i, ty''), Vector (i', ty''') -> i == i' && (is_eq_type ty'' ty''')
  | _ -> is_eq_type ty' ty (* use recursivity to check the commutative pair *)

let rec is_eq_tyvar (tv: CL.tyvar) (tv': CL.tyvar) =
  let (v, ty) = tv in
  let (v', ty') = tv' in
  (v == v') && (is_eq_type ty ty')

let rec is_unsigned (ty: CL.ty) =
  match ty with
  | Uint _ -> true
  | Sint _ -> false
  | Bit -> true
  | Vector (_, ty') -> is_unsigned ty'

let lt_to_tl l = List.fold_right (fun (x, y) (l1, l2) -> (x :: l1, y @ l2)) l ([], [])

let rec remove_dups l =
  match l with
  | [] -> []
| h :: t ->
  if List.mem h t then remove_dups t
  else h :: (remove_dups t)

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

module GhostVector = struct
  open CL.Instr
  open CL.R
  open CL.I

  module S = struct
    let s = false (* TODO: is it always unsigned?*)
    let error = "unsigned x86"
  end

  module I = I (S)

  type param =
    | In
    | Out

  type vector =
    | U16x16

  let get_vghost ghosts gname =
    let vghost = List.find (fun (v, _) -> v.v_name = gname) ghosts in
    vghost

  let get_unfolded_vector_namei v i =
    String.concat "_" [v.v_name; (string_of_uid v.v_id); "v" ; string_of_int i]

  let rec replace_vghosts_rexp ghosts r =
    let aux (v, ty) i =
      let name = get_unfolded_vector_namei v i in
      let v' = get_vghost ghosts name in
      (Rvar v', [(v,ty)])
    in
    match r with
    | Rvar x -> (r, [])
    | Rconst (c1, c2) -> (r, [])
    | Ruext (e, c) ->
      let e',l = replace_vghosts_rexp ghosts e in
      (Ruext (e', c), l)
    | Rsext (e, c) ->
      let e',l = replace_vghosts_rexp ghosts e in
      (Rsext(e', c), l)
    | Runop(s, e) ->
      let e',l = replace_vghosts_rexp ghosts e in
      (Runop(s, e'), l)
    | Rbinop(e1, s, e2) ->
      let e1',l1 = replace_vghosts_rexp ghosts e1 in
      let e2',l2 = replace_vghosts_rexp ghosts e2 in
      let l = l1 @ l2 in
      (Rbinop(e1', s, e2'), l)
    | RVget(e,c) -> (r, [])
    | UnPack (e,us,i) ->
      aux e i
    | Rlimbs (c, e) ->
      let e',l = List.fold_right (fun (x,y) (l1,l2) -> (x::l1, y @ l2)) (List.map (replace_vghosts_rexp ghosts) e) ([], []) in
      (Rlimbs (c, e'), l)

  let rec unfold_ghosts_rpred ghosts pre =
    match pre with
    | RPcmp(e1, s, e2) ->
      let e1', l1 = replace_vghosts_rexp ghosts e1 in
      let e2', l2 = replace_vghosts_rexp ghosts e2 in
      let l = l1 @ l2 in
      RPcmp(e1', s, e2'), l
    | RPnot e ->
      let e', l = unfold_ghosts_rpred ghosts e in
      RPnot e', l
    | RPand rps ->
      let rps', l = lt_to_tl (List.map (unfold_ghosts_rpred ghosts) rps) in
      RPand rps', l
    | RPor  rps ->
      let rps', l = lt_to_tl (List.map (unfold_ghosts_rpred ghosts) rps) in
      RPor rps', l
    | RPeqsmod (e1,e2,e3) ->
      let e1', l1 = replace_vghosts_rexp ghosts e1 in
      let e2', l2 = replace_vghosts_rexp ghosts e2 in
      let e3', l3 = replace_vghosts_rexp ghosts e3 in
      let l = l1 @ l2 @ l3 in
      RPeqsmod(e1',e2',e3'), l

  let unfold_vghosts_rpred ghosts pre =
    lt_to_tl (List.map (unfold_ghosts_rpred ghosts) pre)

  let rec replace_vghosts_eexp ghosts e =
    let aux (v, ty) i =
      let name = get_unfolded_vector_namei v i in
      let v' = get_vghost ghosts name in
      (Ivar v', [(v, ty)])
    in
    match e with
    | Iconst c -> e, []
    | Ivar v -> e, []
    | Iunop (s, e) ->
      let e', l = replace_vghosts_eexp ghosts e in
      Iunop (s, e'), l
    | Ibinop (e1, s, e2) ->
      let e1', l1 = replace_vghosts_eexp ghosts e1 in
      let e2', l2 = replace_vghosts_eexp ghosts e2 in
      let l = l1 @ l2 in
      Ibinop (e1', s, e2'), l
    | Ilimbs (c, l) ->
      let l', ll = lt_to_tl (List.map (replace_vghosts_eexp ghosts) l) in
      Ilimbs (c, l'), ll
    | IUnPack (e, us, i) ->
      aux e i

  let rec unfold_ghosts_epred ghosts pre =
    match pre with
    | Eeq(e1, e2) ->
      let e1', l1 = replace_vghosts_eexp ghosts e1 in
      let e2', l2 = replace_vghosts_eexp ghosts e2 in
      let l = l1 @ l2 in
      Eeq(e1', e2'), l
    | Eeqmod(e1, e2, es) ->
      let e1', l1 = replace_vghosts_eexp ghosts e1 in
      let e2', l2 = replace_vghosts_eexp ghosts e2 in
      let es', l3 = lt_to_tl (List.map (replace_vghosts_eexp ghosts) es) in
      let l = l1 @ l2 @ l3 in
      Eeqmod(e1', e2', es'), l

  let unfold_vghosts_epred ghosts pre =
     lt_to_tl (List.map (unfold_ghosts_epred ghosts) pre )

  let move_to_vghost vl tv =
    let (v, ty) = tv in
    let s = not (is_unsigned ty) in
    let (l_16x16, lty_16x16) as l16x16 = I.var_to_tyvar ~sign:s ~vector:(16,16) v in
    let ll16x16 = Llvar l16x16 in
    let vl16x16 = Avar l16x16 in
    let lvl = Lvatome (List.map (fun tv' -> Llvar tv') vl) in
    let a_1x256 = Avatome [Avar tv] in
    [cast lty_16x16 ll16x16 a_1x256; Op1.mov lvl vl16x16]

  let move_from_vghost vl tv =
    let (v, ty) = tv in
    let s = not (is_unsigned ty) in
    let (l_16x16, lty_16x16) as l16x16 = I.var_to_tyvar ~sign:s ~vector:(16,16) v in
    let ll16x16 = Llvar l16x16 in
    let vl16x16 = Avar l16x16 in
    let va_16x16 = List.map (fun tv' -> Avar tv') vl in
    let a_16x16 = Avatome va_16x16 in
    let (l_1x256, lty_1x256) as l1x256 = I.var_to_tyvar ~sign:s ~vector:(1,256) v in
    let l1x256v = Llvar l1x256 in
    let l_0 = Avecta (l1x256, 0) in
    [Op1.mov ll16x16 a_16x16; cast lty_1x256 l1x256v vl16x16; Op1.mov (Llvar tv) l_0]

  let unfold_vectors formals ret_vars =
    let formals' = remove_dups formals in
    let aux ((v,ty) as tv) =
      let mk_vector = Annot.filter_string_list None ["u16x16", U16x16] in
      match Annot.ensure_uniq1 "vect" mk_vector (v.v_annot) with
      | None -> [tv],[],[]
      | Some U16x16 ->
        let rec unfold_vector i acc s =
          match i with
          | 0 -> acc
          | n ->
            let name = get_unfolded_vector_namei v (i-1) in
            let tv' = I.mk_tmp_lval ~name ~sign:s u16 in
            let ltv' = I.get_lval tv' in
            unfold_vector (n - 1) (ltv' :: acc) s
        in
        let s = not(is_unsigned ty) in
        let vl = unfold_vector 16 [] s in
        if List.exists (is_eq_tyvar tv) ret_vars then
          let il = move_to_vghost vl tv in
          vl,[], il
        else
          let il = move_from_vghost vl tv in
          vl,il,[]
    in
    List.fold_left (fun (acc1,acc2,acc3) tv ->
        let fs,ispre,ispost = aux tv in
        fs @ acc1, ispre @ acc2, ispost @ acc3)
      ([],[],[]) formals'

    let inject_vector_ghosts formals vghost =
      let (v, ty) = vghost in
      let rec build_tyvar_list i acc =
        match i with
        | 0 -> acc
        | n ->
          let name = get_unfolded_vector_namei v (i-1) in
          let v' = get_vghost formals name in
          build_tyvar_list (n - 1) (v' :: acc)
        in
      let vl = build_tyvar_list 16 [] in
      move_to_vghost vl vghost

    let extract_vector_ghosts formals vghost =
      let (v, ty) = vghost in
      let rec build_tyvar_list i acc =
        match i with
        | 0 -> acc
        | n ->
          let name = get_unfolded_vector_namei v (i-1) in
          let v' = get_vghost formals name in
          build_tyvar_list (n - 1) (v' :: acc)
        in
      let vl = build_tyvar_list 16 [] in
      move_from_vghost vl vghost

    let unfold_clauses node formals =
      match node with
      | {iname = "assert"; iargs = [Pred (ep, rp)]} ->
        let ep', l1 = unfold_vghosts_epred formals ep in
        let rp', l2 = unfold_vghosts_rpred formals rp in
        let l = remove_dups (l1 @ l2) in
        let prel = List.fold_right (fun x l -> (inject_vector_ghosts formals x) @ l) l [] in
        prel @ [{iname = "assert"; iargs = [Pred (ep',rp')]}]
      | {iname = "assume"; iargs = [Pred (ep, rp)]} -> (* TODO: for now we assume that assumptions are always preceded by assertions *)
        let ep', l1 = unfold_vghosts_epred formals ep in
        let rp', l2 = unfold_vghosts_rpred formals rp in
        let l = remove_dups (l1 @ l2) in
        let prel = List.fold_right (fun x l -> (inject_vector_ghosts formals x) @ l) l [] in
        let postl = List.fold_right (fun x l -> (extract_vector_ghosts formals x) @ l) l [] in
        prel @ [{iname = "assume"; iargs = [Pred (ep',rp')]}] @ postl
      | {iname = "cut"; iargs = [Pred (ep, rp)]} ->
        let ep', l1 = unfold_vghosts_epred formals ep in
        let rp', l2 = unfold_vghosts_rpred formals rp in
        let l = remove_dups (l1 @ l2) in
        let prel = List.fold_right (fun x l -> (inject_vector_ghosts formals x) @ l) l [] in
        prel @ [{iname = "cut"; iargs = [Pred (ep',rp')]}]
      | _ -> [node]

    let rec unfold_cfg_clauses cfg formals =
      match cfg with
      | h::t ->
        (unfold_clauses h formals) @ (unfold_cfg_clauses t formals)
      | [] -> []
end

module SimplVector = struct
  open Cfg
  open CL.Instr
  open CL.R
  open CL.I

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

  let rec is_equiv_type (ty: CL.ty) (ty': CL.ty) =
    match (ty, ty') with
    | (Uint i, Uint i') -> i == i'
    | (Uint i, Sint i') -> false
    | (Uint i, Bit) -> assert false
    | (Uint i, Vector (i', ty'')) ->
      i == (i' * int_of_ty ty'') && (is_unsigned ty'')
    | (Sint i, Sint i') -> i == i'
    | (Sint i, Bit) -> assert false
    | (Sint i, Vector (i', ty'')) ->
      i == (i' * int_of_ty ty'') && not(is_unsigned ty'')
    | (Bit, Bit) -> true
    | (Bit, Vector (_, _)) -> assert false
    | Vector (i, ty''), Vector (i', ty''') ->
      (i * int_of_ty ty'' == i' * int_of_ty ty''') && ((is_unsigned ty'') == (is_unsigned ty'''))
    | _ -> is_equiv_type ty' ty (* use recursivity to check the commutative pair *)

  let rec get_evars epred =
    let rec aux e =
      begin
      match e with
      | Iconst _ -> []
      | Ivar v -> [v]
      | Iunop (_, e') -> aux e'
      | Ibinop (e1, _, e2) ->
          (aux e1) @ (aux e2)
      | Ilimbs (_, el) -> List.flatten (List.map aux el)
      | IUnPack (v,_,_) -> [v]
      end
    in
    match epred with
    | Eeq (e1, e2) ->
      let vl1 = aux e1 in
      let vl2 = aux e2 in
      vl1 @ vl2
    | Eeqmod (e1, e2, eps) ->
      let vl1 = aux e1 in
      let vl2 = aux e2 in
      let vl3 = List.flatten (List.map aux eps) in
      vl1 @ vl2 @ vl3

  let rec get_rvars rpred =
    let rec aux e =
      begin
      match e with
      | Rvar v -> [v]
      | Rconst _ -> []
      | Ruext (e', _) ->  aux e'
      | Rsext (e', _) -> aux e'
      | Runop (_, e') -> aux e'
      | Rbinop (e1, _, e2) -> (aux e1) @ (aux e2)
      | RVget (v, _) -> [v]
      | UnPack (v,_,_) -> [v]
      | Rlimbs (_, el) -> List.flatten (List.map aux el)
      end
    in
    match rpred with
    | RPcmp (e1, _, e2) ->
      let vl1 = aux e1 in
      let vl2 = aux e2 in
      vl1 @ vl2
    | RPnot e -> get_rvars e
    | RPand rps -> List.flatten (List.map get_rvars rps)
    | RPor rps -> List.flatten (List.map get_rvars rps)
    | RPeqsmod (e1, e2, e3) ->
      let vl1 = aux e1 in
      let vl2 = aux e2 in
      let vl3 = aux e3 in
      vl1 @ vl2 @ vl3

  let get_clause_vars epreds rpreds =
    let epred_rvars = List.flatten (List.map get_evars epreds) in
    let rpred_vars = List.flatten (List.map get_rvars rpreds) in
    remove_dups (epred_rvars @ rpred_vars)

  let rec find_vect_lval tv n  =
      let (v, ty) = tv in
      let aux tv' n' =
        let nI = getPrevI n' in
        match nI with
        | Some i -> find_vect_lval tv' i
        | None -> None
      in
    match n.nkind with
    | {iname = "mov"; iargs = [Lval (Llvar (v',ty')); Atom (Avar (v'', ty''))]} ->
      if v == v' && is_equiv_type ty' ty'' then
        aux (v'',ty'') n
      else
        aux (v, ty) n
    | {iname = "mov"; iargs = [Lval (Llvar (v',ty')) ; Atom (Avecta ((v'', ty''), j))]} ->
      if v == v' && j == 0 && is_equiv_type ty' ty'' then (* do we care if j != 0 ? *)
        aux (v'',ty'') n
      else
        aux (v, ty) n
    | {iname = "mov"; iargs = [Lval (Llvar (v',ty')); Atom (Avatome (Avar (v'', ty'') :: t))]} ->
      let ll = (List.length t) + 1 in
      if ll == 1 && v == v' && is_equiv_type ty' ty'' then
        aux (v'', ty'') n
      else if v == v' && ((int_of_ty ty'') * ll) == (int_of_ty ty') then (* Since we're not able to reconstruct the list, this is no longer invertible *)
        Some (v', ty')
      else
        aux (v, ty) n
    | {iname = "mov"; iargs = [Lval (Llvar (v', ty')); Atom (Aconst _)]} ->
      if v == v' then
        None
      else
        aux (v, ty) n
    | {iname = "cast"; iargs = [Lval (Llvar (v',ty')); Atom (Avar (v'', ty''))]} ->
      if v == v' then
        if is_equiv_type ty' ty'' then
          aux (v'',ty'') n
        else
          Some (v', ty')
      else
        aux (v, ty) n
    | {iname = "cast"; iargs = [Lval (Llvar (v',ty')); Atom (Avatome (Avar (v'', ty'') :: t))]} ->
      let ll = (List.length t) + 1 in
      if ll == 1 && v == v' && is_equiv_type ty' ty'' then
        aux (v'', ty'') n
      else if v == v' && ((int_of_ty ty'') * ll) == (int_of_ty ty') then (* Since we're not able to reconstruct the list, this is no longer invertible *)
        Some (v', ty')
      else
        aux (v, ty) n
    | {iname = "adds"; iargs = [_; Lval (Llvar (v',ty')); Atom (Avar (_, ty'')); Atom (Avar (_, ty'''))]} ->
      if v == v' && (is_equiv_type ty' ty'' || is_equiv_type ty' ty''') then
        Some (v', ty')
      else
        aux (v, ty) n
    | {iname = "add"; iargs = [Lval (Llvar (v',ty'));  Atom (Avar (_, ty'')); Atom (Avar (_, ty'''))]} ->
      if v == v' && (is_equiv_type ty' ty'' || is_equiv_type ty' ty''') then
        Some (v', ty')
      else
        aux (v, ty) n
    | {iname = "subb"; iargs = [_; Lval (Llvar (v',ty')); Atom (Avar (_, ty'')); Atom (Avar (_, ty'''))]} ->
      if v == v' && (is_equiv_type ty' ty'' || is_equiv_type ty' ty''') then
        Some (v', ty')
      else
        aux (v, ty) n
    | {iname = "sub"; iargs = [Lval (Llvar (v',ty'));  Atom (Avar (_, ty'')); Atom (Avar (_, ty'''))]} ->
        if v == v' && (is_equiv_type ty' ty'' || is_equiv_type ty' ty''') then
          Some (v', ty')
        else
          aux (v, ty) n
    | {iname = "mull"; iargs = [Lval (Llvar (vh', tyh')); Lval (Llvar (vl', tyl')); Atom (Avar (_, ty'')); Atom (Avar (_, ty'''))]} ->
      if v == vl' &&  (is_equiv_type  tyl' ty'' || is_equiv_type tyl' ty''') then
        Some (vl', tyl')
      else if v == vh' &&  (is_equiv_type  tyh' ty'' || is_equiv_type tyh' ty''') then
        Some (vh', tyh')
      else
        aux (v, ty) n
    | {iname = "smull"; iargs = [Lval (Llvar (vh', tyh')); Lval (Llvar (vl', tyl')); Atom (Avar (_, ty'')); Atom (Avar (_, ty'''))]} ->
        if v == vl' &&  (is_equiv_type  tyl' ty'' || is_equiv_type tyl' ty''') then
          Some (vl', tyl')
        else if v == vh' &&  (is_equiv_type  tyh' ty'' || is_equiv_type tyh' ty''') then
          Some (vh', tyh')
        else
          aux (v, ty) n
    | {iname = "mul"; iargs = [Lval (Llvar (v', ty')); Atom (Avar (_, ty'')); Atom (Avar (_, ty'''))]} ->
      if v == v' &&  (is_equiv_type  ty' ty'' || is_equiv_type ty' ty''') then
        Some (v', ty')
      else
        aux (v, ty) n
    | {iname = "smul"; iargs = [Lval (Llvar (v', ty')); Atom (Avar (_, ty'')); Atom (Avar (_, ty'''))]} ->
      if v == v' &&  (is_equiv_type  ty' ty'' || is_equiv_type ty' ty''') then
        Some (v', ty')
      else
        aux (v, ty) n
    | {iname = "split"; iargs = [Lval (Llvar (vh', tyh')); Lval (Llvar (vl', tyl')); Atom (Avar (_, ty'')); _]} ->
      if v == vl' && is_equiv_type tyl' ty'' then
        Some (vl', tyl')
      else if v == vh' && is_equiv_type tyh' ty'' then
        Some (vh', tyh')
      else
        aux (v, ty) n
    | {iname = "ssplit"; iargs = [Lval (Llvar (vh', tyh')); Lval (Llvar (vl', tyl')); Atom (Avar (_, ty'')); _]} ->
      if v == vl' && is_equiv_type tyl' ty'' then
        Some (vl', tyl')
      else if v == vh' && is_equiv_type tyh' ty'' then
        Some (vh', tyh')
      else
        aux (v, ty) n
    | {iname = "sar"; iargs = [Lval (Llvar (v', ty')); Atom (Avar (_, ty'')); _]} ->
      if v == v' && is_equiv_type ty' ty'' then
        Some (v', ty')
      else
        aux (v, ty) n
    | {iname = "sars"; iargs = [Lval (Llvar (vh', tyh')); Lval (Llvar (vl', tyl')); Atom (Avar (_, ty'')); _]} ->
      if v == vl' && is_equiv_type tyl' ty'' then
        Some (vl', tyl')
      else if v == vh' && is_equiv_type tyh' ty'' then
        Some (vh', tyh')
      else
        aux (v, ty) n
    | {iname = "broadcast"; iargs = [Lval (Llvar (v', ty')); _; _]} ->
      if v == v' then
        Some (v', ty')
      else
        aux (v, ty) n
    | _ -> aux (v, ty) n (* Keep searching *)

    let sr_epred_lval pred ep =
      let rec aux e =
        match e with
        | Iconst c -> e
        | Ivar v ->
          let l = find_vect_lval v pred in
          begin
            match l with
            | Some v' -> Ivar v'
            | None -> e
          end
        | Iunop (s, e) ->
          let e' = aux e in
          Iunop (s, e')
        | Ibinop (e1, s, e2) ->
          let e1' = aux e1 in
          let e2' = aux e2 in
          Ibinop (e1', s, e2')
        | Ilimbs (c, l) ->
          let l' = List.map aux l in
          Ilimbs (c, l')
        | IUnPack (v, us, i) ->
          let l = find_vect_lval v pred in
          begin
            match l with
            | Some v' -> IUnPack (v', us, i)
            | None -> e
          end
      in
      match ep with
      | Eeq (e1, e2) ->
        let e1' = aux e1 in
        let e2' = aux e2 in
        Eeq (e1', e2')
      | Eeqmod (e1, e2, el) ->
        let e1' = aux e1 in
        let e2' = aux e2 in
        let el' = List.map aux el in
        Eeqmod (e1', e2', el')

    let rec sr_rpred_lval pred rp =
      let rec aux r =
        match r with
        | Rvar v ->
          let l = find_vect_lval v pred in
          begin
            match l with
            | Some v' -> Rvar v'
            | None -> r
          end
        | Rconst (c1, c2) -> r
        | Ruext (e, c) ->
          let e' = aux e in
          Ruext (e', c)
        | Rsext (e, c) ->
          let e' = aux e in
          Rsext(e', c)
        | Runop(s, e) ->
          let e' = aux e in
          Runop(s, e')
        | Rbinop(e1, s, e2) ->
          let e1' = aux e1 in
          let e2' = aux e2 in
          Rbinop(e1', s, e2')
        | RVget(v,c) ->
          let l = find_vect_lval v pred in
          begin
            match l with
            | Some v' -> RVget (v', c)
            | None -> r
          end
        | UnPack (v,us,i) ->
          let l = find_vect_lval v pred in
          begin
            match l with
            | Some v' -> UnPack (v', us, i)
            | None -> r
          end
        | Rlimbs (c, e) ->
          let e' = List.map (aux) e in
          Rlimbs (c, e')
      in
      match rp with
        | RPcmp(e1, s, e2) ->
          let e1' = aux e1 in
          let e2' = aux e2 in
          RPcmp(e1', s, e2')
        | RPnot e ->
          let e' = sr_rpred_lval pred e in
          RPnot e'
        | RPand rps ->
          let rps' = List.map (sr_rpred_lval pred) rps in
          RPand rps'
        | RPor  rps ->
          let rps' = List.map (sr_rpred_lval pred) rps in
          RPor rps'
        | RPeqsmod (e1,e2,e3) ->
          let e1' = aux e1 in
          let e2' = aux e2 in
          let e3' = aux e3 in
          RPeqsmod(e1',e2',e3')

    let sr_clause_lval (el, rl) pred =
      let el' = List.map (sr_epred_lval pred) el in
      let rl' = List.map (sr_rpred_lval pred) rl in
      (el', rl')

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
      | {iname = "add"; iargs = [_; Atom (Avar (v, Vector (i, ty))); Atom (Avar (v', Vector (i', ty')))]} ->
          aux (v, Vector (i, ty)) 1;
          aux (v', Vector (i', ty')) 2;
      | {iname = "mull"; iargs = [_; _; Atom (Avar (v, Vector (i, ty))); Atom (Avar (v', Vector (i', ty')))]} -> 
        aux (v, Vector (i, ty)) 2;
        aux (v', Vector (i', ty')) 3;
      | {iname = "smull"; iargs = [_; _; Atom (Avar (v, Vector (i, ty))); Atom (Avar (v', Vector (i', ty')))]} -> 
          aux (v, Vector (i, ty)) 2;
          aux (v', Vector (i', ty')) 3;
      | {iname = "mul"; iargs = [_; Atom (Avar (v, Vector (i, ty))); Atom (Avar (v', Vector (i', ty')))]} -> 
          aux (v, Vector (i, ty)) 1;
          aux (v', Vector (i', ty')) 2;
      | {iname = "smul"; iargs = [_; Atom (Avar (v, Vector (i, ty))); Atom (Avar (v', Vector (i', ty')))]} -> 
          aux (v, Vector (i, ty)) 1;
          aux (v', Vector (i', ty')) 2;
      | {iname = "sub"; iargs = [_; Atom (Avar (v, Vector (i, ty))); Atom (Avar (v', Vector (i', ty')))]} ->
          aux (v, Vector (i, ty)) 1;
          aux (v', Vector (i', ty')) 2;
      | {iname = "subb"; iargs = [_; _; Atom (Avar (v, Vector (i, ty))); Atom (Avar (v', Vector (i', ty')))]} -> 
        aux (v, Vector (i, ty)) 2;
        aux (v', Vector (i', ty')) 3;
      | {iname = "cast"; iargs = [_; Atom (Avar (v, Vector (i, ty)))]} ->
        aux (v, Vector (i, ty)) 1;
      | {iname = "cast"; iargs = [_; Atom (Avatome [Avar (v, ty)])]} ->
        aux (v, ty) 1; (* TODO: check me *)
      | {iname = "ssplit"; iargs = [_; _; Atom (Avar (v, Vector (i, ty))); _]} ->
        aux (v, Vector (i, ty)) 2;
      | {iname = "split"; iargs = [_; _; Atom (Avar (v, Vector (i, ty))); _]} ->
          aux (v, Vector (i, ty)) 2;
      | {iname = "sar"; iargs = [_; Atom (Avar (v, Vector (i, ty)));_ ]} ->
        aux (v, Vector (i, ty)) 1;
      | {iname = "sars"; iargs = [_; _; Atom (Avar (v, Vector (i, ty))); _]} ->
        aux (v, Vector (i, ty)) 2;
      | {iname = "mov"; iargs = [_; Atom (Avar (v, Vector (i,ty)))]} ->
        aux (v, Vector (i, ty)) 1;
      | {iname = "assert"; iargs = [Pred cl]} ->
        node.nkind <- { iname = "assert"; iargs = [Pred (sr_clause_lval cl pred)]}
      | {iname = "assume"; iargs = [Pred cl]} ->
        node.nkind <- { iname = "assume"; iargs = [Pred (sr_clause_lval cl pred)]}
      | _ -> ()

    let rec sr_lvals node =
      match node.succs with
      | [] -> ()
      | h::_ ->
        sr_lval node h;
        sr_lvals h

  let rec unused_lval ((v, ty) as tv) node = (* Checks if lval is used in any subsequent instruction *)
    let rec aux larg nI =
      let rec is_atom a =
        match a with
        | Aconst _ -> false
        | Avar tv' -> is_eq_tyvar tv tv'
        | Avecta (tv', _) -> is_eq_tyvar tv tv'
        | Avatome l -> (List.fold_left (||) false (List.map is_atom l))
      in
      match larg with
      | [] -> unused_lval tv nI
      | (Atom a) :: t -> not(is_atom a) && (aux t nI)
      | (Pred (el, rl)) :: t ->
        let cl_vars = get_clause_vars el rl in
        not(List.exists (is_eq_tyvar tv) cl_vars) && (aux t nI)
      | (Lval (Llvar tv')) :: t ->  aux t nI (* FIXME *)
        (* if (is_eq_tyvar tv tv') then
          if node.iname != "mov" || node.iname != "cast" then
            aux t nI
          else
            true
        else aux t nI *)
      | _ :: t -> (aux t nI)
      in
    match node with
    | None -> true
    | Some node -> aux node.nkind.iargs (getNextI node)

  let rec nop_uinst cfg ret_vars node =
    let nI = getNextI node in
    match node.nkind with
      | {iname = "cast"; iargs = [Lval (Llvar tv); _]}  ->
        if not(List.exists (is_eq_tyvar tv) ret_vars) && unused_lval tv nI then
          node.nkind <- { iname = "nop"; iargs = [] }
        else ()
      | {iname = "mov"; iargs = [Lval (Llvar tv); _]}  ->
        if not(List.exists (is_eq_tyvar tv) ret_vars) && unused_lval tv nI then
          node.nkind <- { iname = "nop"; iargs = [] }
        else ()
      | _ -> ()

  let rec nop_uinsts cfg ret_vars node =
    nop_uinst cfg ret_vars node;
    let nI = getPrevI node in
    match nI with
    | None -> ()
    | Some i -> nop_uinsts cfg ret_vars i

  let rec remove_nops l =
    match l with
    | [] -> []
    | h::t ->
      begin
      match h with
      | { iname = "nop"; iargs = [] } -> remove_nops t
      | _ -> h :: remove_nops t
      end

  let simpl_cfg cfg ret_vars =
    sr_lvals cfg;
    let nI = getPrevI cfg in
    match nI with
    | None -> cfg
    | Some i ->
      begin
        nop_uinsts cfg ret_vars i;
        let cfg' = cfg_of_prog (remove_nops (prog_of_cfg_rev cfg)) in
        cfg'
      end
end
