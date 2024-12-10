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

module GhostVector = struct
  open CL.Instr
  open CL.R
  open CL.I

  module S = struct
    let s = false (* TODO: is it always unsigned?*)
    let error = "unsigned x86"
  end

  module I = I (S)

  type vector =
    | U16x16

  let get_vghost ghosts gname =
    let vghost = List.find (fun (v, _) -> v.v_name = gname) ghosts in
    vghost

  let get_unfolded_vector_namei v i =
    String.concat "_" [v.v_name; "v" ; string_of_int i]

  let rec replace_vghosts_rexp ghosts r =
    let aux (v, ty) i =
      let name = get_unfolded_vector_namei v i in
      let v' = get_vghost ghosts name in
      Rvar v'
    in
    match r with
    | Rvar x -> r
    | Rconst (c1, c2) -> r
    | Ruext (e, c) ->
      let e' = replace_vghosts_rexp ghosts e in
      Ruext (e', c)
    | Rsext (e, c) ->
      let e' = replace_vghosts_rexp ghosts e in
      Rsext(e', c)
    | Runop(s, e) ->
      let e' = replace_vghosts_rexp ghosts e in
      Runop(s, e')
    | Rbinop(e1, s, e2) ->
      let e1' = replace_vghosts_rexp ghosts e1 in
      let e2' = replace_vghosts_rexp ghosts e2 in
      Rbinop(e1', s, e2')
    | RVget(e,c) -> r
    | UnPack (e,us,i) ->
      aux e i

  let rec unfold_ghosts_rpred ghosts pre =
    match pre with
    | RPcmp(e1, s, e2) ->
      let e1' = replace_vghosts_rexp ghosts e1 in
      let e2' = replace_vghosts_rexp ghosts e2 in
      RPcmp(e1', s, e2')
    | RPnot e ->
      let e' = unfold_ghosts_rpred ghosts e in
      RPnot e'
    | RPand rps ->
      let rps' = List.map (unfold_ghosts_rpred ghosts) rps in
      RPand rps'
    | RPor  rps ->
      let rps' = List.map (unfold_ghosts_rpred ghosts) rps in
      RPor rps'

  let unfold_vghosts_rpred ghosts pre =
    List.map (unfold_ghosts_rpred ghosts) pre

  let rec replace_vghosts_eexp ghosts e =
    let aux (v, ty) i =
      let name = get_unfolded_vector_namei v i in
      let v' = get_vghost ghosts name in
      Ivar v'
    in
    match e with
    | Iconst c -> e
    | Ivar v -> e
    | Iunop (s, e) ->
      let e' = replace_vghosts_eexp ghosts e in
      Iunop (s, e')
    | Ibinop (e1, s, e2) ->
      let e1' = replace_vghosts_eexp ghosts e1 in
      let e2' = replace_vghosts_eexp ghosts e2 in
      Ibinop (e1', s, e2')
    | Ilimbs (c, l) ->
      let l' = List.map (replace_vghosts_eexp ghosts) l in
      Ilimbs (c, l')
    | IUnPack (e, us, i) ->
      aux e i

  let rec unfold_ghosts_epred ghosts pre =
    match pre with
    | Eeq(e1, e2) ->
      let e1' = replace_vghosts_eexp ghosts e1 in
      let e2' = replace_vghosts_eexp ghosts e2 in
      Eeq(e1', e2')
    | Eeqmod(e1, e2, es) ->
      let e1' = replace_vghosts_eexp ghosts e1 in
      let e2' = replace_vghosts_eexp ghosts e2 in
      let es' = List.map (replace_vghosts_eexp ghosts) es in
      Eeqmod(e1', e2', es')

  let unfold_vghosts_epred ghosts pre =
     List.map (unfold_ghosts_epred ghosts) pre

  let unfold_vector formals =
    let aux ((formal,ty) as v) =
      let mk_vector = Annot.filter_string_list None ["u16x16", U16x16] in
      match Annot.ensure_uniq1 "vect" mk_vector (formal.v_annot) with
      | None -> [v],[]
      | Some U16x16 ->
        let rec aux i acc =
          match i with
          | 0 -> acc
          | n ->
            let name = get_unfolded_vector_namei formal (i-1) in
            let v = I.mk_tmp_lval ~name u16 in
            aux (n - 1) (v :: acc)
        in
        let vl = aux 16 [] in
        let va = List.map (fun v -> Avar v) vl in
        let a = Avatome va in
        let (l_16x16, lty_16x16) as l16x16 = I.var_to_tyvar ~vector:(16,16) formal in
        let (l_1x256, lty_1x256) as l1x256 = I.var_to_tyvar ~vector:(1,256) formal in
        let vl16x16 = Avar l16x16 in
        let l_0 = Avecta (l1x256, 0) in
        vl,[cast lty_16x16 l16x16 a;  cast lty_1x256 l1x256 vl16x16; Op1.mov v l_0]
        in
        List.fold_left (fun (acc1,acc2) v ->
            let fs,is = aux v in
            fs @ acc1,is @ acc2)
          ([],[]) formals
end

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

  let rec find_vect_lval tv n  =
      let (v, ty) = tv in
      let aux tv' n' =
        let nI = getPrevI n' in
        match nI with
        | Some i -> find_vect_lval tv' i
        | None -> None
      in
    match n.nkind with
    | {iname = "cast"; iargs = [Lval (v', ty'); Atom (Avar (v'', ty''))]} ->
      if v == v' && is_equiv_type ty' ty'' then
        aux (v'',ty'') n
      else
        aux (v, ty) n
    | {iname = "cast"; iargs = [Lval (v', ty'); Atom (Avatome (Avar (v'', ty'') :: t))]} ->
      let ll = (List.length t) + 1 in
      if v == v' && ((int_of_ty ty'') * ll) == (int_of_ty ty') then
        Some (v', ty')
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

  let rec unused_lval ((v, ty) as tv) nI = (* Checks if lval is used in any subsequent instruction *)
    let diff_lval_tyvar (v', ty') (v'', ty'') = (* Prevent some typecasting problems ??*)
      (v' != v'') || (ty' != ty'')
    in
    let rec var_in_vatome tv' l =
      match l with
        | h :: t ->
          begin
            match h with
            | Avar (tv'') -> not(diff_lval_tyvar tv' tv'') || (var_in_vatome tv' t)
            | Avecta (tv'' , _) -> not(diff_lval_tyvar tv' tv'') || (var_in_vatome tv' t)
            | Avatome l' -> (var_in_vatome tv' t) || (var_in_vatome tv' l')  (* is this valid CL? should we assert false ?? *)
            | _ -> (var_in_vatome tv' t)
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
        | {iname = "mov"; iargs = [_; Atom (Avar tv')]} -> (diff_lval_tyvar tv tv') && (aux tv n)
        | {iname = "mov"; iargs = [_; Atom (Avecta (tv', _))]} -> (diff_lval_tyvar tv tv') && (aux tv n)
        | {iname = "mov"; iargs = [_; Atom (Aconst _)]} -> aux tv n
        | {iname = "mov"; iargs = [_; Atom (Avatome l)]} -> not(var_in_vatome tv l) && (aux tv n)
        | {iname = "cast"; iargs = [_; Atom (Avar tv')]} -> (diff_lval_tyvar tv tv') && (aux tv n)
        | {iname = "cast"; iargs = [_; Atom (Avecta (tv', _))]} -> (diff_lval_tyvar tv tv') && (aux tv n)
        | {iname = "cast"; iargs = [_; Atom (Aconst _)]} -> aux tv n
        | {iname = "cast"; iargs = [_; Atom (Avatome l)]} -> not(var_in_vatome tv l) && (aux tv n)
        | {iname = "adds"; iargs = [_; _; Atom (Avar tv'); Atom (Avar tv'')]} -> (diff_lval_tyvar tv tv') && (diff_lval_tyvar tv tv'') && (aux tv n)
        | {iname = "adds"; iargs = [_; _; Atom (Avecta (tv', _)); Atom (Avecta (tv'', _))]} -> (diff_lval_tyvar tv tv') && (diff_lval_tyvar tv tv'') && (aux tv n)
        | {iname = "add"; iargs = [_; Atom (Avar tv'); Atom (Avar tv'')]} -> (diff_lval_tyvar tv tv') && (diff_lval_tyvar tv tv'') && (aux tv n)
        | {iname = "add"; iargs = [_; Atom (Avecta (tv', _)); Atom (Avecta (tv'', _))]} -> (diff_lval_tyvar tv tv') && (diff_lval_tyvar tv tv'') && (aux tv n)
        | {iname = "subb"; iargs = [_; _; Atom (Avar tv'); Atom (Avar tv'')]} -> (diff_lval_tyvar tv tv') && (diff_lval_tyvar tv tv'') && (aux tv n)
        | {iname = "subb"; iargs = [_; _; Atom (Avecta (tv', _)); Atom (Avecta (tv'', _))]} -> (diff_lval_tyvar tv tv') && (diff_lval_tyvar tv tv'') && (aux tv n)
        | {iname = "sub"; iargs = [_; Atom (Avar tv'); Atom (Avar tv'')]} -> (diff_lval_tyvar tv tv') && (diff_lval_tyvar tv tv'') && (aux tv n)
        | {iname = "sub"; iargs = [_; Atom (Avecta (tv', _)); Atom (Avecta (tv'', _))]} -> (diff_lval_tyvar tv tv') && (diff_lval_tyvar tv tv'') && (aux tv n)
        | {iname = "mull"; iargs = [_; _; Atom (Avar tv'); Atom (Avar tv'')]} -> (diff_lval_tyvar tv tv') && (diff_lval_tyvar tv tv'') && (aux tv n)
        | {iname = "mull"; iargs = [_; _; Atom (Avecta (tv', _)); Atom (Avecta (tv'', _))]} -> (diff_lval_tyvar tv tv') && (diff_lval_tyvar tv tv'') && (aux tv n)
        | _ -> aux tv n
      end

  let rec nop_uinst cfg node =
    let nI = getNextI node in
    match node.nkind with
      | {iname = "cast"; iargs = [Lval tv; _]}  ->
        if unused_lval tv nI then
          node.nkind <- { iname = "nop"; iargs = [] }
        else ()
      | {iname = "mov"; iargs = [Lval tv; _]}  ->
        if unused_lval tv nI then
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
