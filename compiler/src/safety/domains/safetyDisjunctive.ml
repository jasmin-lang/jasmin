open Jasmin
open Prog
open Utils
open Apron
    
open SafetyUtils
open SafetyVar
open SafetyExpr 
open SafetyConstr
open SafetyInterfaces
open SafetyNum


(*------------------------------------------------------------*)
(* Partition Tree Domain *)

type cnstr = { mtcons : Mtcons.t; 
               cpt_uniq : int;
               loc : L.i_loc }

let pp_cnstr fmt c =
  Format.fprintf fmt "(%d) %a: %a"
    (c.cpt_uniq)
    L.pp_iloc c.loc
    Mtcons.print c.mtcons

let pp_cnstrs fmt =
  Format.fprintf fmt "%a"
    (pp_list ~sep:(fun fmt () -> Format.fprintf fmt ";@ ") pp_cnstr)

module Ptree = struct
  (* Trace partitionning, where:
     - [constr] is a constraint, comprising a linear constraint and a 
     program point.
     - [n_true] and [n_false] are abstract states over-approximating traces 
     that went through the constraint, and where it evaluated to, 
     respectively, true and false.  
     - [n_unknwn] over-approximates traces that did not go through the 
     constraint. *)
  type 'a node = { constr   : cnstr;
                n_true   : 'a;
                n_false  : 'a;
                n_unknwn : 'a; }
  
  type 'a t =
    | Node of 'a t node
    | Leaf of 'a


  let rec pp_ptree pp_leaf fmt = function
    | Leaf x -> pp_leaf fmt x
    | Node ({ n_true = Leaf nt;
              n_false = Leaf nf;
              n_unknwn = Leaf nu;} as node) ->
      Format.fprintf fmt "@[<v 0>@[<v 2># @[%a@] :@;\
                          @[%a@]@]@;\
                          @[<v 2># NOT @[%a@] :@;\
                          @[%a@]@]@;\
                          @[<v 2># UNKNOWN @[%a@] :@;\
                          @[%a@]@]@;@]"
        pp_cnstr node.constr
        pp_leaf nt
        pp_cnstr node.constr
        pp_leaf nf
        pp_cnstr node.constr
        pp_leaf nu

    | Node node ->
      Format.fprintf fmt "@[<v 0>\
                          @[<v 2># @[%a@] :@;\
                          @[%a@]@]@;\
                          @[<v 2># NOT @[%a@] :@;\
                          @[%a@]@]@;\
                          @[<v 2># UNKNOWN @[%a@] :@;\
                          @[%a@]@]@;@]"
        pp_cnstr node.constr
        (pp_ptree pp_leaf) node.n_true
        pp_cnstr node.constr
        (pp_ptree pp_leaf) node.n_false
        pp_cnstr node.constr
        (pp_ptree pp_leaf) node.n_unknwn

  let rec same_shape t1 t2 = match t1, t2 with
    | Node n1, Node n2 -> same_shape_n n1 n2
    | Leaf _, Leaf _ -> true
    | _ -> false

  and same_shape_n n1 n2 =
    n1.constr.cpt_uniq = n2.constr.cpt_uniq &&
    same_shape n1.n_true n2.n_true &&
    same_shape n1.n_false n2.n_false &&
    same_shape n1.n_unknwn n2.n_unknwn
    
  let apply (f : 'a -> 'b) (t : 'a t) =
    let rec aux t = match t with
      | Node { constr = c; n_true = nt; n_false = nf; n_unknwn = nu; }
        -> Node { constr   = c;
                  n_true   = aux nt;
                  n_false  = aux nf;
                  n_unknwn = aux nu; } 
      | Leaf x -> Leaf (f x) in
    aux t
      
  let apply2_merge (fmerge : 'a t -> 'b t -> ('a t * 'b t))
      (f : 'a -> 'b -> 'c) t1 t2 =
    let rec aux t1 t2 = match t1,t2 with
      | Node { constr = c ; n_true = nt ; n_false = nf ; n_unknwn = nu ; },
        Node { constr = c'; n_true = nt'; n_false = nf'; n_unknwn = nu'; }
        when c.cpt_uniq = c'.cpt_uniq ->
        Node { constr   = c;
               n_true   = aux nt nt';
               n_false  = aux nf nf';
               n_unknwn = aux nu nu'; }

      | Leaf x1, Leaf x2 -> Leaf (f x1 x2)
      | _ -> raise (Aint_error "Ptree: Shape do not match") in

    let t1, t2 = if same_shape t1 t2 then t1,t2 else fmerge t1 t2 in

    aux t1 t2

  let apply_list (f : 'a list -> 'b) ts =
    let rec aux ts = match ts with
      | [] -> raise (Aint_error "Ptree: apply_l empty list")
      | Node { constr = c; } :: _ ->
        aux_node c ts [] [] []
      | Leaf _ :: _ -> aux_leaf ts []

    and aux_node c ts tts fts uts = match ts with
      | Node { constr = c'; n_true = nt; n_false = nf; n_unknwn = nu; } :: ts'
        when c.cpt_uniq = c'.cpt_uniq ->
        aux_node c ts' (nt :: tts) (nf :: fts) (nu :: uts)
      | [] -> Node { constr   = c;
                     n_true   = aux tts;
                     n_false  = aux fts;
                     n_unknwn = aux uts; }
      | _ -> raise (Aint_error "Ptree: aux_node bad shape")

    and aux_leaf ts xts = match ts with
      | Leaf x :: ts' -> aux_leaf ts' (x :: xts)
      | [] -> Leaf (f xts)
      | _ -> raise (Aint_error "Ptree: aux_leaf bad shape") in

    aux ts

  let eval (fn : cnstr -> 'a -> 'a -> 'a -> 'a)
      (fl : 'b -> 'a)
      (t : 'b t) =
    let rec aux = function
      | Node { constr = c; n_true = nt; n_false = nf; n_unknwn = nu; } ->
        fn c (aux nt) (aux nf) (aux nu)
      | Leaf x -> fl x in
    aux t

  let eval2_merge (fmerge : 'b t -> 'c t -> ('b t * 'c t))
      (fn : cnstr -> 'a -> 'a -> 'a -> 'a)
      (fl : 'b -> 'c -> 'a)
      (t1 : 'b t) (t2 : 'c t) =
    let rec aux t1 t2 = match t1,t2 with
      | Node { constr = c ; n_true = nt ; n_false = nf ; n_unknwn = nu ; },
        Node { constr = c'; n_true = nt'; n_false = nf'; n_unknwn = nu'; }
        when c.cpt_uniq = c'.cpt_uniq ->
        fn c (aux nt nt') (aux nf nf') (aux nu nu')
      | Leaf x1, Leaf x2 -> fl x1 x2
      | _ -> raise (Aint_error "Ptree: eval2 : shape do not match") in

    let t1, t2 = if same_shape t1 t2 then t1,t2 else fmerge t1 t2 in

    aux t1 t2

  let ptree_size t = eval (fun _ a b c -> a + b + c) (fun _ -> 1) t
end



(*---------------------------------------------------------------*)
type cnstr_blk = { cblk_loc : L.i_loc;
                   cblk_cnstrs : cnstr list; }

(* hashconsing *)
module OrdL = struct
  type t = L.i_loc
  let compare l l' = Stdlib.Int.compare l.L.uid_loc l'.L.uid_loc

  let equal l l' =  Stdlib.Int.equal l.L.uid_loc l'.L.uid_loc
end
module ML = Map.Make (OrdL)
    
let hc = ref ML.empty
let _uniq = ref 0

let make_cnstr c i =
  try
    let constr = ML.find i !hc in
    if Mtcons.equal_tcons constr.mtcons c
    then constr
    else begin
      debug (fun () ->
          Format.eprintf "make_cnstr for (%d, line %a):@.\
                          changed constraint from %a to %a@."
            constr.cpt_uniq L.pp_iloc i
            Mtcons.print constr.mtcons
            Mtcons.print c);
          { constr with mtcons = c } end
  with
  | Not_found ->
    incr _uniq;
    let res = { mtcons = c; cpt_uniq = !_uniq; loc = i } in
    hc := ML.add i res !hc;
    res

(* Disjunctive domain. Leaves are already constrained under the branch
   conditions. *)
module AbsDisj (A : AbsNumProdT) : AbsDisjType = struct

  type t = { tree : A.t Ptree.t;
             cnstrs : cnstr_blk list }


  (*---------------------------------------------------------------*)
  let init_blk = { cblk_loc = L.i_dummy ; cblk_cnstrs = [] }

  let make_abs a = { tree = Leaf a;
                     cnstrs = [ init_blk ]; }

  (*---------------------------------------------------------------*)
  let pp_cblk fmt cb =
    Format.fprintf fmt "[{%a} %a]"
      L.pp_iloc cb.cblk_loc
      pp_cnstrs cb.cblk_cnstrs 

  let pp_cblks fmt =
    Format.fprintf fmt "@[<v 0>%a@]"
      (pp_list ~sep:(fun fmt () -> Format.fprintf fmt "@;") pp_cblk)
      
  let cblk_equal cb cb' =
    cb.cblk_loc = cb'.cblk_loc
    && List.length cb.cblk_cnstrs = List.length cb'.cblk_cnstrs
    && List.for_all2 (fun c c' -> c.cpt_uniq = c'.cpt_uniq) 
      cb.cblk_cnstrs cb'.cblk_cnstrs

  (*---------------------------------------------------------------*)
  let same_shape t t' =
    List.length t.cnstrs = List.length t'.cnstrs
    && List.for_all2 cblk_equal t.cnstrs t'.cnstrs

  let compare c c' = Stdlib.compare c.cpt_uniq c'.cpt_uniq

  let equal c c' = compare c c' = 0

  let cnstrs_list l = 
    List.map (fun x -> x.cblk_cnstrs) l |> List.rev |> List.flatten

  let add_constr_unknwn c t =
    Ptree.Node { constr   = c;
                 n_true   = Ptree.apply A.bottom t;
                 n_false  = Ptree.apply A.bottom t;
                 n_unknwn = t; }
      
    
  (* Merge two blocks [t] and [t']. If a constraint [c] appears on the left
     but node on the right, replace [t'] by
     [Node { constr = c; n_true = bottom; n_false = bottom; n_unknwn = t'] *)
  let rec merge_blck mcs t t' = match mcs, t, t' with
    | [], Ptree.Leaf _, Ptree.Leaf _ -> t, t'
    | c0 :: mcs',
      Node { constr = c ; n_true = nt ; n_false = nf ; n_unknwn = nu ; },
      Node { constr = c'; n_true = nt'; n_false = nf'; n_unknwn = nu'; } ->
      if equal c c' && equal c c0 then
        let mnt,mnt' = merge_blck mcs' nt nt'
        and mnf,mnf' = merge_blck mcs' nf nf'
        and mnu,mnu' = merge_blck mcs' nu nu' in
        ( Ptree.Node { constr   = c;
                       n_true   = mnt;
                       n_false  = mnf;
                       n_unknwn = mnu; },
          Ptree.Node { constr   = c;
                       n_true   = mnt';
                       n_false  = mnf';
                       n_unknwn = mnu'; } )
      else if equal c c0
      then merge_blck mcs t (add_constr_unknwn c t')
      else if equal c' c0
      then merge_blck mcs (add_constr_unknwn c t) t'
      else raise (Aint_error "merge_blck: bad shape")

    | c0 :: _, Node { constr = c; }, Ptree.Leaf _ ->
      assert (equal c0 c);
      merge_blck mcs t (add_constr_unknwn c t')

    | c0 :: _, Ptree.Leaf _, Node { constr = c'; } ->
      assert (equal c0 c');
      merge_blck mcs (add_constr_unknwn c' t) t'

    | _ -> raise (Aint_error "merge_blck: bad shape")

  let rec merge_last_blck mcs t t' l = match l with
    | [] -> merge_blck mcs t t'
    | c0 :: l' ->
      match t,t' with
      | Ptree.Node {constr = c ; n_true = nt ; n_false = nf ; n_unknwn = nu ;},
        Ptree.Node {constr = c'; n_true = nt'; n_false = nf'; n_unknwn = nu';} 
        when equal c c' && equal c c0 ->
        let mnt,mnt' = merge_last_blck mcs nt nt' l'
        and mnf,mnf' = merge_last_blck mcs nf nf' l'
        and mnu,mnu' = merge_last_blck mcs nu nu' l' in
        ( Ptree.Node {constr   = c ;
                      n_true   = mnt ;
                      n_false  = mnf ;
                      n_unknwn = mnu ;},
          Ptree.Node {constr   = c;
                      n_true   = mnt';
                      n_false  = mnf';
                      n_unknwn = mnu';} )
      | _ -> assert false

  let tmerge_check cs l cs' l' =
    if not (List.for_all2 cblk_equal l l') then begin
      Format.eprintf "error tmerg:@;l:@;%a@.l':@;%a@."
        pp_cblks l
        pp_cblks  l';
      assert false
    end;
    if not (cs.cblk_loc = cs'.cblk_loc) then begin
      Format.eprintf "%a and %a"
        L.pp_iloc cs.cblk_loc L.pp_iloc cs'.cblk_loc;
      assert false
    end

  let tmerge t t' =
    if same_shape t t' then t, t'
    else match t.cnstrs, t'.cnstrs with
      | [], [] -> t,t'
      | cs :: l, cs' :: l' ->
        tmerge_check cs l cs' l';
        let mcs_cnstrs = 
          List.sort_uniq compare (cs.cblk_cnstrs @ cs'.cblk_cnstrs) in
        let mcs = { cs with cblk_cnstrs = mcs_cnstrs } in
        
        let mt, mt' = 
          merge_last_blck mcs_cnstrs t.tree t'.tree (cnstrs_list l) in
        ( { tree = mt; cnstrs = mcs :: l }, { tree = mt'; cnstrs = mcs :: l } )
      | _ -> assert false

  
  let apply f t = { t with tree = Ptree.apply f t.tree }

  let eval fn fl t = Ptree.eval fn fl t.tree

  let bottom a = apply (fun x -> A.bottom x) a
      
  let top a = apply (fun x -> A.top x) a

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
      let t_lce = List.fold_left (fun acc x -> tmerge acc x |> fst) t l' in
      t_lce :: (List.map (fun x -> tmerge t_lce x |> snd) l')

  let apply_list f ts =
    match merge_list ts with
    | [] -> raise (Aint_error "apply_list: empty list")
    | t :: _ as ts ->
      let tts = List.map (fun x -> x.tree) ts in
      { tree = Ptree.apply_list f tts;
        cnstrs = t.cnstrs }

  let new_cnstr_blck t l =
    let blk = { cblk_loc = l; cblk_cnstrs = [] } in
    { t with cnstrs = blk :: t.cnstrs }

  let tbottom a = Ptree.apply (fun x -> A.bottom x) a

  let build_tree_pair c (mnt,mnt') (mnf,mnf') (mnu,mnu') =
    ( Ptree.Node {constr   = c;
                  n_true   = mnt;
                  n_false  = mnf;
                  n_unknwn = mnu;},
      Ptree.Node {constr   = c;
                  n_true   = mnt';
                  n_false  = mnf';
                  n_unknwn = mnu';} )
    
  (* Insert the constraint in the current block at the correct place.
     If [meet] is true, then meet the [n_true] branch with [c] and the 
     [n_false] branch with [not c]. *)
  let add_cnstr_blck ~meet c t =
    let meet_true a =
      if meet
      then A.meet_constr a c.mtcons
      else a 
    and meet_false a =
      if meet
      then match flip_constr c.mtcons with
        | None -> a
        | Some nc -> A.meet_constr a nc
      else a
    in
    
    let rec add_cnstr_blck t = match t with
    | Ptree.Leaf a ->
      let nt = meet_true a
      and nf = meet_false a in

      ( Ptree.Node { constr   = c ;
                     n_true   = Ptree.Leaf nt ;
                     n_false  = Ptree.Leaf (A.bottom a) ;
                     n_unknwn = Ptree.Leaf (A.bottom a) ;},
        Ptree.Node { constr   = c ;
                     n_true   = Ptree.Leaf (A.bottom a) ;
                     n_false  = Ptree.Leaf nf ;
                     n_unknwn = Ptree.Leaf (A.bottom a) ;} )

    | Ptree.Node {constr = c' ; n_true = nt ; n_false = nf ; n_unknwn = nu ;} ->
      let cc = compare c c' in

      (* [c] must be inserted above [c'] *)
      if cc = -1 then
        let nt' = Ptree.apply (fun a -> meet_true a ) t
        and nf' = Ptree.apply (fun a -> meet_false a) t in

      ( Ptree.Node { constr   = c ;
                     n_true   = nt' ;
                     n_false  = tbottom t ;
                     n_unknwn = tbottom t ;},
        Ptree.Node { constr   = c ;
                     n_true   = tbottom t ;
                     n_false  = nf' ;
                     n_unknwn = tbottom t ;} )


      (* [c] must be inserted below [c'] *)
      else if cc = 1 then
        build_tree_pair c'
          (add_cnstr_blck nt) (add_cnstr_blck nf) (add_cnstr_blck nu)

      (* [c] and [c'] are equal. We need to consider cross-cases here.
          c                       c      
          |---- t                 |---- ⟦c⟧ ∪ ⟦c⟧u ∪ ⟦c⟧f
          |---- u       ===>      |---- ⟂
          |---- f                 |---- ⟦¬c⟧ ∪ ⟦¬c⟧u ∪ ⟦¬c⟧f
         which we then split as follows:
         c                                  c                         
         |---- ⟦c⟧ ∪ ⟦c⟧u ∪ ⟦c⟧f            |---- ⟂
         |---- ⟂                      and   |---- ⟂                   
         |---- ⟂                            |---- ⟦¬c⟧ ∪ ⟦¬c⟧u ∪ ⟦¬c⟧f
      *)
      else
        let nt' = Ptree.apply_list (fun l ->
            let l = List.map (fun a -> A.meet_constr a c.mtcons) l in
            A.join_list l
          ) [nt; nf; nu]
        and nf' = Ptree.apply_list (fun l ->
            let l = List.map (fun a -> match flip_constr c.mtcons with
                | None -> a
                | Some nc -> A.meet_constr a nc) l in
            A.join_list l
          ) [nt; nf; nu] in
        ( Ptree.Node { constr   = c;
                       n_true   = nt';
                       n_false  = tbottom nu;
                       n_unknwn = tbottom nu; },
          Ptree.Node { constr   = c;
                       n_true   = tbottom nu;
                       n_false  = nf';
                       n_unknwn = tbottom nu; } )
    in

    add_cnstr_blck t
  
  (* Go down to the last block in t and apply f, then inductively combine the
     results using fn *)
  let rec apply_last_blck fn f t l = match l,t with
    | [], _ -> f t
    | c0 :: l',
      Ptree.Node { constr = c; n_true = nt; n_false = nf; n_unknwn = nu; }
      when equal c c0 ->
      let mnt = apply_last_blck fn f nt l'
      and mnf = apply_last_blck fn f nf l'
      and mnu = apply_last_blck fn f nu l' in
      fn c mnt mnf mnu

    | _ -> raise (Aint_error "apply_last_blck: bad shape err3")

  let add_cnstr t ~meet c loc =
    match t.cnstrs with
    | cs :: l ->     
      let cnstr = make_cnstr c loc in
      let f x = add_cnstr_blck ~meet:meet cnstr x in

      let sorted_cnstrs = 
        List.sort_uniq compare (cnstr :: cs.cblk_cnstrs) in
      let nblk = { cs with cblk_cnstrs = sorted_cnstrs } in
      let ncs = nblk :: l in
      let tl,tr = apply_last_blck build_tree_pair f t.tree (cnstrs_list l) in
      ( { tree = tl; cnstrs = ncs }, { tree = tr; cnstrs = ncs } )

    | _ -> raise (Aint_error "add_cnstr: empty list")

  let pop_cnstr_blck t loc = match t.cnstrs with
    | blk :: l ->
      (* This assert is to check that constraint blocks 'open' and 'close'
         are properly nested. *)
      assert (blk.cblk_loc = loc);
      let f x =
        let tree =
          Ptree.eval
            (fun _ a1 a2 a3 -> A.join_list [a1; a2; a3])
            (fun a -> a) x in
        Ptree.Leaf tree
      and fn c mnt mnf mnu = Ptree.Node {constr   = c;
                                         n_true   = mnt;
                                         n_false  = mnf;
                                         n_unknwn = mnu; } in

      { tree =  apply_last_blck fn f t.tree (cnstrs_list l);
        cnstrs =  l }
    | _ -> raise (Aint_error "pop_cnstr_blck: empty list")

  let pop_all_blcks t = 
    let a = Ptree.eval
        (fun _ a1 a2 a3 -> A.join_list [a1; a2; a3]) (fun a -> a) t.tree in
    make_abs a
                      
  (* Make a top value defined on the given variables *)
  let make l = make_abs (A.make l)

  let meet = apply2 A.meet
  let meet_list = apply_list A.meet_list

  let join = apply2 A.join
  let join_list = apply_list A.join_list

  let widening oc = apply2 (A.widening oc)

  let forget_list t l =
    if l = [] then t
    else apply (fun x -> A.forget_list x l) t

  let is_included = eval2 (fun _ a1 a2 a3 -> a1 && a2 && a3) A.is_included
  let is_bottom = eval (fun _ a1 a2 a3 -> a1 && a2 && a3) A.is_bottom

  let rec get_leaf = function
    | Ptree.Node { n_true = nt } -> get_leaf nt
    | Ptree.Leaf x -> x 
      
  (* All leaves should have the same environment *)
  let get_env t = A.get_env (get_leaf t.tree)

  (* All leaves should have the same environment *)
  let top_no_disj a =
    let leaf = A.top (get_leaf a.tree) in
    { cnstrs = [init_blk]; tree = Ptree.Leaf leaf; }

  let to_shape a shp =
    assert (a.cnstrs = [init_blk]);
    let leaf = get_leaf a.tree in
    apply (fun _ -> leaf) shp 

  let remove_disj a =
    (* Note that we could evaluate [a] into a list of abstract elements, and
       do a single join at the end. It may be better. *)
    let a = eval (fun _ b1 b2 b3 -> A.join_list [b1; b2; b3]) ident a in
    {cnstrs = [init_blk]; tree = Ptree.Leaf a; }

  let expand t v l = apply (fun x -> A.expand x v l) t

  let fold t l = apply (fun x -> A.fold x l) t

  let bman : Box.t Manager.t = BoxManager.man
  let box_of_int int = Abstract0.of_box bman 1 0 (Array.init 1 (fun _ -> int))
  let box_join b1 b2 b3 =
    let bs = Array.of_list [b1; b2; b3] in
    Abstract0.join_array bman bs
  let int_of_box b = Abstract0.bound_dimension bman b 0

  (* Interval does not support joins, so we go through level 0 boxes. *)
  let bound_variable t v =
    eval (fun _ -> box_join) (fun x -> A.bound_variable x v |> box_of_int ) t
    |> int_of_box

  let bound_texpr t e =
    eval (fun _ -> box_join) (fun x -> A.bound_texpr x e |> box_of_int ) t
    |> int_of_box

  let assign_expr ?force:(force=false) (t : t) (ves : (mvar * Mtexpr.t) list) =
    apply (fun x -> A.assign_expr ~force:force x ves) t

  let meet_constr t c = apply (fun x -> A.meet_constr x c) t
  let meet_constr_list t cs = apply (fun x -> A.meet_constr_list x cs) t

  let sat_constr t c =
    eval (fun _ a b c -> a && b && c) (fun x -> A.sat_constr x c) t
    
  let unify = apply2 A.unify

  let change_environment t l = apply (fun x -> A.change_environment x l) t

  let remove_vars t l = apply (fun x -> A.remove_vars x l) t

  let to_box = eval
      (fun _ a1 a2 a3 ->
         let ass = Array.of_list [a1; a2; a3] in
         Abstract1.join_array bman ass)
      A.to_box


  let of_box bt tshape = apply (fun a -> A.of_box bt a) tshape

  let set_rel   t v = apply (fun a -> A.set_rel a v) t
  let set_unrel t v = apply (fun a -> A.set_unrel a v) t 

  let dom_st_update t v info = apply (fun a -> A.dom_st_update a v info) t 
    
  let shrt_tree t =
    (* See Ptree.eval for the order *)
    let fn c mnt mnf mnu = match mnt, mnf, mnu with
      | Ptree.Leaf lmnt, Ptree.Leaf lmnf, Ptree.Leaf lmnu ->
        if A.is_bottom lmnt && A.is_bottom lmnf && A.is_bottom lmnu
        then Ptree.Leaf lmnt
        else Ptree.Node { constr   = c;
                          n_true   = mnt;
                          n_false  = mnf;
                          n_unknwn = mnu; }
      | _ -> Ptree.Node { constr   = c;
                          n_true   = mnt;
                          n_false  = mnf;
                          n_unknwn = mnu; } in

    let fl a = Ptree.Leaf a in
    
    eval fn fl t

  let print ?full:(full=false) fmt t =
    (* Useful to debug constrait blocks *)
    (* Format.eprintf "debug: constraints:@; %a@.@."
     *   pp_cblks t.cnstrs;     *)
    Ptree.pp_ptree (fun fmt a ->
        if A.is_bottom a then Format.fprintf fmt "⟂@;"
        else A.print ~full:full fmt a) fmt (shrt_tree t)
end


(*------------------------------------------------------------*)
(* Simple Domain Lifting *)

(* Lifts a non-relational domain without disjunctions. *)
module LiftToDisj (A : AbsNumType) : AbsDisjType = struct
  include A

  let of_box _t _ = assert false
    
  let dom_st_update t _ _ = t
  let set_rel t _ = t
  let set_unrel t _ = t
      
  let top_no_disj t = t
  let to_shape t _ = t
  let remove_disj t = t
  let new_cnstr_blck t _ = t
  let add_cnstr t ~meet:_ _ _ = t, t
  let pop_cnstr_blck t _ = t
  let pop_all_blcks t = t
end
