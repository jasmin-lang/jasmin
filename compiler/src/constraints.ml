(* -------------------------------------------------------------------- *)
(* FIXME remove this *)
module Utils = struct
type 'a pp = Format.formatter -> 'a -> unit

let rec pp_list sep pp fmt xs =
  let pp_list = pp_list sep pp in
  match xs with
  | []      -> ()
  | [x]     -> Format.fprintf fmt "%a" pp x
  | x :: xs -> Format.fprintf fmt "%a%(%)%a" pp x sep pp_list xs
end
(* ---------------------------------------------------------------------- *)
(* FIXME remove this code of Francois Pottier and add external dependency *)
module UnionFind : sig
  type 'a elem
  val make : 'a -> 'a elem
  val eq : 'a elem -> 'a elem -> bool
  val find : 'a elem -> 'a elem
  val get : 'a elem -> 'a
  val set : 'a elem -> 'a -> unit
  val union : 'a elem -> 'a elem -> 'a elem
  val merge : ('a -> 'a -> 'a ) -> 'a elem -> 'a elem -> 'a elem
end = struct

  type rank = int

  type 'a content =
    | Link of { mutable parent : 'a elem }
    | Root of { mutable rank : rank; mutable value : 'a }

  and 'a elem =
    'a content ref

  let make (v : 'a) : 'a elem =
    ref (Root { rank = 0; value = v })

  let rec find (x : 'a elem) : 'a elem =
    match !x with
    | Root _ ->
        x
    | Link ({ parent = y } as link) ->
        let z = find y in
        if z != y then link.parent <- z;
        z

  let eq (x : 'a elem) (y : 'a elem) : bool =
    x == y || find x == find y

  let get (x : 'a elem) : 'a =
    let x = find x in
    match !x with
    | Root { value = v; _ } -> v
    | Link _ -> assert false

  let set (x : 'a elem) (v : 'a) : unit =
    let x = find x in
    match !x with
    | Root root -> root.value <- v
    | Link _ -> assert false

  let union (x : 'a elem) (y : 'a elem) : 'a elem =
    let x = find x
    and y = find y in
    if x == y then x else
    match !x, !y with
    | Root ({ rank = rx; _ } as rootx), Root { rank = ry; _ } ->
      if rx < ry then begin
        x := Link { parent = y };
        y
      end else if rx > ry then begin
        y := Link { parent = x };
        x
      end else begin
        y := Link { parent = x};
        rootx.rank <- rx + 1;
        x
      end
    | Root _, Link _
    | Link _, Root _
    | Link _, Link _ ->
        assert false

  let merge (f : 'a -> 'a -> 'a) (x : 'a elem) (y : 'a elem) : 'a elem =
    let x = find x
    and y = find y in
    if x == y then x else
      match !x, !y with
      | Root ({ rank = rx; value = vx } as rootx),
        Root ({ rank = ry; value = vy } as rooty) ->
        let v = f vx vy in
        if rx < ry then begin
          x := Link { parent = y };
          if v != vy then rooty.value <- v;
          y
        end else if rx > ry then begin
          y := Link { parent = x };
          if v != vx then rootx.value <- v;
          x
        end else begin
          y := Link { parent = x };
          rootx.rank <- rx + 1;
          if v != vx then rootx.value <- v;
          x
        end
    | Root _, Link _
    | Link _, Root _
    | Link _, Link _ ->
        assert false

end

(* --------------------------------------------------------- *)
(* Variables level and predefined constants                  *)

module Vl : sig
  type t

  val compare : t -> t -> int
  val equal   : t -> t -> bool
  val hash    : t -> int

  val public    : t
  val transient : t
  val secret    : t

  val is_public    : t -> bool
  val is_secret    : t -> bool
  val is_transient : t -> bool

  val constants   : t list
  val is_constant : t -> bool
  val is_uni      : t -> bool

  val fresh : ?name:string -> unit -> t

  val name : t -> string

  val to_string : t -> string
  val pp : Format.formatter -> t -> unit

end = struct
  type t = {
    name : string;
    uid : int;
  }

  let name t = t.name

  let uid = ref (-1)

  let fresh ?(name="?") _ =
    incr uid;
    { name; uid = !uid; }

  let public = fresh ~name:"public" ()
  let transient = fresh ~name:"transient" ()
  let secret = fresh ~name:"secret" ()

  let compare vl1 vl2 = vl1.uid - vl2.uid

  let equal vl1 vl2 = vl1.uid = vl2.uid

  let hash vl = vl.uid

  let is_uni vl = vl.name = "?"

  let to_string vl =
    if is_uni vl then vl.name ^ (string_of_int vl.uid)
    else vl.name

  let pp fmt vl =
    Format.fprintf fmt "%s" (to_string vl)

  let constants = [public; transient; secret]

  let is_constant vl = List.exists (equal vl) constants

  let is_public    vl = equal public vl
  let is_secret    vl = equal secret vl
  let is_transient vl = equal transient vl

end

module Hvl = Hashtbl.Make(Vl)
module Mvl = Map.Make(Vl)
module Svl = Set.Make(Vl)

let constants = Svl.of_list Vl.constants

(* --------------------------------------------------------- *)
(* Inequalities                                              *)

module Lvl : sig
  type t
  val vlevel : t -> Vl.t
  val successors : t -> t list
  val fresh : Vl.t -> t list -> t

  val equal : t -> t -> bool
  val le : t -> t -> bool

  (* Do not use this function until you are sure that the merge will not make the constraints inconsistant *)
  val merge : t -> t -> t

  exception Unsat of (Svl.t * t list * t * t)
  val add_le : t -> t -> unit
  val iter : (t -> unit) -> t -> unit

 (* val clear_successors : t -> unit *)

  (* Warning use this function only when you are sure to not create cycle *)
  val add_successors : t -> t list -> unit

  val pp   : Format.formatter -> t -> unit
  val pp_s : ?debug:bool -> Format.formatter -> t -> unit

  val is_public    : t -> bool
  val is_secret    : t -> bool
  val is_transient : t -> bool

  val simplify : tokeep:(t-> bool) -> t -> unit

end = struct

  type level =
    { vlevel : Vl.t; (* l *)
      succ   : t list;   (* l' \in succ => l <= l' *)
    }
  and t = level UnionFind.elem

  let repr (e:t) = UnionFind.find e

  let fresh vlevel succ = UnionFind.make { vlevel; succ }

  let vlevel (e:t) = (UnionFind.get e).vlevel
  let successors (e:t) = (UnionFind.get e).succ

  let is_public    (e:t) = Vl.is_public    (vlevel e)
  let is_transient (e:t) = Vl.is_transient (vlevel e)
  let is_secret    (e:t) = Vl.is_secret    (vlevel e)


  let visited = Hvl.create 97
  let clear_visited () = Hvl.clear visited
  let is_visited vl = Hvl.mem visited vl
  let set_visited vl = Hvl.add visited vl ()

  let equal (e1:t) (e2:t) = Vl.equal (vlevel e1) (vlevel e2)

  let le (e1:t) (e2:t) =
    let vl1 = vlevel e1 in
    let vl2 = vlevel e2 in
    if Vl.is_public vl1 || Vl.is_secret vl2 then true
    else begin
      clear_visited();
      let rec find e =
        let vl = vlevel e in
        Vl.equal vl vl2 ||
          (not (is_visited vl) && (set_visited vl; List.exists find (successors e))) in
      find e1
    end

  let iter (f : t -> unit) e =
    clear_visited ();
    let rec iter e =
      let vl = vlevel e in
      if not (is_visited vl) then
        (f e; set_visited vl; List.iter iter (successors e)) in
    iter e

  let path = Hvl.create 97
  let clear_path () = Hvl.clear path
  let add_path vl e = Hvl.add path vl (Some (repr e)); true
  let add_nopath vl = Hvl.add path vl None; false

  (* [between l l' = s ]
        forall l1 \in s, l <= l1 <= l' *)
  let between (e:t) (e':t) =
    clear_path();
    let vl' = vlevel e' in
    (* e <= e1 *)
    let rec find e1 =
      let vl1 = vlevel e1 in
      match Hvl.find path vl1 with
      | None -> false (* no path from e1 to e' *)
      | Some _ -> true (* e1 <= e' *)
      | exception Not_found ->
        if vl1 = vl' then  (* e <= e1 = e' *)
          add_path vl1 e1
        else
          let tests = List.map find (successors e1) in
          if List.exists (fun b -> b) tests then (* e1 <= s <= e' *)
            add_path vl1 e1
          else add_nopath vl1 in
     ignore (find e);
     Hvl.fold (fun _ e1 l -> match e1 with None -> l | Some e1 -> e1 :: l) path []

  let succ = Hvl.create 97
  let clear_succ () = Hvl.clear succ
  let add_succ vl e = Hvl.replace succ vl (UnionFind.find e)

  let merge (e1:t) (e2:t) =
    clear_succ ();
    let merge_level (l1:level) (l2:level) =
      (* (vl1, succ1) (vl2, succ2) *)
      let add e =
        let vl = vlevel e in
        if Vl.equal l1.vlevel vl || Vl.equal l2.vlevel vl then ()
        else add_succ vl e in
      List.iter add l1.succ;
      List.iter add l2.succ;
      let vlevel =
        if Vl.is_constant l2.vlevel ||
           Vl.is_uni l1.vlevel && not (Vl.is_uni l2.vlevel) then l2.vlevel
        else l1.vlevel in
      let succ =
        if Hvl.length succ = 1 then
          Hvl.fold (fun _ e s -> e :: s) succ []
        else (* remove secret *)
          Hvl.fold (fun vl e s -> if Vl.equal vl Vl.secret then s else e :: s) succ [] in
      { vlevel; succ } in
    UnionFind.merge merge_level e1 e2

 (* let clear_successors (e:t) =
    clear_succ ();
    let lvl = UnionFind.get e in
    List.iter (fun s -> add_succ (vlevel s) s) lvl.succ;
    UnionFind.set e { lvl with succ = Hvl.fold (fun _ e s -> e :: s) succ [] } *)

  let add_successors (e:t) succ =
    let lvl = UnionFind.get e in
    UnionFind.set e { lvl with succ = List.fold_left (fun ss s -> repr s :: ss) lvl.succ succ }

  exception Unsat of (Svl.t * t list * t * t)
  (* Add the constraint l1 <= l2 *)

  let add_le (l1:t) (l2:t) =
    if le l1 l2 then ()  (* constraint already present do nothing *)
    else
      match between l2 l1 with
      | [] -> (* no cycle, add the constraint *)
        let lvl = UnionFind.get l1 in
        let lvl = { lvl with succ = l2 :: lvl.succ } in
        UnionFind.set l1 lvl;
      | e :: es as ees -> (* cycle found *)
        (* Check that we do not merge two constants *)
        let cnst = Svl.inter (Svl.of_list (List.map vlevel ees)) constants in
        if (2 <= Svl.cardinal cnst) then raise (Unsat(cnst, ees, l1, l2));
        ignore (List.fold_left merge e es)

  let pp fmt l = Vl.pp fmt (vlevel l)

  let pp_s ?(debug=false) fmt l =
    let vl = vlevel l in
    let succ = successors l in
    let pp succ =
      Format.fprintf fmt "%a <= @[%a@],@ " Vl.pp vl
        (Utils.pp_list "@ " (fun fmt s -> Vl.pp fmt (vlevel s))) succ in
    if debug then pp succ
    else
      let succ =
        if Vl.is_public vl then [] else List.filter (fun s -> not (is_secret s)) succ in
      if succ <> [] then pp succ

  let simplify ~(tokeep:t -> bool) (l:t) =
    let long = true and short = false in
    let _R = Hvl.create 97 in
    let rec visite x =
      let vx = vlevel x in
      try Hvl.find _R vx
      with Not_found ->
        let _M : (t * bool) Hvl.t = Hvl.create 23 in
        let add_M z (ez, p) =
          let p' = p || (try snd (Hvl.find _M z) with Not_found -> short) in
          Hvl.replace _M z (ez, p') in
        let do_s y =
          let yin = tokeep y in
          Hvl.iter (if yin then (fun z (ez, _p) -> Hvl.replace _M z (ez,long))
                    else (fun z ep -> add_M z ep)) (visite y);
          if yin then add_M (vlevel y) (y, short) in
        List.iter do_s (successors x);
        Hvl.add _R vx _M;
        (* now clear the successor of x *)
        let succ =
          Hvl.fold (fun _ (s, p) succ -> if p = short then s :: succ else succ) _M [] in
        let lvl = UnionFind.get x in
        UnionFind.set x { lvl with succ };
        _M in
    ignore (visite l)

end

(* ----------------------------------------------------------- *)
(* paired types. Essentially a shorthand for adding inequalities *)
module VlPairs = struct
  type t = Lvl.t * Lvl.t

  let add_le (n1, s1) (n2, s2) =
    Lvl.add_le n1 n2; Lvl.add_le s1 s2
  let add_le_speculative s' (_, s) = Lvl.add_le s' s

  let equal (n1, s1) (n2, s2) =
    Lvl.equal n1 n2 && Lvl.equal s1 s2

  let normalise (l, _) = (l, l)
end


(* ----------------------------------------------------------- *)

module C : sig
  type constraints

  val init : unit -> constraints

  val public    : constraints -> Lvl.t
  val transient : constraints -> Lvl.t
  val secret    : constraints -> Lvl.t

  val fresh : ?name:string -> constraints -> Lvl.t

  val pp_debug : Format.formatter -> constraints -> unit
  val pp       : Format.formatter -> constraints -> unit

  val simplify : constraints -> unit
  val prune    : constraints -> Lvl.t list -> unit
  val optimize : constraints -> tomax:Lvl.t list -> tomin:Lvl.t list -> unit
  val clone    : constraints -> constraints -> (Lvl.t -> Lvl.t)
  val is_instance : (Lvl.t -> Lvl.t) -> constraints -> constraints -> bool

end = struct

  type constraints = {
    (* FIXME : repr is not needed it can be remove, it is useful only for printing *)
    repr      : Lvl.t Hvl.t;
    public    : Lvl.t;
    transient : Lvl.t;
    secret    : Lvl.t;
  }

  let public c = c.public
  let transient c = c.transient
  let secret c = c.secret

  let add_vl tbl vl successors =
    let l = Lvl.fresh vl successors in
    Hvl.add tbl vl l;
    l

  let init () =
    let repr = Hvl.create 257 in
    let secret    = add_vl repr Vl.secret    [] in
    let transient = add_vl repr Vl.transient [secret] in
    let public    = add_vl repr Vl.public    [transient] in
    { repr; public; transient; secret }

  let fresh ?name c =
    (* FIXME: can we remove secret if we do a special case for "add_le secret l" ?
       i.e. set l and all variable greater than l to secret *)
    let l = add_vl c.repr (Vl.fresh ?name ()) [c.secret] in
    Lvl.add_successors c.public [l];
    l

  let pp_debug fmt c =
    (* print equalities *)
    Format.fprintf fmt "@[<v>";
    Hvl.iter (fun vl l ->
        let vl' = Lvl.vlevel l in
        if not (Vl.equal vl vl') then Format.fprintf fmt "%a = %a@ " Vl.pp vl Vl.pp vl') c.repr;
    (* print inequalities *)
    Lvl.iter (Lvl.pp_s ~debug:true fmt) c.public;
    Format.fprintf fmt "@]"

  let pp fmt c =
    (* Do not print equalities or public <= l or l <= secret *)
    Format.fprintf fmt "@[";
    Lvl.iter (Lvl.pp_s ~debug:false fmt) c.public;
    Format.fprintf fmt "@]"

  (* [simplify c] simplify the graph by removing the transitive edge *)
  let simplify (c:constraints) =
    Lvl.simplify ~tokeep:(fun _ -> true) c.public

  let prune (c:constraints) (ltokeep: Lvl.t list) =
    let tokeep = Hvl.create 31 in
    List.iter (fun l -> Hvl.replace tokeep (Lvl.vlevel l) ()) (c.public :: c.transient :: c.secret :: ltokeep);
    Lvl.simplify ~tokeep:(fun l -> Hvl.mem tokeep (Lvl.vlevel l)) c.public

  type minmax =
    | Minimize
    | Maximize
    | MinMax

  (*
  let pp_minmax fmt = function
    | Maximize -> Format.fprintf fmt "Maximize"
    | MinMax   -> Format.fprintf fmt "MinMax"
    | Minimize -> Format.fprintf fmt "Minimize"
  *)

  let optimize (c:constraints) ~(tomax : Lvl.t list) ~(tomin : Lvl.t list) =
    let minmax = Hvl.create 97 in
    let add mm l =
      let vl = Lvl.vlevel l in
      match Hvl.find minmax vl with
      | mm' -> if mm <> mm' then Hvl.replace minmax vl MinMax
      | exception Not_found -> Hvl.add minmax vl mm in
    add MinMax (public c); add MinMax (transient c); add MinMax (secret c);
    List.iter (add Maximize) tomax; List.iter (add Minimize) tomin;

    let get_minmax l =
      try Hvl.find minmax (Lvl.vlevel l) with Not_found -> MinMax in

    let merge_minmax l s =
      let lmm = get_minmax l in
      let smm = get_minmax s in
      let mm = if lmm = smm then lmm else MinMax in
      add mm l; add mm s in


    let progress = ref true in
    while !progress do
      progress := false;
      (* try to maximize first *)
      Lvl.iter (fun l ->
          if get_minmax l = Maximize then
            match Lvl.successors l with
            | [s] ->
              progress := true;
              merge_minmax l s;
              ignore (Lvl.merge l s)
            | _ -> ()) (public c);
      if not !progress then
        begin
          (* Compute the table of predessors *)
          let pred = Hvl.create 97 in
          let get_pred l = try Hvl.find pred (Lvl.vlevel l) with Not_found -> Svl.empty in
          let add_pred p s = Hvl.replace pred (Lvl.vlevel s) (Svl.add (Lvl.vlevel p) (get_pred s)) in
          Lvl.iter (fun l -> List.iter (add_pred l) (Lvl.successors l)) (public c);
          (* minimize *)
          Lvl.iter (fun l ->
              if get_minmax l = Minimize then
                let p = get_pred l in
                if Svl.cardinal p = 1 then
                  let p = Hvl.find c.repr (Svl.choose p) in
                  progress := true;
                  merge_minmax p l;
                  ignore (Lvl.merge p l)) (public c);
        end;
      if !progress then simplify c
    done






 (* let norm (c:constraints) =
    Lvl.iter Lvl.clear_successors c.public *)

  (* clone c and add the constraints in c' *)
  let clone (c:constraints) (c':constraints) =
    let subst = Hvl.create 31 in
    let rec do_l l =
      let vl = Lvl.vlevel l in
      try Hvl.find subst vl
      with Not_found ->
        let successors = List.map do_l (Lvl.successors l) in
        let l =
          if Vl.is_public vl  then c'.public
          else if Vl.is_transient vl then c'.transient
          else if Vl.is_secret vl then c'.secret
          else begin
            assert (not (Vl.is_constant vl));
            add_vl c'.repr (Vl.fresh ~name:(Vl.name vl) ()) []
          end in
        Lvl.add_successors l successors;
        Hvl.add subst vl l;
        l in
    ignore (do_l c.public);
    do_l
    (* t | C *)

  let is_instance (rho : Lvl.t (* c *) -> Lvl.t (* cu *) ) _cu c =
    try
      Lvl.iter (fun l ->
          let lu = rho l in
          if List.for_all (fun s -> Lvl.le lu (* rho l*) (rho s)) (Lvl.successors l) then ()
          else raise Not_found) c.public;
      true
    with Not_found -> false

end

(*
let _ =
  try
  let c = C.init () in
  let pp s = Format.printf "%s@.%a@.@." s C.pp_debug c in
  pp "0";

  let l1 = C.fresh ~name:"l1" c in
  let l2 = C.fresh ~name:"l2" c in
  let l3 = C.fresh ~name:"l3" c in
  let l4 = C.fresh ~name:"l4" c in
  let l5 = C.fresh ~name:"l5" c in
  pp "1";

  Lvl.add_le l2 l1; pp "2";
  Lvl.add_le l2 l3; pp "3";
  Lvl.add_le l2 l4; pp "4";
  Lvl.add_le l3 l5; pp "5";
  Lvl.add_le l5 l2; pp "6";

  (* C.norm c; pp "6-norm"; *)

  Lvl.add_le l2 (C.public c); pp "8";

  with Lvl.Unsat _ -> Format.printf "Unsat@."

let _ =
  try
  let c = C.init () in
  let pp s = Format.printf "%s@.%a@.@." s C.pp_debug c in
  pp "0";

  let l1 = C.fresh ~name:"l1" c in
  let l2 = C.fresh ~name:"l2" c in
  let l3 = C.fresh ~name:"l3" c in
  let l4 = C.fresh ~name:"l4" c in
  let l5 = C.fresh ~name:"l5" c in
  let l6 = C.fresh ~name:"l6" c in
  pp "1";

  Lvl.add_le l2 l4; pp "2";
  Lvl.add_le l2 l3; pp "3";
  Lvl.add_le l2 l1; pp "4";
  Lvl.add_le l3 l5; pp "5";
  Lvl.add_le l1 l5; pp "6";
  Lvl.add_le l6 l3; pp "7";
  C.prune c [l6;l2;l1;l5];
  pp "prune";
  Format.printf "prune pp@.%a@.@." C.pp c;

  with Lvl.Unsat _ -> Format.printf "Unsat@."



Rajouter une info sur les levels qui dise que si l doit etre public
alors l1 doit etre <= transient.
On doit generaliser cela a un ensemble de level.

Si on fait un init_msf:
  Pour tout les registres on peut faire la chose suivante:
  soit l le niveau du registre r
    si l = secret || l = public on fait rien
    si l <= transient alors le nouveau type de r est public
    sinon on cree un nouveau level l' qui contient les contraintes:
       l' <= l
       l' = public => l <= transient
    si par la suite l'ajout de nouvelle contrainte force l' a etre public alors
    on doit rajouter la contrainte l = transient i.e l <= transient && transient <= l

  On doit pouvoir faire de meme pour les variables de stack, mais attention
  on doit etre capable de retrouver les ancients types (i.e l) si on fait un store.

  Une solution c'est d'avoir un flag dans MSF qui indique qu'on est sur de pas etre en mod speculatif.

Il faut ajouter ces contraintes:

lj' = pub   => lj <= trans
lj' = trans => false
lj' = sec   => lj = sec

lj = sec   => lj' = sec
lj = trans => lj' = pub
lj' = pub  => lj  = pub
*)
