open Datatypes
open FMapAVL
open FMapFacts
open Nat0
open Eqtype
open Seq
open Ssrbool
open Ssreflect
open Ssrfun

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

module type CmpType =
 sig
  val t : Equality.coq_type

  val cmp : Equality.sort -> Equality.sort -> comparison
 end

module MkOrdT =
 functor (T:CmpType) ->
 struct
  type t = Equality.sort

  (** val compare :
      Equality.sort -> Equality.sort -> Equality.sort OrderedType.coq_Compare **)

  let compare x y =
    let c = T.cmp x y in
    (match c with
     | Eq -> OrderedType.EQ
     | Lt -> OrderedType.LT
     | Gt -> OrderedType.GT)

  (** val eq_dec : Equality.sort -> Equality.sort -> bool **)

  let eq_dec x y =
    let _evar_0_ = true in
    let _evar_0_0 = false in
    let _evar_0_1 = false in
    (match T.cmp x y with
     | Eq -> _evar_0_
     | Lt -> _evar_0_0
     | Gt -> _evar_0_1)
 end

module type CompuEqDec =
 sig
  val t : Equality.coq_type

  val eq_dec : Equality.sort -> Equality.sort -> bool
 end

module type MAP =
 sig
  module K :
   CmpType

  type 'x t

  val empty : 'a1 t

  val get : 'a1 t -> Equality.sort -> 'a1 option

  val set : 'a1 t -> Equality.sort -> 'a1 -> 'a1 t

  val remove : 'a1 t -> Equality.sort -> 'a1 t

  val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t

  val mapi : (Equality.sort -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t

  val map2 :
    (Equality.sort -> 'a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2
    t -> 'a3 t

  val elements : 'a1 t -> (Equality.sort * 'a1) list

  val fold : (Equality.sort -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2

  val in_codom : Equality.coq_type -> Equality.sort -> Equality.sort t -> bool

  val elementsP :
    Equality.coq_type -> (Equality.sort * Equality.sort) -> Equality.sort t
    -> reflect
 end

module Mmake =
 functor (K__1:CmpType) ->
 struct
  module K = K__1

  module Ordered = MkOrdT(K__1)

  module Map = Make(Ordered)

  module Facts = WFacts_fun(Ordered)(Map)

  type 't t = 't Map.t

  (** val empty : 'a1 t **)

  let empty =
    Map.empty

  (** val get : 'a1 t -> Equality.sort -> 'a1 option **)

  let get m k =
    Map.find k m

  (** val set : 'a1 t -> Equality.sort -> 'a1 -> 'a1 Map.t **)

  let set m k v =
    Map.add k v m

  (** val remove : 'a1 t -> Equality.sort -> 'a1 Map.t **)

  let remove m k =
    Map.remove k m

  (** val map : ('a1 -> 'a2) -> 'a1 Map.t -> 'a2 Map.t **)

  let map f m =
    Map.map f m

  (** val mapi : (Map.key -> 'a1 -> 'a2) -> 'a1 Map.t -> 'a2 Map.t **)

  let mapi f m =
    Map.mapi f m

  (** val raw_map2 :
      (Equality.sort -> 'a1 option -> 'a2 option -> 'a3 option) -> 'a1
      Map.Raw.tree -> 'a2 Map.Raw.tree -> 'a3 Map.Raw.tree **)

  let raw_map2 f m1 m2 =
    Map.Raw.map2_opt (fun k d o -> f k (Some d) o)
      (Map.Raw.map_option (fun k d -> f k (Some d) None))
      (Map.Raw.map_option (fun k d' -> f k None (Some d'))) m1 m2

  (** val elements : 'a1 Map.t -> (Map.key * 'a1) list **)

  let elements m =
    Map.elements m

  (** val fold : (Map.key -> 'a1 -> 'a2 -> 'a2) -> 'a1 Map.t -> 'a2 -> 'a2 **)

  let fold f m i =
    Map.fold f m i

  (** val in_codom :
      Equality.coq_type -> Equality.sort -> Equality.sort t -> bool **)

  let in_codom t0 v m =
    fold (fun _ v' b -> (||) b (eq_op t0 v v')) m false

  (** val map2 :
      (Equality.sort -> 'a1 option -> 'a2 option -> 'a3 option) -> 'a1 t ->
      'a2 t -> 'a3 t **)

  let map2 f m1 m2 =
    raw_map2 f (Map.this m1) (Map.this m2)

  (** val elementsP :
      Equality.coq_type -> (Equality.sort * Equality.sort) -> Equality.sort t
      -> reflect **)

  let elementsP t0 kv m =
    ssr_have __
      (let _evar_0_ = fun _ _ -> ReflectT in
       let _evar_0_0 = fun _ _ -> ReflectF in
       (match Lazy.force
        (boolP
          (in_mem (Obj.magic kv)
            (mem (seq_predType (prod_eqType K__1.t t0))
              (Obj.magic Map.elements m)))) with
        | AltTrue -> _evar_0_ __
        | AltFalse -> _evar_0_0 __))
 end

module DMmake =
 functor (K:CmpType) ->
 functor (E:CompuEqDec) ->
 struct
  type 'p boxed = { box_t : Equality.sort; box_v : 'p }

  (** val box_t : 'a1 boxed -> Equality.sort **)

  let box_t b =
    b.box_t

  (** val box_v : 'a1 boxed -> 'a1 **)

  let box_v b =
    b.box_v

  (** val from_boxed : Equality.sort -> 'a1 boxed option -> 'a1 option **)

  let from_boxed k = function
  | Some b0 ->
    let { box_t = k'; box_v = v } = b0 in
    if E.eq_dec k' k then Some v else None
  | None -> None

  module Map = Mmake(K)

  type 'p t = 'p boxed Map.t

  (** val empty : 'a1 t **)

  let empty =
    Map.empty

  (** val get : 'a1 t -> Equality.sort -> 'a1 option **)

  let get m k =
    from_boxed k (Map.get m k)

  (** val set : 'a1 t -> Equality.sort -> 'a1 -> 'a1 boxed Map.Map.t **)

  let set m k v =
    Map.set m k { box_t = k; box_v = v }

  (** val map : (Equality.sort -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t **)

  let map f m =
    Map.map (fun b -> { box_t = (box_t b); box_v = (f (box_t b) (box_v b)) })
      m

  (** val map2 :
      (Equality.sort -> 'a1 option -> 'a2 option -> 'a3 option) -> 'a1 t ->
      'a2 t -> 'a3 t **)

  let map2 f m1 m2 =
    Map.map2 (fun k o1 o2 ->
      Option.map (fun x -> { box_t = k; box_v = x })
        (f k (from_boxed k o1) (from_boxed k o2))) m1 m2
 end

module MkMOrdT =
 functor (T:CmpType) ->
 struct
  type t = Equality.sort

  (** val compare : t -> t -> comparison **)

  let compare =
    T.cmp

  (** val eq_dec : t -> t -> bool **)

  let eq_dec x y =
    let _evar_0_ = fun _ -> true in
    let _evar_0_0 = fun _ -> false in
    (match eqP T.t x y with
     | ReflectT -> _evar_0_ __
     | ReflectF -> _evar_0_0 __)
 end

module Smake =
 functor (T:CmpType) ->
 struct
  module Ordered = MkMOrdT(T)

  module Raw =
   struct
    type elt = Equality.sort

    type tree =
    | Leaf
    | Node of Int.Z_as_Int.t * tree * Equality.sort * tree

    (** val empty : tree **)

    let empty =
      Leaf

    (** val is_empty : tree -> bool **)

    let is_empty = function
    | Leaf -> true
    | Node (_, _, _, _) -> false

    (** val mem : Equality.sort -> tree -> bool **)

    let rec mem x = function
    | Leaf -> false
    | Node (_, l, k, r) ->
      (match T.cmp x k with
       | Eq -> true
       | Lt -> mem x l
       | Gt -> mem x r)

    (** val min_elt : tree -> elt option **)

    let rec min_elt = function
    | Leaf -> None
    | Node (_, l, x, _) ->
      (match l with
       | Leaf -> Some x
       | Node (_, _, _, _) -> min_elt l)

    (** val max_elt : tree -> elt option **)

    let rec max_elt = function
    | Leaf -> None
    | Node (_, _, x, r) ->
      (match r with
       | Leaf -> Some x
       | Node (_, _, _, _) -> max_elt r)

    (** val choose : tree -> elt option **)

    let choose =
      min_elt

    (** val fold : (elt -> 'a1 -> 'a1) -> tree -> 'a1 -> 'a1 **)

    let rec fold f t0 base =
      match t0 with
      | Leaf -> base
      | Node (_, l, x, r) -> fold f r (f x (fold f l base))

    (** val elements_aux :
        Equality.sort list -> tree -> Equality.sort list **)

    let rec elements_aux acc = function
    | Leaf -> acc
    | Node (_, l, x, r) -> elements_aux (x :: (elements_aux acc r)) l

    (** val elements : tree -> Equality.sort list **)

    let elements =
      elements_aux []

    (** val rev_elements_aux :
        Equality.sort list -> tree -> Equality.sort list **)

    let rec rev_elements_aux acc = function
    | Leaf -> acc
    | Node (_, l, x, r) -> rev_elements_aux (x :: (rev_elements_aux acc l)) r

    (** val rev_elements : tree -> Equality.sort list **)

    let rev_elements =
      rev_elements_aux []

    (** val cardinal : tree -> nat **)

    let rec cardinal = function
    | Leaf -> O
    | Node (_, l, _, r) -> S (add (cardinal l) (cardinal r))

    (** val maxdepth : tree -> nat **)

    let rec maxdepth = function
    | Leaf -> O
    | Node (_, l, _, r) -> S (max (maxdepth l) (maxdepth r))

    (** val mindepth : tree -> nat **)

    let rec mindepth = function
    | Leaf -> O
    | Node (_, l, _, r) -> S (min (mindepth l) (mindepth r))

    (** val for_all : (elt -> bool) -> tree -> bool **)

    let rec for_all f = function
    | Leaf -> true
    | Node (_, l, x, r) ->
      if if f x then for_all f l else false then for_all f r else false

    (** val exists_ : (elt -> bool) -> tree -> bool **)

    let rec exists_ f = function
    | Leaf -> false
    | Node (_, l, x, r) ->
      if if f x then true else exists_ f l then true else exists_ f r

    type enumeration =
    | End
    | More of elt * tree * enumeration

    (** val cons : tree -> enumeration -> enumeration **)

    let rec cons s e =
      match s with
      | Leaf -> e
      | Node (_, l, x, r) -> cons l (More (x, r, e))

    (** val compare_more :
        Equality.sort -> (enumeration -> comparison) -> enumeration ->
        comparison **)

    let compare_more x1 cont = function
    | End -> Gt
    | More (x2, r2, e3) ->
      (match T.cmp x1 x2 with
       | Eq -> cont (cons r2 e3)
       | x -> x)

    (** val compare_cont :
        tree -> (enumeration -> comparison) -> enumeration -> comparison **)

    let rec compare_cont s1 cont e2 =
      match s1 with
      | Leaf -> cont e2
      | Node (_, l1, x1, r1) ->
        compare_cont l1 (compare_more x1 (compare_cont r1 cont)) e2

    (** val compare_end : enumeration -> comparison **)

    let compare_end = function
    | End -> Eq
    | More (_, _, _) -> Lt

    (** val compare : tree -> tree -> comparison **)

    let compare s1 s2 =
      compare_cont s1 compare_end (cons s2 End)

    (** val equal : tree -> tree -> bool **)

    let equal s1 s2 =
      match compare s1 s2 with
      | Eq -> true
      | _ -> false

    (** val subsetl : (tree -> bool) -> Equality.sort -> tree -> bool **)

    let rec subsetl subset_l1 x1 s2 = match s2 with
    | Leaf -> false
    | Node (_, l2, x2, r2) ->
      (match T.cmp x1 x2 with
       | Eq -> subset_l1 l2
       | Lt -> subsetl subset_l1 x1 l2
       | Gt -> if mem x1 r2 then subset_l1 s2 else false)

    (** val subsetr : (tree -> bool) -> Equality.sort -> tree -> bool **)

    let rec subsetr subset_r1 x1 s2 = match s2 with
    | Leaf -> false
    | Node (_, l2, x2, r2) ->
      (match T.cmp x1 x2 with
       | Eq -> subset_r1 r2
       | Lt -> if mem x1 l2 then subset_r1 s2 else false
       | Gt -> subsetr subset_r1 x1 r2)

    (** val subset : tree -> tree -> bool **)

    let rec subset s1 s2 =
      match s1 with
      | Leaf -> true
      | Node (_, l1, x1, r1) ->
        (match s2 with
         | Leaf -> false
         | Node (_, l2, x2, r2) ->
           (match T.cmp x1 x2 with
            | Eq -> if subset l1 l2 then subset r1 r2 else false
            | Lt -> if subsetl (subset l1) x1 l2 then subset r1 s2 else false
            | Gt -> if subsetr (subset r1) x1 r2 then subset l1 s2 else false))

    type t = tree

    (** val height : t -> Int.Z_as_Int.t **)

    let height = function
    | Leaf -> Int.Z_as_Int._0
    | Node (h, _, _, _) -> h

    (** val singleton : Equality.sort -> tree **)

    let singleton x =
      Node (Int.Z_as_Int._1, Leaf, x, Leaf)

    (** val create : t -> Equality.sort -> t -> tree **)

    let create l x r =
      Node
        ((Int.Z_as_Int.add (Int.Z_as_Int.max (height l) (height r))
           Int.Z_as_Int._1), l, x, r)

    (** val assert_false : t -> Equality.sort -> t -> tree **)

    let assert_false =
      create

    (** val bal : t -> Equality.sort -> t -> tree **)

    let bal l x r =
      let hl = height l in
      let hr = height r in
      if Int.Z_as_Int.ltb (Int.Z_as_Int.add hr Int.Z_as_Int._2) hl
      then (match l with
            | Leaf -> assert_false l x r
            | Node (_, ll, lx, lr) ->
              if Int.Z_as_Int.leb (height lr) (height ll)
              then create ll lx (create lr x r)
              else (match lr with
                    | Leaf -> assert_false l x r
                    | Node (_, lrl, lrx, lrr) ->
                      create (create ll lx lrl) lrx (create lrr x r)))
      else if Int.Z_as_Int.ltb (Int.Z_as_Int.add hl Int.Z_as_Int._2) hr
           then (match r with
                 | Leaf -> assert_false l x r
                 | Node (_, rl, rx, rr) ->
                   if Int.Z_as_Int.leb (height rl) (height rr)
                   then create (create l x rl) rx rr
                   else (match rl with
                         | Leaf -> assert_false l x r
                         | Node (_, rll, rlx, rlr) ->
                           create (create l x rll) rlx (create rlr rx rr)))
           else create l x r

    (** val add : Equality.sort -> tree -> tree **)

    let rec add x = function
    | Leaf -> Node (Int.Z_as_Int._1, Leaf, x, Leaf)
    | Node (h, l, y, r) ->
      (match T.cmp x y with
       | Eq -> Node (h, l, y, r)
       | Lt -> bal (add x l) y r
       | Gt -> bal l y (add x r))

    (** val join : tree -> elt -> t -> t **)

    let rec join l = match l with
    | Leaf -> add
    | Node (lh, ll, lx, lr) ->
      (fun x ->
        let rec join_aux r = match r with
        | Leaf -> add x l
        | Node (rh, rl, rx, rr) ->
          if Int.Z_as_Int.ltb (Int.Z_as_Int.add rh Int.Z_as_Int._2) lh
          then bal ll lx (join lr x r)
          else if Int.Z_as_Int.ltb (Int.Z_as_Int.add lh Int.Z_as_Int._2) rh
               then bal (join_aux rl) rx rr
               else create l x r
        in join_aux)

    (** val remove_min : tree -> elt -> t -> t * elt **)

    let rec remove_min l x r =
      match l with
      | Leaf -> (r, x)
      | Node (_, ll, lx, lr) ->
        let (l', m) = remove_min ll lx lr in ((bal l' x r), m)

    (** val merge : tree -> tree -> tree **)

    let merge s1 s2 =
      match s1 with
      | Leaf -> s2
      | Node (_, _, _, _) ->
        (match s2 with
         | Leaf -> s1
         | Node (_, l2, x2, r2) ->
           let (s2', m) = remove_min l2 x2 r2 in bal s1 m s2')

    (** val remove : Equality.sort -> tree -> tree **)

    let rec remove x = function
    | Leaf -> Leaf
    | Node (_, l, y, r) ->
      (match T.cmp x y with
       | Eq -> merge l r
       | Lt -> bal (remove x l) y r
       | Gt -> bal l y (remove x r))

    (** val concat : tree -> tree -> tree **)

    let concat s1 s2 =
      match s1 with
      | Leaf -> s2
      | Node (_, _, _, _) ->
        (match s2 with
         | Leaf -> s1
         | Node (_, l2, x2, r2) ->
           let (s2', m) = remove_min l2 x2 r2 in join s1 m s2')

    type triple = { t_left : t; t_in : bool; t_right : t }

    (** val t_left : triple -> t **)

    let t_left t0 =
      t0.t_left

    (** val t_in : triple -> bool **)

    let t_in t0 =
      t0.t_in

    (** val t_right : triple -> t **)

    let t_right t0 =
      t0.t_right

    (** val split : Equality.sort -> tree -> triple **)

    let rec split x = function
    | Leaf -> { t_left = Leaf; t_in = false; t_right = Leaf }
    | Node (_, l, y, r) ->
      (match T.cmp x y with
       | Eq -> { t_left = l; t_in = true; t_right = r }
       | Lt ->
         let { t_left = ll; t_in = b; t_right = rl } = split x l in
         { t_left = ll; t_in = b; t_right = (join rl y r) }
       | Gt ->
         let { t_left = rl; t_in = b; t_right = rr } = split x r in
         { t_left = (join l y rl); t_in = b; t_right = rr })

    (** val inter : tree -> tree -> tree **)

    let rec inter s1 s2 =
      match s1 with
      | Leaf -> Leaf
      | Node (_, l1, x1, r1) ->
        (match s2 with
         | Leaf -> Leaf
         | Node (_, _, _, _) ->
           let { t_left = l2'; t_in = pres; t_right = r2' } = split x1 s2 in
           if pres
           then join (inter l1 l2') x1 (inter r1 r2')
           else concat (inter l1 l2') (inter r1 r2'))

    (** val diff : tree -> tree -> tree **)

    let rec diff s1 s2 =
      match s1 with
      | Leaf -> Leaf
      | Node (_, l1, x1, r1) ->
        (match s2 with
         | Leaf -> s1
         | Node (_, _, _, _) ->
           let { t_left = l2'; t_in = pres; t_right = r2' } = split x1 s2 in
           if pres
           then concat (diff l1 l2') (diff r1 r2')
           else join (diff l1 l2') x1 (diff r1 r2'))

    (** val union : tree -> tree -> tree **)

    let rec union s1 s2 =
      match s1 with
      | Leaf -> s2
      | Node (_, l1, x1, r1) ->
        (match s2 with
         | Leaf -> s1
         | Node (_, _, _, _) ->
           let { t_left = l2'; t_in = _; t_right = r2' } = split x1 s2 in
           join (union l1 l2') x1 (union r1 r2'))

    (** val filter : (elt -> bool) -> tree -> tree **)

    let rec filter f = function
    | Leaf -> Leaf
    | Node (_, l, x, r) ->
      let l' = filter f l in
      let r' = filter f r in if f x then join l' x r' else concat l' r'

    (** val partition : (elt -> bool) -> t -> t * t **)

    let rec partition f = function
    | Leaf -> (Leaf, Leaf)
    | Node (_, l, x, r) ->
      let (l1, l2) = partition f l in
      let (r1, r2) = partition f r in
      if f x
      then ((join l1 x r1), (concat l2 r2))
      else ((concat l1 r1), (join l2 x r2))

    (** val ltb_tree : Equality.sort -> tree -> bool **)

    let rec ltb_tree x = function
    | Leaf -> true
    | Node (_, l, y, r) ->
      (match T.cmp x y with
       | Gt -> (&&) (ltb_tree x l) (ltb_tree x r)
       | _ -> false)

    (** val gtb_tree : Equality.sort -> tree -> bool **)

    let rec gtb_tree x = function
    | Leaf -> true
    | Node (_, l, y, r) ->
      (match T.cmp x y with
       | Lt -> (&&) (gtb_tree x l) (gtb_tree x r)
       | _ -> false)

    (** val isok : tree -> bool **)

    let rec isok = function
    | Leaf -> true
    | Node (_, l, x, r) ->
      (&&) ((&&) ((&&) (isok l) (isok r)) (ltb_tree x l)) (gtb_tree x r)

    module MX =
     struct
      module OrderTac =
       struct
        module OTF =
         struct
          type t = Equality.sort

          (** val compare : Equality.sort -> Equality.sort -> comparison **)

          let compare =
            T.cmp

          (** val eq_dec : Equality.sort -> Equality.sort -> bool **)

          let eq_dec =
            Ordered.eq_dec
         end

        module TO =
         struct
          type t = Equality.sort

          (** val compare : Equality.sort -> Equality.sort -> comparison **)

          let compare =
            T.cmp

          (** val eq_dec : Equality.sort -> Equality.sort -> bool **)

          let eq_dec =
            OTF.eq_dec
         end
       end

      (** val eq_dec : Equality.sort -> Equality.sort -> bool **)

      let eq_dec =
        Ordered.eq_dec

      (** val lt_dec : Equality.sort -> Equality.sort -> bool **)

      let lt_dec x y =
        let c = coq_CompSpec2Type x y (T.cmp x y) in
        (match c with
         | CompLtT -> true
         | _ -> false)

      (** val eqb : Equality.sort -> Equality.sort -> bool **)

      let eqb x y =
        if eq_dec x y then true else false
     end

    type coq_R_min_elt =
    | R_min_elt_0 of tree
    | R_min_elt_1 of tree * Int.Z_as_Int.t * tree * Equality.sort * tree
    | R_min_elt_2 of tree * Int.Z_as_Int.t * tree * Equality.sort * tree
       * Int.Z_as_Int.t * tree * Equality.sort * tree * elt option
       * coq_R_min_elt

    type coq_R_max_elt =
    | R_max_elt_0 of tree
    | R_max_elt_1 of tree * Int.Z_as_Int.t * tree * Equality.sort * tree
    | R_max_elt_2 of tree * Int.Z_as_Int.t * tree * Equality.sort * tree
       * Int.Z_as_Int.t * tree * Equality.sort * tree * elt option
       * coq_R_max_elt

    module L =
     struct
      module MO =
       struct
        module OrderTac =
         struct
          module OTF =
           struct
            type t = Equality.sort

            (** val compare : Equality.sort -> Equality.sort -> comparison **)

            let compare =
              T.cmp

            (** val eq_dec : Equality.sort -> Equality.sort -> bool **)

            let eq_dec =
              Ordered.eq_dec
           end

          module TO =
           struct
            type t = Equality.sort

            (** val compare : Equality.sort -> Equality.sort -> comparison **)

            let compare =
              T.cmp

            (** val eq_dec : Equality.sort -> Equality.sort -> bool **)

            let eq_dec =
              OTF.eq_dec
           end
         end

        (** val eq_dec : Equality.sort -> Equality.sort -> bool **)

        let eq_dec =
          Ordered.eq_dec

        (** val lt_dec : Equality.sort -> Equality.sort -> bool **)

        let lt_dec x y =
          let c = coq_CompSpec2Type x y (T.cmp x y) in
          (match c with
           | CompLtT -> true
           | _ -> false)

        (** val eqb : Equality.sort -> Equality.sort -> bool **)

        let eqb x y =
          if eq_dec x y then true else false
       end
     end

    (** val flatten_e : enumeration -> elt list **)

    let rec flatten_e = function
    | End -> []
    | More (x, t0, r) -> x :: (app (elements t0) (flatten_e r))

    type coq_R_bal =
    | R_bal_0 of t * Equality.sort * t
    | R_bal_1 of t * Equality.sort * t * Int.Z_as_Int.t * tree
       * Equality.sort * tree
    | R_bal_2 of t * Equality.sort * t * Int.Z_as_Int.t * tree
       * Equality.sort * tree
    | R_bal_3 of t * Equality.sort * t * Int.Z_as_Int.t * tree
       * Equality.sort * tree * Int.Z_as_Int.t * tree * Equality.sort * 
       tree
    | R_bal_4 of t * Equality.sort * t
    | R_bal_5 of t * Equality.sort * t * Int.Z_as_Int.t * tree
       * Equality.sort * tree
    | R_bal_6 of t * Equality.sort * t * Int.Z_as_Int.t * tree
       * Equality.sort * tree
    | R_bal_7 of t * Equality.sort * t * Int.Z_as_Int.t * tree
       * Equality.sort * tree * Int.Z_as_Int.t * tree * Equality.sort * 
       tree
    | R_bal_8 of t * Equality.sort * t

    type coq_R_remove_min =
    | R_remove_min_0 of tree * elt * t
    | R_remove_min_1 of tree * elt * t * Int.Z_as_Int.t * tree
       * Equality.sort * tree * (t * elt) * coq_R_remove_min * t * elt

    type coq_R_merge =
    | R_merge_0 of tree * tree
    | R_merge_1 of tree * tree * Int.Z_as_Int.t * tree * Equality.sort * tree
    | R_merge_2 of tree * tree * Int.Z_as_Int.t * tree * Equality.sort * 
       tree * Int.Z_as_Int.t * tree * Equality.sort * tree * t * elt

    type coq_R_concat =
    | R_concat_0 of tree * tree
    | R_concat_1 of tree * tree * Int.Z_as_Int.t * tree * Equality.sort
       * tree
    | R_concat_2 of tree * tree * Int.Z_as_Int.t * tree * Equality.sort
       * tree * Int.Z_as_Int.t * tree * Equality.sort * tree * t * elt

    type coq_R_inter =
    | R_inter_0 of tree * tree
    | R_inter_1 of tree * tree * Int.Z_as_Int.t * tree * Equality.sort * tree
    | R_inter_2 of tree * tree * Int.Z_as_Int.t * tree * Equality.sort * 
       tree * Int.Z_as_Int.t * tree * Equality.sort * tree * t * bool * 
       t * tree * coq_R_inter * tree * coq_R_inter
    | R_inter_3 of tree * tree * Int.Z_as_Int.t * tree * Equality.sort * 
       tree * Int.Z_as_Int.t * tree * Equality.sort * tree * t * bool * 
       t * tree * coq_R_inter * tree * coq_R_inter

    type coq_R_diff =
    | R_diff_0 of tree * tree
    | R_diff_1 of tree * tree * Int.Z_as_Int.t * tree * Equality.sort * tree
    | R_diff_2 of tree * tree * Int.Z_as_Int.t * tree * Equality.sort * 
       tree * Int.Z_as_Int.t * tree * Equality.sort * tree * t * bool * 
       t * tree * coq_R_diff * tree * coq_R_diff
    | R_diff_3 of tree * tree * Int.Z_as_Int.t * tree * Equality.sort * 
       tree * Int.Z_as_Int.t * tree * Equality.sort * tree * t * bool * 
       t * tree * coq_R_diff * tree * coq_R_diff

    type coq_R_union =
    | R_union_0 of tree * tree
    | R_union_1 of tree * tree * Int.Z_as_Int.t * tree * Equality.sort * tree
    | R_union_2 of tree * tree * Int.Z_as_Int.t * tree * Equality.sort * 
       tree * Int.Z_as_Int.t * tree * Equality.sort * tree * t * bool * 
       t * tree * coq_R_union * tree * coq_R_union
   end

  module E =
   struct
    type t = Equality.sort

    (** val compare : Equality.sort -> Equality.sort -> comparison **)

    let compare =
      T.cmp

    (** val eq_dec : Equality.sort -> Equality.sort -> bool **)

    let eq_dec =
      Ordered.eq_dec
   end

  type elt = Equality.sort

  type t_ =
    Raw.t
    (* singleton inductive, whose constructor was Mkt *)

  (** val this : t_ -> Raw.t **)

  let this t0 =
    t0

  type t = t_

  (** val mem : elt -> t -> bool **)

  let mem x s =
    Raw.mem x (this s)

  (** val add : elt -> t -> t **)

  let add x s =
    Raw.add x (this s)

  (** val remove : elt -> t -> t **)

  let remove x s =
    Raw.remove x (this s)

  (** val singleton : elt -> t **)

  let singleton x =
    Raw.singleton x

  (** val union : t -> t -> t **)

  let union s s' =
    Raw.union (this s) (this s')

  (** val inter : t -> t -> t **)

  let inter s s' =
    Raw.inter (this s) (this s')

  (** val diff : t -> t -> t **)

  let diff s s' =
    Raw.diff (this s) (this s')

  (** val equal : t -> t -> bool **)

  let equal s s' =
    Raw.equal (this s) (this s')

  (** val subset : t -> t -> bool **)

  let subset s s' =
    Raw.subset (this s) (this s')

  (** val empty : t **)

  let empty =
    Raw.empty

  (** val is_empty : t -> bool **)

  let is_empty s =
    Raw.is_empty (this s)

  (** val elements : t -> elt list **)

  let elements s =
    Raw.elements (this s)

  (** val choose : t -> elt option **)

  let choose s =
    Raw.choose (this s)

  (** val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1 **)

  let fold f s =
    Raw.fold f (this s)

  (** val cardinal : t -> nat **)

  let cardinal s =
    Raw.cardinal (this s)

  (** val filter : (elt -> bool) -> t -> t **)

  let filter f s =
    Raw.filter f (this s)

  (** val for_all : (elt -> bool) -> t -> bool **)

  let for_all f s =
    Raw.for_all f (this s)

  (** val exists_ : (elt -> bool) -> t -> bool **)

  let exists_ f s =
    Raw.exists_ f (this s)

  (** val partition : (elt -> bool) -> t -> t * t **)

  let partition f s =
    let p = Raw.partition f (this s) in ((fst p), (snd p))

  (** val eq_dec : t -> t -> bool **)

  let eq_dec s0 s'0 =
    let b = Raw.equal s0 s'0 in if b then true else false

  (** val compare : t -> t -> comparison **)

  let compare s s' =
    Raw.compare (this s) (this s')

  (** val min_elt : t -> elt option **)

  let min_elt s =
    Raw.min_elt (this s)

  (** val max_elt : t -> elt option **)

  let max_elt s =
    Raw.max_elt (this s)
 end
