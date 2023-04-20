require import AllCore SmtMap List.
(*---*) import CoreMap.

require import JUtils.

(*-------------------------------------------------------------------- *)

abstract theory MonoArray.

  type elem.
  op dfl : elem.

  op size: int.

  axiom ge0_size : 0 <= size.

  type t.

  op "_.[_]"  : t -> int -> elem.

  op init : (int -> elem) -> t.

  axiom get_out (t:t) i : !(0 <= i < size) => t.[i] = dfl.

  axiom initE (f:int -> elem) i :
    (init f).[i] = if 0 <= i < size then f i else dfl.

  axiom ext_eq (t1 t2: t) :
    (forall x, 0 <= x < size => t1.[x] = t2.[x]) =>
    t1 = t2.

  lemma tP (t1 t2: t) :
    t1 = t2 <=> forall i, 0 <= i < size => t1.[i] = t2.[i].
  proof. by move=> />;apply ext_eq. qed.

  lemma init_ext (f1 f2: int -> elem):
    (forall x, 0 <= x < size => f1 x = f2 x) =>
    init f1 = init f2.
  proof. by move=> h;apply ext_eq => i hi;rewrite !initE hi h. qed.

  (* -------------------------------------------------------------------- *)
  lemma initiE (f:int -> elem) i : 0 <= i < size => (init f).[i] = f i.
  proof. by move=> hi;rewrite initE hi. qed.

  hint simplify initiE.
  (* -------------------------------------------------------------------- *)
  op "_.[_<-_]" (t:t) (i:int) (e:elem) =
    init (fun j => if j = i then e else t.[j])
  axiomatized by setE.

  lemma get_set_if (t:t) (i j :int) (a:elem) :
    t.[i <- a].[j] = if 0 <= i < size /\ j = i then a else t.[j].
  proof.
    rewrite setE initE /=; smt (get_out).
  qed.

  lemma get_setE (t:t) (x y:int) (a:elem) :
    0 <= x < size => t.[x<-a].[y] = if y = x then a else t.[y].
  proof. by move=> hx;rewrite get_set_if hx. qed.

  lemma nosmt set_eqiE (t : t) x y a :
    0 <= x < size => y = x => t.[x <- a].[y] = a.
  proof. by move=> h1 ->;rewrite get_setE. qed.

  lemma nosmt set_neqiE (t : t) x y a :
    y <> x => t.[x <- a].[y] = t.[y].
  proof. by rewrite get_set_if => /neqF ->. qed.

  hint simplify (set_eqiE, set_neqiE).

  lemma set_out (i : int) (e : elem) (t : t):
    ! (0 <= i < size) => t.[i <- e] = t.
  proof.
    by move=> hi; apply ext_eq => j hj; rewrite get_set_if hi.  
  qed.

  lemma set_neg (i : int) (e : elem) (t : t):
    i < 0 => t.[i<- e] = t.
  proof. move=> hi;apply set_out => /#. qed.

  lemma set_above (i : int) (e : elem) (t : t):
    size <= i => t.[i <- e] = t.
  proof. move=> hi;apply set_out => /#. qed.

  lemma set_set_if (t : t) (k k' : int) (x x' : elem):
       t.[k <- x].[k' <- x']
    =  if   k = k'
       then t.[k' <- x']
       else t.[k' <- x'].[k <- x].
  proof.
    apply ext_eq => i hi;case (k = k') => [<<- | neqk];rewrite !get_set_if /#.
  qed.

  lemma set_set_eq (t : t) (k : int) (x x' : elem):
    t.[k <- x].[k <- x'] = t.[k <- x'].
  proof. by rewrite set_set_if. qed.

  lemma set_set_eq_s (t : t) (k1 k2 : int) (x x' : elem):
    k1 = k2 => t.[k1 <- x].[k2 <- x'] = t.[k2 <- x'].
  proof. move=> ->; apply set_set_eq. qed.

  hint simplify set_out.

  lemma set_set_swap (t : t) (k k' : int) (x x' : elem):
    k <> k' => t.[k <- x].[k' <- x'] = t.[k' <- x'].[k <- x].
  proof. by rewrite set_set_if => ->. qed.

  lemma set_notmod (t:t) i : t.[i <- t.[i]] = t.
  proof.
    by apply ext_eq => j hj; rewrite get_set_if; case: (0 <= i < size /\ j = i).
  qed.

  (* -------------------------------------------------------------------- *)
  op of_list (l:elem list) =
    init (fun i => nth dfl l i)
  axiomatized by of_listE.

  op to_list (t:t) =
    mkseq (fun i => t.[i]) size
  axiomatized by to_listE.

  lemma size_to_list (t:t): size (to_list t) = size.
  proof. rewrite to_listE size_mkseq /max; smt (ge0_size). qed.

  lemma get_of_list (l:elem list) i : 0 <= i < size =>
    (of_list l).[i] = nth dfl l i.
  proof. by move=> hi;rewrite of_listE initiE. qed.

  lemma get_to_list (t : t) i : nth dfl (to_list t) i = t.[i].
  proof.
    rewrite to_listE nth_mkseq_if; case:(0 <= i < size) => hi //.
    rewrite get_out //.
  qed.

  lemma of_listK (l : elem list) : size l = size =>
    to_list (of_list l) = l.
  proof.
    move=> h; apply (eq_from_nth dfl); 1:by rewrite size_to_list h.
    move=> i; rewrite size_to_list => hi.
    by rewrite get_to_list // get_of_list.
  qed.

  lemma to_listK : cancel to_list of_list.
  proof.
    move=> t; apply ext_eq => i hi.
    by rewrite get_of_list // get_to_list.
  qed.

  lemma to_list_inj : injective to_list.
  proof. by apply/(can_inj _ _ to_listK). qed.

  hint simplify (get_of_list, get_to_list, size_to_list)@0.
  hint simplify [reduce] to_listK@0.
(*  hint simplify [reduce] to_listE@1. *)

  lemma init_of_list f : init f = of_list (map f (iota_ 0 size)).
  proof.
    apply tP => i hi;rewrite get_of_list // (nth_map 0) 1:size_iota 1:/#.
    by rewrite nth_iota // initiE.
  qed.

  lemma of_listW (p : elem -> bool) (xs : elem list) :
        all p xs
     => size <= size xs
     => forall (i : int), 0 <= i < size => p (of_list xs).[i].
  proof.
  move=> pxs ge128_sz_xs i rg_i; rewrite get_of_list //.
  by move/allP: pxs; apply; rewrite mem_nth /#.
  qed.

  (* -------------------------------------------------------------------- *)
  op create (a:elem) = init (fun (i:int) => a).

  lemma createiE (a:elem) i : 0 <= i < size => (create a).[i] = a.
  proof. by apply initiE. qed.

  lemma createL (a:elem) : create a = of_list (map (fun i => a) (iota_ 0 size)).
  proof. by rewrite /create init_of_list. qed.

  hint simplify createiE @0.

  (* -------------------------------------------------------------------- *)
  op map (f: elem -> elem) (t:t) : t =
     init (fun i => f t.[i])
  axiomatized by mapE.

  lemma mapiE f t i : 0 <= i < size => (map f t).[i] = f t.[i].
  proof. by rewrite mapE;apply initiE. qed.

  lemma map_of_list f ws :
    map f (of_list ws) = of_list (mapN f dfl ws size).
  proof.
    by apply tP => i hi; rewrite mapiE // !get_of_list // nth_mapN.
  qed.

  lemma map_to_list f t :
    map f t = of_list (map f (to_list t)).
  proof. by rewrite to_listE mapE /= -map_comp // init_of_list. qed.

  hint simplify (mapiE, map_of_list)@0.
(*  hint simplify map_to_list@1. *)

  (* -------------------------------------------------------------------- *)
  op map2 (f: elem -> elem -> elem) (t1 t2:t) : t =
    init (fun i => f t1.[i] t2.[i])
  axiomatized by map2E.

  lemma map2iE f t1 t2 i : 0 <= i < size => (map2 f t1 t2).[i] = f t1.[i] t2.[i].
  proof. by rewrite map2E;apply initiE. qed.

  lemma map2_of_list f ws1 ws2 :
    map2 f (of_list ws1) (of_list ws2) = of_list (mapN2 f dfl dfl ws1 ws2 size).
  proof.
    by apply tP => i hi; rewrite map2iE // !get_of_list // nth_mapN2.
  qed.

  lemma map2_to_list f t1 t2 :
    map2 f t1 t2 = of_list (map2 f (to_list t1) (to_list t2)).
  proof.
    rewrite to_listE map2E map2_zip init_of_list /=;congr.
    apply (eq_from_nth dfl).
    + rewrite !size_map size_zip !size_map StdOrder.IntOrder.minrE /=. 
      smt (size_iota ge0_size).
    move=> i; rewrite size_map => hi.
    rewrite (nth_map 0) 1:// (nth_map (dfl,dfl)).
    + rewrite size_zip StdOrder.IntOrder.minrE /= !size_map.
      smt (size_iota ge0_size).
    rewrite /= nth_zip ?size_map //=; 1: smt (size_iota ge0_size).
    rewrite !(nth_map 0) // !nth_iota //; smt (ge0_size size_iota).
  qed.

  hint simplify (map2iE, map2_of_list)@0.
(*  hint simplify (map2_to_list)@1. *)

  (* -------------------------------------------------------------------- *)
  op all_eq (t1 t2: t) =
    all (fun x => t1.[x] = t2.[x]) (iotared 0 size).

  lemma all_eq_eq (t1 t2: t) : all_eq t1 t2 => t1 = t2.
  proof.
    by move=> /allP h; apply ext_eq => x /mem_range hx; apply h; rewrite iotaredE.
  qed.

  lemma all_eqP (t1 t2: t) : all_eq t1 t2 <=> t1 = t2.
  proof.
    split; 1:by apply all_eq_eq.
    by move=> ->;apply /allP.
  qed.

  (* -------------------------------------------------------------------- *)
  op fill (f : int -> elem) (k len : int) (t : t) =
    init (fun i => if k <= i < k + len then f i else t.[i])
  axiomatized by fillE.

  lemma filliE (f : int -> elem) (k len:int) (t : t)  i : 0 <= i < size =>
    (fill f k len t).[i] = if k <= i < k + len then f i else t.[i].
  proof. by move=> hi;rewrite fillE initiE. qed.

  hint simplify filliE.

  (* -------------------------------------------------------------------- *)
  op sub (t: t) k len = mkseq (fun (i:int) => t.[k+i]) len.

  lemma size_sub t k len : 0 <= len => size (sub t k len) = len.
  proof. move=> hl; rewrite size_mkseq /max /#. qed.

  lemma nth_sub (t : t) k len i : 0 <= i < len =>
    nth dfl (sub t k len) i = t.[k + i].
  proof. by move=> h0i; rewrite nth_mkseq. qed.

end MonoArray.

abstract theory PolyArray.

  op size: int.

  axiom ge0_size : 0 <= size.

  type 'a t.

  op "_.[_]" : 'a t -> int -> 'a.

  op init : (int -> 'a) -> 'a t.

  axiom get_out (t:'a t) i : !(0 <= i < size) => t.[i] = witness.

  axiom initE (f:int -> 'a) i :
    (init f).[i] = if 0 <= i < size then f i else witness.

  axiom ext_eq (t1 t2: 'a t) :
    (forall x, 0 <= x < size => t1.[x] = t2.[x]) =>
    t1 = t2.

  lemma tP (t1 t2: 'a t) :
    t1 = t2 <=> forall i, 0 <= i < size => t1.[i] = t2.[i].
  proof. by move=> />;apply ext_eq. qed.

  (* -------------------------------------------------------------------- *)
  lemma initiE (f:int -> 'a) i : 0 <= i < size => (init f).[i] = f i.
  proof. by move=> hi;rewrite initE hi. qed.

  hint simplify initiE.

  (* -------------------------------------------------------------------- *)
  op "_.[_<-_]" (t:'a t) (i:int) (e:'a) =
    init (fun j => if j = i then e else t.[j])
  axiomatized by setE.

  lemma get_set_if (t:'a t) (i j :int) (a:'a) :
    t.[i <- a].[j] = if 0 <= i < size /\ j = i then a else t.[j].
  proof.
    rewrite setE initE /=; smt (get_out).
  qed.

  lemma get_setE (t:'a t) (x y:int) (a:'a) :
    0 <= x < size => t.[x<-a].[y] = if y = x then a else t.[y].
  proof. by move=> hx; rewrite get_set_if hx. qed.

  lemma nosmt set_eqiE (t : 'a t) x y a :
    0 <= x < size => y = x => t.[x <- a].[y] = a.
  proof. by move=> h1 ->;rewrite get_setE. qed.

  lemma nosmt set_neqiE (t : 'a t) x y a :
    0 <= x < size => y <> x => t.[x <- a].[y] = t.[y].
  proof. by move=> h1; rewrite get_setE // => ->. qed.

  hint simplify (set_eqiE, set_neqiE).

  lemma set_out (i : int) (e : 'a) (t : 'a t):
    ! (0 <= i < size) => t.[i <- e] = t.
  proof.
    by move=> hi; apply ext_eq => j hj; rewrite get_set_if hi.  
  qed.

  lemma set_neg (i : int) (e : 'a) (t : 'a t):
    i < 0 => t.[i<- e] = t.
  proof. move=> hi;apply set_out => /#. qed.

  lemma set_above (i : int) (e : 'a) (t : 'a t):
    size <= i => t.[i <- e] = t.
  proof. move=> hi;apply set_out => /#. qed.

  lemma set_set_if (t : 'a t) (k k' : int) (x x' : 'a):
       t.[k <- x].[k' <- x']
    =  if   k = k'
       then t.[k' <- x']
       else t.[k' <- x'].[k <- x].
  proof.
    apply ext_eq => i hi;case (k = k') => [<<- | neqk];rewrite !get_set_if /#.
  qed.

  lemma set_set_eq (t : 'a t) (k : int) (x x' : 'a):
    t.[k <- x].[k <- x'] = t.[k <- x'].
  proof. by rewrite set_set_if. qed.

  lemma set_set_eq_s (t : 'a t) (k1 k2 : int) (x x' : 'a):
    k1 = k2 => t.[k1 <- x].[k2 <- x'] = t.[k2 <- x'].
  proof. move=> ->; apply set_set_eq. qed.

  hint simplify (set_set_eq_s, set_out).

  lemma set_set_swap (t : 'a t) (k k' : int) (x x' : 'a):
    k <> k' => t.[k <- x].[k' <- x'] = t.[k' <- x'].[k <- x].
  proof. by rewrite set_set_if => ->. qed.

  lemma set_notmod (t:'a t) i : t.[i <- t.[i]] = t.
  proof.
    by apply ext_eq => j hj; rewrite get_set_if; case: (0 <= i < size /\ j = i).
  qed.

  lemma init_set (t:'a t) (f : int -> 'a) :
    foldl (fun (a : 'a t) i => a.[i <- f i]) t (iota_ 0 size) =
    init f.
  proof.
    apply ext_eq=> x hx; rewrite initiE 1://.
    have h : forall sz, sz <= size => 0 <= x < sz => 
      (foldl (fun (a : 'a t) (i : int) => a.[i <- f i]) t (iota_ 0 sz)).[x] = f x; last by apply (h size).
    elim /natind; 1: smt().
    by move=> {hx} sz hsz0 ih hsize hx; rewrite iotaSr 1:// -cats1 foldl_cat /=; smt (get_setE).
  qed.

  (* -------------------------------------------------------------------- *)
  op create (a:'a) = init (fun (i:int) => a)
  axiomatized by createE.

  lemma createiE (a:'a) i : 0 <= i < size => (create a).[i] = a.
  proof. by rewrite createE;apply initiE. qed.

  hint simplify createiE.

  (* -------------------------------------------------------------------- *)
  op map ['a, 'b] (f: 'a -> 'b) (t:'a t) : 'b t =
     init (fun i => f t.[i])
  axiomatized by mapE.

  lemma mapiE ['a, 'b] (f: 'a -> 'b) t i : 0 <= i < size => (map f t).[i] = f t.[i].
  proof. by rewrite mapE;apply initiE. qed.

  hint simplify mapiE.

  (* -------------------------------------------------------------------- *)
  op map2 ['a, 'b, 'c] (f: 'a -> 'b -> 'c) t1 t2 =
     init (fun i => f t1.[i] t2.[i])
  axiomatized by map2E.

  lemma map2iE ['a, 'b, 'c] (f: 'a -> 'b -> 'c) t1 t2 i : 0 <= i < size =>
    (map2 f t1 t2).[i] = f t1.[i] t2.[i].
  proof. by rewrite map2E;apply initiE. qed.

  hint simplify map2iE.

  (* -------------------------------------------------------------------- *)
  op all_eq (t1 t2: 'a t) =
    all (fun x => t1.[x] = t2.[x]) (iotared 0 size).

  lemma ext_eq_all (t1 t2: 'a t) :
    all_eq t1 t2 <=> t1 = t2.
  proof.
    split.
    + by move=> /allP h; apply ext_eq => x /mem_range hx; apply h; rewrite iotaredE.
    by move=> ->;apply /allP.
  qed.

  lemma all_eq_eq (t1 t2: 'a t) : all_eq t1 t2 => t1 = t2.
  proof. by move=> /ext_eq_all. qed.

  (* -------------------------------------------------------------------- *)

  op of_list (dfl:'a) (l:'a list) =
    init (fun i => nth dfl l i).

  op to_list (t:'a t) =
    mkseq (fun i => t.[i]) size.

  lemma size_to_list (t:'a t): size (to_list t) = size.
  proof. rewrite size_mkseq /max; smt (ge0_size). qed.

  lemma get_of_list (dfl:'a) (l:'a list) i : 0 <= i < size =>
    (of_list dfl l).[i] = nth dfl l i.
  proof. by move=> hi;rewrite /of_list initiE. qed.

  hint simplify get_of_list.

  lemma get_to_list (t : 'a t) i :
    nth witness (to_list t) i = t.[i].
  proof.
    rewrite nth_mkseq_if; case:(0 <= i < size) => hi //.
    rewrite get_out //.
  qed.

  hint simplify (get_of_list, get_to_list).

  lemma of_listK (dfl:'a) (l : 'a list) : size l = size =>
    to_list (of_list dfl l) = l.
  proof.
    move=> h; apply (eq_from_nth witness); 1:by rewrite size_to_list h.
    move=> i; rewrite size_to_list => hi.
    rewrite get_to_list // get_of_list //.
    by rewrite nth_onth (onth_nth witness) // h.
  qed.

  lemma to_listK (dfl:'a) : cancel to_list (of_list dfl).
  proof.
    move=> t; apply ext_eq => i hi.
    by rewrite get_of_list // nth_onth (onth_nth witness) ?size_to_list //=
      get_to_list.
  qed.

  lemma to_list_inj ['a] : injective (to_list<:'a>).
  proof. by apply/(can_inj _ _ (to_listK witness)). qed.

  (* The following rules are for reduction *)
  lemma map_of_list ['a, 'b] (f:'a -> 'b) dfa ws :
    map f (of_list dfa ws) = of_list (f dfa) (map f ws).
  proof.
    apply tP => i hi; rewrite mapiE // !get_of_list //.
    case (i < size ws) => isws.
    + by rewrite (nth_map dfa) // /#.
    by rewrite nth_out 1:/# nth_out // size_map 1:/#.
  qed.

  lemma map2_of_list (f:'a -> 'b -> 'c) df1 df2 ws1 ws2 :
    map2 f (of_list df1 ws1) (of_list df2 ws2) =
      of_list (f df1 df2) (mapN2 f df1 df2 ws1 ws2 size).
  proof.
    by apply tP => i hi; rewrite map2iE // !get_of_list // nth_mapN2.
  qed.

  hint simplify (map_of_list, map2_of_list)@0.

  (* -------------------------------------------------------------------- *)
  op fill (f : int -> 'a) (k len : int) (t : 'a t) =
    init (fun i => if k <= i < k + len then f i else t.[i])
  axiomatized by fillE.

  lemma filliE (f : int -> 'a) (k len:int) (t : 'a t)  i : 0 <= i < size =>
    (fill f k len t).[i] = if k <= i < k + len then f i else t.[i].
  proof. by move=> hi;rewrite fillE initiE. qed.

  hint simplify filliE.

  (* -------------------------------------------------------------------- *)
  op sub (t: 'a t) k len = mkseq (fun (i:int) => t.[k+i]) len.

  lemma size_sub (t:'a t) k len : 0 <= len => size (sub t k len) = len.
  proof. move=> hl; rewrite size_mkseq /max /#. qed.

  lemma nth_sub (dfl:'a) (t : 'a t) k len i : 0 <= i < len =>
    nth dfl (sub t k len) i = t.[k + i].
  proof. by move=> h0i; rewrite nth_mkseq. qed.


  (* -------------------------------------------------------------------- *)
  op all (f : 'a -> bool) (t : 'a t) =
     all (fun i => f t.[i]) (iota_ 0 size).

  lemma allP (t: 'a t) f : all f t <=> (forall i, 0 <= i < size => f t.[i]).
  proof.
    rewrite /all (allP);split => h i /=.
    + by move=> hi;apply h;rewrite mem_iota //; case: hi.
    by rewrite mem_iota /= => h1; apply h;case h1.
  qed.

  (* -------------------------------------------------------------------- *)
  op is_init (t: 'a option t) = all is_init t.

  lemma is_init_Some (t:'a t) : is_init (map Some t).
  proof. by rewrite /is_init allP => i hi; rewrite mapiE. qed.

  hint simplify [eqtrue] is_init_Some.

end PolyArray.
