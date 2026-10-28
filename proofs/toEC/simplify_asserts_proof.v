(* * Correctness of the pass simplify_asserts.

   The pass rewrites the assertions only, with facts that hold on every path
   that reaches them (constants, full masks, bytes of masks known to be
   0xFF, copies of arrays); a rewritten assertion that holds implies the
   original one, on the same state. The rest of the code is unchanged. The
   facts rely on a total mode: a write out of the bounds of an array leaves
   it unchanged, which keeps a full mask full. The pass runs after
   [explicit_init], on programs whose semantics is the mode [total_init].

   The relation [wiequiv_f] only constrains the runs of its first program that
   do not fail: the statement is that of the direction needed, from the
   transformed program to the source. The two runs go through the same
   states; the invariant is that the facts of the analysis hold in the
   current state ([ahold]): a constant is the value of its variable, the
   bytes of a mask that a fact gives are in its bounds and 0xFF, a copy holds
   the value of its array, and the bounds of a fill are integer expressions
   of local variables that evaluate to the bounds of its 0xFF bytes. *)

From mathcomp Require Import ssreflect ssrfun ssrbool ssralg eqtype word_ssrZ.
From mathcomp Require Import ssrnat seq.
Require Import seq_extra compiler_util psem psem_facts sopn_facts.
Require Import simplify_asserts.
Import Lia.

#[local] Existing Instance progUnit.
#[local] Existing Instance nosubword.
#[local] Existing Instance indirect_c.

(* ------------------------------------------------------------------------- *)
(* Sets of bytes                                                              *)

(* The byte [k] is in one of the intervals of [l]. *)
Definition in_ivs (l : seq (Z * Z)) (k : Z) : bool :=
  has (fun ab => (ab.1 <=? k) && (k <? ab.2))%Z l.

Lemma in_ivs_cons ab l k : in_ivs (ab :: l) k = ((ab.1 <=? k) && (k <? ab.2))%Z || in_ivs l k.
Proof. by []. Qed.

Lemma iv_addP a b l k :
  in_ivs (iv_add a b l) k = ((a <=? k) && (k <? b))%Z || in_ivs l k.
Proof.
elim: l a b => [ | [c d] l ih] a b /=.
+ by rewrite /in_ivs; case: ZleP => /= ?; rewrite ?orbF //; case: (ZleP a k) => //= ?; case: ZltP => //= ?; lia.
have hab : ((a <=? k) && (k <? b))%Z = false -> forall x y, [|| ((a <=? k) && (k <? b))%Z, x | y] = x || y by move=> ->.
case: ZleP => hba.
+ rewrite hab //; apply/negbTE/negP => /andP [/ZleP ? /ZltP ?]; lia.
case: ZltP => hbc; first by [].
case: ZltP => hda.
+ by rewrite in_ivs_cons ih /= orbCA.
rewrite ih !orbA; congr orb.
by case: (ZleP (Z.min a c) k); case: (ZltP k (Z.max b d)); case: (ZleP a k); case: (ZltP k b); case: (ZleP c k); case: (ZltP k d) => /= *; lia.
Qed.

Lemma iv_unionP l1 l2 k : in_ivs (iv_union l1 l2) k = in_ivs l1 k || in_ivs l2 k.
Proof. by elim: l1 => //= -[a b] l1 ih; rewrite iv_addP ih orbA. Qed.

Lemma iv_inter1P a b l2 acc k :
  in_ivs (foldr (fun cd l => iv_add (Z.max a cd.1) (Z.min b cd.2) l) acc l2) k =
  ((a <=? k) && (k <? b))%Z && in_ivs l2 k || in_ivs acc k.
Proof.
elim: l2 => [ | [c d] l2 ih2] /=; first by rewrite andbF.
rewrite iv_addP ih2 andb_orr orbA; congr orb; congr orb.
by case: (ZleP (Z.max a c) k); case: (ZltP k (Z.min b d)); case: (ZleP a k); case: (ZltP k b); case: (ZleP c k); case: (ZltP k d) => /= *; lia.
Qed.

Lemma iv_interP l1 l2 k : in_ivs (iv_inter l1 l2) k = in_ivs l1 k && in_ivs l2 k.
Proof. by rewrite /iv_inter; elim: l1 => //= -[a b] l1 ih; rewrite iv_inter1P ih andb_orl. Qed.

Lemma iv_removeP l a b k :
  in_ivs (iv_remove l a b) k = in_ivs l k && ~~ ((a <=? k) && (k <? b))%Z.
Proof.
rewrite /iv_remove; elim: l => //= -[c d] l ih; rewrite !iv_addP ih andb_orl orbA; congr orb.
by rewrite /=; case: (ZleP c k); case: (ZltP k (Z.min d a)); case: (ZleP (Z.max c b) k); case: (ZltP k d); case: (ZleP a k); case: (ZltP k b) => /= *; lia.
Qed.

Lemma iv_shiftP k0 l k : in_ivs (iv_shift k0 l) k = in_ivs l (k - k0).
Proof.
elim: l => //= -[a b] l ih; rewrite ih; congr orb.
by rewrite /=; case: (ZleP (a + k0) k); case: (ZltP k (b + k0)); case: (ZleP a (k - k0)); case: (ZltP (k - k0) b) => /= *; lia.
Qed.

Lemma iv_inclP l a b k : iv_incl l a b -> (a <= k < b)%Z -> in_ivs l k.
Proof.
rewrite /iv_incl => /orP [/ZleP ? ? | /hasP [[c d] hin /andP /= [/ZleP ? /ZleP ?]] ?]; first lia.
by apply/hasP; exists (c, d) => //=; apply/andP; split; [apply/ZleP | apply/ZltP]; lia.
Qed.

Lemma in_ivs_take n l k : in_ivs (take n l) k -> in_ivs l k.
Proof. by elim: l n => [ | ab l ih] [ | n] //= /orP [-> // | /ih ->]; rewrite orbT. Qed.

Lemma iv_boundsP len k : in_ivs (iv_bounds len) k = ((0 <=? k) && (k <? len))%Z.
Proof. by rewrite /iv_bounds iv_addP orbF. Qed.

(* ------------------------------------------------------------------------- *)
(* The meaning of the facts                                                   *)

Definition vlen (v : value) : Z := if v is Varr n _ then n else 0.

Lemma arr_lenE {sm : SemMode} vm x : arr_len x = vlen vm.[x].
Proof.
have := Vm.getP_mode (sm := sm) vm x; rewrite /arr_len.
case: (vtype x) => /= [ | | ws len | ws] /compat_valEl.
1,2: by move=> [-> | [? ->]].
+ by move=> [? ->].
by move=> [-> | [? [? ->]]].
Qed.

(* The bytes of [l] are in the bounds of the array [v] and are 0xFF. *)
Definition ffb (v : value) (l : seq (Z * Z)) : Prop :=
  match v with
  | Varr n t => forall k, in_ivs l k -> (0 <= k < n)%Z /\ WArray.is_initb t k
  | _ => forall k, ~~ in_ivs l k
  end.

Lemma ffb_nil v : ffb v [::].
Proof. by case: v. Qed.

Lemma ffb_sub v l l' : (forall k, in_ivs l' k -> in_ivs l k) -> ffb v l -> ffb v l'.
Proof.
case: v => /= [ b | z | n t | ws w | ty h] hsub h' k.
3: by move=> /hsub /h'.
all: by apply/negP => /hsub; apply/negP/h'.
Qed.

(* The variables read by a stable expression are integers. *)
Lemma stable_read e z : is_stable_int e -> Sv.In z (read_e e) -> vtype z = aint.
Proof.
elim: e => [z' | b | ws n | x | al aa w x e ih | aa w len x e ih | al w e ih | o e ih | o e1 ih1 e2 ih2 | o es ih | t b ihb e1 ih1 e2 ih2] //=.
+ by move=> _; rewrite /read_e /=; SvD.fsetdec.
+ by move=> /andP [hx /eqP h]; rewrite read_e_var /read_gvar hx => /SvD.F.singleton_iff <-.
+ by case: o => // -[] // /ih.
case: o => // -[] // /andP [/ih1 h1 /ih2 h2]; rewrite read_e_Papp2 => /Sv.union_spec [/h1 | /h2] //.
Qed.

Section SEM.

Context
  {syscall_state : Type} {ep : EstateParams syscall_state} {spp : SemPexprParams}
  (gd : glob_decls).

Notation sem s e := (sem_pexpr (sm := total) true gd s e).

(* The value of [x] in [s], read as the expressions of the total mode do. *)
Notation vget s x := (Vm.get (sm := total) (evm s) x).

(* The fact [a] on the variable [x] holds in the state [s]. The bounds of a
   fill are integer expressions of local variables, evaluated in [s]. *)
Definition afact (s : estate) (x : var) (a : aval) : Prop :=
  let v := vget s x in
  match a with
  | Aconst c => val_of_lit c = Some v
  | Acopy y => v = vget s y
  | Afill lo n =>
    [/\ is_stable_int lo, is_stable_int n &
      exists lo' n', [/\ sem s lo = ok (Vint lo'), sem s n = ok (Vint n') &
                         ffb v (ivs_of_aval (arr_len x) (Afill (Pconst lo') (Pconst n')))]]
  | Afull | Ainit _ => ffb v (ivs_of_aval (arr_len x) a)
  end.

(* The facts of [S] hold in [s]. *)
Definition ahold (S : astate) (s : estate) := forall x a, Mvar.get S x = Some a -> afact s x a.

Lemma afact_ivs s x a : afact s x a -> ffb (vget s x) (ivs_of_aval (arr_len x) a).
Proof.
case: a => //= [c _ | y _ | lo n [_ _ [lo' [n' [hlo hn h]]]]]; try exact: ffb_nil.
case: lo hlo => /=; try by move=> *; apply ffb_nil.
move=> z [] ?; subst z; case: n hn => /=; try by move=> *; apply ffb_nil.
by move=> z [] ?; subst z.
Qed.

Lemma ivs_of_varP S s x : ahold S s -> ffb (vget s x) (ivs_of_var S x).
Proof.
rewrite /ivs_of_var => hS; case h: Mvar.get => [a | ]; last exact: ffb_nil.
have := hS _ _ h; case: a h => [c | | y | lo n | l] h; try by move/afact_ivs.
case hy: Mvar.get => [b | ]; last by move=> _; apply ffb_nil.
move=> /= hxy; rewrite (arr_lenE (sm := total) (evm s) x) hxy -arr_lenE.
exact: afact_ivs (hS _ _ hy).
Qed.

Lemma val_of_litP s e v : val_of_lit e = Some v -> sem s e = ok v.
Proof. by case: e => //= [ z [<-] | b [<-] | [] // ws [] // z [<-]]. Qed.

Lemma lit_of_valP s v e : lit_of_val v = Some e -> sem s e = ok v.
Proof.
case: v => //= [ b [<-] | z [<-] | ws w [<-]] //=.
by rewrite /sem_sop1 /= wrepr_unsigned.
Qed.

(* The folding of a closed operation evaluates as the operation. *)
Lemma fold_app1P s o e1 : sem s (fold_app1 o e1) = sem s (Papp1 o e1).
Proof.
rewrite /fold_app1; case: val_of_lit => [ _ | ] //.
case h1: (val_of_lit e1) => [v1 | ] //; case h: sem_sop1 => [v | ] //; case hl: lit_of_val => [e | ] //=.
by rewrite (lit_of_valP s hl) (val_of_litP s h1) /= h.
Qed.

Lemma fold_app2P s o e1 e2 : sem s (fold_app2 o e1 e2) = sem s (Papp2 o e1 e2).
Proof.
rewrite /fold_app2; case h1: (val_of_lit e1) => [v1 | ] //; case h2: (val_of_lit e2) => [v2 | ] //.
case h: sem_sop2 => [v | ] //; case hl: lit_of_val => [e | ] //=.
by rewrite (lit_of_valP s hl) (val_of_litP s h1) (val_of_litP s h2) /= h.
Qed.

Lemma fold_eP s e : sem s (fold_e e) = sem s e.
Proof.
elim: e => //= [o e1 ih | o e1 ih1 e2 ih2].
+ by rewrite fold_app1P /= ih.
by rewrite fold_app2P /= ih1 ih2.
Qed.

Lemma val_of_lit_defined c v : val_of_lit c = Some v -> is_defined v.
Proof. by case: c => //= [z [<-] | b [<-] | [] // ws [] // z [<-]]. Qed.

(* The simplification of an expression evaluates as the expression. *)
Lemma simpl_eP S s e : ahold S s -> sem s (simpl_e S e) = sem s e.
Proof.
move=> hS; elim: e => //=.
2-4,8: by move=> > ->; try move=> > ->; try move=> > ->.
+ move=> x; rewrite /alocal; case hx: is_lvar => //.
  case h: Mvar.get => [a | ] //; case: a h => // c /hS /= h.
  by rewrite (val_of_litP s h) /get_gvar hx /get_var (val_of_lit_defined h).
+ by move=> o e he; rewrite fold_app1P /= he.
+ by move=> o e1 h1 e2 h2; rewrite fold_app2P /= h1 h2.
move=> o es hes; have -> // : mapM (sem_pexpr (sm := total) true gd s) [seq simpl_e S i | i <- es] = mapM (sem_pexpr (sm := total) true gd s) es.
elim: es hes => //= e es ih hes.
by rewrite hes; [rewrite ih // => e' he'; apply hes; right | left].
Qed.

Lemma ffb_fill len lo n (w : u8) :
  w = wrepr U8 (-1) ->
  ffb (Varr (rdflt (WArray.empty _) (WArray.fill len
     (map (fun k => if (lo <=? k) && (k <? lo + n) then w else 0%R)%Z (ziota 0 len)))))
    (iv_inter (iv_add lo (lo + n) [::]) (iv_bounds len)).
Proof.
move=> -> k; rewrite iv_interP iv_addP iv_boundsP rdflt_fill_map_initb orbF.
move=> /and3P [-> h0 hl]; rewrite h0 hl eqxx; split => //; move: h0 hl => /ZleP ? /ZltP ?; lia.
Qed.

(* The bytes of a sub-array are those of the array, in its window. *)
Lemma ffb_get_sub n (t : WArray.array n) aa ws slen i l :
  ffb (Varr t) l ->
  let start := (i * mk_scale aa ws)%Z in
  ffb (Varr (WArray.Build_array (arr_size ws slen) (WArray.get_sub_data n aa ws slen (WArray.arr_data t) i)))
      (iv_shift (- start) (iv_inter l (iv_add start (start + arr_size ws slen) [::]))).
Proof.
move=> h start k; rewrite iv_shiftP iv_interP iv_addP orbF => /andP [/h [hb hi] /andP [/ZleP ? /ZltP ?]].
have hk : (0 <= k < arr_size ws slen)%Z by lia.
split => //; move: hi; rewrite /WArray.is_initb /= WArray.get_sub_data_get8 /= /WArray.get_in_bounds -/start.
have -> : (k - - start = start + k)%Z by lia.
have -> : ((0 <=? k) && (k <? arr_size ws slen))%Z by apply/andP; split; [apply/ZleP | apply/ZltP]; lia.
have -> // : ((0 <=? start + k) && (start + k <? n))%Z by apply/andP; split; [apply/ZleP | apply/ZltP]; lia.
Qed.

Lemma get_lvarP s x : is_lvar x -> sem s (Pvar x) = ok (vget s x.(gv)).
Proof. by move=> hx; rewrite /= /get_gvar hx /get_var get_total_defined. Qed.

(* The bytes known to be 0xFF in the value of an expression. *)
Lemma ivs_of_eP S s len e v : ahold S s -> sem s e = ok v -> ffb v (ivs_of_e S len e).
Proof.
move=> hS; case: e => [z | b | ws n | x | al aa ws x e | aa ws slen x e | al ws e | o e | o e1 e2 | o es | ty b e1 e2] he; try exact: ffb_nil.
+ rewrite /ivs_of_e; case: andP => [[hx _] | _]; last exact: ffb_nil.
  by move: he; rewrite get_lvarP // => -[<-]; apply ivs_of_varP.
+ case: e he => [i | > | > | > | > | > | > | > | > | > | >] he; try exact: ffb_nil.
  rewrite /ivs_of_e; case: andP => [[hx /eqP <-] | _]; last exact: ffb_nil.
  have := ivs_of_varP (gv x) hS.
  move: he; rewrite /= /get_gvar hx /get_var get_total_defined /=.
  by case: (vget s (gv x)) => // n t [<-]; apply: ffb_get_sub.
case: o he => [ > | > | ws flen | >] he; try exact: ffb_nil.
case: es he => [ | e1 es] he; first exact: ffb_nil.
case: e1 he => [lo | > | > | > | > | > | > | > | > | > | >] he; try exact: ffb_nil.
case: es he => [ | e2 es] he; first exact: ffb_nil.
case: e2 he => [n | > | > | > | > | > | > | > | > | > | >] he; try exact: ffb_nil.
case: es he => [ | e3 es] he; first exact: ffb_nil.
case: e3 he => [> | > | > | > | > | > | > | o1 p | > | > | >] he; try exact: ffb_nil.
case: o1 he; try (move=> *; exact: ffb_nil).
case; try (move=> *; exact: ffb_nil).
case: p => [z | > | > | > | > | > | > | > | > | > | >] he; try exact: ffb_nil.
case: es he => [ | ? ?] he; last exact: ffb_nil.
rewrite /ivs_of_e; case: andP => [[/eqP <- /eqP hz] | _]; last exact: ffb_nil.
move: he; rewrite /= /sem_sop1 /= sem_opN_fill => -[<-].
exact: ffb_fill.
Qed.

(* ------------------------------------------------------------------------- *)
(* The initialisation tests                                                   *)

Lemma sem_eint_leP s a b r : sem s (eint_le a b) = ok (Vbool r) ->
  exists x y, [/\ sem s a = ok (Vint x), sem s b = ok (Vint y) & r = (x <=? y)%Z].
Proof.
rewrite /= /sem_sop2 /=; t_xrbindP => va -> vb -> x /to_intI -> y /to_intI -> /= [] <-.
by exists x, y.
Qed.

Lemma sem_eandP s a b r : sem s (eand a b) = ok (Vbool r) ->
  exists ra rb, [/\ sem s a = ok (Vbool ra), sem s b = ok (Vbool rb) & r = ra && rb].
Proof.
rewrite /= /sem_sop2 /=; t_xrbindP => va -> vb -> x /to_boolI -> y /to_boolI -> /= [] <-.
by exists x, y.
Qed.

Lemma sem_eorP s a b r : sem s (eor a b) = ok (Vbool r) ->
  exists ra rb, [/\ sem s a = ok (Vbool ra), sem s b = ok (Vbool rb) & r = ra || rb].
Proof.
rewrite /= /sem_sop2 /=; t_xrbindP => va -> vb -> x /to_boolI -> y /to_boolI -> /= [] <-.
by exists x, y.
Qed.

Lemma sem_eint_addP s a b v : sem s (eint_add a b) = ok v ->
  exists x y, [/\ sem s a = ok (Vint x), sem s b = ok (Vint y) & v = Vint (x + y)].
Proof.
rewrite /= /sem_sop2 /=; t_xrbindP => va -> vb -> x /to_intI -> y /to_intI -> /= <-.
by exists x, y.
Qed.

(* The condition [eall_cells n inb] evaluates [n] and [inb]. *)
Lemma eall_cellsP s n inb : sem s (eall_cells n inb) = ok (Vbool true) ->
  exists vn r, [/\ sem s n = ok (Vint vn), sem s inb = ok (Vbool r) & (vn <= 0)%Z \/ r].
Proof.
have hor : sem s (eor (eint_le n (Pconst 0)) inb) = ok (Vbool true) ->
  exists vn r, [/\ sem s n = ok (Vint vn), sem s inb = ok (Vbool r) & (vn <= 0)%Z \/ r].
+ move=> /sem_eorP [ra [rb [h1 h2 h]]].
  have [x [y [hx hy hr]]] := sem_eint_leP h1.
  case: hy => ?; subst y ra; exists x, rb; split => //.
  by case/esym/orP: h => [/ZleP | ]; auto.
rewrite /eall_cells; case: n hor => // k hor.
by case: ZltP => // _ h; exists k, true; split => //; right.
Qed.

Lemma ein_boundsP s len lo n r : sem s (ein_bounds len lo n) = ok (Vbool r) ->
  exists lo' n', [/\ sem s lo = ok (Vint lo'), sem s n = ok (Vint n') & r = (0 <=? lo')%Z && (lo' + n' <=? len)%Z].
Proof.
move=> /sem_eandP [ra [rb [/sem_eint_leP [z [lo' [[<-] hlo ->]]] /sem_eint_leP [v [len' [/sem_eint_addP [lo'' [n' [hlo' hn [->]]]] [<-] ->]]] ->]]].
by move: hlo'; rewrite hlo => -[] ?; subst lo''; exists lo', n'.
Qed.

Lemma barr_holds s m lo n len k (t : WArray.array k) a b :
  k = len -> sem s m = ok (Varr t) -> sem s lo = ok (Vint a) -> sem s n = ok (Vint b) ->
  (forall j, (a <= j < a + b)%Z -> WArray.is_initb t j) ->
  sem_eassert gd s (PappN_safety (Ois_barr_init len) [:: m; lo; n]) = ok true.
Proof.
move=> hk hm hlo hn h; rewrite /= hm hlo hn /= (barr_initE _ _ _ hk); congr ok.
by apply/allP => j; rewrite in_ziota => /andP [/ZleP ? /ZltP ?]; apply h; lia.
Qed.
Lemma vget_arr s x ws len : vtype x = aarr ws len -> exists t : WArray.array (arr_size ws len), vget s x = Varr t.
Proof. by move=> hx; have := Vm.getP_mode (sm := total) (evm s) x; rewrite hx => /compat_valEl. Qed.
Lemma sem_psubE s aa ws slen x e i n (t : WArray.array n) :
  is_lvar x -> vget s x.(gv) = Varr t -> sem s e = ok (Vint i) ->
  sem s (Psub aa ws slen x e) =
    ok (Varr (WArray.Build_array (arr_size ws slen) (WArray.get_sub_data n aa ws slen (WArray.arr_data t) i))).
Proof. by move=> hx ht he; rewrite /= /get_gvar hx /get_var get_total_defined /= ht /= he. Qed.

Lemma no_cellP s len m lo n : is_no_cell len m lo n ->
  sem_eassert gd s (PappN_safety (Ois_barr_init len) [:: m; lo; n]) = ok true.
Proof.
rewrite /is_no_cell; case: lo => // a; case: n => // b /andP [/ZleP hb hm].
have hall : forall k (t : WArray.array k), forall j, (a <= j < a + b)%Z -> WArray.is_initb t j by move=> ???; lia.
case: m hm => // [x | aa ws slen x [] // i].
+ case hty: vtype => [ | | wsx xlen | ] /andP [hx] //= /eqP hl.
  have [t ht] := vget_arr s hty.
  have hm : sem s (Pvar x) = ok (Varr t) by rewrite get_lvarP // ht.
  exact: (barr_holds (lo := Pconst a) (n := Pconst b) hl hm erefl erefl (hall _ t)).
case hty: vtype => [ | | wsx xlen | ]; rewrite ?andbF // andbT => /andP [hx /eqP hl].
have [t ht] := vget_arr s hty.
exact: (barr_holds (lo := Pconst a) (n := Pconst b) hl (sem_psubE aa ws slen (e := Pconst i) hx ht erefl) erefl erefl (hall _ _)).
Qed.

Lemma ffb_varr v l j : ffb v l -> in_ivs l j -> exists n (t : WArray.array n), v = Varr t.
Proof.
case: v => /= [b | z | n t | ws w | ty h] hf hj; try by have := hf j; rewrite hj.
by exists n, t.
Qed.

(* An expression with a byte known to be 0xFF evaluates to an array. *)
Lemma ivs_of_e_sem S s len m j : ahold S s -> in_ivs (ivs_of_e S len m) j ->
  exists n (t : WArray.array n), n = len /\ sem s m = ok (Varr t).
Proof.
move=> hS; case: m => [z | b | ws n | x | al aa ws x e | aa ws slen x e | al ws e | o e | o e1 e2 | o es | ty b e1 e2] //.
+ rewrite /ivs_of_e; case: andP => [[hx /eqP hl] | //] hj.
  have [n [t ht]] := ffb_varr (ivs_of_varP (gv x) hS) hj.
  exists n, t; rewrite get_lvarP // ht; split => //.
  by rewrite -hl (arr_lenE (sm := total) (evm s)) ht.
+ case: e => // i; rewrite /ivs_of_e; case: andP => [[hx /eqP hl] | //].
  rewrite iv_shiftP iv_interP => /andP [hj _].
  have [n [t ht]] := ffb_varr (ivs_of_varP (gv x) hS) hj.
  by exists (arr_size ws slen), (WArray.Build_array (arr_size ws slen) (WArray.get_sub_data n aa ws slen (WArray.arr_data t) i)); rewrite (sem_psubE aa ws slen (e := Pconst i) hx ht erefl).
case: o => [ > | > | ws flen | >]; try done.
case: es => [ | e1 es]; first done.
case: e1 => [lo | > | > | > | > | > | > | > | > | > | >]; try done.
case: es => [ | e2 es]; first done.
case: e2 => [n | > | > | > | > | > | > | > | > | > | >]; try done.
case: es => [ | e3 es]; first done.
case: e3 => [> | > | > | > | > | > | > | o1 p | > | > | >]; try done.
case: o1; try done.
case; try done.
case: p => [z | > | > | > | > | > | > | > | > | > | >]; try done.
case: es => [ | ? ?]; last done.
rewrite /ivs_of_e; case: andP => [[/eqP hl _] | //] _.
by eexists; eexists; split; last by rewrite /= /sem_sop1 /= sem_opN_fill.
Qed.

Lemma init_ivsP S s len m lo n : ahold S s -> is_init_ivs S len m lo n ->
  sem_eassert gd s (PappN_safety (Ois_barr_init len) [:: m; lo; n]) = ok true.
Proof.
move=> hS; rewrite /is_init_ivs; case: lo => // a; case: n => // b /andP [/ZltP hb hincl].
have [k [t [hk hm]]] := ivs_of_e_sem hS (iv_inclP hincl (k := a) ltac:(lia)).
apply: (barr_holds (lo := Pconst a) (n := Pconst b) hk hm erefl erefl) => j hj.
have := ivs_of_eP len hS hm.
by move=> /(_ j (iv_inclP hincl hj)) [].
Qed.

Lemma is_full_varP S s x : ahold S s -> is_full_var S x ->
  is_lvar x /\ ffb (vget s x.(gv)) (iv_bounds (arr_len x.(gv))).
Proof.
rewrite /is_full_var /alocal => hS; case: ifP => // hx hf; split => //; move: hf.
case h: (Mvar.get S (gv x)) => [a | ] //; case: a h => // [ | y] h; first by move=> _; exact: (hS _ _ h).
case hy: (Mvar.get S y) => [b | ] //; case: b hy => // hy _.
have /= hxy := hS _ _ h; have /= := hS _ _ hy.
by rewrite (arr_lenE (sm := total) (evm s) (gv x)) (arr_lenE (sm := total) (evm s) y) hxy.
Qed.

Lemma is_fullP S s len m : ahold S s -> is_full S len m ->
  exists k (t : WArray.array k), [/\ k = len, sem s m = ok (Varr t) & forall j, (0 <= j < len)%Z -> WArray.is_initb t j].
Proof.
move=> hS; case: m => // [x | o es]; rewrite /is_full.
+ case hty: vtype => [ | | ws xlen | ] // /andP [/(is_full_varP hS) [hx hf] /eqP hl].
  have [t ht] := vget_arr s hty.
  exists (arr_size ws xlen), t; rewrite get_lvarP // ht; split => // j hj.
  move: hf; rewrite ht /arr_len hty /= => /(_ j); rewrite iv_boundsP.
  by case => //; apply/andP; split; [apply/ZleP | apply/ZltP]; lia.
case: o => // ws flen /andP [/eqP hl]; rewrite /is_full_fill.
case: es => [ | e1 es]; first done.
case: e1 => [lo | > | > | > | > | > | > | > | > | > | >]; try done.
case: es => [ | e2 es]; first done.
case: e2 => [n | > | > | > | > | > | > | > | > | > | >]; try done.
case: es => [ | e3 es]; first done.
case: e3 => [> | > | > | > | > | > | > | o1 p | > | > | >]; try done.
case: o1; try done.
case; try done.
case: p => [z | > | > | > | > | > | > | > | > | > | >]; try done.
case: es => [ | ? ?]; last done.
move=> /and3P [/ZleP hlo /ZleP hn /eqP hz].
eexists; eexists; split; first exact: hl; first by rewrite /= /sem_sop1 /= sem_opN_fill.
move=> j hj; rewrite rdflt_fill_map_initb hz.
have -> : ((lo <=? j) && (j <? lo + n))%Z by apply/andP; split; [apply/ZleP | apply/ZltP]; lia.
by rewrite eqxx andbT; apply/andP; split; [apply/ZleP | apply/ZltP]; lia.
Qed.

(* A test on a full mask amounts to the condition on its bounds. *)
Lemma eboundsP s len m lo n k (t : WArray.array k) :
  k = len -> sem s m = ok (Varr t) -> (forall j, (0 <= j < len)%Z -> WArray.is_initb t j) ->
  sem s (ebounds len lo n) = ok (Vbool true) ->
  sem_eassert gd s (PappN_safety (Ois_barr_init len) [:: m; lo; n]) = ok true.
Proof.
move=> hk hm hfull /eall_cellsP [vn [r [hn /ein_boundsP [lo' [n' [hlo hn' ->]]] h]]].
move: hn'; rewrite hn => -[] ?; subst n'.
apply: (barr_holds hk hm hlo hn) => j hj; apply hfull.
by case: h => [? | /andP [/ZleP ? /ZleP ?]]; lia.
Qed.

(* The first byte tested in the array of a sub-array. *)
Lemma sem_startP s aa ws i lo lo1 z :
  let sc := mk_scale aa ws in
  let start := if sc == 1%Z then i else Papp2 (Omul Op_int) i (Pconst sc) in
  sem s lo = ok (Vint lo1) ->
  sem s (if lo is Pconst 0 then start else eint_add start lo) = ok (Vint z) ->
  exists iv, sem s i = ok (Vint iv) /\ z = (iv * mk_scale aa ws + lo1)%Z.
Proof.
move=> sc start hlo.
have hst : forall z, sem s start = ok (Vint z) -> exists iv, sem s i = ok (Vint iv) /\ z = (iv * sc)%Z.
+ rewrite /start; case: eqP => hsc z'.
  + by move=> h; exists z'; rewrite h hsc Z.mul_1_r.
  rewrite /= /sem_sop2 /=; t_xrbindP => vi -> x /to_intI -> y.
  by exists x.
case: lo hlo => [[ | p | p] | > | > | > | > | > | > | > | > | > | >] hlo; try (move=> /sem_eint_addP [x [y [/hst [iv [hi ->]] hy [->]]]]; exists iv; split => //; move: hy; rewrite hlo => -[->]).
2-11: by [].
case: hlo => <- /hst [iv [hi ->]]; exists iv; split => //; lia.
Qed.

Lemma esub_boundsP S s len aa ws slen x i lo n wsx lenx :
  ahold S s -> vtype x.(gv) = aarr wsx lenx -> is_full_var S x -> arr_size ws slen = len ->
  sem s (esub_bounds len (arr_size wsx lenx) aa ws i lo n) = ok (Vbool true) ->
  sem_eassert gd s (PappN_safety (Ois_barr_init len) [:: Psub aa ws slen x i; lo; n]) = ok true.
Proof.
move=> hS hty /(is_full_varP hS) [hx hf] hl.
rewrite /esub_bounds => /eall_cellsP [vn [r [hn /sem_eandP [ra [rb [/ein_boundsP [lo1 [n1 [hlo hn1 ->]]] /ein_boundsP [z [n2 [hz hn2 ->]]] ->]]] h]]].
move: hn1 hn2; rewrite hn => -[] ? [] ?; subst n1 n2.
have [iv [hi hz']] := sem_startP hlo hz; subst z.
have [t ht] := vget_arr s hty.
apply: (barr_holds hl (sem_psubE aa ws slen hx ht hi) hlo hn) => j hj.
case: h => [? | /and3P [/andP [/ZleP ? /ZleP ?] /ZleP ? /ZleP ?]]; first lia.
move: hf; rewrite ht /arr_len hty /= => /(_ (iv * mk_scale aa ws + j)%Z); rewrite iv_boundsP.
case; first by apply/andP; split; [apply/ZleP | apply/ZltP]; lia.
move=> _ hinit; rewrite /WArray.is_initb /= WArray.get_sub_data_get8 /= /WArray.get_in_bounds.
have -> : ((0 <=? j) && (j <? arr_size ws slen))%Z by apply/andP; split; [apply/ZleP | apply/ZltP]; lia.
by have -> : ((0 <=? iv * mk_scale aa ws + j) && (iv * mk_scale aa ws + j <? arr_size wsx lenx))%Z by apply/andP; split; [apply/ZleP | apply/ZltP]; lia.
Qed.

Lemma efill_boundsP S s len x ws xlen flo fn lo n :
  ahold S s -> is_lvar x -> Mvar.get S x.(gv) = Some (Afill flo fn) -> vtype x.(gv) = aarr ws xlen ->
  arr_size ws xlen = len ->
  sem s (efill_bounds len flo fn lo n) = ok (Vbool true) ->
  sem_eassert gd s (PappN_safety (Ois_barr_init len) [:: Pvar x; lo; n]) = ok true.
Proof.
move=> hS hx /hS [_ _ [a [b [ha hb hf]]]] hty hl.
rewrite /efill_bounds => /eall_cellsP [vn [r [hn /sem_eandP [ra [rb [/ein_boundsP [lo1 [n1 [hlo hn1 ->]]] /sem_eandP [r1 [r2 [hle1 hle2 ->]]] ->]]] h]]].
have [a' [lo2 [ha' hlo2 ?]]] := sem_eint_leP hle1; subst r1.
have [e1 [e2 [he1 he2 ?]]] := sem_eint_leP hle2; subst r2.
have [lo3 [n3 [hlo3 hn3 [?]]]] := sem_eint_addP he1; subst e1.
have [a4 [b4 [ha4 hb4 [?]]]] := sem_eint_addP he2; subst e2.
move: ha' hlo2 hlo3 hn3 ha4 hb4 hn1; rewrite ha hb hlo hn => -[?] [?] [?] [?] [?] [?] [?]; subst.
have [t ht] := vget_arr s hty.
have hm : sem s (Pvar x) = ok (Varr t) by rewrite get_lvarP // ht.
apply: (barr_holds erefl hm hlo hn) => j hj.
case: h => [? | /and3P [/andP [/ZleP ? /ZleP ?] /ZleP ? /ZleP ?]]; first lia.
move: hf; rewrite ht /arr_len hty /ivs_of_aval => /(_ j); rewrite iv_interP iv_addP iv_boundsP orbF.
case; last by [].
by apply/andP; split; apply/andP; split; [apply/ZleP | apply/ZltP | apply/ZleP | apply/ZltP]; lia.
Qed.

(* When the condition that a test amounts to holds, so does the test. *)
Lemma is_init_boundsP S s len m lo n c :
  ahold S s -> is_init_bounds S len m lo n = Some c -> sem s c = ok (Vbool true) ->
  sem_eassert gd s (PappN_safety (Ois_barr_init len) [:: m; lo; n]) = ok true.
Proof.
move=> hS; rewrite /is_init_bounds.
case: orP => [[/no_cellP h | /(init_ivsP hS) h] _ _ | _]; first exact: h; first exact: h.
case: ifP => [/(is_fullP hS) [k [t [hk hm hfull]]] [<-] | _]; first exact: eboundsP hk hm hfull.
case: m => // [x | aa ws slen x i].
+ rewrite /alocal; case: ifP => // hx; case h: Mvar.get => [ [] // flo fn | ] //.
  case hty: vtype => [ | | ws xlen | ] //; case: eqP => // hl [<-].
  exact: efill_boundsP hS hx h hty hl.
case hty: vtype => [ | | wsx lenx | ] //; case: andP => // -[hf /eqP hl] [<-].
exact: esub_boundsP hS hty hf hl.
Qed.

(* ------------------------------------------------------------------------- *)
(* The assertions                                                             *)

(* The assertion holds, [None] standing for [true]. *)
Definition aholds s (oa : option eassert) :=
  if oa is Some a then sem_eassert gd s a = ok true else True.

Lemma aandP s a1 a2 : aholds s (aand a1 a2) -> aholds s a1 /\ aholds s a2.
Proof.
case: a1 a2 => [a1 | ] [a2 | ] //=.
by t_xrbindP => b1 -> b2 -> /andP [-> ->].
Qed.

Lemma simpl_pexpr_aP s e : aholds s (simpl_pexpr_a e) -> sem_eassert gd s (Pexpr e) = ok true.
Proof.
elim: e => //=.
+ by case.
move=> [] // e1 h1 e2 h2 /aandP [/h1 {}h1 /h2 {}h2].
move: h1 h2; t_xrbindP => v1 -> h1 v2 -> h2.
by rewrite (to_boolI h1) (to_boolI h2).
Qed.

Lemma simpl_esP S s es : ahold S s ->
  mapM (sem_pexpr (sm := total) true gd s) (map (simpl_e S) es) = mapM (sem_pexpr (sm := total) true gd s) es.
Proof. by move=> hS; elim: es => //= e es ->; rewrite simpl_eP. Qed.

(* When the simplified assertion holds, so does the original one. *)
Lemma simpl_aP S s a : ahold S s -> aholds s (simpl_a S a) -> sem_eassert gd s a = ok true.
Proof.
move=> hS; elim: a => /=.
+ by move=> e /simpl_pexpr_aP /=; rewrite simpl_eP.
+ move=> o es; rewrite -(simpl_esP es hS); move: (map (simpl_e S) es) => es'.
  case: o => len //; case: es' => [ | m [ | lo [ | n [ | ? ?]]]] //.
  case h: is_init_bounds => [c | ] // /simpl_pexpr_aP /=; rewrite fold_eP; t_xrbindP => v hv /to_boolI ?; subst v.
  exact: (is_init_boundsP hS h hv).
+ by [].
+ by move=> e1 e2; rewrite !simpl_eP.
by move=> a1 h1 a2 h2 /aandP [/h1 -> /h2 ->].
Qed.

(* ------------------------------------------------------------------------- *)
(* The facts learnt from an assertion                                         *)

Lemma ahold_set S s x a : ahold S s -> afact s x a -> ahold (Mvar.set S x a) s.
Proof. by move=> hS ha y b; rewrite Mvar.setP; case: eqP => [<- [<-] | _ /hS]. Qed.

Lemma ahold_fold_full S s xs :
  (forall z, Sv.In z xs -> afact s z Afull) -> ahold S s ->
  ahold (Sv.fold (fun y S => Mvar.set S y Afull) xs S) s.
Proof.
rewrite Sv.fold_spec => hxs; have : forall z, z \in Sv.elements xs -> afact s z Afull.
+ by move=> z /Sv_elemsP; apply hxs.
elim: (Sv.elements xs) S => //= z l ih S hl hS.
apply ih; first by move=> ? h; apply hl; rewrite inE h orbT.
by apply ahold_set => //; apply hl; rewrite inE eqxx.
Qed.

Lemma afact_full_eq s x y : vget s x = vget s y -> afact s y Afull -> afact s x Afull.
Proof. by rewrite /= (arr_lenE (sm := total) (evm s) x) (arr_lenE (sm := total) (evm s) y) => ->. Qed.

Lemma aset_fullP S s x : ahold S s -> afact s x Afull -> ahold (aset_full S x) s.
Proof.
move=> hS hx; rewrite /aset_full.
set xs := if Mvar.get S x is Some (Acopy y) then _ else _.
have hxs : forall z, Sv.In z xs -> afact s z Afull.
+ rewrite /xs; case h: Mvar.get => [ [] | ]; try by move=> z /SvD.F.singleton_iff <-.
  move=> z /Sv.add_spec [-> | /SvD.F.singleton_iff <- //].
  by apply: afact_full_eq hx; rewrite (hS _ _ h).
apply ahold_fold_full => // w a; rewrite Mvar.mapP.
case h: (Mvar.get S w) => [b | ] //= [<-].
have := hS _ _ h; case: b h => // z h /= hwz; case: ifP => // /Sv_memP /hxs; exact: afact_full_eq.
Qed.

Definition is_initbv (v : value) k := if v is Varr _ t then WArray.is_initb t k else false.

(* The bytes of [l] in the bounds of [v] are 0xFF. *)
Definition ffbw (v : value) (l : seq (Z * Z)) :=
  forall k, in_ivs l k -> (0 <= k < vlen v)%Z -> is_initbv v k.

Lemma ffb_w v l : ffb v l -> ffbw v l.
Proof.
case: v => /= [b | z | n t | ws w | ty hty] h k hk /= hb; try lia.
exact: (h k hk).2.
Qed.

Lemma aof_ivsP v l a : ffbw v l -> aof_ivs (vlen v) l = Some a ->
  ffb v (ivs_of_aval (vlen v) a) /\ (a = Afull \/ exists l', a = Ainit l').
Proof.
move=> h; rewrite /aof_ivs.
have : forall k, in_ivs (take iv_max (iv_inter l (iv_bounds (vlen v)))) k -> in_ivs l k /\ (0 <= k < vlen v)%Z.
+ move=> k /in_ivs_take; rewrite iv_interP iv_boundsP => /andP [-> /andP [/ZleP ? /ZltP ?]]; split => //; lia.
move: (take _ _) => l' hl'.
have hf : ffb v l'.
+ case: v h hl' => /= [b | z | n t | ws w | ty hty] h hl' k; try by apply/negP => /hl' [_ /= ?]; lia.
  by move=> /hl' [hk hb]; split => //; apply (h k hk hb).
case: l' hl' hf => // ab l2 hl' hf; case: ifP => hincl [<-]; split; auto; last by right; eexists.
apply: ffb_sub hf => k; rewrite /ivs_of_aval iv_boundsP => /andP [/ZleP ? /ZltP ?].
by apply: (iv_inclP hincl); lia.
Qed.

Lemma afact_aof s x l a : ffbw (vget s x) l -> aof_ivs (arr_len x) l = Some a -> afact s x a.
Proof.
rewrite (arr_lenE (sm := total) (evm s) x) => h /(aof_ivsP h) [hf [? | [l' ?]]]; subst a;
  by rewrite /afact (arr_lenE (sm := total) (evm s) x).
Qed.

Lemma afact_init_eq s x y l : vget s x = vget s y -> afact s y (Ainit l) -> afact s x (Ainit l).
Proof. by rewrite /= => ->. Qed.

Lemma aadd_ivsP S s x a b : ahold S s ->
  (forall j, (a <= j < b)%Z -> is_initbv (vget s x) j) -> ahold (aadd_ivs S x a b) s.
Proof.
move=> hS hab; rewrite /aadd_ivs; case: ifP => // _.
set y := if Mvar.get S x is Some (Acopy y) then y else x.
have hy : vget s x = vget s y.
+ by rewrite /y; case h: Mvar.get => [ [] | ] //; rewrite (hS _ _ h).
set S' := match aof_ivs _ _ with Some Afull => _ | _ => _ end.
have : ahold S' s; last by case: (Mvar.get S y) => [ [] | ].
have hw : ffbw (vget s x) (iv_add a b (ivs_of_var S x)).
+ move=> k; rewrite iv_addP => /orP [/andP [/ZleP ? /ZltP ?] _ | hk]; first by apply hab; lia.
  exact: ffb_w (ivs_of_varP x hS) k hk.
rewrite /S'; case h: aof_ivs => [f | ] //.
have hf := afact_aof hw h.
case: f h hf => [c | | z | lo n | l] h hf; try by move: h; rewrite /aof_ivs; case: take => // ? ?; case: ifP.
+ exact: aset_fullP.
apply: ahold_set hS _; apply: afact_init_eq hf; exact: esym hy.
Qed.

(* The facts that an assertion that holds establishes hold. *)
Lemma learn_aP S s a : ahold S s -> sem_eassert gd s a = ok true -> ahold (learn_a S a) s.
Proof.
elim: a S => /=.
+ move=> p S hS; case: p => // x; case: andP => [[hx /eqP hty] | //].
  rewrite get_lvarP //= => h; apply: ahold_set hS _; by rewrite /= (to_boolI h).
+ move=> o es S hS; case: o => // len.
  case: es => [ | e1 es]; first by move=> _.
  case: e1 => [> | > | > | x | > | > | > | > | > | > | >]; try by move=> _.
  case: es => [ | e2 es]; first by move=> _.
  case: e2 => [lo | > | > | > | > | > | > | > | > | > | >]; try by move=> _.
  case: es => [ | e3 es]; first by move=> _.
  case: e3 => [k | > | > | > | > | > | > | > | > | > | >]; try by move=> _.
  case: es => [ | ? ?]; last by move=> _.
  case: ifP => // hx; case hty: vtype => [ | | ws xlen | ] //; case: eqP => // hl.
  have [t ht] := vget_arr s hty.
  rewrite /= /get_gvar hx /get_var get_total_defined ht /= (barr_initE _ _ _ hl) => -[] /allP hall.
  have hin : forall j, (lo <= j < lo + k)%Z -> is_initbv (vget s (gv x)) j.
  + by move=> j hj; rewrite ht /=; apply hall; rewrite in_ziota; apply/andP; split; [apply/ZleP | apply/ZltP]; lia.
  case: ifP => [/andP [/ZleP ? /ZleP ?] | _]; last exact: aadd_ivsP.
  apply: aset_fullP hS _; rewrite /= /arr_len hty ht => j; rewrite iv_boundsP => /andP [/ZleP ? /ZltP ?].
  split => //; have := hin j; rewrite ht; apply; lia.
+ by [].
+ by [].
move=> a1 h1 a2 h2 S hS; t_xrbindP => b1 hb1 b2 hb2 hb.
case: b1 hb1 hb => // hb1; case: b2 hb2 => // hb2 _.
by apply: h2 (h1 _ hS hb1) hb2.
Qed.

(* ------------------------------------------------------------------------- *)
(* Equal facts, joins                                                         *)

Lemma eq_expr_val_of_lit e1 e2 : eq_expr e1 e2 -> val_of_lit e1 = val_of_lit e2.
Proof.
case: e1 => [z | b | > | > | > | > | > | o e | > | > | >]; case: e2 => [z' | b' | > | > | > | > | > | o' e' | > | > | >] //=.
+ by move=> /eqP ->.
+ by move=> /eqP ->.
move=> /andP [/eqP <-]; case: o => // ws; case: e => [z | > | > | > | > | > | > | > | > | > | >]; case: e' => [z' | > | > | > | > | > | > | > | > | > | >] //=.
by move=> /eqP ->.
Qed.

Lemma eq_expr_stable e1 e2 : eq_expr e1 e2 -> is_stable_int e1 = is_stable_int e2.
Proof.
elim: e1 e2 => [z | b | ws n | x | al aa w x e ih | aa w len x e ih | al w e ih | o e ih | o a1 ih1 a2 ih2 | o es ih | t b ihb a1 ih1 a2 ih2] e2.
all: case: e2 => //=.
+ by move=> y /andP [/eqP h1 /eqP h2]; rewrite /is_lvar h1 h2.
+ by move=> o' e' /andP [/eqP <- /ih ->].
by move=> o' e1' e2' /andP [/andP [/eqP <- /ih1 ->] /ih2 ->].
Qed.
Lemma aval_beqP s x a1 a2 : aval_beq a1 a2 -> afact s x a1 <-> afact s x a2.
Proof.
case: a1 a2 => [c1 | | y1 | lo1 n1 | l1] [c2 | | y2 | lo2 n2 | l2] //=.
+ by move=> /eq_expr_val_of_lit ->.
+ by move=> /eqP ->.
+ move=> /andP [hlo hn]; rewrite (eq_expr_stable hlo) (eq_expr_stable hn) (eq_exprP _ _ _ hlo) (eq_exprP _ _ _ hn).
  by [].
by move=> /eqP ->.
Qed.

Lemma ajoinP S1 S2 s : ahold S1 s \/ ahold S2 s -> ahold (ajoin S1 S2) s.
Proof.
move=> h x a; rewrite /ajoin Mvar.map2P //.
case h1: (Mvar.get S1 x) => [a1 | ] //; case h2: (Mvar.get S2 x) => [a2 | ] //.
case: ifP => hb.
+ move=> [<-]; case: h => hS; first exact: hS _ _ h1.
  by apply/(aval_beqP _ _ hb); apply: hS _ _ h2.
apply: afact_aof => k; rewrite iv_interP => /andP [hk1 hk2].
by case: h => hS; [apply: ffb_w (afact_ivs (hS _ _ h1)) k hk1 | apply: ffb_w (afact_ivs (hS _ _ h2)) k hk2].
Qed.

Lemma in_keys (l : seq (var * aval)) x : x \in map fst l <-> exists a, List.In (x, a) l.
Proof.
elim: l => [ | [y b] l ih] /=; first by split => // -[].
rewrite inE; split.
+ by case/orP => [/eqP -> | /ih [a h]]; [exists b; left | exists a; right].
by move=> [a [[-> _] | h]]; [rewrite eqxx | apply/orP; right; apply/ih; exists a].
Qed.

(* Two states with the same facts. *)
Lemma aeqP S1 S2 s : aeq S1 S2 -> ahold S1 s -> ahold S2 s.
Proof.
rewrite /aeq /asize => /andP [/eqP hsz /allInP hall] hS x b hb.
have hsub : {subset map fst (Mvar.elements S1) <= map fst (Mvar.elements S2)}.
+ move=> y /in_keys [a ha]; have := hall _ ha; rewrite /=.
  by case h: Mvar.get => [c | ] // _; apply/in_keys; exists c; apply/Mvar.elementsIn.
have hsz' : size (map fst (Mvar.elements S2)) <= size (map fst (Mvar.elements S1)) by rewrite !size_map hsz.
have [_ heq] := uniq_min_size (Mvar.elementsU S1) hsub hsz'.
have : x \in map fst (Mvar.elements S1).
+ by rewrite heq; apply/in_keys; exists b; apply/Mvar.elementsIn.
move=> /in_keys [a ha]; have := hall _ ha; rewrite /= hb => hab.
by apply/(aval_beqP _ _ hab); apply: hS; apply/(Mvar.elementsIn (x, a)).
Qed.

(* ------------------------------------------------------------------------- *)
(* The writes                                                                 *)

Lemma stable_semP s s' e : is_stable_int e ->
  (forall y, Sv.In y (read_e e) -> vget s y = vget s' y) -> sem s e = sem s' e.
Proof.
elim: e => [z | b | ws n | x | al aa w x e ih | aa w len x e ih | al w e ih | o e ih | o e1 ih1 e2 ih2 | o es ih | t b ihb e1 ih1 e2 ih2] //=.
+ move=> /andP [hx _] h; rewrite /get_gvar hx /get_var !get_total_defined h //.
  by rewrite read_e_var /read_gvar hx; SvD.fsetdec.
+ by case: o => // -[] // /ih h hr; rewrite h.
case: o => // -[] // /andP [/ih1 h1 /ih2 h2] hr; rewrite h1 ?h2 // => y hy; apply hr; rewrite read_e_Papp2; SvD.fsetdec.
Qed.

Lemma vget_eq_ex s s' xs y : evm s =[\ xs] evm s' -> ~ Sv.In y xs -> vget s y = vget s' y.
Proof. by move=> h hy; apply: Vm.get_eq_mode erefl (h y hy). Qed.

(* The facts kept by [akill] still hold after a write to [xs]. *)
Lemma akillP S s s' xs : ahold S s -> evm s =[\ xs] evm s' -> ahold (akill S xs) s'.
Proof.
move=> hS heq y a; rewrite /akill Mvar.filter_mapP.
case h: (Mvar.get S y) => [b | ] //=; case: Sv_memP => // hy.
case hk: akeep => // -[<-]; have := hS _ _ h.
have hyy := vget_eq_ex heq hy.
case: b h hk => /= [c | | z | lo n | l] h hk.
1,2,5: by rewrite hyy.
+ move=> hyz; rewrite -hyy hyz; apply: vget_eq_ex heq _ => hz.
  by move: hk; case: Sv_memP.
move=> [hlo hn [lo' [n' [hl hn' hf]]]]; split => //; exists lo', n'; rewrite -hyy; split => //.
all: have hd : forall z, Sv.In z (Sv.union (read_e lo) (read_e n)) -> ~ Sv.In z xs.
1,3: by move/Sv.is_empty_spec: hk; rewrite read_e_Papp2 => hk z h1 h2; apply: (hk z); SvD.fsetdec.
+ rewrite -hl; symmetry; apply: stable_semP hlo _ => z hz; apply: vget_eq_ex heq _; apply hd; SvD.fsetdec.
rewrite -hn'; symmetry; apply: stable_semP hn _ => z hz; apply: vget_eq_ex heq _; apply hd; SvD.fsetdec.
Qed.
Lemma write_var_vget s s' (x : var_i) v :
  write_var true x v s = ok s' -> is_defined v -> type_of_val v = eval_atype (vtype x) ->
  vget s' x = v /\ evm s =[\ Sv.singleton x] evm s'.
Proof.
move=> hw hd ht; split; last exact: vrvP_var hw.
move: hw; rewrite /write_var; t_xrbindP => vm /set_varP [_ _ ->] <- /=.
by rewrite Vm.get_modeE /= Vm.setP_eq vm_truncate_val_eq // hd.
Qed.

Lemma aassignP S s s' x oa :
  ahold S s -> evm s =[\ Sv.singleton x] evm s' ->
  (forall a, oa = Some a -> a <> Acopy x -> afact s' x a) -> ahold (aassign S x oa) s'.
Proof.
move=> hS heq ha; have hk := akillP hS heq; rewrite /aassign.
case: oa ha => [a | ] // ha; case: a ha => [c | | y | lo n | l] ha; try (apply: ahold_set hk (ha _ erefl _) => //).
case: eqP => [// | hyx]; apply: ahold_set hk (ha _ erefl _) => -[] /esym.
by move=> h; apply hyx; rewrite h.
Qed.

Lemma write_arr_vget s s' (x : var_i) ws len v v' :
  vtype x = aarr ws len -> truncate_val (eval_atype (aarr ws len)) v = ok v' ->
  write_var true x v' s = ok s' -> vget s' x = v /\ evm s =[\ Sv.singleton x] evm s'.
Proof.
move=> hx /truncate_val_typeE [t -> ->] hw.
by apply: (write_var_vget hw) => //=; rewrite hx.
Qed.

Lemma aval_of_e_ivs S s s' (x : var_i) ws len e v v' a :
  ahold S s -> sem s e = ok v -> vtype x = aarr ws len ->
  truncate_val (eval_atype (aarr ws len)) v = ok v' -> write_var true x v' s = ok s' ->
  aof_ivs (arr_len x) (ivs_of_e S (arr_len x) e) = Some a -> afact s' x a.
Proof.
move=> hS he hx htr hw; have [hv _] := write_arr_vget hx htr hw.
apply: afact_aof; rewrite hv; exact: ffb_w (ivs_of_eP _ hS he).
Qed.

Lemma aval_of_e_fill S s s' (x : var_i) ws len es v v' :
  ahold S s -> sem s (PappN (Oarr_fill ws len) es) = ok v -> vtype x = aarr ws len ->
  truncate_val (eval_atype (aarr ws len)) v = ok v' -> write_var true x v' s = ok s' ->
  (is_full_fill ws len es -> afact s' x Afull) /\
  (forall lo n, is_ones_fill es = Some (lo, n) -> afact s' x (Afill lo n)).
Proof.
move=> hS he hx htr hw; have [hv heq] := write_arr_vget hx htr hw.
have hlen : arr_len x = arr_size ws len by rewrite /arr_len hx.
split.
+ move=> hfull; have : is_full S (arr_size ws len) (PappN (Oarr_fill ws len) es) by rewrite /= eqxx.
  move=> /(is_fullP hS) [k [t [hk hm hall]]]; move: he; rewrite hm => -[hvt].
  rewrite /= hv -hvt hlen => j; rewrite iv_boundsP => /andP [/ZleP ? /ZltP ?]; subst k; split; [lia | apply hall; lia].
move=> lo n; rewrite /is_ones_fill.
case: es he => [ | lo' [ | n' [ | e3 es]]] he; try done.
case: e3 he => [> | > | > | > | > | > | > | o1 p | > | > | >] he; try done.
case: o1 he; try done.
case; try done.
case: p => [z | > | > | > | > | > | > | > | > | > | >] he; try done.
case: es he => [ | ? ?] he; last done.
case: ifP => // /and3P [/eqP hz hlo hn] [??]; subst lo' n'.
move: he; rewrite /=; t_xrbindP => vs vlo hlo' vs' vn hn'.
move=> <- <- /sem_opN_fillI [a [b [? ? hvf]]]; subst vlo vn.
have hst : forall e, is_stable_int e -> sem s' e = sem s e.
+ move=> e0 he0; apply: (stable_semP he0) => y hy; symmetry; apply: vget_eq_ex heq _ => /SvD.F.singleton_iff hyx.
  by have := stable_read he0 hy; rewrite -hyx hx.
split => //; exists a, b; rewrite !hst // hlo' hn'; split => //.
rewrite hv hvf hlen hz; exact: ffb_fill.
Qed.

Lemma aval_of_eP S s s' x ty e v v' a :
  ahold S s -> sem s e = ok v -> truncate_val (eval_atype ty) v = ok v' ->
  write_var true x v' s = ok s' -> aval_of_e S x ty e = Some a -> a <> Acopy x -> afact s' x a.
Proof.
move=> hS he htr hw; rewrite /aval_of_e; case: eqP => // hty.
have hw' : forall v'', v' = v'' -> is_defined v'' -> type_of_val v'' = eval_atype (vtype x) ->
  vget s' x = v'' /\ evm s =[\ Sv.singleton x] evm s'.
+ by move=> v'' <-; apply: write_var_vget hw.
have hne : forall z, z <> v_var x -> vget s' z = vget s z.
+ by move=> z hz; symmetry; apply: vget_eq_ex (vrvP_var hw) _ => /SvD.F.singleton_iff h; apply hz; rewrite h.
case: e he => [z | b | > | y | > | aa ws slen y i | > | o1 e1 | > | o es | >] he; try by case: ty hty htr.
+ case: ty hty htr => //= hty; case: he => <- [?] [<-] _; subst v'.
  have [|hx _] := hw' _ erefl erefl; first by rewrite -hty.
  by rewrite /= hx.
+ case: ty hty htr => //= hty; case: he => <- [?] [<-] _; subst v'.
  have [|hx _] := hw' _ erefl erefl; first by rewrite -hty.
  by rewrite /= hx.
+ case: ty hty htr => //= ws len hty; case: andP => // -[hy /eqP hyty].
  move: he; rewrite get_lvarP // => -[?]; subst v.
  move=> /truncate_val_typeE [t ht ?]; subst v'.
  have [|hx heq] := hw' _ erefl erefl; first by rewrite -hty.
  have hxa : vtype x = aarr ws len by [].
  have hlen : arr_len x = arr_len (gv y) by rewrite /arr_len hyty hxa.
  case h: (Mvar.get S (gv y)) => [b | ]; last first.
  + move=> [<-] hax /=; rewrite hx hne ?ht // => hyx; apply hax; rewrite hyx.
    by [].
  have hb := hS _ _ h; case: b h hb => [c | | z | lo n | l] h hb // [<-] hax.
  + by move: hb; rewrite /= hx hlen ht.
  + by move: hb; rewrite /= hx -ht => ->; rewrite hne // => hzx; apply hax; rewrite hzx.
  + have hst : forall e, is_stable_int e -> sem s' e = sem s e.
    + move=> e0 he0; apply: (stable_semP he0) => z hz; rewrite hne // => hzx.
      by have := stable_read he0 hz; rewrite hzx hxa.
    move: hb => /= [hlo hn [lo' [n' [h1 h2 hf]]]]; split => //; exists lo', n'.
    by rewrite !hst // hx hlen -ht.
  by move: hb; rewrite /= hx ht.
+ case: ty hty htr => //= ws' len' hty htr h _.
  exact: (aval_of_e_ivs hS he (esym hty) htr hw h).
+ case: o1 he => // ws he; case: e1 he => // z he; case: ty hty htr => //= ws' hty; case: eqP => // ?; subst ws'.
  move: he; rewrite /= /sem_sop1 /= => -[<-]; rewrite /truncate_val /= truncate_word_u => -[?] [<-] _; subst v'.
  have [|hx _] := hw' _ erefl erefl; first by rewrite -hty.
  by rewrite /= hx.
case: o he => // ws len he; case: ty hty htr => //= ws' len' hty htr.
case: eqP => // -[? ?]; subst ws' len'.
have [hf ho] := aval_of_e_fill hS he (esym hty) htr hw.
case: ifP => [/hf h [<-] // | _].
by case h: is_ones_fill => [ [lo n] | ] // [<-] _; apply ho.
Qed.

Lemma set_ffbw n (t t' : WArray.array n) al aa ws i (w : word ws) l :
  WArray.set (sm := total) t al aa i w = ok t' -> ffb (Varr t) l ->
  let off := (i * mk_scale aa ws)%Z in
  ffbw (Varr t') (iv_remove l off (off + wsize_size ws)) /\
  (w = wrepr ws (-1) -> ffbw (Varr t') (iv_add off (off + wsize_size ws) l)).
Proof.
move=> hset hf off; split.
+ move=> k; rewrite iv_removeP => /andP [hk hnk] hb /=; rewrite /WArray.is_initb (set_total_data hset) /=.
  have -> : [&& (0 <=? k - i * mk_scale aa ws)%Z, (k - i * mk_scale aa ws <? wsize_size ws)%Z & WArray.in_bound t k] = false.
  + apply/negbTE; move: hnk; rewrite /off; apply: contra => /and3P [/ZleP ? /ZltP ? _].
    by apply/andP; split; [apply/ZleP | apply/ZltP]; lia.
  exact: (hf k hk).2.
move=> ? k; subst w; rewrite iv_addP /off => hk /= hb; rewrite /WArray.is_initb (set_total_data hset) /=.
case: ifP => [/and3P [/ZleP h1 /ZltP h2 _] | hn]; first by rewrite wread8_m1 //; lia.
case/orP: hk => [/andP [/ZleP h1 /ZltP h2] | hk]; last exact: (hf k hk).2.
move/negbT: hn; rewrite /WArray.in_bound !negb_and => /or3P [/ZleP | /ZltP | /orP [/ZleP | /ZltP]]; lia.
Qed.

Lemma set_sub_ffbw lena (t : WArray.array lena) aa ws len i (b : WArray.array (arr_size ws len)) l le :
  ffb (Varr t) l -> ffb (Varr b) le ->
  let off := (i * mk_scale aa ws)%Z in
  let t' := WArray.Build_array lena (WArray.set_sub_data lena aa ws len (WArray.arr_data t) i (WArray.arr_data b)) in
  ffbw (Varr t') (iv_union (iv_shift off le) (iv_remove l off (off + arr_size ws len))) /\
  (iv_incl le 0 (arr_size ws len) -> ffbw (Varr t') l).
Proof.
move=> hf hb off t'; split.
+ move=> k; rewrite iv_unionP iv_shiftP iv_removeP => hk /= hkb.
  rewrite /WArray.is_initb /t' /= WArray.set_sub_data_get8 /= -/off.
  case: ifP => [/and4P [/ZleP ? /ZltP ? _ _] | hn].
  + case/orP: hk => [hk | /andP [_ /negP []]]; first exact: (hb _ hk).2.
    by apply/andP; split; [apply/ZleP | apply/ZltP]; lia.
  case/orP: hk => [hk | /andP [hk _]]; last exact: (hf _ hk).2.
  have [? _] := hb _ hk; move/negbT: hn; rewrite !negb_and => /or4P [/ZleP | /ZltP | /ZleP | /ZltP]; lia.
move=> hincl k hk /= hkb; rewrite /WArray.is_initb /t' /= WArray.set_sub_data_get8 /= -/off.
case: ifP => [/and4P [/ZleP ? /ZltP ? _ _] | _]; last exact: (hf _ hk).2.
by apply: (hb _ (iv_inclP hincl _)).2; lia.
Qed.

Lemma aset_ivsP S s s' x l : ahold S s -> evm s =[\ Sv.singleton x] evm s' -> ffbw (vget s' x) l ->
  ahold (aset_ivs S x l) s'.
Proof.
move=> hS heq hl; have hk := akillP hS heq; rewrite /aset_ivs.
by case h: aof_ivs => [a | ] //; apply: ahold_set hk (afact_aof hl h).
Qed.

(* The facts depend on the variables only. *)
Lemma ahold_vm S s s' : evm s = evm s' -> ahold S s -> ahold S s'.
Proof.
move=> heq hS; have := @akillP S s s' Sv.empty hS.
have he : evm s =[\Sv.empty] evm s' by rewrite heq.
move=> /(_ he) h y a hy; apply h; rewrite /akill Mvar.filter_mapP hy /=.
case: a {hy} => //=.
move=> lo n; have -> // : disjoint (read_e (eint_add lo n)) Sv.empty.
by apply/Sv.is_empty_spec; SvD.fsetdec.
Qed.

Lemma ffbw_sub v l l' : (forall k, in_ivs l' k -> in_ivs l k) -> ffbw v l -> ffbw v l'.
Proof. by move=> hsub h k /hsub; apply h. Qed.
Lemma ffbw_nil v : ffbw v [::].
Proof. by []. Qed.
Lemma vget_arr_type s x n (t : WArray.array n) : vget s x = Varr t -> eval_atype (vtype x) = carr n.
Proof. by move=> h; have := Vm.getP_mode (sm := total) (evm s) x; rewrite h => /compat_valE. Qed.
Lemma is_onesP s ws ty e v v' (w : word ws) : is_ones ws ty e -> sem s e = ok v ->
  truncate_val (eval_atype ty) v = ok v' -> to_word ws v' = ok w -> w = wrepr ws (-1).
Proof.
case: e => // -[] // ws' [] // z /and3P [/eqP ? /eqP ? /eqP hz]; subst ws' ty.
rewrite /= /sem_sop1 /= => -[<-]; rewrite /truncate_val /= truncate_word_u => -[<-] /=.
by rewrite truncate_word_u hz => -[<-].
Qed.

Lemma aassgnP S s s' lv ty e v v' :
  ahold S s -> sem s e = ok v -> truncate_val (eval_atype ty) v = ok v' ->
  write_lval (sm := total) true gd lv v' s = ok s' -> ahold (aassgn S lv ty e) s'.
Proof.
move=> hS he htr hw; rewrite /aassgn; rewrite -(simpl_eP _ hS) in he; move: (simpl_e S e) he => {}e he.
case: lv hw => [vi tyn | x | al ws y ei | al aa ws x i | aa ws len x i] /= hw.
+ by move: hw; rewrite /write_none; t_xrbindP => _ _ <-.
+ by apply: (aassignP hS (vrvP_var hw)) => a ha hax; exact: (aval_of_eP hS he htr hw ha hax).
+ move: hw; t_xrbindP.
  by move=> *; subst s'; apply: (ahold_vm _ hS).
+ move: hw; rewrite /get_var get_total_defined /=.
  have hf := ivs_of_varP x hS.
  case hx: (vget s x) hf => [ | | n t | | ] // hf; t_xrbindP => iv vi hi /to_intI ? w hw' t' hset hwr; subst vi.
  have [hv heq] := write_var_vget hwr erefl (esym (vget_arr_type hx)).
  apply: (aset_ivsP hS heq); rewrite hv.
  have hik : forall k, simpl_e S i = Pconst k -> iv = k
    by move=> k hk; move: hi; rewrite -(simpl_eP _ hS) hk => -[].
  have [h1 h2] := set_ffbw hset hf.
  case: ifP => hones.
  - have hw1 := is_onesP hones he htr hw'.
    case: (simpl_e S i) hik => [k | > | > | > | > | > | > | > | > | > | >] hik.
    1: by rewrite -(hik k erefl); exact: (h2 hw1).
    1-10: by apply: (ffbw_sub _ (h2 hw1)) => k hk; rewrite iv_addP hk orbT.
  - case: (simpl_e S i) hik => [k | > | > | > | > | > | > | > | > | > | >] hik; try exact: ffbw_nil.
    by rewrite -(hik k erefl).
move: hw; rewrite /get_var get_total_defined /=.
have hf := ivs_of_varP x hS.
case hx: (vget s x) hf => [ | | n t | | ] // hf; t_xrbindP => iv vi hi /to_intI ? b hb hwr; subst vi.
have [hv heq] := write_var_vget hwr erefl (esym (vget_arr_type hx)).
apply: (aset_ivsP hS heq); rewrite hv.
have hik : forall k, simpl_e S i = Pconst k -> iv = k
  by move=> k hk; move: hi; rewrite -(simpl_eP _ hS) hk => -[].
have hle : ffb (Varr b) (if ty == aarr ws len then ivs_of_e S (arr_size ws len) e else [::]).
+ case: eqP => [? | _]; last exact: ffb_nil.
  subst ty; have hvf := ivs_of_eP (arr_size ws len) hS he.
  move: htr => /truncate_val_typeE [t0 ? ?]; subst v v'.
  by move: hb; rewrite to_arrK => -[<-].
have [h1 h2] := set_sub_ffbw aa iv hf hle.
case: (simpl_e S i) hik => [k | > | > | > | > | > | > | > | > | > | >] hik.
1: by rewrite -(hik k erefl); exact: h1.
1-10: by case: ifP => // /h2.
Qed.

Lemma afact_keep s s' xs y a : afact s y a -> evm s =[\ xs] evm s' -> ~ Sv.In y xs -> akeep xs a ->
  afact s' y a.
Proof.
move=> hf heq hy hk.
have h : ahold (Mvar.set (Mvar.empty _) y a) s.
+ by move=> z b; rewrite Mvar.setP; case: eqP => // <- [<-].
apply: (akillP h heq); rewrite /akill Mvar.filter_mapP Mvar.setP_eq /=.
by case: Sv_memP => // _; rewrite hk.
Qed.

Lemma akeep_sub xs xs' a : Sv.Subset xs' xs -> akeep xs a -> akeep xs' a.
Proof.
move=> hsub; case: a => [c | | z | lo n | l] /=.
1,2,5: by [].
+ by apply: contra => /Sv_memP h; apply/Sv_memP; clear -hsub h; SvD.fsetdec.
by move=> /Sv.is_empty_spec h; apply/Sv.is_empty_spec; clear -hsub h; SvD.fsetdec.
Qed.

Lemma ahold_empty s : ahold (Mvar.empty _) s.
Proof. by move=> x a; rewrite Mvar.get0. Qed.

End SEM.

(* ------------------------------------------------------------------------- *)
(* The loops                                                                  *)

Section LOOP.

Context
  {asm_op : Type} {asmop : asmOp asm_op}
  {syscall_state : Type} {ep : EstateParams syscall_state} {spp : SemPexprParams}
  (gd : glob_decls).

(* The state at the head of the loop that [wloop] analyses the body from:
   implied by the state on entry and by the state after the body. *)
Lemma wloopP body n S S1 c1 c2 : wloop body n S = (S1, c1, c2) ->
  exists S0 S2, [/\ body S0 = (S1, S2, c1, c2), forall s, ahold gd S s -> ahold gd S0 s & forall s, ahold gd S2 s -> ahold gd S0 s].
Proof.
elim: n S => [ | n ih] S /=.
all: case h: (body S) => [[[s1 s2] c4] c3]; case: ifP => heq.
1,3: by move=> [<- <- <-]; exists S, s2; split => // s hs; apply: (aeqP heq); apply: ajoinP; right.
+ case h': (body (Mvar.empty _)) => [[[s3 s4] c6] c5] [<- <- <-].
  by exists (Mvar.empty _), s4; split => // s _; exact: ahold_empty.
move=> /ih [S0 [S2 [hb h1 h2]]]; exists S0, S2; split => // s hs; apply h1; apply ajoinP; left; exact hs.
Qed.

End LOOP.

(* ------------------------------------------------------------------------- *)
(* The two programs                                                           *)

Section PROOF.

Context
  {asm_op syscall_state : Type} {ep : EstateParams syscall_state}
  {spp : SemPexprParams} {sip : SemInstrParams asm_op syscall_state}
  {E E0 : Type -> Type} {wE : with_Error E E0} {rE : EventRels E0}.

#[local] Existing Instance withassert_nocontract.
#[local] Existing Instance total_init.

Context (p : uprog) (ev : extra_val_t).

Notation p' := (simplify_asserts_prog p).
Notation gd := (p_globs p).

Lemma sem_tot s e : sem_pexpr (sm := total_init) true gd s e = sem_pexpr (sm := total) true gd s e.
Proof. by apply: sem_pexpr_is_totalE. Qed.

Lemma write_lval_tot x v s : write_lval (sm := total_init) true gd x v s = write_lval (sm := total) true gd x v s.
Proof. by apply: write_lval_is_totalE. Qed.

Lemma ahold_add S0 s x (oa : option aval) (b : aval -> bool) :
  ahold gd S0 s -> (forall a, oa = Some a -> b a -> afact gd s x a) ->
  ahold gd (match oa with Some a => if b a then Mvar.set S0 x a else S0 | None => S0 end) s.
Proof. by move=> hS h; case: oa h => // a h; case: ifP => // hb; apply: ahold_set hS (h _ erefl hb). Qed.

Lemma aopnP S s s' xs o es :
  ahold gd S s -> sem_sopn gd o s xs es = ok s' -> ahold gd (aopn S xs o es) s'.
Proof.
move=> hS; rewrite /sem_sopn; t_xrbindP => vo va hva hex hw.
have hk := akillP hS (vrvsP hw).
rewrite /aopn; case: o hex => [[] | | ] //.
move=> ty hex; case: ty hex => [ | | ws len | ws] hex; try exact hk.
case: xs hw hk => [ | lv1 xs] hw hk; first exact hk.
case: lv1 hw hk => [ > | x1 | > | > | >] hw hk; try exact hk.
case: xs hw hk => [ | lv2 xs] hw hk; first exact hk.
case: lv2 hw hk => [ > | x2 | > | > | >] hw hk; try exact hk.
case: xs hw hk => [ | ? ?] hw hk; last exact hk.
case: es hva => [ | e1 [ | e2 [ | ? ?]]] hva; try exact hk.
case: ifP => [/and3P [/eqP hx1 /eqP hx2 hne] | _]; last exact hk.
have [a1 [a2 [? ?]]] := exec_swapE hex; subst va vo.
move: hva; rewrite /sem_pexprs /=; t_xrbindP.
move=> v1 hv1 vs2 v2 hv2 ? ? hvs2; subst v1 vs2; case: hvs2 => ?; subst v2.
rewrite sem_tot -(simpl_eP _ hS) in hv1; rewrite sem_tot -(simpl_eP _ hS) in hv2.
move: hw; rewrite /=; t_xrbindP => s1 hw1 s2 hw2 [?]; subst s2.
have hxs : Sv.Equal (vrvs [:: Lvar x1; Lvar x2]) (Sv.union (Sv.singleton x1) (Sv.singleton x2)).
+ by rewrite !vrvs_cons vrv_var vrv_var /vrvs /=; clear; SvD.fsetdec.
have htr : forall a : WArray.array (arr_size ws len), truncate_val (eval_atype (aarr ws len)) (Varr a) = ok (Varr a).
+ by move=> a; rewrite /truncate_val /= to_arrK.
have hcp : forall z a, Sv.In z (vrvs [:: Lvar x1; Lvar x2]) -> akeep (vrvs [:: Lvar x1; Lvar x2]) a -> a <> Acopy z.
+ by move=> z a hz hka ?; subst a; move: hka => /=; case: Sv_memP.
have hne' : v_var x1 <> v_var x2 by move=> h; move: hne; rewrite h eqxx.
have hin1 : Sv.In x1 (vrvs [:: Lvar x1; Lvar x2]) by rewrite hxs; clear; SvD.fsetdec.
have hin2 : Sv.In x2 (vrvs [:: Lvar x1; Lvar x2]) by rewrite hxs; clear; SvD.fsetdec.
apply: ahold_add.
+ apply: ahold_add hk _ => a ha hka.
  have heq1 := vrvP_var hw1.
  have [vm2 hw2' heq2] := write_var_eq_ex hw2 (eq_exS heq1).
  move: hw1; rewrite /write_var; t_xrbindP => vm1 _ ?; subst s1.
  have hs : forall (s0 : estate) vm, with_vm (with_vm s0 vm) (evm s0) = s0 by case.
  rewrite hs in hw2'.
  have := aval_of_eP hS hv1 (htr a1) hw2' ha (hcp _ _ hin2 hka).
  move=> h; apply: (afact_keep h (eq_exS heq2)).
  + by move=> /SvD.F.singleton_iff h'; apply hne'; rewrite h'.
  by apply: (akeep_sub _ hka); rewrite hxs; clear; SvD.fsetdec.
move=> a ha hka.
have := aval_of_eP hS hv2 (htr a2) hw1 ha (hcp _ _ hin1 hka).
move=> h; apply: (afact_keep h (vrvP_var hw2)).
+ by move=> /SvD.F.singleton_iff h'; apply hne'; rewrite h'.
by apply: (akeep_sub _ hka); rewrite hxs; clear; SvD.fsetdec.
Qed.

(* Both programs are in the same state, where the facts hold. *)
Definition R (S : astate) (s t : estate) := s = t /\ ahold gd S s.

Lemma simpl_assgn S x tg ty e ii :
  wequiv_rec p' p ev ev eq_spec (R S) [:: MkI ii (Cassgn x tg ty e)] [:: MkI ii (Cassgn x tg ty e)]
    (R (aassgn S x ty e)).
Proof.
apply wequiv_assgn_core => s _ s' [<- hS] h; exists s' => //; split => //.
move: h; rewrite /sem_assgn; t_xrbindP => v hv v' htr hw.
by apply: aassgnP hS _ htr _; [rewrite -sem_tot | rewrite -write_lval_tot].
Qed.

Lemma simpl_opn S xs tg o es ii :
  wequiv_rec p' p ev ev eq_spec (R S) [:: MkI ii (Copn xs tg o es)] [:: MkI ii (Copn xs tg o es)]
    (R (aopn S xs o es)).
Proof.
apply wequiv_opn_esem => s _ s' [<- hS] h; exists s'; last by split => //; apply: aopnP hS h.
by rewrite esem1 /= h.
Qed.

Lemma ahold_upd S s s' wdb xs fr :
  ahold gd S s -> upd_estate (sm := total_init) wdb gd xs fr s = ok s' -> ahold gd (akill S (vrvs xs)) s'.
Proof.
move=> hS hw; apply: akillP (vrvsP hw).
by apply: ahold_vm hS.
Qed.

Lemma simpl_syscall S xs o es ii :
  wequiv_rec p' p ev ev eq_spec (R S) [:: MkI ii (Csyscall xs o es)] [:: MkI ii (Csyscall xs o es)]
    (R (akill S (vrvs xs))).
Proof.
apply wequiv_syscall_esem => s _ s1 [<- hS].
rewrite esem1 /= /sem_syscall; t_xrbindP => vs hvs fr hfr hw.
exists s1; first by rewrite hvs /= hfr /= hw.
by split => //; apply: ahold_upd hS hw.
Qed.

Lemma simpl_call S xs fn es ii :
  wequiv_rec p' p ev ev eq_spec (R S) [:: MkI ii (Ccall xs fn es)] [:: MkI ii (Ccall xs fn es)]
    (R (akill S (vrvs xs))).
Proof.
apply wequiv_call_eq_wa.
+ by move=> s _ v [<- _] ->; exists v.
+ by [].
+ by move=> s1 _ vs [<- _].
+ exact: (@wequiv_fun_rec _ _ _ _ _ _ _ _ _ _ p' p ev ev eq_spec ii ii fn fn).
+ by [].
move=> fs s _ s' [<- hS] hw; exists s' => //; split => //.
exact: ahold_upd hS hw.
Qed.

Lemma simpl_assert S a ii :
  let: (S', c') := simpl_i S (MkI ii (Cassert a)) in
  wequiv_rec p' p ev ev eq_spec (R S) c' [:: MkI ii (Cassert a)] (R S').
Proof.
case: a => lbl a /=.
have : forall s, ahold gd S s -> aholds gd s (simpl_a S a) -> sem_eassert gd s a = ok true.
+ by move=> s; apply simpl_aP.
case: simpl_a => [a' | ] hsa.
+ apply wequiv_assert => _; split => // s _ [<- hS] /= ha'; split; first exact: hsa hS ha'.
  by split => //; apply: learn_aP hS ha'.
apply wequiv_assert_right => s _ [<- hS]; split => //.
by rewrite /sem_assert /= (hsa _ hS).
Qed.

Lemma simpl_i_forE S ii x r c : simpl_i S (MkI ii (Cfor x r c)) =
  let body s := let: (s2, c) := simpl_c simpl_i (akill1 s x) c in (s, s2, c, [::]) in
  let: (s, c, _) := wloop body (iv_max * (asize S).+1) S in (s, [:: MkI ii (Cfor x r c)]).
Proof. by []. Qed.

Lemma simpl_i_whileE S ii a c1 e ii_w c2 : simpl_i S (MkI ii (Cwhile a c1 e ii_w c2)) =
  let body s :=
    let: (s1, c1) := simpl_c simpl_i s c1 in
    let: (s2, c2) := simpl_c simpl_i s1 c2 in
    (s1, s2, c1, c2) in
  let: (s1, c1, c2) := wloop body (iv_max * (asize S).+1) S in
  (s1, [:: MkI ii (Cwhile a c1 e ii_w c2)]).
Proof. by []. Qed.

Let Psi (i : instr) := forall S,
  wequiv_rec p' p ev ev eq_spec (R S) (simpl_i S i).2 [:: i] (R (simpl_i S i).1).

Let Psi_r (i : instr_r) := forall ii, Psi (MkI ii i).

Let Psc (c : cmd) := forall S,
  wequiv_rec p' p ev ev eq_spec (R S) (simpl_c simpl_i S c).2 c (R (simpl_c simpl_i S c).1).

Lemma simpl_cP c : Psc c.
Proof.
apply (cmd_rect (Pr := Psi_r) (Pi := Psi) (Pc := Psc)) => //.
+ by move=> S; apply wequiv_nil.
+ move=> i c0 hi hc S /=.
  have := hi S; case: simpl_i => S1 ci /= hi'.
  have := hc S1; case: simpl_c => S2 c2 /= hc'.
  rewrite -(cat1s i c0).
  exact: (wequiv_cat hi' hc').
+ by move=> x tg ty e ii S; apply simpl_assgn.
+ by move=> xs tg o es ii S; apply simpl_opn.
+ by move=> xs o es ii S; apply simpl_syscall.
+ by move=> a ii S; have := simpl_assert S a ii; case: simpl_i.
+ move=> e c1 c2 hc1 hc2 ii S /=.
  have := hc1 S; case: simpl_c => S1 c1' /= hc1'.
  have := hc2 S; case: simpl_c => S2 c2' /= hc2'.
  apply wequiv_if_eq; first by move=> s _ v [<- _] ->; exists v.
  case.
  + eapply wequiv_weaken; last exact hc1'.
    + by [].
    by move=> s t [-> h]; split => //; apply ajoinP; left.
  eapply wequiv_weaken; last exact hc2'.
  + by [].
  by move=> s t [-> h]; split => //; apply ajoinP; right.
+ move=> x dir lo hi c0 hc ii S; rewrite simpl_i_forE; cbv zeta.
  case hw: (wloop _ _ _) => [[S1 c1] c2] /=.
  have [S0 [S2 [hb h1 h2]]] := wloopP gd hw.
  move: hb; case hs: simpl_c => [S3 c3] [? ? ? ?]; subst S0 S3 c1 c2.
  have := hc (akill1 S1 x); rewrite hs /= => hc'.
  apply (wequiv_for_eq (P := R S1) (Pi := R (akill1 S1 x))).
  + by move=> s t [-> h]; split => //; apply h1.
  + by move=> s _ v [<- _] ->; exists v.
  + move=> i s _ s' [<- hS] hwr; exists s' => //; split => //.
    by rewrite /akill1; apply: (akillP hS (vrvP_var hwr)).
  eapply wequiv_weaken; last exact hc'.
  + by [].
  by move=> s t [-> h]; split => //; apply h2.
+ move=> al c1 e info c2 hc1 hc2 ii S; rewrite simpl_i_whileE; cbv zeta.
  case hw: (wloop _ _ _) => [[S1 c1'] c2'] /=.
  have [S0 [S2 [hb h1 h2]]] := wloopP gd hw.
  move: hb; case hs1: simpl_c => [S3 c3]; case hs2: simpl_c => [S4 c4] [? ? ? ?]; subst S3 S4 c3 c4.
  have := hc1 S0; rewrite hs1 /= => hc1'.
  have := hc2 S1; rewrite hs2 /= => hc2'.
  eapply wequiv_weaken with (P2 := R S0) (Q2 := R S1); last apply wequiv_while_eq.
  + by move=> s t [-> h]; split => //; apply h1.
  + by [].
  + by move=> s _ v [<- _] ->; exists v.
  + exact hc1'.
  eapply wequiv_weaken; last exact hc2'.
  + by [].
  by move=> s t [-> h]; split => //; apply h2.
by move=> xs fn es ii S; apply simpl_call.
Qed.
Lemma simplify_asserts_tgt_src_aux fn :
  wiequiv_f p' p ev ev (rpreF (eS := eq_spec)) fn fn (rpostF (eS := eq_spec)).
Proof.
apply wequiv_fun_ind_wa => {}fn _ fs _ [<- <-] fd.
rewrite get_map_prog; case: get_fundef => // fd0 [<-]; exists fd0 => //.
move=> _; split => // s hinit; exists s => //.
exists (R (Mvar.empty _)), (R (simpl_c simpl_i (Mvar.empty _) (f_body fd0)).1); split => //.
+ exact: simpl_cP.
by move=> s1 _ fr [<- _] h; exists fr.
Qed.

End PROOF.

(* When the transformed program runs without failure, in the mode
   [total_init] with its assertions evaluated, the source runs with the same
   results. *)
Lemma simplify_asserts_tgt_src :
  forall {asm_op syscall_state : Type} {ep : EstateParams syscall_state}
    {spp : SemPexprParams} {sip : SemInstrParams asm_op syscall_state}
    {E E0 : Type -> Type} {wE : with_Error E E0} {rE : EventRels E0}
    (p : prog) (ev : extra_val_t),
  forall fn,
  wiequiv_f (sm1 := total_init) (sm2 := total_init)
    (wa1 := withassert_nocontract) (wa2 := withassert_nocontract)
    (simplify_asserts_prog p) p ev ev (rpreF (eS := eq_spec)) fn fn (rpostF (eS := eq_spec)).
Proof.
move=> asm_op syscall_state ep spp sip E E0 wE rE p ev fn.
exact: simplify_asserts_tgt_src_aux.
Qed.
