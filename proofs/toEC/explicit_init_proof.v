(* * Correctness of the pass explicit_init.

   The instrumented program, run in the mode [total_init] (every output of an
   instruction is defined: the semantics the extraction to EasyCrypt computes)
   with assertions enabled, refines the original program run in the total
   mode. The masks are fresh variables that record exactly the raw
   initialisation of the variables of the program; on the variables of the
   program the two states agree on their total reads, which is all the total
   mode observes. *)

From mathcomp Require Import ssreflect ssrfun ssrbool ssralg eqtype word_ssrZ.
Require Import psem psem_facts compiler_util explicit_init safety_common_proof.
Require Import sopn_facts sopn_semi_facts safety_cond_facts safety_common safety_proof.
Require Import pseudo_operator slh_ops.
Import Utf8 Lia.

Local Open Scope Z_scope.
Local Open Scope seq_scope.

Section EXPLICIT_INIT_PROOF.

#[local] Existing Instance progUnit.

Context
  {asm_op syscall_state : Type}
  {ep : EstateParams syscall_state}
  {spp : SemPexprParams}
  {sip : SemInstrParams asm_op syscall_state}.

#[local] Existing Instance sCP_unit.
#[local] Existing Instance nosubword.
#[local] Existing Instance indirect_c.
(* The assertions are evaluated: [withassert] or [withassert_nocontract]. *)
Context {wa : WithAssert}.
Hypothesis assert_allowed_wa : assert_allowed.

Variable (p : uprog) (ev : extra_val_t).
Variable (mask : var -> var).
Variable (p' : uprog).

Notation gd := (p_globs p).
Notation pm := (map_prog (explicit_init_fd mask) p).
Notation mask_of := (mask_of mask).
Notation mask_lv := (mask_lv mask).
Notation mask_v := (mask_v mask).
Notation mask_gv := (mask_gv mask).

(* ------------------------------------------------------------------------- *)
(* The masks                                                                  *)

(* A mask is a fresh variable: distinct variables have distinct masks, no mask
   is a variable of the program, and the mask of [x] is a boolean for a scalar
   [x] and an array of the type of [x] for an array. *)
Hypothesis mask_inj : injective mask.
Hypothesis mask_fresh : forall x y, Sv.In y (vars_p (p_funcs p)) -> mask x <> y.
Hypothesis mask_type :
  forall x, vtype (mask x) = if is_arr_var x then vtype x else abool.

Lemma is_arr_var_mask x : is_arr_var (mask x) = is_arr_var x.
Proof using mask_type. by rewrite {1}/is_arr_var mask_type; case: ifP. Qed.

(* The contracts are not part of [vars_p]: their variables are fresh too. *)
Hypothesis mask_fresh_contract :
  forall fn fd ci, get_fundef (p_funcs p) fn = Some fd -> f_contract fd = Some ci ->
  forall x y, Sv.In y (vars_l (f_iparams ci ++ f_ires ci)) -> mask x <> y.

Definition is_mask (y : var) := exists x, mask x = y.

(* No instruction of the architecture outputs an array ([is_not_carr_ltype] in
   [arch_extra.v]): only the pseudo-operations handled by the pass do. *)
Hypothesis asm_op_tout :
  forall o : asm_op_t, all is_not_carr (map eval_atype (tout (asm_op_instr o))).

Hypothesis explicit_init_ok : explicit_init_prog mask p = ok p'.

(* ------------------------------------------------------------------------- *)
(* The checks of the pass                                                     *)

Lemma explicit_init_okE :
  [/\ p' = pm, all check_glob_init gd &
      forall fn fd, get_fundef (p_funcs p) fn = Some fd -> check_fd gd fd = ok tt].
Proof using explicit_init_ok.
move: explicit_init_ok; rewrite /explicit_init_prog; t_xrbindP => hg hf <-.
split => // fn fd /get_fundef_in' hin.
by have := allMP hin hf; move=> /add_funnameP /add_finfoP.
Qed.

(* A global array is initialised exactly in its bounds. *)
Lemma get_global_arr_init x len (t : WArray.array len) :
  get_global gd x = ok (Varr t) -> forall i, WArray.is_init t i = (0 <=? i) && (i <? len).
Proof using explicit_init_ok.
have [_ hg _] := explicit_init_okE.
rewrite /get_global; case hx: get_global_value => [g | ] //.
have := (seq_extra.allInP _ _ hg) _ (assoc_mem' hx).
case: ifP => // _; case: g {hx} => //= len' t' /andP [/allP hin /Mz.allP hout] heq.
have : Varr t' = Varr t by congruence.
move=> /Varr_inj [?]; subst len' => /= ?; subst t' => i.
rewrite /WArray.is_init; case h: Mz.get => [w | ].
- by rewrite (hout _ _ h).
have := hin i; rewrite in_ziota /WArray.is_init h Z.add_0_l.
by case: (_ && _) => // /(_ isT).
Qed.

(* ------------------------------------------------------------------------- *)
(* The relation between the states                                            *)

(* The mask of an array value: a cell of the mask is [0xFF] exactly where the
   cell of the array is initialised. *)
Definition arr_mask_of {len} (t tm : WArray.array len) :=
  forall i, WArray.is_initb tm i = WArray.is_init t i.

(* The same on values: a value that is not an array has no initialised cell,
   and none is [0xFF] in a mask that is not an array. *)
Definition is_initv (v : value) i := if v is Varr _ t then WArray.is_init t i else false.
Definition is_initbv (v : value) i := if v is Varr _ t then WArray.is_initb t i else false.
Definition val_mask_of (v m : value) := forall i, is_initbv m i = is_initv v i.

(* The masks of [vm1] describe the values of [vm2]: the mask of a scalar [x]
   holds exactly when [x] is defined in [vm2]; the mask of an array [x] is a
   mask of its value. A mask never written reads as [false] or as an empty
   array in the total mode.
   The scalars of [X] are written, defined, and their masks are not written
   yet: between a call and the masks of its scalar results, between the counter
   of a loop and its mask, between the parameters of a function and their
   masks. *)
Definition mask_inv (X : Sv.t) (vm1 vm2 : Vm.t) : Prop :=
  (forall x, ~~ is_arr_var x ->
     if Sv.mem x X then is_true (is_defined vm2.[x]%vm)
     else Vm.get (sm := total) vm1 (mask x) = Vbool (is_defined vm2.[x]%vm)) /\
  (forall x, val_mask_of vm2.[x]%vm (Vm.get (sm := total) vm1 (mask x))).

(* [vm1] is the variable map of the instrumented program, [vm2] the one of the
   original program. They agree on the total reads of every variable that is
   not a mask (an undefined scalar of [vm2] reads as its default value, which
   is what [total_init] gives to an undefined output), and the masks of [vm1]
   describe [vm2]. *)
Definition prog_eq (vm1 vm2 : Vm.t) :=
  forall x, ~ is_mask x -> Vm.get (sm := total) vm1 x = Vm.get (sm := total) vm2 x.

Definition mask_vm X (vm1 vm2 : Vm.t) : Prop := prog_eq vm1 vm2 /\ mask_inv X vm1 vm2.

Definition mask_st_ex X := st_rel (fun _ : unit => mask_vm X) tt.

Notation mask_st := (mask_st_ex Sv.empty).

(* The values a call exchanges: in the instrumented program every array is
   followed by its mask; the scalars are the same on both sides and
   defined. *)
Inductive mask_vals : values -> values -> Prop :=
| mask_vals_nil : mask_vals [::] [::]
| mask_vals_scalar v vs1 vs2 :
    ~~ is_carr (type_of_val v) -> is_defined v ->
    mask_vals vs1 vs2 -> mask_vals (v :: vs1) (v :: vs2)
| mask_vals_arr len (t tm : WArray.array len) vs1 vs2 :
    arr_mask_of t tm -> mask_vals vs1 vs2 -> mask_vals (Varr t :: Varr tm :: vs1) (Varr t :: vs2).

Definition mask_fs (fs1 fs2 : fstate) :=
  [/\ fscs fs1 = fscs fs2, fmem fs1 = fmem fs2 & mask_vals (fvals fs1) (fvals fs2)].

Definition mask_spec : EquivSpec :=
  {| rpreF_ := fun fn1 fn2 fs1 fs2 => fn1 = fn2 /\ mask_fs fs1 fs2
   ; rpostF_ := fun fn1 fn2 fs1 fs2 fr1 fr2 => mask_fs fr1 fr2 |}.

(* Without arrays, no mask is exchanged: the values are the same on both
   sides, and defined. *)
Lemma mask_vals_scalarsE vs1 vs2 :
  all (fun v => ~~ is_carr (type_of_val v)) vs2 ->
  mask_vals vs1 vs2 <-> vs1 = vs2 /\ all is_defined vs2.
Proof.
elim: vs2 vs1 => [|v vs2 ih] vs1 /=.
- by move=> _; split => [h | [-> _]]; [inversion h | constructor].
move=> /andP [hv /ih{}ih]; split.
- move=> h; inversion h; subst.
  + by have [-> ->] := (ih vs0).1 H4; rewrite H3.
  + by [].
move=> [-> /andP [hd hds]]; constructor => //.
by apply/ih.
Qed.

(* Only the scalars of [X] matter. *)
Lemma mask_inv_eq X X' vm1 vm2 :
  (forall x, ~~ is_arr_var x -> Sv.In x X <-> Sv.In x X') ->
  mask_inv X vm1 vm2 -> mask_inv X' vm1 vm2.
Proof.
move=> hX [hsc har]; split => // x hx.
have := hsc x hx; case: (Sv_memP x X) => h; case: (Sv_memP x X') => h' //.
all: by have := hX x hx; tauto.
Qed.

(* ------------------------------------------------------------------------- *)
(* The masks and the variables of the program                                 *)

Definition no_mask (X : Sv.t) := forall y, Sv.In y X -> ~ is_mask y.

Lemma no_maskI X Y : Sv.Subset X Y -> no_mask Y -> no_mask X.
Proof. by move=> hsub h y hy; apply: h; apply: hsub. Qed.

Lemma no_mask_vars_p : no_mask (vars_p (p_funcs p)).
Proof using mask_fresh. by move=> y hy [x hx]; apply: (mask_fresh hy hx). Qed.

Lemma prog_eq_eq_on X vm1 vm2 : no_mask X -> prog_eq vm1 vm2 -> eq_on (sm := total) X vm1 vm2.
Proof. by move=> hX h x /hX; apply: h. Qed.

(* Expressions of the program read no mask: they evaluate alike on both sides. *)
Lemma prog_eq_sem_pexpr {sm1 sm2 : SemMode} wdb s1 s2 e :
  is_total (sm := sm1) -> is_total (sm := sm2) ->
  no_mask (read_e e) -> prog_eq (evm s1) (evm s2) -> emem s1 = emem s2 ->
  sem_pexpr (sm := sm1) wdb gd s1 e = sem_pexpr (sm := sm2) wdb gd s2 e.
Proof.
move=> h1 h2 hX heq hmem.
rewrite (sem_pexpr_is_totalE gd (sm2 := total)) ?h1 //.
rewrite (sem_pexpr_is_totalE gd (sm1 := sm2) (sm2 := total)) ?h2 //.
by apply: (eq_on_sem_pexpr (sm := total)) => //; apply: prog_eq_eq_on.
Qed.

(* ------------------------------------------------------------------------- *)
(* The masks of the expressions                                               *)

(* In the array [efill ws len lo n z], the cell [k] is [0xFF] exactly when it
   is in the array and in [lo, lo + n), and [z] is [0xFF]. *)
Lemma sem_efill s ws len elo en lo n z v :
  sem_pexpr (sm := total) true gd s (efill ws len elo en z) = ok v ->
  sem_pexpr (sm := total) true gd s elo = ok (Vint lo) ->
  sem_pexpr (sm := total) true gd s en = ok (Vint n) ->
  forall k, is_initbv v k =
    [&& 0 <=? k, k <? arr_size ws len, lo <=? k, k <? lo + n & wrepr U8 z == wrepr U8 (-1)].
Proof.
rewrite /=; t_xrbindP => _ v1 hv1 _ v2 hv2 <- <- + hlo hn.
rewrite hlo in hv1; rewrite hn in hv2; case: hv1 hv2 => <- [<-].
rewrite /sem_opN /= truncate_word_u /= => -[<-] k /=.
rewrite rdflt_fill_map_initb.
by case: (lo <=? k); case: (k <? lo + n) => //=; rewrite ?andbF.
Qed.

Lemma sem_efill_type s ws len elo en z v :
  sem_pexpr (sm := total) true gd s (efill ws len elo en z) = ok v ->
  type_of_val v = carr (arr_size ws len).
Proof. by rewrite /=; t_xrbindP => > _ > _ _ > _; rewrite /sem_opN; t_xrbindP => > _ <-. Qed.

(* The full mask of an array: every cell of the array is [0xFF], and no other. *)
Lemma sem_efull s ws len m :
  sem_pexpr (sm := total) true gd s (efull_mask ws len) = ok m ->
  forall i, is_initbv m i = (0 <=? i) && (i <? arr_size ws len).
Proof.
move=> hm i; rewrite (sem_efill hm erefl erefl) Z.add_0_l eqxx andbT.
by case: (0 <=? i); case: (i <? _).
Qed.

Lemma sem_eempty s ws len m :
  sem_pexpr (sm := total) true gd s (eempty_mask ws len) = ok m ->
  forall i, is_initbv m i = false.
Proof.
move=> hm i; rewrite (sem_efill hm erefl erefl) Z.add_0_r.
by apply/negbTE/negP => /and5P [_ _ /ZleP ? /ZltP ? _]; lia.
Qed.

(* A mask of a value stays one under the truncation of both. *)
Lemma val_mask_of_truncate ty v v' m m' :
  truncate_val ty v = ok v' -> truncate_val ty m = ok m' ->
  val_mask_of v m -> val_mask_of v' m'.
Proof.
case: ty => [||n|ws] /truncate_val_typeE.
- by move=> [b _ ->] /truncate_val_typeE [b' _ ->].
- by move=> [b _ ->] /truncate_val_typeE [b' _ ->].
- by move=> [a -> ->] /truncate_val_typeE [a' -> ->].
by move=> [w [ws' [w' [_ _ ->]]]] /truncate_val_typeE [? [? [? [_ _ ->]]]].
Qed.

(* The array filled with a list of the right size is initialised exactly in
   its bounds. *)
Lemma rdflt_fill_init len l i :
  size l = Z.to_nat len ->
  WArray.is_init (rdflt (WArray.empty len) (WArray.fill len l)) i = (0 <=? i) && (i <? len).
Proof.
move=> /fill_size_ok [a ha]; rewrite ha /= /WArray.is_init (fill_data ha).
by case: (_ && _).
Qed.

(* A literal array, an array filled by [Oarr_fill], is initialised exactly in
   its bounds. *)
Lemma sem_opN_Oarray_exact {sm : SemMode} len vs v :
  sem_opN (sm := sm) (Oarray len) vs = ok v ->
  exists2 t : WArray.array (arr_size U8 len), v = Varr t &
    forall i, WArray.is_init t i = (0 <=? i) && (i <? arr_size U8 len).
Proof.
have hQ : sem_forall (fun t : WArray.array (arr_size U8 len) =>
                        forall i, WArray.is_init t i = (0 <=? i) && (i <? arr_size U8 len))
            _ (sem_opN_total (Oarray len)).
- rewrite /=.
  apply: sem_forall_ecast.
  apply: (sem_forall_prod_app (P := fun x => size x = (Z.to_nat len + size [::])%nat)); last by apply: size_collect.
  move=> l /= hl i; apply: rdflt_fill_init.
  by rewrite hl Nat.add_0_r /arr_size wsize8 Z.mul_1_l.
by move=> /(sem_opN_forall hQ) [t -> ht]; exists t.
Qed.

Lemma sem_opN_Oarr_fill_exact {sm : SemMode} ws len vs v :
  sem_opN (sm := sm) (Oarr_fill ws len) vs = ok v ->
  exists2 t : WArray.array (arr_size ws len), v = Varr t &
    forall i, WArray.is_init t i = (0 <=? i) && (i <? arr_size ws len).
Proof.
have hQ : sem_forall (fun t : WArray.array (arr_size ws len) =>
                        forall i, WArray.is_init t i = (0 <=? i) && (i <? arr_size ws len))
            _ (sem_opN_total (Oarr_fill ws len)).
- move=> lo n w /= i; apply: rdflt_fill_init.
  by rewrite size_map size_ziota.
by move=> /(sem_opN_forall (op := Oarr_fill ws len) hQ) [t -> ht]; exists t.
Qed.

(* An expression that is not of an array type ([is_arr_expr]) evaluates to a
   value that is not an array. *)
Lemma sem_pexpr_not_arr {sm : SemMode} s e v :
  ~~ is_arr_expr e -> sem_pexpr (sm := sm) true gd s e = ok v -> ~~ is_carr (type_of_val v).
Proof.
case: e => //=.
1,2: by move=> ? _ [<-].
- move=> g hg /get_gvar_compat /= [_ hc].
  move: hg; rewrite /is_arr_var; case: v hc => [b | z | len t | ws w | ty h] /compat_valE //=.
  + by case: (vtype (gv g)).
  by case: (vtype (gv g)) => [ | | ws len | ws] /=; case: ty h.
- move=> > _; apply: on_arr_gvarP => n t _ _; t_xrbindP.
  by move=> > _ _ > _ <-.
- by move=> > _; t_xrbindP => > _ _ > _ <-.
- move=> o > _; t_xrbindP => > _; rewrite /sem_sop1; t_xrbindP => > _ > _ <-; rewrite type_of_to_val.
  clear -o; case: o => //=.
  + by case.
  by move=> _ [].
- move=> o > _; t_xrbindP => > _ > _; rewrite /sem_sop2; t_xrbindP => > _ > _ > _ <-; rewrite type_of_to_val.
  clear -o; case: o => //=.
  1-3,8,9: by case.
  1-4: by move=> _ [].
  by move=> _ ? [].
- move=> o > ho; t_xrbindP => > _; rewrite /sem_opN; t_xrbindP => > _ <-; rewrite type_of_to_val.
  by clear -o ho; case: o ho.
move=> ty > hty; t_xrbindP => > _ _ > _ /truncate_val_has_type h1 > _ /truncate_val_has_type h2 <-.
by case: ifP => _; rewrite ?h1 ?h2; case: (ty) hty.
Qed.

Lemma is_initv_not_arr v i : ~~ is_carr (type_of_val v) -> is_initv v i = false.
Proof. by case: v. Qed.

(* [mask_of e] is the mask of the value of [e] in a state whose masks describe
   its own variables. *)
Lemma mask_ofP s e v m :
  no_mask (read_e e) ->
  (forall x, ~ is_mask x ->
     val_mask_of (Vm.get (sm := total) (evm s) x) (Vm.get (sm := total) (evm s) (mask x))) ->
  sem_pexpr (sm := total) true gd s e = ok v ->
  sem_pexpr (sm := total) true gd s (mask_of e) = ok m ->
  val_mask_of v m.
Proof using explicit_init_ok mask_type.
move=> + hself.
elim: e v m => [z | b | ws n | x | al aa sz x e he | aa sz len x e he | al sz e he | op e he
  | op e1 he1 e2 he2 | op es hes | t e he e1 he1 e2 he2] v m hX.
1,2,5,7,8,9: by move=> hv [<-] i; rewrite is_initv_not_arr //; apply: sem_pexpr_not_arr hv.
- by move=> [<-] /sem_eempty h i; rewrite h /= /WArray.is_init /=.
- case: x hX => x [] hX /=.
  + rewrite /get_gvar /= /get_var; t_xrbindP => _ <- _ <-.
    by apply: hself; apply: hX; rewrite read_e_var /read_gvar /=; SvD.fsetdec.
  rewrite /get_gvar /= => hget.
  case hty: (vtype x) => [||ws len|ws] /=.
  1,2,4: move=> [<-] i; rewrite is_initv_not_arr //.
  1-3: by have := type_of_get_global hget; rewrite hty => ->.
  move=> /(sem_efull (s := s)) hm i; rewrite hm.
  have := type_of_get_global hget; rewrite hty /=.
  case: v hget => //= [n t | ty h] hget.
  + by move=> [?]; subst n; rewrite (get_global_arr_init hget).
  by move: hget; rewrite /get_global; case: get_global_value => // -[] > ; case: ifP.
- case: x hX => x [] hX /=.
  + apply: on_arr_gvarP => n t htx hget.
    t_xrbindP => i vi hvi hi <-.
    apply: on_arr_gvarP => n' tm htm hgetm; rewrite hvi /= hi /= => -[<-] k /=.
    have hxa : is_arr_var x by move: htx; rewrite /is_arr_var; case: (vtype x).
    have ? : n' = n by move: htm htx; rewrite mask_type hxa => -> [].
    subst n'.
    rewrite /WArray.is_initb /WArray.is_init /= !WArray.get_sub_data_get8 /=.
    case: ifP => // _.
    move: hget hgetm; rewrite /get_gvar /= /get_var; t_xrbindP => _ hx _ hmx.
    have := hself x _ (i * mk_scale aa sz + k); rewrite hx hmx /WArray.get_in_bounds.
    case: ifP => // _; apply.
    by apply: hX; rewrite read_e_Psub /read_gvar /=; SvD.fsetdec.
  apply: on_arr_gvarP => n t htx hget.
  t_xrbindP => i vi hvi hi <-.
  move: htx; rewrite /eglob_sub_mask; case: (vtype x) => // wsg leng [?]; subst n.
  have hlo : sem_pexpr (sm := total) true gd s
      (Papp1 (Oneg Op_int) (Papp2 (Omul Op_int) e (Pconst (mk_scale aa sz)))) =
      ok (Vint (- (i * mk_scale aa sz))).
  - by rewrite /= hvi /= /sem_sop2 /= hi.
  move=> hm k; rewrite (sem_efill hm hlo erefl) eqxx andbT.
  rewrite /= /WArray.is_init /= WArray.get_sub_data_get8 /=.
  case: (ZleP 0 k) => ? //=; case: (ZltP k (arr_size sz len)) => ? //=.
  have := get_global_arr_init hget (i * mk_scale aa sz + k); rewrite /WArray.is_init /WArray.get_in_bounds.
  case: ifP => [hb -> | hb _]; move: hb;
  by case: (ZleP (- (i * mk_scale aa sz)) k) => ?; case: (ZltP k _) => ?;
     case: (ZleP 0 _) => ?; case: (ZltP _ (arr_size _ _)) => ? //=; lia.
- move=> hv; move: (hv); rewrite /=; t_xrbindP => vs _ hop.
  clear hX hes; move: hop; case: op hv => [ws1 pe | len | ws len | cf] hv.
  1,4: by move=> _ /= [<-] i; rewrite is_initv_not_arr //; apply: sem_pexpr_not_arr hv.
  + move=> /sem_opN_Oarray_exact [t -> ht] /(sem_efull (s := s)) hm k.
    by rewrite hm /= ht.
  by move=> /sem_opN_Oarr_fill_exact [t -> ht] /(sem_efull (s := s)) hm k; rewrite hm /= ht.
rewrite /=; t_xrbindP => b vb hvb hb v1 v1' hv1 htr1 v2 v2' hv2 htr2 <-.
move=> b' vb'; rewrite hvb => -[<-]; rewrite hb => -[<-] m1 m1' hm1 htm1 m2 m2' hm2 htm2 <-.
have hX1 : no_mask (read_e e1) by apply: no_maskI hX; rewrite read_e_Pif; SvD.fsetdec.
have hX2 : no_mask (read_e e2) by apply: no_maskI hX; rewrite read_e_Pif; SvD.fsetdec.
case: (b).
- exact: (val_mask_of_truncate htr1 htm1 (he1 _ _ hX1 hv1 hm1)).
exact: (val_mask_of_truncate htr2 htm2 (he2 _ _ hX2 hv2 hm2)).
Qed.

(* ------------------------------------------------------------------------- *)
(* The writes of the masks and of the variables                               *)

(* A variable that is not an array has no cell. *)
Lemma is_initbv_scalar {sm : SemMode} vm y i :
  ~~ is_arr_var y -> is_initbv (Vm.get (sm := sm) vm y) i = false.
Proof.
move=> hy; have := Vm.getP_mode (sm := sm) vm y.
case: (Vm.get vm y) => //= n t /compat_valE.
by move: hy; rewrite /is_arr_var; case: vtype.
Qed.

Lemma is_initv_scalar {sm : SemMode} vm y i :
  ~~ is_arr_var y -> is_initv (Vm.get (sm := sm) vm y) i = false.
Proof.
move=> hy; have := Vm.getP_mode (sm := sm) vm y.
case: (Vm.get vm y) => //= n t /compat_valE.
by move: hy; rewrite /is_arr_var; case: vtype.
Qed.

(* A variable and its mask written together: the mask of a scalar holds exactly
   where the scalar is defined, the mask of an array is a mask of it. *)
Lemma mask_inv_set_var X x m v vm1 vm1' vm2 vm2' :
  mask_inv X vm1 vm2 ->
  (~~ is_arr_var x -> ~~ Sv.mem x X /\ m = Vbool (is_defined v)) ->
  val_mask_of v m ->
  set_var true vm1 (mask x) m = ok vm1' ->
  set_var true vm2 x v = ok vm2' ->
  mask_inv X vm1' vm2'.
Proof using mask_inj mask_type.
move=> [hsc har] hdef hval hs1 hs2.
have hz1 := set_var_eq_ex hs1; have hz2 := set_var_eq_ex hs2.
split.
- move=> z hz; case: (x =P z) => [? | hne]; last first.
  + rewrite -(get_total_eq_ex (z := mask z) hz1).
    + rewrite -hz2; first by apply: hsc.
      by move=> /SvD.F.singleton_iff.
    by move=> /SvD.F.singleton_iff /mask_inj.
  subst z; have [/negbTE -> ?] := hdef hz; subst m.
  move: hs1 hs2 => /set_varP [_ htm ->] /set_varP [_ htv ->].
  rewrite Vm.setP_eq; have /= <- := vm_truncate_val_defined htv.
  by rewrite Vm.get_modeE Vm.setP_eq mask_type (negbTE hz).
move=> z; case: (x =P z) => [? | hne]; last first.
- rewrite -(get_total_eq_ex (z := mask z) hz1); last by move=> /SvD.F.singleton_iff /mask_inj.
  by rewrite -hz2; [apply: har | move=> /SvD.F.singleton_iff].
subst z; case hxa: (is_arr_var x); last first.
- by move=> i; rewrite is_initbv_scalar ?is_initv_scalar ?is_arr_var_mask ?hxa.
rewrite (set_var_arr_get hs2 hxa) Vm.get_totalE.
- by rewrite (set_var_arr_get hs1) // is_arr_var_mask.
move: hxa => /is_aarrP [ws [len hty]]; have := Vm.getP vm1' (mask x).
by rewrite mask_type /is_arr_var hty /= => /compat_valEl [? ->].
Qed.

(* Every byte of the word [-1] is [0xFF]. *)
Lemma wread8_m1 ws k :
  0 <= k < wsize_size ws -> LE.wread8 (wrepr ws (-1)) k = wrepr U8 (-1).
Proof.
move=> hk.
have hall : all (eq_op^~ (wrepr U8 (-1))) (LE.encode (wrepr ws (-1))).
- by case: ws {hk}; vm_compute.
rewrite /LE.wread8; apply/eqP; apply: (all_nthP 0%R hall).
rewrite LE.size_encode; apply/ssrnat.ltP; lia.
Qed.

(* A cell and its mask written at the same place: the mask is full on the
   cell. *)
Lemma set_total_mask len ws (t t' tm tm' : WArray.array len) al aa i (w : word ws) :
  WArray.set (sm := total) t al aa i w = ok t' ->
  WArray.set (sm := total) tm al aa i (wrepr ws (-1)) = ok tm' ->
  arr_mask_of t tm -> arr_mask_of t' tm'.
Proof.
move=> h hm hinit j; rewrite (set_total_is_init j h) -hinit /WArray.is_initb (set_total_data hm) /=.
case: ifP => [/and3P [/ZleP ? /ZltP ? _] | _] //.
by rewrite wread8_m1 ?eqxx //; lia.
Qed.

(* A sub-array and its mask written at the same place. *)
Lemma set_sub_total_mask lena aa ws len (t t' tm tm' : WArray.array lena) i
    (b bm : WArray.array (arr_size ws len)) :
  WArray.set_sub (sm := total) aa t i b = ok t' ->
  WArray.set_sub (sm := total) aa tm i bm = ok tm' ->
  arr_mask_of t tm -> arr_mask_of b bm -> arr_mask_of t' tm'.
Proof.
rewrite /WArray.set_sub /= => -[<-] [<-] ht hb j.
by rewrite /WArray.is_initb /WArray.is_init /= !WArray.set_sub_data_get8 /=; case: ifP => _; [apply: hb | apply: ht].
Qed.

(* The index of an array destination. *)
Definition lv_idx (lv : lval) : option pexpr :=
  match lv with
  | Laset _ _ _ _ e | Lasub _ _ _ _ e => Some e
  | Lvar _ | Lnone _ _ | Lmem _ _ _ _ => None
  end.

(* A destination and its mask written at the same place. *)
Lemma mask_inv_mirror X lv m v a a' c c' :
  mask_inv X (evm a) (evm c) ->
  (forall e, lv_idx lv = Some e ->
     sem_pexpr (sm := total) true gd a e = sem_pexpr (sm := total) true gd c e) ->
  (forall x, lv = Lvar x -> ~~ is_arr_var x -> ~~ Sv.mem x X /\ m = Vbool (is_defined v)) ->
  (forall al aa ws x e, lv = Laset al aa ws x e -> m = Vword (wrepr ws (-1))) ->
  val_mask_of v m ->
  write_lval (sm := total) true gd (mask_lv lv) m a = ok a' ->
  write_lval (sm := total) true gd lv v c = ok c' ->
  mask_inv X (evm a') (evm c').
Proof using mask_inj mask_type.
move=> hinv hidx hdef hcell hval.
case: lv hidx hdef hcell => [vi ty | x | al ws x e | al aa ws x e | aa ws len x e] /= hidx hdef hcell.
- by move=> /write_noneP [-> _ _] /write_noneP [-> _ _].
- rewrite /write_var; t_xrbindP => vm1 hs1 <- vm2 hs2 <- /=.
  by apply: mask_inv_set_var hinv (hdef _ erefl) hval hs1 hs2.
- by t_xrbindP => > _ _ > _ > _ <- > _ _ > _ > _ <-.
- apply: on_arr_varP => n tm htm hgetm; t_xrbindP => i vi hvi hi w' hw' tm' hset' hw1.
  apply: on_arr_varP => n' t htx hgetx; rewrite -(hidx _ erefl) hvi /= hi /=.
  t_xrbindP => w hw t' hset hw2.
  have hxa : is_arr_var x by move: htx; rewrite /is_arr_var; case: (vtype x).
  have ? : n' = n by move: htm htx; rewrite mask_type hxa => -> [].
  subst n'.
  move: hw1 hw2; rewrite /write_var; t_xrbindP => vm1 hs1 <- vm2 hs2 <-.
  apply: (mask_inv_set_var hinv _ _ hs1 hs2); first by rewrite hxa.
  move: hw'; rewrite (hcell _ _ _ _ _ erefl) /= truncate_word_u => -[?]; subst w'.
  apply: (set_total_mask hset hset').
  have := hinv.2 x; move: hgetx hgetm; rewrite /get_var -get_total_arr //; t_xrbindP => _ -> _ ->.
  by apply.
apply: on_arr_varP => n tm htm hgetm; t_xrbindP => i vi hvi hi bm hbm hw1.
apply: on_arr_varP => n' t htx hgetx; rewrite -(hidx _ erefl) hvi /= hi /=.
t_xrbindP => b hb hw2.
have hxa : is_arr_var x by move: htx; rewrite /is_arr_var; case: (vtype x).
have ? : n' = n by move: htm htx; rewrite mask_type hxa => -> [].
subst n'.
move: hw1 hw2; rewrite /write_var; t_xrbindP => vm1 hs1 <- vm2 hs2 <-.
apply: (mask_inv_set_var hinv _ _ hs1 hs2); first by rewrite hxa.
apply: (set_sub_total_mask (t := t) (tm := tm) (i := i) (b := b) (bm := bm) erefl erefl).
- have := hinv.2 x; move: hgetx hgetm; rewrite /get_var -get_total_arr //; t_xrbindP => _ -> _ ->.
  by apply.
by move: hval; rewrite (to_arrI hb) (to_arrI hbm).
Qed.

(* A defined scalar written alone, its mask not written yet. *)
Lemma mask_inv_set_var_r X a x v vm2 vm2' :
  mask_inv X a vm2 -> ~~ is_arr_var x -> is_defined v ->
  set_var true vm2 x v = ok vm2' ->
  mask_inv (Sv.add x X) a vm2'.
Proof using mask_type.
move=> [hsc har] hx hv hs2; have hz2 := set_var_eq_ex hs2.
split => z.
- move=> hz; rewrite SvD.F.add_b; case: (x =P z) => [? | hne]; last first.
  + rewrite /SvD.F.eqb; case: SvD.F.eq_dec => // _ /=.
    by rewrite -hz2; [apply: hsc | move=> /SvD.F.singleton_iff].
  subst z; rewrite /SvD.F.eqb; case: SvD.F.eq_dec => // _ /=.
  by move: hs2 => /set_varP [_ htv ->]; rewrite Vm.setP_eq; have /= <- := vm_truncate_val_defined htv.
case: (x =P z) => [? | hne]; last first.
- by rewrite -hz2; [apply: har | move=> /SvD.F.singleton_iff].
by subst z => i; rewrite is_initbv_scalar ?is_initv_scalar ?is_arr_var_mask ?(negbTE hx).
Qed.

(* A destination that writes no variable. *)
Lemma write_lval_novar lv v c c' :
  (if lv is (Lnone _ _ | Lmem _ _ _ _) then true else false) ->
  write_lval (sm := total) true gd lv v c = ok c' -> evm c' = evm c.
Proof.
case: lv => //= [vi ty | al ws x e] _.
- by move=> /write_noneP [-> _ _].
by t_xrbindP => > _ _ > _ > _ <-.
Qed.

(* The mask of a variable written alone. *)
Lemma mask_inv_set_mask_l X x m a a' c :
  mask_inv X a c ->
  (if is_arr_var x then val_mask_of c.[x] m else m = Vbool (is_defined c.[x])) ->
  set_var true a (mask x) m = ok a' ->
  mask_inv (Sv.remove x X) a' c.
Proof using mask_inj mask_type.
move=> [hsc har] hx hs1; have hz1 := set_var_eq_ex hs1.
split => z.
- move=> hz; rewrite SvD.F.remove_b; case: (x =P z) => [? | hne]; last first.
  + rewrite /SvD.F.eqb; case: SvD.F.eq_dec => //= _; rewrite andbT.
    rewrite -(get_total_eq_ex (z := mask z) hz1); first by apply: hsc.
    by move=> /SvD.F.singleton_iff /mask_inj.
  subst z; rewrite /SvD.F.eqb; case: SvD.F.eq_dec => //= _; rewrite andbF.
  move: hx; rewrite (negbTE hz) => ?; subst m.
  move: hs1 => /set_varP [_ htm ->].
  by rewrite Vm.get_modeE Vm.setP_eq mask_type (negbTE hz).
case: (x =P z) => [? | hne]; last first.
- rewrite -(get_total_eq_ex (z := mask z) hz1); first by apply: har.
  by move=> /SvD.F.singleton_iff /mask_inj.
subst z; move: hx; case: ifP => hxa hx; last by move=> i; rewrite is_initbv_scalar ?is_initv_scalar ?is_arr_var_mask ?hxa.
have hmxa : is_arr_var (mask x) by rewrite is_arr_var_mask.
by rewrite get_total_arr // (set_var_arr_get hs1).
Qed.
(* Writing a mask leaves the variables of the program untouched. *)
Lemma prog_eq_set_mask x m a a' c :
  set_var true a (mask x) m = ok a' -> prog_eq a c -> prog_eq a' c.
Proof.
move=> /set_var_eq_ex hz h y hy; rewrite -(get_total_eq_ex hz); first by apply: h.
by move=> /SvD.F.singleton_iff hm; apply: hy; exists x.
Qed.

(* A destination of the program written on both sides with the same value. *)
Lemma prog_eq_write_lval lv v a a' c :
  prog_eq (evm a) (evm c) -> escs a = escs c -> emem a = emem c ->
  no_mask (vars_lval lv) ->
  write_lval (sm := total) true gd lv v a = ok a' ->
  exists2 c', write_lval (sm := total) true gd lv v c = ok c' &
    [/\ escs a' = escs c', emem a' = emem c' & prog_eq (evm a') (evm c')].
Proof.
move=> h hscs hmem hX hw.
have heq : eq_on (sm := total) (read_rv lv) (evm a) (evm c).
- by apply: prog_eq_eq_on h; apply: no_maskI hX; rewrite /vars_lval; SvD.fsetdec.
have [vm2 hw2 /(eq_on_mode (sm := total)) heq2] := write_lval_eq_on1 heq hw.
rewrite with_vm_evm // in hw2.
exists (with_vm a' vm2) => //; split => //= y hy.
case: (Sv_memP y (vrv lv)) => hyv; first by apply: heq2.
rewrite -(get_total_eq_ex (vrvP hw)) // -(get_total_eq_ex (vrvP hw2)) //.
by apply: h.
Qed.
(* The same, where the instrumented program writes the defaulted value: an
   undefined output is a boolean, whose total read is its default value. *)
Lemma prog_eq_write_lval_dflt lv v a a' c :
  prog_eq (evm a) (evm c) -> escs a = escs c -> emem a = emem c ->
  no_mask (vars_lval lv) -> DB true v ->
  write_lval (sm := total) true gd lv (value_dflt v) a = ok a' ->
  exists2 c', write_lval (sm := total) true gd lv v c = ok c' &
    [/\ escs a' = escs c', emem a' = emem c' & prog_eq (evm a') (evm c')].
Proof.
move=> h hscs hmem hX; rewrite /value_dflt; case: ifP => [_ _ | hd]; first by apply: prog_eq_write_lval.
case: v hd => // t ht _ /=; rewrite /DB /= => /eqP ?; subst t.
case: lv hX => [vi ty | x | al ws x e | al aa ws x e | aa ws len x e] /= hX.
- move=> /write_noneP [-> htr _]; exists c; last by split.
  by rewrite /write_none; case: (eval_atype ty) htr.
- rewrite /write_var; t_xrbindP => vm1 /set_varP [_ htr ->] <-.
  have hty : eval_atype (vtype x) = cbool by case: (eval_atype (vtype x)) htr.
  rewrite (set_var_truncate (wdb := true) (x := x) (v := Vundef cbool ht)) //=; last by rewrite hty.
  eexists; first reflexivity.
  split => //= y hy; case: (v_var x =P y) => [<- | hne].
  + rewrite [LHS]Vm.get_modeE [RHS]Vm.get_modeE !Vm.setP_eq hty /=.
    done.
  have h1 : forall vm w, Vm.get (sm := total) vm.[x <- w] y = Vm.get (sm := total) vm y.
  + by move=> vm w; apply: (Vm.get_eq_mode erefl); rewrite Vm.setP_neq //; apply/eqP.
  by rewrite !h1; apply: h.
- by t_xrbindP.
- apply: on_arr_varP => n t _ _.
  rewrite /=; case: (sem_pexpr true gd a e) => //= ve; case: to_int => //.
apply: on_arr_varP => n0 t0 _ _; t_xrbindP => ? ? _ _ ? /to_arrI.
done.
Qed.
Lemma prog_eq_write_lvals_dflt lvs vs a a' c :
  prog_eq (evm a) (evm c) -> escs a = escs c -> emem a = emem c ->
  no_mask (vars_lvals lvs) -> all (DB true) vs ->
  write_lvals (sm := total) true gd a lvs (map value_dflt vs) = ok a' ->
  exists2 c', write_lvals (sm := total) true gd c lvs vs = ok c' &
    [/\ escs a' = escs c', emem a' = emem c' & prog_eq (evm a') (evm c')].
Proof.
elim: lvs vs a c => [ | lv lvs ih] [ | v vs] //= a c h hscs hmem hX.
- by move=> _ [<-]; exists c.
move=> /andP [hdb hdbs]; t_xrbindP => a1 hw1 hws.
have hX1 : no_mask (vars_lval lv).
- by apply: no_maskI hX; rewrite /vars_lval /vars_lvals read_rvs_cons vrvs_cons; SvD.fsetdec.
have hXs : no_mask (vars_lvals lvs).
- by apply: no_maskI hX; rewrite /vars_lvals read_rvs_cons vrvs_cons; SvD.fsetdec.
have [c1 -> [hscs1 hmem1 h1]] := prog_eq_write_lval_dflt h hscs hmem hX1 hdb hw1.
exact: ih h1 hscs1 hmem1 hXs hdbs hws.
Qed.
(* The writes of the variables of the program leave the masks untouched. *)
Lemma mask_inv_prog_l X W vm1 vm1' vm2 :
  no_mask W -> vm1 =[\W] vm1' -> mask_inv X vm1 vm2 -> mask_inv X vm1' vm2.
Proof.
move=> hW heq [hsc har]; have hm : forall x, Vm.get (sm := total) vm1' (mask x) = Vm.get (sm := total) vm1 (mask x).
- by move=> x; symmetry; apply: (get_total_eq_ex heq) => /hW; apply; exists x.
by split => x; rewrite hm; [apply: hsc | apply: har].
Qed.

(* The masks of the instrumented program describe its own arrays. *)
Lemma mask_vm_self X vm1 vm2 x :
  mask_vm X vm1 vm2 -> ~ is_mask x ->
  val_mask_of (Vm.get (sm := total) vm1 x) (Vm.get (sm := total) vm1 (mask x)).
Proof using mask_type.
move=> [heq [_ har]] hx; case hxa: (is_arr_var x); last first.
- by move=> i; rewrite is_initbv_scalar ?is_initv_scalar ?is_arr_var_mask ?hxa.
by rewrite (heq _ hx) get_total_arr.
Qed.

(* The mask of a cell: every byte is [0xFF]. *)
Lemma sem_cell_mask ii lv ws s s' :
  esem (sm := total_init) pm ev [:: set_cell_mask mask ii lv ws] s = ok s' ->
  write_lval (sm := total) true gd (mask_lv lv) (Vword (wrepr ws (-1))) s = ok s'.
Proof.
rewrite esem_assgn1 /sem_assgn /=; t_xrbindP.
rewrite /truncate_val /= truncate_word_u /= => _ [<-] hw.
by rewrite (write_lval_is_totalE gd (sm2 := total)) // in hw.
Qed.

Lemma assgn_mask_inv ii lv ty e v v' s0 s1 s2 s2' :
  mask_vm Sv.empty (evm s0) (evm s2) -> emem s0 = emem s2 ->
  no_mask (Sv.union (read_e e) (vars_lval lv)) ->
  sem_pexpr (sm := total) true gd s0 e = ok v -> truncate_val (eval_atype ty) v = ok v' ->
  esem (sm := total_init) pm ev (explicit_init_assgn mask ii lv ty e) s0 = ok s1 ->
  write_lval (sm := total) true gd lv v' s2 = ok s2' ->
  mask_inv Sv.empty (evm s1) (evm s2').
Proof using explicit_init_ok mask_inj mask_type.
move=> hvm hmem hX hv htr hm hw; move: hm.
have hXe : no_mask (read_e e) by apply: no_maskI hX; SvD.fsetdec.
have hidx : forall e', lv_idx lv = Some e' ->
    sem_pexpr (sm := total) true gd s0 e' = sem_pexpr (sm := total) true gd s2 e'.
- move=> e' he'; apply: prog_eq_sem_pexpr => //; last exact: hvm.1.
  apply: no_maskI hX; case: (lv) he' => //= > [<-]; rewrite /vars_lval /read_rv /= read_eE; SvD.fsetdec.
case: lv hX hw hidx => [vi tyn | x | al ws x e' | al aa ws x e' | aa ws len x e'] hX hw hidx;
  rewrite [explicit_init_assgn _ _ _ _ _]/=.
- by move=> [<-]; rewrite (write_lval_novar _ hw) //; exact: hvm.2.
- case: ifP => hxa; rewrite esem_assgn1 /sem_assgn.
  + t_xrbindP => mv hmv mv' htm hwm.
    rewrite (sem_pexpr_is_totalE gd (sm2 := total)) // in hmv.
    apply: (mask_inv_mirror (lv := Lvar x) hvm.2 hidx _ _ _ hwm hw) => //.
    + by move=> _ [<-]; rewrite hxa.
    move=> i; apply: (val_mask_of_truncate htr htm _ i).
    by apply: (mask_ofP hXe _ hv hmv) => y hy; apply: (mask_vm_self hvm).
  t_xrbindP => mv [<-] mv' /= [<-] hwm.
  apply: (mask_inv_mirror (lv := Lvar x) hvm.2 hidx _ _ _ hwm hw) => //.
  + by move=> _ [<-] _; rewrite SvD.F.empty_b (truncate_val_defined htr).
  move=> i; case: v' hw {htr} => //= len t hw.
  by have := write_lval_arr (sm := total) (spp := spp) (gd := gd) (lv := Lvar x) (v := Varr t) erefl hw; rewrite /= hxa.
- by move=> [<-]; rewrite (write_lval_novar _ hw) //; exact: hvm.2.
- move=> /sem_cell_mask hwm.
  apply: (mask_inv_mirror (lv := Laset al aa ws x e') hvm.2 hidx _ _ _ hwm hw) => //.
  + by move=> > [] _ _ <-.
  move=> i; case: v' {htr} hw => //= len t; apply: on_arr_varP => > _ _; t_xrbindP.
  by [].
rewrite esem_assgn1 /sem_assgn; t_xrbindP => mv hmv mv' htm hwm.
rewrite (write_lval_is_totalE gd (sm2 := total)) // in hwm.
rewrite (sem_pexpr_is_totalE gd (sm2 := total)) // in hmv.
apply: (mask_inv_mirror (lv := Lasub aa ws len x e') hvm.2 hidx _ _ _ hwm hw) => //.
move=> i; apply: (val_mask_of_truncate htr htm _ i).
by apply: (mask_ofP hXe _ hv hmv) => y hy; apply: (mask_vm_self hvm).
Qed.
Definition is_mask_assgn (i : instr) :=
  if i is MkI _ (Cassgn lv _ _ _) then ~~ lv_write_mem lv else false.

(* A command that writes masks only leaves the program variables, the memory
   and the system state untouched. *)
Lemma esem_mask_cmd c s0 s1 :
  all is_mask_assgn c -> (forall y, Sv.In y (write_c c) -> is_mask y) ->
  esem (sm := total_init) pm ev c s0 = ok s1 ->
  [/\ escs s1 = escs s0, emem s1 = emem s0 & forall vm, prog_eq (evm s0) vm -> prog_eq (evm s1) vm].
Proof.
elim: c s0 => [ | [ii ir] c ih] s0 /=.
- by move=> _ _ [<-].
case: ir => // lv tg ty e /andP [hlv hall] hW.
have hW1 : forall y, Sv.In y (vrv lv) -> is_mask y.
- by move=> y hy; apply: hW; rewrite write_c_cons write_Ii write_i_assgn; SvD.fsetdec.
have hWc : forall y, Sv.In y (write_c c) -> is_mask y.
- by move=> y hy; apply: hW; rewrite write_c_cons; SvD.fsetdec.
t_xrbindP => s1' hs1 hc; move: hs1; rewrite /sem_assgn; t_xrbindP => v _ v' _ hw.
have [-> -> h] := ih _ hall hWc hc.
have [hscs hmem] := lv_write_scs_mem hw; split => //.
- by rewrite -hmem.
move=> vm hp; apply: h => y hy; rewrite -(get_total_eq_ex (vrvP hw)); first by apply: hp.
by move=> /hW1 /hy.
Qed.


Lemma mask_cmd_assgn ii lv ty e :
  all is_mask_assgn (explicit_init_assgn mask ii lv ty e) /\
  forall y, Sv.In y (write_c (explicit_init_assgn mask ii lv ty e)) -> is_mask y.
Proof.
case: lv => [vi tyn | x | al ws x e' | al aa ws x e' | aa ws len x e'] /=.
1,3: by split => // y; rewrite write_c_nil => /SvD.F.empty_iff.
- by case: ifP => _; split => // y; rewrite write_c_assgn1 /= => /SvD.F.singleton_iff <-; exists x.
all: by split => // y; rewrite write_c_assgn1 /= => /SvD.F.singleton_iff <-; exists x.
Qed.

Lemma assgnP ii lv tg ty e s0 s1' s2 :
  no_mask (vars_I (MkI ii (Cassgn lv tg ty e))) ->
  mask_st s0 s2 ->
  esem (sm := total_init) pm ev (explicit_init_assgn mask ii lv ty e ++ [:: MkI ii (Cassgn lv tg ty e)]) s0 = ok s1' ->
  exists2 s2', esem (sm := total) p ev [:: MkI ii (Cassgn lv tg ty e)] s2 = ok s2' & mask_st s1' s2'.
Proof using explicit_init_ok mask_inj mask_type.
move=> hX [hscs hmem hvm]; rewrite esem_cat; t_xrbindP => s1 hmask.
have [hall hW] := mask_cmd_assgn ii lv ty e.
have [hscs1 hmem1 hp1] := esem_mask_cmd hall hW hmask.
rewrite esem_assgn1 /sem_assgn; t_xrbindP => v hv v' htr hw.
have hX' : no_mask (Sv.union (read_e e) (vars_lval lv)).
- apply: no_maskI hX; rewrite /vars_I /vars_lval read_Ii write_Ii read_i_assgn write_i_assgn; SvD.fsetdec.
have hXe : no_mask (read_e e) by apply: no_maskI hX'; SvD.fsetdec.
have hXl : no_mask (vars_lval lv) by apply: no_maskI hX'; SvD.fsetdec.
have hp12 := hp1 _ hvm.1.
have hp10 : prog_eq (evm s1) (evm s0) by apply: hp1.
have hv2 : sem_pexpr (sm := total) true gd s2 e = ok v.
- by rewrite -hv; symmetry; apply: prog_eq_sem_pexpr => //; rewrite hmem1.
have hv0 : sem_pexpr (sm := total) true gd s0 e = ok v.
- by rewrite -hv; symmetry; apply: prog_eq_sem_pexpr => //; rewrite hmem1.
rewrite (write_lval_is_totalE gd (sm2 := total)) // in hw.
have [s2' hw2 [hs hm hp]] := prog_eq_write_lval hp12 (etrans hscs1 hscs) (etrans hmem1 hmem) hXl hw.
exists s2'; first by rewrite esem_assgn1 /sem_assgn hv2 /= htr.
split => //; split => //.
apply: (mask_inv_prog_l (W := vrv lv)); first by apply: no_maskI hXl; rewrite /vars_lval; SvD.fsetdec.
- exact: vrvP hw.
exact: assgn_mask_inv hvm hmem hX' hv0 htr hmask hw2.
Qed.

Lemma prog_eq_sem_pexprs {sm1 sm2 : SemMode} wdb s1 s2 es :
  is_total (sm := sm1) -> is_total (sm := sm2) ->
  no_mask (read_es es) -> prog_eq (evm s1) (evm s2) -> emem s1 = emem s2 ->
  sem_pexprs (sm := sm1) wdb gd s1 es = sem_pexprs (sm := sm2) wdb gd s2 es.
Proof.
move=> h1 h2 hX heq hmem.
rewrite (sem_pexprs_is_totalE gd (sm2 := total)) ?h1 //.
rewrite (sem_pexprs_is_totalE gd (sm1 := sm2) (sm2 := total)) ?h2 //.
by apply: (eq_on_sem_pexprs (sm := total)) => //; apply: prog_eq_eq_on.
Qed.

(* The mask of an array expression has the type of the expression. *)
Lemma mask_of_type s e v m :
  is_arr_expr e ->
  sem_pexpr (sm := total) true gd s e = ok v ->
  sem_pexpr (sm := total) true gd s (mask_of e) = ok m ->
  type_of_val m = type_of_val v.
Proof using mask_type.
have hpif : forall ty b e1 e2 m, sem_pexpr (sm := total) true gd s (Pif ty b e1 e2) = ok m -> type_of_val m = eval_atype ty.
- move=> ty b e1 e2 m0 /=; t_xrbindP => > _ _ > _ /truncate_val_has_type h1 > _ /truncate_val_has_type h2 <-.
  by case: ifP.
case: e => //=.
- move=> ws len _ [<-]; rewrite /sem_opN /=.
  by t_xrbindP => > _ _ <-.
- move=> g; rewrite /is_arr_var => hg /get_gvar_compat /= [_ /compat_valEl hv]; case: ifP => hgl.
  + by case: (vtype (gv g)) hg hv => //= ws len _ [t ->] /sem_opN_Oarr_fill_init [? -> _].
  move=> /get_gvar_compat /= [_ /compat_valEl]; rewrite mask_type /is_arr_var hg.
  by case: (vtype (gv g)) hg hv => //= ws len _ [? ->] [? ->].
- move=> aa ws len g e _; apply: on_arr_gvarP => n t hty hg; t_xrbindP => i vi _ _ <-.
  case: is_glob.
  + case: (vtype (gv g)) hty => // wsg leng _.
    by move=> /sem_efill_type ->.
  by rewrite /=; apply: on_arr_gvarP => ????; t_xrbindP => > _ _ <-.
- move=> o > ho; t_xrbindP => > _; rewrite /sem_opN; t_xrbindP => > _ <-.
  rewrite type_of_to_val.
  by clear -s ho; case: o ho => // [len | ws len] _ /sem_efill_type ->.
by move=> ty b e1 e2 _ hv hm; rewrite (hpif _ _ _ _ _ hm) (hpif _ _ _ _ _ hv).
Qed.

(* An expression of an array type evaluates to an array. *)
Lemma sem_pexpr_arr {sm : SemMode} s e v :
  is_arr_expr e -> sem_pexpr (sm := sm) true gd s e = ok v -> is_carr (type_of_val v).
Proof.
case: e => //=.
- by move=> > _ [<-].
- move=> g; rewrite /is_arr_var => hg /get_gvar_compat /= [_ /compat_valEl].
  by case: (vtype (gv g)) hg => //= ws len _ [? ->].
- move=> > _; apply: on_arr_gvarP => ????; t_xrbindP.
  by move=> > _ _ > _ <-.
- move=> o > ho; t_xrbindP => > _; rewrite /sem_opN; t_xrbindP => > _ <-; rewrite type_of_to_val.
  by clear -ho; case: o ho.
move=> ty > hty; t_xrbindP => > _ _ > _ /truncate_val_has_type h1 > _ /truncate_val_has_type h2 <-.
by case: ifP => _; rewrite ?h1 ?h2; case: (ty) hty.
Qed.


(* The initialisation of the cells of an array expression, read on its mask,
   when the expression has a value. *)
Lemma arr_init_eP X s1 s2 len e v lo n :
  mask_st_ex X s1 s2 -> no_mask (read_es [:: e; lo; n]) -> is_arr_expr e ->
  sem_pexpr (sm := total) true gd s2 e = ok v ->
  sem_eassert gd s1 (PappN_safety (Ois_barr_init len) [:: mask_of e; lo; n]) = ok true ->
  sem_eassert gd s2 (PappN_safety (Ois_arr_init len) [:: e; lo; n]) = ok true.
Proof using explicit_init_ok mask_type.
move=> [hscs hmem hvm] hXs hxa hve /=; t_xrbindP.
move=> _ m hm _ vl hl _ vn hn <- <- <-.
rewrite /sem_opN_safety /=; t_xrbindP => tm /to_arrI ? lo1 hlo1 n1 hn1 hall; subst m.
have hsame : forall e0, no_mask (read_e e0) ->
    sem_pexpr (sm := total) true gd s2 e0 = sem_pexpr (sm := total) true gd s1 e0.
- by move=> e0 h0; symmetry; apply: prog_eq_sem_pexpr => //; exact: hvm.1.
have hXe : no_mask (read_e e) by apply: no_maskI hXs; rewrite !read_es_cons; SvD.fsetdec.
rewrite hve (hsame lo) ?hl ?(hsame n) ?hn /=; last 2 first.
- by apply: no_maskI hXs; rewrite !read_es_cons; SvD.fsetdec.
- by apply: no_maskI hXs; rewrite !read_es_cons; SvD.fsetdec.
have hve1 : sem_pexpr (sm := total) true gd s1 e = ok v by rewrite -hsame.
have hmo := mask_ofP hXe (fun y hy => mask_vm_self hvm hy) hve1 hm.
have := mask_of_type hxa hve1 hm; have := sem_pexpr_defined hve.
case: v hve hve1 hmo => //= len1 t _ _ hmo _ [?]; subst len1.
rewrite to_arrK /= hlo1 hn1 /=; congr ok.
by apply/allP => i /(allP hall); have /= <- := hmo i.
Qed.

(* The initialisation of the cells of a local array, of a sub-array of a
   local array or of a declared global array ([check_arr_init]), read on its
   mask. A local array has a value in the total mode, and so has a sub-array
   of it, whose index the mask evaluates; a declared global has a value. *)
Lemma arr_init_aP X s1 s2 len e lo n :
  mask_st_ex X s1 s2 -> no_mask (read_es [:: e; lo; n]) ->
  check_arr_init gd (PappN_safety (Ois_arr_init len) [:: e; lo; n]) ->
  sem_eassert gd s1 (PappN_safety (Ois_barr_init len) [:: mask_of e; lo; n]) = ok true ->
  sem_eassert gd s2 (PappN_safety (Ois_arr_init len) [:: e; lo; n]) = ok true.
Proof using explicit_init_ok mask_type.
move=> hst hXs hc hs; have [hscs hmem hvm] := hst.
have := hs; rewrite /=; t_xrbindP => _ m hm _ vl hl _ vn hn <- <- <-.
rewrite /sem_opN_safety /=; t_xrbindP => tm /to_arrI ? _ _ _ _ _; subst m.
case: e hXs hc hs hm => // [x | aa ws alen x i] hXs hx hs hm; simpl in hx.
- have [hlx | [hg /is_okP [v hgv]]] : is_lvar x \/ (is_glob x /\ is_ok (get_global gd (gv x))).
  + by move: hx; rewrite is_lvar_is_glob; case: is_glob => /=; auto.
  + rewrite is_lvar_is_glob in hlx; rewrite /= (negbTE hlx) /= in hm.
    have hxa : is_arr_var (gv x).
    * move: hm => /get_gvar_compat /= [_ /compat_valEl]; rewrite mask_type.
      by case: is_arr_var => //= -[ | [? //] ].
    have hve : sem_pexpr (sm := total) true gd s2 (Pvar x) = ok (evm s2).[gv x].
    * rewrite /= /get_gvar is_lvar_is_glob hlx /get_var.
      by rewrite (get_total_arr _ hxa) arr_defined.
    exact: (arr_init_eP hst hXs hxa hve hs).
  rewrite /= hg in hm.
  have hxa : is_arr_var (gv x) by move: hm; rewrite /is_arr_var; case: (vtype (gv x)).
  have hve : sem_pexpr (sm := total) true gd s2 (Pvar x) = ok v.
  + by rewrite /= /get_gvar is_lvar_is_glob hg.
  exact: (arr_init_eP hst hXs hxa hve hs).
rewrite is_lvar_is_glob in hx; rewrite /= (negbTE hx) /= in hm.
move: hm; apply: on_arr_gvarP => n0 t0 htm hgm; t_xrbindP => j vj hvj hj _ _.
have hxa : is_arr_var (gv x).
- by move: htm; rewrite /= mask_type /is_arr_var; case: (vtype (gv x)).
have /is_aarrP [wsx [lenx htyx]] := hxa.
have [nx [tx htx]] : exists nx (tx : WArray.array nx), (evm s2).[gv x] = Varr tx.
- have := Vm.getP (evm s2) (gv x); rewrite htyx /= => /compat_valEl [t1 h1].
  by exists (arr_size wsx lenx), t1.
have hgx : get_gvar (sm := total) true gd (evm s2) x = ok (Varr tx).
- by rewrite /get_gvar is_lvar_is_glob hx /get_var (get_total_arr _ hxa) htx.
have hi : sem_pexpr (sm := total) true gd s2 i = ok vj.
- rewrite -hvj; symmetry; apply: prog_eq_sem_pexpr => //; last exact: hvm.1.
  by apply: no_maskI hXs; rewrite !read_es_cons read_e_Psub; SvD.fsetdec.
have hve : sem_pexpr (sm := total) true gd s2 (Psub aa ws alen x i) =
  ok (Varr (WArray.Build_array (arr_size ws alen)
    (WArray.get_sub_data nx aa ws alen (WArray.arr_data tx) j))).
- by rewrite /= hgx /= hi /= hj.
exact: (arr_init_eP hst hXs _ hve hs).
Qed.

(* The assertions of the instrumented program imply the original ones. *)
Lemma explicit_init_aP X var_init s1 s2 a :
  mask_st_ex X s1 s2 -> no_mask (read_eassert a) -> check_arr_init gd a ->
  (forall x : var_i, Sv.In x (read_eassert a) ->
     sem_pexpr (sm := total) true gd s1 (var_init x) = ok (Vbool true) ->
     is_var_init (evm s2) x) ->
  sem_eassert gd s1 (explicit_init_a mask var_init a) = ok true ->
  sem_eassert gd s2 a = ok true.
Proof using explicit_init_ok mask_type.
move=> hst; have [hscs hmem hvm] := hst.
elim: a => [e | o es | x | e1 e2 | a1 ih1 a2 ih2] hX hc hvi.
- by rewrite /= (prog_eq_sem_pexpr (sm2 := total) _ _ _ _ hvm.1 hmem).
- have heqs : mapM (sem_pexpr (sm := total) true gd s1) es = mapM (sem_pexpr (sm := total) true gd s2) es.
  + by apply: (prog_eq_sem_pexprs (sm2 := total)) hvm.1 hmem.
  have hunch : forall o', sem_eassert gd s1 (PappN_safety o' es) = sem_eassert gd s2 (PappN_safety o' es).
  + by move=> o'; rewrite /= heqs.
  clear hvi; case: o hX hc => len hX hc; last by rewrite [explicit_init_a _ _ _]/= hunch.
  case: es hunch heqs hX hc => [|e [|lo [|n [|? ?]]]] hunch heqs hX hc;
    try by rewrite [explicit_init_a _ _ _]/= hunch.
  by apply: arr_init_aP hst _ hc; move: hX; rewrite read_eassert_PappN.
- by rewrite /=; t_xrbindP => v hv /to_boolI ?; subst v; rewrite (hvi _ _ hv) //; rewrite read_eassert_Pis_var_init; SvD.fsetdec.
- have hs : forall e0, no_mask (read_e e0) ->
    sem_pexpr (sm := total) true gd s1 e0 = sem_pexpr (sm := total) true gd s2 e0.
  + by move=> e0 h0; apply: prog_eq_sem_pexpr => //; exact: hvm.1.
  rewrite /= !hs ?hmem //; apply: no_maskI hX; rewrite read_eassert_Pis_mem_init; SvD.fsetdec.
move: hc => /= /andP [hc1 hc2].
have hX1 : no_mask (read_eassert a1) by apply: no_maskI hX; rewrite read_eassert_Pand; SvD.fsetdec.
have hX2 : no_mask (read_eassert a2) by apply: no_maskI hX; rewrite read_eassert_Pand; SvD.fsetdec.
have hvi1 : forall x : var_i, Sv.In x (read_eassert a1) ->
    sem_pexpr (sm := total) true gd s1 (var_init x) = ok (Vbool true) -> is_var_init (evm s2) x.
- by move=> x hx; apply: hvi; rewrite read_eassert_Pand; SvD.fsetdec.
have hvi2 : forall x : var_i, Sv.In x (read_eassert a2) ->
    sem_pexpr (sm := total) true gd s1 (var_init x) = ok (Vbool true) -> is_var_init (evm s2) x.
- by move=> x hx; apply: hvi; rewrite read_eassert_Pand; SvD.fsetdec.
rewrite /=; t_xrbindP => b1 hb1 b2 hb2.
move=> /andP [h1 h2]; move: hb1 hb2; rewrite h1 h2 => hb1 hb2.
by rewrite (ih1 hX1 hc1 hvi1 hb1) (ih2 hX2 hc2 hvi2 hb2).
Qed.
Lemma list_ltuple_filter_exact ts (msk : seq bool) (t : sem_tuple_t ts) :
  size msk = size ts ->
  List.Forall2 (fun tb v => is_defined v = if tb.1 is cbool then tb.2 else true)
    (zip ts msk) (list_ltuple (filter_tuple ts msk t)).
Proof.
elim: ts msk t => [ | t1 ts ih] [ | b msk] //= t [hsz].
case: ts ih t hsz => [ | t2 ts] ih t hsz /=.
- case: msk hsz => // _; constructor; last by constructor.
  by case: t1 t {ih} => //= ?; case: b.
constructor; last exact: (ih msk t.2 hsz).
by case: t1 t {ih} => //= ?; case: b.
Qed.

(* The total semantics defines an output exactly when it is not a boolean or
   its initialisation condition holds. *)
Lemma exec_sopn_init_exact o vs vs2 :
  exec_sopn (sm := total) o vs = ok vs2 ->
  List.Forall2 (fun tc v => is_defined v = if tc.1 is abool then safety_cond_holds vs tc.2 else true)
    (zip (tout (get_instr_desc o)) (i_init (get_instr_desc o))) vs2.
Proof.
rewrite /exec_sopn /sopn_sem; t_xrbindP => _ _ <- t + <-.
set d := get_instr_desc o.
rewrite /semi /mk_semi mk_semi_aux_app_sopnE; t_xrbindP => vs' htr t' _ /= _ <-.
case/and4P: (i_wf d) => _ hwt /ssrnat.eqnP hsz _.
have := list_ltuple_filter_exact t' (msk := [seq safety_cond_holds vs' i | i <- i_init d]).
rewrite !size_map hsz => /(_ erefl).
rewrite -/d; move: (list_ltuple _) hwt hsz => l.
elim: (tout d) (i_init d) l => [ | ty tys ih] [ | c cs] l //= hwt hsz hF; inversion hF; subst => //.
move: hwt => /andP [hc hcs]; constructor; last by apply: ih => //; case: hsz.
by rewrite H1 /= -(safety_cond_holds_truncate htr hc); case: (ty).
Qed.

(* The mask written for a scalar output holds exactly where the output is
   defined. *)
Lemma out_mask_exact s es o vs vs2 :
  sem_pexprs (sm := total) true gd s es = ok vs ->
  exec_sopn (sm := total) o vs = ok vs2 ->
  List.Forall2 (fun ce v => forall b, sem_pexpr (sm := total) true gd s ce = ok (Vbool b) -> b = is_defined v)
    (map2 (out_mask es) (tout (get_instr_desc o)) (i_init (get_instr_desc o))) vs2.
Proof.
move=> hes hex.
have hsz : size es = size (map eval_atype (tin (get_instr_desc o))).
- by rewrite size_map -(exec_sopn_size hex) (size_mapM hes).
have hwt := instr_desc_init_wt (get_instr_desc o).
have hexpr := i_init_expr (get_instr_desc o).
move: hwt hexpr => /(_ _pd _msf_size) hwt /(_ _pd _msf_size) hexpr.
move: (exec_sopn_init_exact hex) hwt hexpr; clear hex.
elim: (tout _) (i_init _) vs2 => [ | ty tys ih] [ | c cs] [ | v vs'] //= hF; inversion hF; subst.
move=> /andP [hc hcs] /andP [hce hces]; constructor; last by apply: ih.
move=> b; rewrite H2 /out_mask; case: (ty) => [ | | ws len | ws] /=; last 3 first.
1-3: by move=> [].
have hb : safety_cond_below (size es) c by rewrite hsz; exact: (safety_cond_type_below (eqP hc)).
by move=> /(sem_pexpr_sc_to_e hes hce hb); rewrite /safety_cond_holds => ->.
Qed.
Lemma mask_cmd_out ii lv ce :
  all is_mask_assgn (explicit_init_out mask ii lv ce) /\
  forall y, Sv.In y (write_c (explicit_init_out mask ii lv ce)) -> is_mask y.
Proof.
case: lv => [vi tyn | x | al ws x e' | al aa ws x e' | aa ws len x e'] /=.
1,3,5: by split => // y; rewrite write_c_nil => /SvD.F.empty_iff.
- case: ifP => _; first by split => // y; rewrite write_c_nil => /SvD.F.empty_iff.
  by split => // y; rewrite write_c_assgn1 /= => /SvD.F.singleton_iff <-; exists x.
by split => // y; rewrite write_c_assgn1 /= => /SvD.F.singleton_iff <-; exists x.
Qed.

Lemma opn_mask_step ii lv ce v s2 a a1 c c1 :
  mask_inv Sv.empty (evm a) (evm c) -> prog_eq (evm a) (evm s2) -> emem a = emem s2 ->
  (forall e, lv_idx lv = Some e ->
     sem_pexpr (sm := total) true gd a e = sem_pexpr (sm := total) true gd c e) ->
  no_mask (read_e ce) ->
  (forall b, sem_pexpr (sm := total) true gd s2 ce = ok (Vbool b) -> b = is_defined v) ->
  ~~ is_carr (type_of_val v) ->
  esem (sm := total_init) pm ev (explicit_init_out mask ii lv ce) a = ok a1 ->
  write_lval (sm := total) true gd lv v c = ok c1 ->
  mask_inv Sv.empty (evm a1) (evm c1).
Proof using mask_inj mask_type.
move=> hinv hp hmem hidx hXc hdef hv ha hw.
have hna := write_lval_nonarr hv hw.
case: lv hidx ha hw hna => [vi ty | x | al ws x e | al aa ws x e | aa ws len x e] hidx ha hw hna //;
  move: ha; rewrite [explicit_init_out _ _ _ _]/=.
- by move=> [<-]; rewrite (write_lval_novar _ hw).
- rewrite (negbTE hna) esem_assgn1 /sem_assgn; t_xrbindP => mv hmv mv' htm hwm.
  apply: (mask_inv_mirror (lv := Lvar x) hinv hidx _ _ _ hwm hw) => //.
  + move=> _ [<-] _; rewrite SvD.F.empty_b; split => //.
    move: htm => /truncate_val_typeE [b ? ->]; subst mv; congr Vbool; apply: hdef.
    by rewrite -hmv; symmetry; apply: prog_eq_sem_pexpr.
  by move=> i; rewrite is_initv_not_arr //; case/truncate_val_typeE: htm => ? _ ->.
- by move=> [<-]; rewrite (write_lval_novar _ hw).
move=> /sem_cell_mask hwm.
apply: (mask_inv_mirror (lv := Laset al aa ws x e) hinv hidx _ _ _ hwm hw) => //.
- by move=> > [] _ _ <-.
by move=> i; rewrite is_initv_not_arr.
Qed.
Lemma lv_idx_var lv : is_var_lv lv -> lv_idx lv = None.
Proof. by case: lv. Qed.

Lemma opn_masks_inv ii lvs ces vs2 s2 a a' c c' :
  mask_inv Sv.empty (evm a) (evm c) -> prog_eq (evm a) (evm s2) -> emem a = emem s2 ->
  (forall e, lv_idx (head (Lnone dummy_var_info abool) lvs) = Some e ->
     sem_pexpr (sm := total) true gd a e = sem_pexpr (sm := total) true gd c e) ->
  all is_var_lv (behead lvs) ->
  no_mask (read_es ces) ->
  List.Forall2 (fun ce v => forall b, sem_pexpr (sm := total) true gd s2 ce = ok (Vbool b) -> b = is_defined v) ces vs2 ->
  all (fun v => ~~ is_carr (type_of_val v)) vs2 ->
  esem (sm := total_init) pm ev (flatten (map2 (explicit_init_out mask ii) lvs ces)) a = ok a' ->
  write_lvals (sm := total) true gd c lvs vs2 = ok c' ->
  mask_inv Sv.empty (evm a') (evm c').
Proof using mask_inj mask_type.
elim: lvs ces vs2 a c => [ | lv lvs ih] ces vs2 a c hinv hp hmem hidx hvar hXc hdef hna.
- have -> : map2 (explicit_init_out mask ii) [::] ces = [::] by case: ces {hXc hdef}.
  by case: vs2 {hdef hna} => //= -[<-] [<-].
case: hdef hXc hna => [ | ce v ces' vs' hcev hdef'] hXc hna //=.
rewrite esem_cat; t_xrbindP => a1 ha1 ha2 c1 hc1 hc2.
move: hna => /andP [hv hna].
have [hall hW] := mask_cmd_out ii lv ce.
have [hscs1 hmem1 hp1] := esem_mask_cmd hall hW ha1.
have hXce : no_mask (read_e ce) by apply: no_maskI hXc; rewrite read_es_cons; SvD.fsetdec.
have hXcs : no_mask (read_es ces') by apply: no_maskI hXc; rewrite read_es_cons; SvD.fsetdec.
have hinv1 := opn_mask_step hinv hp hmem hidx hXce hcev hv ha1 hc1.
apply: (ih ces' vs' a1 c1 hinv1 (hp1 _ hp) _ _ _ hXcs hdef' hna ha2 hc2).
- by rewrite hmem1.
- by case: (lvs) hvar => //= lv' ? /andP [/lv_idx_var ->].
by case: (lvs) hvar => //= ? ? /andP [].
Qed.

Lemma read_e_out_mask es t c : Sv.Subset (read_e (out_mask es t c)) (read_es es).
Proof.
clear -es t c; rewrite /out_mask; case: t; last 3 first.
1-3: by rewrite /read_e /=; SvD.fsetdec.
exact: read_e_sc_to_e.
Qed.

Lemma mask_cmd_opn ii lvs ces :
  all is_mask_assgn (flatten (map2 (explicit_init_out mask ii) lvs ces)) /\
  forall y, Sv.In y (write_c (flatten (map2 (explicit_init_out mask ii) lvs ces))) -> is_mask y.
Proof.
elim: lvs ces => [ | lv lvs ih] [ | ce ces] /=; try by split => // y; rewrite write_c_nil => /SvD.F.empty_iff.
have [h1 h2] := mask_cmd_out ii lv ce; have [h3 h4] := ih ces.
rewrite all_cat h1 h3; split => // y; rewrite write_c_app => /Sv.union_spec [/h2 | /h4] //.
Qed.

Lemma opnP ii lvs tg o es s0 s1' s2 :
  no_mask (vars_I (MkI ii (Copn lvs tg o es))) ->
  all is_var_lv (behead lvs) ->
  (forall vs vs2, size vs = size es -> exec_sopn (sm := total) o vs = ok vs2 ->
     size vs2 = size lvs -> all (fun v => ~~ is_carr (type_of_val v)) vs2) ->
  mask_st s0 s2 ->
  esem (sm := total_init) pm ev (explicit_init_opn mask ii lvs o es ++ [:: MkI ii (Copn lvs tg o es)]) s0 = ok s1' ->
  exists2 s2', esem (sm := total) p ev [:: MkI ii (Copn lvs tg o es)] s2 = ok s2' & mask_st s1' s2'.
Proof using mask_inj mask_type.
move=> hX hvar hna [hscs hmem hvm]; rewrite esem_cat; t_xrbindP => s1 hmask.
have [hall hW] := mask_cmd_opn ii lvs (map2 (out_mask es) (tout (get_instr_desc o)) (i_init (get_instr_desc o))).
have [hscs1 hmem1 hp1] := esem_mask_cmd hall hW hmask.
rewrite esem_opn1 /sem_sopn; t_xrbindP => vs1 vs hvs hex hw.
have hXes : no_mask (read_es es).
- by apply: no_maskI hX; rewrite /vars_I read_Ii write_Ii read_i_opn write_i_opn; SvD.fsetdec.
have hXl : no_mask (vars_lvals lvs).
- by apply: no_maskI hX; rewrite /vars_I /vars_lvals read_Ii write_Ii read_i_opn write_i_opn; SvD.fsetdec.
have hp12 := hp1 _ hvm.1.
have hvs2 : sem_pexprs (sm := total) true gd s2 es = ok vs.
- by rewrite -hvs; symmetry; apply: prog_eq_sem_pexprs => //; rewrite hmem1.
have hvs0 : sem_pexprs (sm := total) true gd s0 es = ok vs.
- rewrite -hvs; symmetry; apply: prog_eq_sem_pexprs => //.
  by apply: (hp1 _ (fun _ _ => erefl)).
have [vs2 hex2 ?] := (exec_sopn_total_initP o vs vs1).1 hex; subst vs1.
rewrite (write_lvals_is_totalE gd (sm2 := total)) // in hw.
have [s2' hw2 [hs hm hp]] :=
  prog_eq_write_lvals_dflt hp12 (etrans hscs1 hscs) (etrans hmem1 hmem) hXl (exec_sopn_DB hex2) hw.
exists s2'.
- by rewrite esem_opn1 /sem_sopn hvs2 /= hex2.
split => //; split => //.
apply: (mask_inv_prog_l (W := vrvs lvs)); first by apply: no_maskI hXl; rewrite /vars_lvals; SvD.fsetdec.
- exact: vrvsP hw.
apply: (opn_masks_inv (s2 := s2) hvm.2 hvm.1 hmem _ hvar _ (out_mask_exact hvs2 hex2) _ hmask hw2).
- move=> e he; apply: prog_eq_sem_pexpr => //; last exact: hvm.1.
  apply: no_maskI hXl; case: (lvs) he => //= lv ? he.
  rewrite /vars_lvals read_rvs_cons; case: (lv) he => //= > [<-]; rewrite /read_rv /= read_eE; SvD.fsetdec.
- apply: no_maskI hXes; elim: (tout _) (i_init _) => [ | t ts ih] [ | c cs] /=; try by rewrite /read_es /=; SvD.fsetdec.
  by rewrite read_es_cons; have := ih cs; have := @read_e_out_mask es t c; SvD.fsetdec.
apply: (hna vs) => //.
- by rewrite (size_mapM hvs).
by rewrite (size_fold2 hw2).
Qed.


(* The total copy initialises exactly the cells of its result. *)
Lemma copy_total_init ws n (a : WArray.array (arr_size ws n)) k :
  WArray.is_init (@copy_total ws n a) k = (0 <=? k) && (k <? arr_size ws n).
Proof.
case hk: (_ && _); first by apply: copy_total_is_init; move: hk => /andP [/ZleP ? /ZltP ?].
rewrite /copy_total.
have : ~~ WArray.is_init (WArray.empty (arr_size ws n)) k by [].
elim: (ziota 0 n) (WArray.empty _) => [ | i l ih] t //= ht.
- exact: negbTE.
apply: ih; rewrite /copy_set; case h: WArray.set => [t' | //].
by rewrite (set_total_is_init k h) /WArray.in_bound hk andbF /= andbF.
Qed.
Lemma lv_write_mem_mask_lv lv : lv_write_mem (mask_lv lv) = lv_write_mem lv.
Proof. by case: lv. Qed.


(* The mask of a destination writes masks only. *)
Lemma vrv_mask_lv lv y : Sv.In y (vrv (mask_lv lv)) -> is_mask y.
Proof.
case: lv => /= [vi ty | x | al ws x e | al aa ws x e | aa ws len x e].
1,3: by move=> /SvD.F.empty_iff.
all: by move=> /SvD.F.singleton_iff <-; exists x.
Qed.

(* The mask written for the single array output of an instruction. *)
Lemma arr_mask_writeP ii ws len lv me s0 s1 :
  esem (sm := total_init) pm ev [:: set_arr_mask mask ii ws len lv me] s0 = ok s1 ->
  exists m m', [/\ sem_pexpr (sm := total) true gd s0 me = ok m,
    truncate_val (carr (arr_size ws len)) m = ok m',
    write_lval (sm := total) true gd (mask_lv lv) m' s0 = ok s1,
    [/\ escs s1 = escs s0, emem s1 = emem s0 & forall vm, prog_eq (evm s0) vm -> prog_eq (evm s1) vm] &
    ~~ lv_write_mem lv].
Proof.
rewrite /set_arr_mask esem_assgn1 /sem_assgn; t_xrbindP => m hm m' htr hw.
rewrite (sem_pexpr_is_totalE gd (sm2 := total)) // in hm.
rewrite (write_lval_is_totalE gd (sm2 := total)) // in hw.
have hnm : ~~ lv_write_mem lv.
- case/truncate_val_typeE: htr => a _ hm'; subst m'.
  by case: lv hw => //= al ws' x e; t_xrbindP.
exists m, m'; split => //.
have [hscs hmem] := lv_write_scs_mem hw; split => //.
- by rewrite hmem // lv_write_mem_mask_lv.
move=> vm hp y hy; rewrite -(get_total_eq_ex (vrvP hw)); first by apply: hp.
by move=> /vrv_mask_lv.
Qed.

Lemma opn1_arrP ii lv tg o es ws len me s0 s1' s2 :
  no_mask (vars_I (MkI ii (Copn [:: lv] tg o es))) ->
  (forall m m' vs v, sem_pexpr (sm := total) true gd s0 me = ok m ->
     truncate_val (carr (arr_size ws len)) m = ok m' ->
     sem_pexprs (sm := total) true gd s0 es = ok vs ->
     exec_sopn (sm := total) o vs = ok [:: v] -> val_mask_of v m') ->
  mask_st s0 s2 ->
  esem (sm := total_init) pm ev [:: set_arr_mask mask ii ws len lv me; MkI ii (Copn [:: lv] tg o es)] s0 = ok s1' ->
  exists2 s2', esem (sm := total) p ev [:: MkI ii (Copn [:: lv] tg o es)] s2 = ok s2' & mask_st s1' s2'.
Proof using mask_inj mask_type.
move=> hX hval [hscs hmem hvm]; rewrite -cat1s esem_cat; t_xrbindP => s1 /arr_mask_writeP.
move=> [m [m' [hm htr hwm [hscs1 hmem1 hp1] hnm]]].
rewrite esem_opn1 /sem_sopn; t_xrbindP => vs1 vs hvs hex hw.
have hXes : no_mask (read_es es).
- by apply: no_maskI hX; rewrite /vars_I read_Ii write_Ii read_i_opn write_i_opn; SvD.fsetdec.
have hXl : no_mask (vars_lvals [:: lv]).
- by apply: no_maskI hX; rewrite /vars_I /vars_lvals read_Ii write_Ii read_i_opn write_i_opn; SvD.fsetdec.
have hp12 := hp1 _ hvm.1.
have hvs2 : sem_pexprs (sm := total) true gd s2 es = ok vs.
- by rewrite -hvs; symmetry; apply: prog_eq_sem_pexprs => //; rewrite hmem1.
have hvs0 : sem_pexprs (sm := total) true gd s0 es = ok vs.
- rewrite -hvs; symmetry; apply: prog_eq_sem_pexprs => //.
  by apply: (hp1 _ (fun _ _ => erefl)).
have [vs2 hex2 ?] := (exec_sopn_total_initP o vs vs1).1 hex; subst vs1.
rewrite (write_lvals_is_totalE gd (sm2 := total)) // in hw.
have [s2' hw2 [hs hm' hp]] :=
  prog_eq_write_lvals_dflt hp12 (etrans hscs1 hscs) (etrans hmem1 hmem) hXl (exec_sopn_DB hex2) hw.
exists s2'.
- by rewrite esem_opn1 /sem_sopn hvs2 /= hex2.
split => //; split => //.
apply: (mask_inv_prog_l (W := vrvs [:: lv])); first by apply: no_maskI hXl; rewrite /vars_lvals; SvD.fsetdec.
- exact: vrvsP hw.
clear hex hw.
case: vs2 hex2 hw2 => [ | v [ | ? ?]] hex2 //=; t_xrbindP => // s2'' hw2 ?; subst s2''.
case/truncate_val_typeE: (htr) => tm ? ?; subst m m'.
apply: (mask_inv_mirror hvm.2 _ _ _ (hval _ _ _ _ hm htr hvs0 hex2) hwm hw2).
- move=> e0 he0; apply: prog_eq_sem_pexpr => //; last exact: hvm.1.
  apply: no_maskI hXl; case: (lv) he0 => //= > [<-]; rewrite /vars_lvals /read_rvs /= read_eE; SvD.fsetdec.
- move=> x ? hx; subst lv; move: hwm; rewrite /= /write_var; t_xrbindP => ? /set_varP [_ + _].
  by rewrite mask_type (negbTE hx).
by move=> al aa ws0 x e ?; subst lv; move: hwm => /=; apply: on_arr_varP => > _ _; t_xrbindP.
Qed.

Lemma exec_copy_init ws len vs v :
  exec_sopn (sm := total) (Opseudo_op (Ocopy ws len)) vs = ok [:: v] ->
  forall i, is_initv v i = (0 <=? i) && (i <? arr_size ws len).
Proof.
rewrite /exec_sopn /sopn_sem /=; t_xrbindP => t.
case: vs => // a [] //=; t_xrbindP => a' ha.
- by move=> <- <- i /=; apply: copy_total_init.
by [].
Qed.

Lemma copyP ii lv tg ws len es s0 s1' s2 :
  no_mask (vars_I (MkI ii (Copn [:: lv] tg (Opseudo_op (Ocopy ws len)) es))) ->
  mask_st s0 s2 ->
  esem (sm := total_init) pm ev [:: set_arr_mask mask ii ws len lv (efull_mask ws len);
                                    MkI ii (Copn [:: lv] tg (Opseudo_op (Ocopy ws len)) es)] s0 = ok s1' ->
  exists2 s2', esem (sm := total) p ev [:: MkI ii (Copn [:: lv] tg (Opseudo_op (Ocopy ws len)) es)] s2 = ok s2'
             & mask_st s1' s2'.
Proof using mask_inj mask_type.
move=> hX; apply: opn1_arrP => // m m' vs v /sem_efull hm /truncate_val_typeE [a ? ?] _ hex i; subst m m'.
by rewrite hm (exec_copy_init hex).
Qed.

Lemma protectP ii lv tg o ws len e e' s0 s1' s2 :
  (o = SLHprotect_ptr ws len \/ o = SLHprotect_ptr_fail ws len) ->
  no_mask (vars_I (MkI ii (Copn [:: lv] tg (Oslh o) [:: e; e']))) ->
  mask_st s0 s2 ->
  esem (sm := total_init) pm ev [:: set_arr_mask mask ii ws len lv (mask_of e);
                                    MkI ii (Copn [:: lv] tg (Oslh o) [:: e; e'])] s0 = ok s1' ->
  exists2 s2', esem (sm := total) p ev [:: MkI ii (Copn [:: lv] tg (Oslh o) [:: e; e'])] s2 = ok s2'
             & mask_st s1' s2'.
Proof using explicit_init_ok mask_inj mask_type.
move=> ho hX hst; apply: opn1_arrP => // m m' vs v hm /truncate_val_typeE [a ? ?] hvs hex; subst m m'.
have -> := exec_protect_ptr ho hex.
move: hvs => /=; t_xrbindP.
move=> ve hve _ _ _ _ <- /=.
apply: (mask_ofP _ _ hve hm).
- by apply: no_maskI hX; rewrite /vars_I read_Ii write_Ii read_i_opn write_i_opn read_es_cons; SvD.fsetdec.
case: hst => _ _ hvm.
by move=> y hy; apply: (mask_vm_self hvm).
Qed.

(* Variables and their masks written by the same instruction. *)
Lemma mirror_lvals_inv lvs mvs vs a a' c c' :
  mask_inv Sv.empty (evm a) (evm c) -> all is_var_lv lvs ->
  List.Forall2 val_mask_of vs mvs ->
  all (fun m => is_carr (type_of_val m)) mvs ->
  write_lvals (sm := total) true gd a (mask_lvs mask lvs) mvs = ok a' ->
  write_lvals (sm := total) true gd c lvs vs = ok c' ->
  mask_inv Sv.empty (evm a') (evm c').
Proof using mask_inj mask_type.
elim: lvs mvs vs a c => [ | lv lvs ih] mvs vs a c hinv hvar hval hmarr.
- by case: mvs vs {hval hmarr} => [ | ??] [ | ??] //= [<-] [<-].
case: hval hmarr => [ | v m vs' mvs' hvm hval'] hmarr //=.
move: hvar hmarr => /= /andP [hv hvar] /andP [hm hmarr].
t_xrbindP => a1 hwa1 hwa c1 hwc1 hwc.
apply: (ih _ _ a1 c1 _ hvar hval' hmarr hwa hwc).
apply: (mask_inv_mirror hinv _ _ _ hvm hwa1 hwc1).
- by case: (lv) hv.
- move=> x ? hx; subst lv; move: hwa1; rewrite /= /write_var; t_xrbindP => ? /set_varP [hdb + _].
  rewrite mask_type (negbTE hx).
  by case: (m) hm hdb => //=; case.
by move=> > ?; subst lv.
Qed.

Lemma vrvs_mask_lvs lvs y : Sv.In y (vrvs (mask_lvs mask lvs)) -> is_mask y.
Proof.
elim: lvs => [ | lv lvs ih] /=; first by rewrite /vrvs /= => /SvD.F.empty_iff.
by rewrite vrvs_cons => /Sv.union_spec [/vrv_mask_lv | /ih].
Qed.
Lemma swapP ii lvs tg ws len es s0 s1' s2 :
  let o := Opseudo_op (Oswap (aarr ws len)) in
  no_mask (vars_I (MkI ii (Copn lvs tg o es))) ->
  (ssrnat.leq 2 (size lvs) -> all is_var_lv lvs) ->
  mask_st s0 s2 ->
  esem (sm := total_init) pm ev [:: MkI ii (Copn (mask_lvs mask lvs) tg o (mask_es mask es));
                                    MkI ii (Copn lvs tg o es)] s0 = ok s1' ->
  exists2 s2', esem (sm := total) p ev [:: MkI ii (Copn lvs tg o es)] s2 = ok s2' & mask_st s1' s2'.
Proof using explicit_init_ok mask_inj mask_type.
move=> o hX hok [hscs hmem hvm]; rewrite -cat1s esem_cat esem_opn1 /sem_sopn; t_xrbindP.
move=> s1 ms' ms hms hexm hwm; rewrite esem_opn1 /sem_sopn; t_xrbindP => vs' vs hvs hex hw.
have [m1 [m2 [? ?]]] := exec_swapE hexm; subst ms ms'.
have [a1 [a2 [? ?]]] := exec_swapE hex; subst vs vs'.
rewrite (sem_pexprs_is_totalE gd (sm2 := total)) // in hms.
rewrite (sem_pexprs_is_totalE gd (sm2 := total)) // in hvs.
rewrite (write_lvals_is_totalE gd (sm2 := total)) // in hwm.
rewrite (write_lvals_is_totalE gd (sm2 := total)) // in hw.
have [hscs1 hmem1] := write_lvals_arr_mem (vs := [:: Varr m2; Varr m1]) erefl hwm.
have hp1 : forall vm, prog_eq (evm s0) vm -> prog_eq (evm s1) vm.
- move=> vm hp y hy; rewrite -(get_total_eq_ex (vrvsP hwm)); first by apply: hp.
  by move=> /vrvs_mask_lvs.
have hXes : no_mask (read_es es).
- by apply: no_maskI hX; rewrite /vars_I read_Ii write_Ii read_i_opn write_i_opn; SvD.fsetdec.
have hXl : no_mask (vars_lvals lvs).
- by apply: no_maskI hX; rewrite /vars_I /vars_lvals read_Ii write_Ii read_i_opn write_i_opn; SvD.fsetdec.
have hp12 := hp1 _ hvm.1.
have hvs2 : sem_pexprs (sm := total) true gd s2 es = ok [:: Varr a1; Varr a2].
- rewrite -hvs; symmetry; apply: prog_eq_sem_pexprs => //.
  by rewrite -hmem1.
have hvs0 : sem_pexprs (sm := total) true gd s0 es = ok [:: Varr a1; Varr a2].
- rewrite -hvs; symmetry; apply: prog_eq_sem_pexprs => //.
  by apply: (hp1 _ (fun _ _ => erefl)).
have [vs2 hex2 hvs2'] := (exec_sopn_total_initP o _ _).1 hex.
have [b1 [b2 [hb ?]]] := exec_swapE hex2; subst vs2.
case: hb => ? ?; subst b1 b2.
have [s2' hw2 [hs hm' hp]] :=
  prog_eq_write_lvals_dflt (vs := [:: Varr a2; Varr a1]) hp12 (etrans (esym hscs1) hscs) (etrans (esym hmem1) hmem) hXl erefl hw.
exists s2'.
- by rewrite esem_opn1 /sem_sopn hvs2 /= hex2.
split => //; split => //.
apply: (mask_inv_prog_l (W := vrvs lvs)); first by apply: no_maskI hXl; rewrite /vars_lvals; SvD.fsetdec.
- exact: vrvsP hw.
have hval : List.Forall2 val_mask_of [:: Varr a2; Varr a1] [:: Varr m2; Varr m1].
- case: es hms hvs0 hXes {hvs hvs2 hX} => [ | e1 [ | e2 [ | ? ?]]] //=; t_xrbindP => //.
  + move=> z hm1 z0 z1 hm2 ? ? hz1 z2 he1 z3 z4 he2 ? ? hz4 hXes'; subst.
    case: hz1 => ?; case: hz4 => ?; subst.
    have hself : forall x, ~ is_mask x ->
      val_mask_of (Vm.get (sm := total) (evm s0) x) (Vm.get (sm := total) (evm s0) (mask x)).
    * by move=> y hy; apply: (mask_vm_self hvm).
    have hX1 : no_mask (read_e e1) by apply: no_maskI hXes'; rewrite !read_es_cons; SvD.fsetdec.
    have hX2 : no_mask (read_e e2) by apply: no_maskI hXes'; rewrite !read_es_cons; SvD.fsetdec.
    constructor; first exact: (mask_ofP hX2 hself he2 hm2).
    by constructor => //; exact: (mask_ofP hX1 hself he1 hm1).
  move=> z hm1 z0 z1 hm2 z2 z3 hm3 z4 hm4 ? ? ? hz; subst.
  by case: hz.
apply: (mirror_lvals_inv hvm.2 _ hval _ hwm hw2) => //.
apply: hok; have := size_fold2 hwm; by rewrite /mask_lvs size_map => ->.
Qed.

Lemma fexec_random_mem ws len fs fs' :
  fexec_syscall (RandomBytes ws len) fs = ok fs' -> fmem fs' = fmem fs.
Proof.
by rewrite /fexec_syscall /= /exec_getrandom_u; t_xrbindP => z z0 z1 _ z2 _ h1 h2 h3; subst; case: h3 => <-.
Qed.

Lemma fexec_random_init ws len fs fs' :
  fexec_syscall (RandomBytes ws len) fs = ok fs' ->
  exists2 v, fvals fs' = [:: v] & forall i, is_initv v i = (0 <=? i) && (i <? arr_size ws len).
Proof.
rewrite /fexec_syscall /=.
rewrite /exec_getrandom_u; t_xrbindP.
move=> _ _ _ _ t ht <- <- [<-] /=; exists (Varr t) => // i /=.
by rewrite /WArray.is_init (fill_data ht); case: (_ && _).
Qed.

(* The random bytes fill their destination, whose mask is full. *)
Lemma syscall_arrP ii lv ws len es s0 s1' s2 :
  no_mask (vars_I (MkI ii (Csyscall [:: lv] (RandomBytes ws len) es))) ->
  mask_st s0 s2 ->
  esem (sm := total_init) pm ev [:: set_arr_mask mask ii ws len lv (efull_mask ws len);
                                    MkI ii (Csyscall [:: lv] (RandomBytes ws len) es)] s0 = ok s1' ->
  exists2 s2', esem (sm := total) p ev [:: MkI ii (Csyscall [:: lv] (RandomBytes ws len) es)] s2 = ok s2'
             & mask_st s1' s2'.
Proof using mask_inj mask_type.
move=> hX [hscs hmem hvm]; rewrite -cat1s esem_cat; t_xrbindP => s1 /arr_mask_writeP.
move=> [m [m' [hm htr hwm [hscs1 hmem1 hp1] hnm]]].
rewrite esem_syscall1 /sem_syscall; t_xrbindP => vs hvs fs hfs hw.
have hXes : no_mask (read_es es).
- by apply: no_maskI hX; rewrite /vars_I read_Ii write_Ii read_i_syscall write_i_syscall; SvD.fsetdec.
have hXl : no_mask (vars_lval lv).
- by apply: no_maskI hX; rewrite /vars_I /vars_lval read_Ii write_Ii read_i_syscall write_i_syscall /vars_lvals read_rvs_cons vrvs_cons; SvD.fsetdec.
have hp12 := hp1 _ hvm.1.
rewrite (sem_pexprs_is_totalE gd (sm2 := total)) // in hvs.
have hvs2 : sem_pexprs (sm := total) true gd s2 es = ok vs.
- by rewrite -hvs; symmetry; apply: prog_eq_sem_pexprs => //; rewrite hmem1.
have hfs2 : fexec_syscall (RandomBytes ws len) (mk_fstate vs s2) = ok fs.
- by rewrite /mk_fstate -hscs -hmem -hscs1 -hmem1.
have [v hv hinit] := fexec_random_init hfs.
have hmfs := fexec_random_mem hfs.
move: hw; rewrite /upd_estate hv /=; t_xrbindP => s1'' hw ?; subst s1''.
rewrite (write_lval_is_totalE gd (sm2 := total)) // in hw.
have := prog_eq_write_lval (c := with_scs (with_mem s2 (fmem fs)) (fscs fs)) _ _ _ hXl hw.
move=> /(_ hp12 erefl erefl) [s2' hw2 [hs hm' hp]].
exists s2'.
- by rewrite ?esem_syscall1 /sem_syscall hvs2 /= hfs2 /= /upd_estate hv /= hw2.
split => //; split => //.
apply: (mask_inv_prog_l (W := vrv lv)); first by apply: no_maskI hXl; rewrite /vars_lval; SvD.fsetdec.
- exact: vrvP hw.
rewrite /=.
case/truncate_val_typeE: (htr) => a ? ?; subst m m'.
apply: (mask_inv_mirror (c := with_scs (with_mem s2 (fmem fs)) (fscs fs)) hvm.2 _ _ _ _ hwm hw2).
- move=> e he; have hXe : no_mask (read_e e).
  + by apply: no_maskI hXl; case: (lv) he => //= > [<-]; rewrite /vars_lval /read_rv /= read_eE; SvD.fsetdec.
  apply: (prog_eq_sem_pexpr (sm2 := total)) => //=; first exact: hvm.1.
  by rewrite hmfs /= hmem1.
- move=> x ? hx; subst lv; move: hwm; rewrite /= /write_var; t_xrbindP => ? /set_varP [_ + _].
  by rewrite mask_type (negbTE hx).
- by move=> al aa ws0 x e ?; subst lv; move: hwm => /=; apply: on_arr_varP => > _ _; t_xrbindP.
by move=> i /=; rewrite hinit -(sem_efull hm).
Qed.

(* The random bytes written in a destination that is not an array. *)
Lemma syscall_otherP ii lvs ws len es s0 s1' s2 :
  (if lvs is [:: Lvar _] then false else true) -> all is_var_lv lvs ->
  no_mask (vars_I (MkI ii (Csyscall lvs (RandomBytes ws len) es))) ->
  mask_st s0 s2 ->
  esem (sm := total_init) pm ev [:: MkI ii (Csyscall lvs (RandomBytes ws len) es)] s0 = ok s1' ->
  exists2 s2', esem (sm := total) p ev [:: MkI ii (Csyscall lvs (RandomBytes ws len) es)] s2 = ok s2'
             & mask_st s1' s2'.
Proof using mask_inj mask_type.
move=> hlvs hvar hX [hscs hmem hvm]; rewrite esem_syscall1 /sem_syscall; t_xrbindP => vs hvs fs hfs hw.
have hXes : no_mask (read_es es).
- by apply: no_maskI hX; rewrite /vars_I read_Ii write_Ii read_i_syscall write_i_syscall; SvD.fsetdec.
rewrite (sem_pexprs_is_totalE gd (sm2 := total)) // in hvs.
have hvs2 : sem_pexprs (sm := total) true gd s2 es = ok vs.
- by rewrite -hvs; symmetry; apply: prog_eq_sem_pexprs => //; exact: hvm.1.
have hfs2 : fexec_syscall (RandomBytes ws len) (mk_fstate vs s2) = ok fs.
- by rewrite /mk_fstate -hscs -hmem.
have [v hv hinit] := fexec_random_init hfs.
move: hw; rewrite /upd_estate hv.
case: lvs hlvs hvar hX => [ | lv [ | ? ?]] //= hlvs hvar hX; t_xrbindP => // s1'' hw ?; subst s1''.
have hXl : no_mask (vars_lval lv).
- by apply: no_maskI hX; rewrite /vars_I /vars_lval read_Ii write_Ii read_i_syscall write_i_syscall /vars_lvals read_rvs_cons vrvs_cons; SvD.fsetdec.
rewrite (write_lval_is_totalE gd (sm2 := total)) // in hw.
have := prog_eq_write_lval (c := with_scs (with_mem s2 (fmem fs)) (fscs fs)) _ _ _ hXl hw.
move=> /(_ hvm.1 erefl erefl) [s2' hw2 [hs hm' hp]].
exists s2'.
- by rewrite ?esem_syscall1 /sem_syscall hvs2 /= hfs2 /= /upd_estate hv /= hw2.
split => //; split => //.
apply: (mask_inv_prog_l (W := vrv lv)); first by apply: no_maskI hXl; rewrite /vars_lval; SvD.fsetdec.
- exact: vrvP hw.
rewrite (write_lval_novar _ hw2) /=; last by case: (lv) hlvs hvar.
exact: hvm.2.
Qed.

(* Truncating the values exchanged by a call at the types of the
   instrumented function and at the original ones. *)
Lemma truncate_mask_vals tys vs1 vs1' vs2 :
  mapM2 ErrType dc_truncate_val (map eval_atype (List.flat_map with_mask_ty tys)) vs1 = ok vs1' ->
  mask_vals vs1 vs2 ->
  exists2 vs2', mapM2 ErrType dc_truncate_val (map eval_atype tys) vs2 = ok vs2' & mask_vals vs1' vs2'.
Proof.
elim: tys vs1 vs1' vs2 => [ | ty tys ih] vs1 vs1' vs2 /=.
- by case: vs1 => // -[<-] h; inversion h; exists [::] => //; constructor.
move=> h hv; case: hv h => [ | v vs1'' vs2'' hna hdef hv | len t tm vs1'' vs2'' htm hv] //=.
- by case: ty.
- case: ty => [||ws len|ws] /=; t_xrbindP.
  1,2,4: move=> v' htr vs1r /ih /(_ hv) [vs2r -> hvr] <-; rewrite htr /=; eexists; first reflexivity.
  1,2: constructor => //; [by case/truncate_val_typeE: htr => ? _ -> | exact: truncate_val_defined htr].
  constructor => //; [by case/truncate_val_typeE: htr => ? [? [? [_ _ ->]]] | exact: truncate_val_defined htr].
  by move=> z /truncate_val_typeE [a ? _]; subst v.
case: ty => [||ws n|ws] /=; t_xrbindP.
1,2,4: by [].
move=> z /truncate_varr [-> [a _ ?]] _ z1 /truncate_varr [-> _] vs1r /ih /(_ hv) [vs2r -> hvr] <- <-; subst len.
rewrite /dc_truncate_val /=.
have -> : truncate_val (carr (arr_size ws n)) (Varr t) = ok (Varr t) by rewrite /truncate_val /= to_arrK.
by eexists; [reflexivity | constructor].
Qed.

Lemma write_vars_mask X xs vs1 vs2 s1 s1' s2 :
  mask_st_ex X s1 s2 -> no_mask (vars_l xs) -> mask_vals vs1 vs2 ->
  write_vars true (List.flat_map (with_mask_x mask) xs) vs1 s1 = ok s1' ->
  exists2 s2', write_vars true xs vs2 s2 = ok s2' & mask_st_ex (Sv.union (vars_l xs) X) s1' s2'.
Proof using asm_op ep mask mask_inj mask_type p sip spp syscall_state.
elim: xs vs1 vs2 X s1 s2 => [ | x xs ih] vs1 vs2 X s1 s2 hst hX hv /=.
- by case: hv => //= [[<-]]; exists s2.
have hXx : no_mask (vars_lval (Lvar x)) by apply: no_maskI hX; rewrite /vars_lval /=; SvD.fsetdec.
have hXs : no_mask (vars_l xs) by apply: no_maskI hX => /=; SvD.fsetdec.
case: hst => hscs hmem [hp hinv].
case: hv => [ | v vs1' vs2' hna hdef hv | len t tm vs1' vs2' htm hv]; rewrite /with_mask_x; case hxa: (is_arr_var x).
1,2: by [].
- rewrite /= /write_var; t_xrbindP => s1a vm /set_varP [_ htr _].
  by move: hxa htr; rewrite /is_arr_var; case: (vtype x) => //= ??; case: v hna {hdef} => //= ty h _; case: ty h.
3: by rewrite /= /write_var; t_xrbindP => s1a vm /set_varP [_ htr _]; move: hxa htr; rewrite /is_arr_var; case: (vtype x).
- rewrite /=; t_xrbindP => s1a hw1 hws.
  have [s2a hw2 [hsa hma hpa]] := prog_eq_write_lval (lv := Lvar x) hp hscs hmem hXx hw1.
  have hinva : mask_inv (Sv.add x X) (evm s1a) (evm s2a).
  + apply: (mask_inv_prog_l (W := Sv.singleton x)); first by apply: no_maskI hXx; rewrite /vars_lval /=; SvD.fsetdec.
    * exact: vrvP_var hw1.
    move: hw2; rewrite /= /write_var; t_xrbindP => vm hs ?; subst s2a.
    by apply: (mask_inv_set_var_r hinv _ hdef hs); move: hxa; rewrite /is_arr_var => ->.
  have [s2' hws2 [? ? [? hinv']]] := ih _ _ _ _ _ (And3 hsa hma (conj hpa hinva)) hXs hv hws.
  exists s2'; first by move: hw2 => /= ->.
  by split => //; split => //; apply: mask_inv_eq hinv' => ? _; SvD.fsetdec.
rewrite /=; t_xrbindP => s1a hw1 /=; t_xrbindP => s1b hwm hws.
have [s2a hw2 [hsa hma hpa]] := prog_eq_write_lval (lv := Lvar x) hp hscs hmem hXx hw1.
move: hwm; rewrite /write_var; t_xrbindP => vm1 hsm ?; subst s1b.
have hinva : mask_inv X vm1 (evm s2a).
- move: hw2; rewrite /= /write_var; t_xrbindP => vm hs ?; subst s2a => /=.
  apply: (@mask_inv_set_var X x (Varr tm) (Varr t) (evm s1a) vm1 (evm s2) vm _ _ htm hsm hs).
  + apply: (mask_inv_prog_l (W := Sv.singleton x)); first by apply: no_maskI hXx; rewrite /vars_lval /=; SvD.fsetdec.
    * exact: vrvP_var hw1.
    exact: hinv.
  by move: hxa; rewrite /is_arr_var => ->.
have hpb : prog_eq vm1 (evm s2a) by apply: (prog_eq_set_mask hsm).
have [s2' hws2 [? ? [? hinv']]] := ih _ _ _ (with_vm s1a vm1) _ (And3 hsa hma (conj hpb hinva)) hXs hv hws.
exists s2'; first by move: hw2; rewrite /= /write_var => -> /=.
split => //; split => //; apply: mask_inv_eq hinv' => y hy.
have hne : y <> v_var x by move=> ?; subst y; move: hy hxa; rewrite /is_arr_var => /negbTE ->.
SvD.fsetdec.
Qed.
Lemma opn_caseP ii lvs tg o es s0 s1' s2 :
  no_mask (vars_I (MkI ii (Copn lvs tg o es))) ->
  (ssrnat.leq 2 (size lvs) -> all is_var_lv lvs) -> mask_st s0 s2 ->
  esem (sm := total_init) pm ev (explicit_init_i mask (MkI ii (Copn lvs tg o es))) s0 = ok s1' ->
  exists2 s2', esem (sm := total) p ev [:: MkI ii (Copn lvs tg o es)] s2 = ok s2' & mask_st s1' s2'.
Proof using asm_op_tout explicit_init_ok mask_inj mask_type.
move=> hX hvar; have hbh : all is_var_lv (behead lvs).
- by case: (lvs) hvar => [ | lv [ | lv' lvs']] //= /(_ isT) /andP [].
move: hX hvar hbh; case: o => [po | so | ao].
3: by move=> hX _ hbh hst /= hs; apply: (opnP hX hbh _ hst hs) => vs vs2 _ /(exec_sopn_not_carr (o := Oasm ao) (asm_op_tout ao)).
2: case: so => [ | | | ws | ws len | ws len].
2-5: by move=> hX _ hbh hst /= hs; apply: (opnP hX hbh _ hst hs) => vs vs2 _ hex _; apply: (exec_sopn_not_carr _ hex).
2,3: case: lvs => [ | lv [ | lv' lvs]]; case: es => [ | e [ | e' [ | e'' es]]].
8: by move=> hX _ _ hst; apply: (protectP (or_introl erefl) hX hst).
19: by move=> hX _ _ hst; apply: (protectP (or_intror erefl) hX hst).
2-23: by move=> hX _ hbh hst /= hs; apply: (opnP hX hbh _ hst hs) => vs vs2 hsz hex hsz2; have := exec_sopn_size hex; have := exec_sopn_tout_size hex; rewrite hsz hsz2.
case: po => [sop tys | ws len | ty | len | | ws | ws | ws | ty].
1,3-8: by move=> hX _ hbh hst /= hs; apply: (opnP hX hbh _ hst hs) => vs vs2 _ hex _; apply: (exec_sopn_not_carr _ hex).
- case: lvs => [ | lv [ | lv' lvs]]; case: es => [ | e [ | e' es]].
  5: by move=> hX _ _ hst; apply: copyP hX hst.
  1-8: by move=> hX _ hbh hst hs; apply: (opnP hX hbh _ hst hs) => vs vs2 hsz hex hsz2; have := exec_sopn_size hex; have := exec_sopn_tout_size hex; rewrite hsz hsz2.
case: ty => [ | | ws len | ws].
1,2,4: by move=> hX _ hbh hst hs; apply: (opnP hX hbh _ hst hs) => vs vs2 _ hex _; apply: (exec_sopn_not_carr _ hex).
by move=> hX hvar _ hst hs; apply: (swapP hX hvar hst hs).
Qed.

Lemma syscall_caseP ii lvs o es s0 s1' s2 :
  no_mask (vars_I (MkI ii (Csyscall lvs o es))) -> all is_var_lv lvs -> mask_st s0 s2 ->
  esem (sm := total_init) pm ev (explicit_init_i mask (MkI ii (Csyscall lvs o es))) s0 = ok s1' ->
  exists2 s2', esem (sm := total) p ev [:: MkI ii (Csyscall lvs o es)] s2 = ok s2' & mask_st s1' s2'.
Proof using mask_inj mask_type.
case: o => ws len hX hvar hst hs.
case: lvs hX hvar hs => [ | lv [ | lv' lvs]] hX hvar hs.
- by apply: (syscall_otherP _ hvar hX hst) => //; exact hs.
- case: lv hX hvar hs => [ ?? | x | ???? | ????? | ?????] hX hvar hs; try by apply: (syscall_otherP _ hvar hX hst) => //; exact hs.
  by apply: (syscall_arrP hX hst hs).
by case: lv hX hvar hs => [ ?? | x | ???? | ????? | ?????] hX hvar hs;
  apply: (syscall_otherP _ hvar hX hst) => //; exact hs.
Qed.

(* A result of a call that is not an array, written alike on both sides: the
   mask of a scalar is written after the call. *)
Lemma same_write_step X lv v a a1 c :
  mask_st_ex X a c -> no_mask (vars_lval lv) -> is_defined v ->
  (if lv is Lvar x then ~~ is_arr_var x else if lv is Lnone _ _ then true else false) ->
  write_lval (sm := total) true gd lv v a = ok a1 ->
  exists2 c1, write_lval (sm := total) true gd lv v c = ok c1 & mask_st_ex (Sv.union (vrv lv) X) a1 c1.
Proof using mask_inj mask_type.
move=> [hscs hmem [hp hinv]] hX hdef hlv hw.
have [c1 hw2 [hsa hma hpa]] := prog_eq_write_lval hp hscs hmem hX hw.
exists c1 => //; split => //; split => //.
have hXv : no_mask (vrv lv) by apply: no_maskI hX; rewrite /vars_lval; SvD.fsetdec.
have {}hinv := mask_inv_prog_l hXv (vrvP hw) hinv.
case: lv hlv hw2 {hX hXv hw hpa} => //= [vi ty | x] hlv hw2.
- by rewrite (write_lval_novar (lv := Lnone vi ty) _ hw2) //; apply: mask_inv_eq hinv => ? _; SvD.fsetdec.
move: hw2; rewrite /write_var; t_xrbindP => vm hs <- /=.
by apply: mask_inv_eq (mask_inv_set_var_r hinv hlv hdef hs) => ? _; SvD.fsetdec.
Qed.



(* An array result of a call followed by its mask. *)
Lemma mask_write_step X (x : var_i) len (t tm : WArray.array len) a a1 a2 c :
  mask_st_ex X a c -> ~ is_mask x -> arr_mask_of t tm ->
  write_var true x (Varr t) a = ok a1 ->
  write_var true (mask_v x) (Varr tm) a1 = ok a2 ->
  exists2 c1, write_var true x (Varr t) c = ok c1 & mask_st_ex X a2 c1.
Proof using mask_inj mask_type.
move=> [hscs hmem [hp hinv]] hx htm.
rewrite /write_var; t_xrbindP => vm0 hs0 <- vm1 hs1 <-.
have [vm2 hs2] : exists vm2, set_var true (evm c) x (Varr t) = ok vm2.
- by move: hs0 => /set_varP [hdb htr _]; rewrite (set_var_truncate hdb htr); eexists.
rewrite hs2 /=; eexists; first reflexivity.
split => //; split.
- move=> y hy; rewrite -(get_total_eq_ex (set_var_eq_ex hs1)); last first.
  + by move=> /SvD.F.singleton_iff ?; apply: hy; exists x.
  case: (v_var x =P y) => [<- | hne].
  + move: hs0 hs2 => /set_varP [_ _ ->] /set_varP [_ _ ->] /=.
    by rewrite [LHS]Vm.get_modeE [RHS]Vm.get_modeE !Vm.setP_eq.
  rewrite -(get_total_eq_ex (set_var_eq_ex hs0)); last by move=> /SvD.F.singleton_iff.
  by rewrite -(get_total_eq_ex (set_var_eq_ex hs2)); [apply: hp | move=> /SvD.F.singleton_iff].
move: hs1 => /= hs1 /=.
apply: (mask_inv_set_var (m := Varr tm) (v := Varr t) _ _ _ hs1 hs2).
- apply: (mask_inv_prog_l (W := Sv.singleton x) _ (set_var_eq_ex hs0) hinv).
  by move=> y /SvD.F.singleton_iff <-.
- by rewrite /is_arr_var => hxa; move: hs2 => /set_varP [_ + _]; case: (vtype x) hxa.
exact: htm.
Qed.

(* The results of a call, which are variables: an array is followed by its
   mask; the masks of the scalars are written after the call. *)
Lemma call_lvsP X lvs vs1 vs2 a a' c :
  mask_st_ex X a c -> no_mask (vars_lvals lvs) -> all is_var_lv lvs -> mask_vals vs1 vs2 ->
  write_lvals (sm := total) true gd a (List.flat_map (with_mask_lv mask) lvs) vs1 = ok a' ->
  exists2 c', write_lvals (sm := total) true gd c lvs vs2 = ok c' &
    mask_st_ex (Sv.union (vrvs lvs) X) a' c'.
Proof using mask_inj mask_type.
elim: lvs vs1 vs2 X a c => [ | lv lvs ih] vs1 vs2 X a c hst hX /= hvar hv.
- case: hv => //=; move=> [<-]; exists c => //.
have hXl : no_mask (vars_lval lv) by apply: no_maskI hX; rewrite /vars_lvals /vars_lval /= vrvs_cons read_rvs_cons; SvD.fsetdec.
have {hX} hXs : no_mask (vars_lvals lvs) by apply: no_maskI hX; rewrite /vars_lvals /vars_lval /= vrvs_cons read_rvs_cons; SvD.fsetdec.
move: hvar => /andP [hlv hvar].
have hU : forall Y a0 c0, (forall y, ~~ is_arr_var y -> Sv.In y Y -> Sv.In y (Sv.union (vrv lv) X)) ->
    (forall y, ~~ is_arr_var y -> Sv.In y (Sv.union (vrv lv) X) -> Sv.In y Y) ->
    mask_st_ex (Sv.union (vrvs lvs) Y) a0 c0 -> mask_st_ex (Sv.union (vrvs (lv :: lvs)) X) a0 c0.
- move=> Y a0 c0 h1 h2 [? ? [? hinv]]; split => //; split => //; apply: mask_inv_eq hinv => y hy.
  by have := h1 y hy; have := h2 y hy; rewrite vrvs_cons; SvD.fsetdec.
case: hv => [ | v vs1' vs2' hna hdef hv | len t tm vs1' vs2' htm hv].
- by case: (lv) => //= [? [] | x] //; case: is_arr_var.
- have hstep : (if lv is Lvar x then ~~ is_arr_var x else if lv is Lnone _ _ then true else false) ->
    with_mask_lv mask lv = [:: lv] ->
    write_lvals (sm := total) true gd a (with_mask_lv mask lv ++ List.flat_map (with_mask_lv mask) lvs) (v :: vs1') = ok a' ->
    exists2 c', (Let x := write_lval (sm := total) true gd lv v c in write_lvals (sm := total) true gd x lvs vs2') = ok c' &
      mask_st_ex (Sv.union (vrvs (lv :: lvs)) X) a' c'.
  + move=> hl -> /=; t_xrbindP => a1 hw1 hws.
    have [c1 hw2 hst1] := same_write_step hst hXl hdef hl hw1.
    have [c2 hws2 hst2] := ih _ _ _ _ _ hst1 hXs hvar hv hws.
    by exists c2; [rewrite hw2 | apply: hU hst2 => ? _; SvD.fsetdec].
  case: lv hlv hXl hU hstep => //= [vi ty | x] _ hXl hU hstep.
  + case: ty hXl hU hstep => [ | | ws len | ws] hXl hU hstep; try by apply: hstep.
    move=> /=; t_xrbindP => a1 hw1 _.
    by have := write_none_nonarr (sm := total) (spp := spp) (gd := gd) (vi := vi) (ty := aarr ws len) hna hw1.
  case hx: (is_arr_var x) hstep => hstep.
  + move=> /=; t_xrbindP => a1 hw1 _.
    have := write_lval_nonarr (sm := total) (spp := spp) (gd := gd) (lv := Lvar x) hna hw1.
    by rewrite /= hx.
  by apply: hstep => //=; rewrite hx.
case: lv hlv hXl hU => //= [vi ty | x] _ hXl hU.
- case: ty hXl hU => [ | | ws len' | ws] hXl hU //=; t_xrbindP.
  move=> a1 hw1 a2 hw2 hws.
  have [? htr1 hdb1] := write_noneP hw1; have [? _ _] := write_noneP hw2; subst a1 a2.
  have [c2 hws2 hst2] := ih _ _ _ _ _ hst hXs hvar hv hws.
  exists c2; last by apply: hU hst2 => ? _; SvD.fsetdec.
  by rewrite /write_none htr1 hdb1 /=.
case hx: (is_arr_var x) => /=; t_xrbindP; last first.
- move=> a1 hw1 _.
  have := write_lval_arr (sm := total) (spp := spp) (gd := gd) (lv := Lvar x) (v := Varr t) erefl hw1.
  by rewrite /= hx.
move=> a1 hw1 a2 hwm hws.
have hxm : ~ is_mask x by apply: hXl; rewrite /vars_lval /=; SvD.fsetdec.
have [c1 hw2 hst1] := mask_write_step hst hxm htm hw1 hwm.
have [c2 hws2 hst2] := ih _ _ _ _ _ hst1 hXs hvar hv hws.
exists c2; first by rewrite /= hw2.
apply: hU hst2 => y hy; have hne : y <> v_var x by move=> ?; subst y; move: hy hx; rewrite /is_arr_var => /negbTE ->.
- by SvD.fsetdec.
by SvD.fsetdec.
Qed.
(* The arguments of a call: an array is followed by its mask. *)
Lemma with_mask_esP X s1 s2 es vs1 :
  mask_st_ex X s1 s2 -> no_mask (read_es es) ->
  sem_pexprs (sm := total) true gd s1 (List.flat_map (with_mask_e mask) es) = ok vs1 ->
  exists2 vs2, sem_pexprs (sm := total) true gd s2 es = ok vs2 & mask_vals vs1 vs2.
Proof using explicit_init_ok mask_type.
move=> hst; elim: es vs1 => [ | e es ih] vs1 hX /=.
- by move=> [<-]; exists [::] => //; constructor.
have hXe : no_mask (read_e e) by apply: no_maskI hX; rewrite read_es_cons; SvD.fsetdec.
have {hX} hXs : no_mask (read_es es) by apply: no_maskI hX; rewrite read_es_cons; SvD.fsetdec.
have hee : sem_pexpr (sm := total) true gd s2 e = sem_pexpr (sm := total) true gd s1 e.
- by case: hst => _ hmem [hp _]; symmetry; apply: prog_eq_sem_pexpr.
rewrite /with_mask_e hee; case ha: (is_arr_expr e) => /=; t_xrbindP.
- move=> v hv _ m hm vs hvs <- <-.
  have [vs2 hvs2 hmv] := ih _ hXs hvs.
  have [_ _ hvm0] := hst.
  have hvm := mask_ofP hXe (fun x hx => mask_vm_self hvm0 hx) hv hm.
  have [len [t ?]] : exists len (t : WArray.array len), v = Varr t.
  + have := sem_pexpr_defined hv; have := sem_pexpr_arr ha hv.
    by case: v {hv hvm} => // len t _ _; exists len, t.
  subst v; have /type_of_valI /= [tm ?] := mask_of_type ha hv hm; subst m.
  by exists (Varr t :: vs2); [rewrite hv hvs2 | constructor].
move=> v hv vs hvs <-; have [vs2 hvs2 hmv] := ih _ hXs hvs.
exists (v :: vs2); first by rewrite hv hvs2.
by constructor => //; [apply: (sem_pexpr_not_arr (negbT ha) hv) | apply: sem_pexpr_defined hv].
Qed.

(* The masks of the scalar results of a call, written after it: the results
   are defined. *)
Lemma res_masksP X ii lvs a a' c :
  mask_st_ex X a c -> all is_var_lv lvs ->
  (forall y, ~~ is_arr_var y -> Sv.In y X -> Sv.In y (vrvs lvs)) ->
  (forall y, ~~ is_arr_var y -> Sv.In y (vrvs lvs) -> is_defined (evm c).[y]) ->
  esem (sm := total_init) pm ev
    (List.flat_map (fun lv => explicit_init_out mask ii lv (Pbool true)) lvs) a = ok a' ->
  mask_st a' c.
Proof using mask_inj mask_type.
elim: lvs X a => [ | lv lvs ih] X a hst /=.
- move=> _ hX _ [<-]; case: hst => ? ? [? hinv]; split => //; split => //.
  by apply: mask_inv_eq hinv => y hy; split => [/(hX _ hy) | ]; rewrite /vrvs /= => /SvD.F.empty_iff.
move=> /andP [hlv hvar] hX hdef; rewrite esem_cat; t_xrbindP => a1 ha1.
have hdef' : forall y, ~~ is_arr_var y -> Sv.In y (vrvs lvs) -> is_defined (evm c).[y].
- by move=> y hy hin; apply: hdef => //; rewrite vrvs_cons; SvD.fsetdec.
case: lv hlv hX hdef ha1 => //= [vi ty | x] _ hX hdef.
- move=> [<-]; apply: ih hst hvar _ hdef' => y hy /(hX _ hy).
  by rewrite vrvs_cons /=; SvD.fsetdec.
case hx: is_arr_var.
- move=> [<-]; apply: ih hst hvar _ hdef' => y hy /(hX _ hy).
  rewrite vrvs_cons /=; have : y <> v_var x by move=> ?; subst y; move: hy hx; rewrite /is_arr_var => /negbTE ->.
  by SvD.fsetdec.
rewrite esem_assgn1 /sem_assgn; t_xrbindP => mv [<-] mv' /= [<-] hw.
move: hw; rewrite /write_var; t_xrbindP => vm hsv <-.
apply: (ih (Sv.remove x X)) hvar _ hdef'.
- case: hst => hscs hmem [hp hinv]; split => //; split.
  + exact: (prog_eq_set_mask hsv hp).
  apply: (mask_inv_set_mask_l hinv _ hsv).
  have hxs : ~~ is_arr_var x by rewrite hx.
  by rewrite (negbTE hxs) hdef // vrvs_cons /=; SvD.fsetdec.
move=> y hy /SvD.F.remove_iff [/(hX _ hy)]; rewrite vrvs_cons /=; SvD.fsetdec.
Qed.
(* A variable never written is undefined, or an array with no initialised cell,
   and so is its mask. *)
Lemma mask_vm_init : mask_vm Sv.empty Vm.init Vm.init.
Proof using mask_type.
split => //; split => x.
- move=> hx; rewrite SvD.F.empty_b (Vm.get_modeE (sm := total) Vm.init (mask x)) Vm.initP mask_type (negbTE hx) /=.
  by rewrite Vm.initP; move: hx; rewrite /is_arr_var; case: (vtype x).
move=> i; rewrite (Vm.get_modeE (sm := total) Vm.init (mask x)) !Vm.initP mask_type.
by rewrite /is_arr_var; case: (vtype x).
Qed.

(* The checks of a contract. *)
Lemma contract_checkE fn fd ci :
  get_fundef (p_funcs p) fn = Some fd -> f_contract fd = Some ci ->
  [/\ Sv.Subset (read_easserts [seq a.2 | a <- f_pre ci]) (vars_l (f_iparams ci)),
      Sv.Subset (read_easserts [seq a.2 | a <- f_post ci])
                (Sv.union (vars_l (f_iparams ci)) (vars_l (f_ires ci))),
      all (check_arr_init gd) [seq a.2 | a <- f_pre ci] &
      all (check_arr_init gd) [seq a.2 | a <- f_post ci]].
Proof using explicit_init_ok.
move=> hfd hci; have [_ _ h] := explicit_init_okE.
move: (h _ _ hfd); rewrite /check_fd hci /= /check_ci; t_xrbindP.
move=> _ /Sv.subset_spec h1 /Sv.subset_spec h2.
by rewrite all_cat => /andP [].
Qed.


Lemma contract_no_mask fn fd ci :
  get_fundef (p_funcs p) fn = Some fd -> f_contract fd = Some ci ->
  [/\ no_mask (vars_l (f_iparams ci)), no_mask (vars_l (f_ires ci)),
      no_mask (read_easserts [seq a.2 | a <- f_pre ci])
    & no_mask (read_easserts [seq a.2 | a <- f_post ci])].
Proof using ep explicit_init_ok mask_fresh_contract spp.
move=> hfd hci; have [h1 h2 _ _] := contract_checkE hfd hci.
have h : no_mask (vars_l (f_iparams ci ++ f_ires ci)).
- by move=> y hy [x hx]; apply: (mask_fresh_contract hfd hci hy hx).
by split; apply: no_maskI h; rewrite vars_l_cat; SvD.fsetdec.
Qed.

(* The assertions of a contract: the variables they read are bound by the
   contract, hence initialised. *)
Lemma contract_assertsP X s1 s2 (asrts : seq assertion) us :
  mask_st_ex X s1 s2 -> no_mask (read_easserts [seq a.2 | a <- asrts]) ->
  all (check_arr_init gd) [seq a.2 | a <- asrts] ->
  (forall x : var_i, Sv.In x (read_easserts [seq a.2 | a <- asrts]) -> is_var_init (evm s2) x) ->
  mapM (sem_assert gd s1) [seq (a.1, explicit_init_contract_a mask a.2) | a <- asrts] = ok us ->
  exists us', mapM (sem_assert gd s2) asrts = ok us'.
Proof using assert_allowed_wa explicit_init_ok mask_type.
move=> hst + + hdef; elim: asrts us hdef => [ | a asrts ih] us hdef /=; first by exists [::].
move=> hX /andP [hc1 hc]; t_xrbindP => ha us1 hus1 _.
have hX1 : no_mask (read_eassert a.2) by apply: no_maskI hX; rewrite read_easserts_cons; SvD.fsetdec.
have {hX} hX2 : no_mask (read_easserts [seq a.2 | a <- asrts]) by apply: no_maskI hX; rewrite read_easserts_cons; SvD.fsetdec.
have hd1 : forall x : var_i, Sv.In x (read_eassert a.2) -> is_var_init (evm s2) x.
- by move=> x hx; apply: hdef; rewrite /= read_easserts_cons; SvD.fsetdec.
have hd2 : forall x : var_i, Sv.In x (read_easserts [seq a.2 | a <- asrts]) -> is_var_init (evm s2) x.
- by move=> x hx; apply: hdef; rewrite /= read_easserts_cons; SvD.fsetdec.
have [us' hus'] := ih us1 hd2 hX2 hc hus1.
move: ha; rewrite /sem_assert /=; t_xrbindP.
move=> _ [] // hb _ _.
rewrite assert_allowed_wa (explicit_init_aP hst hX1 hc1 _ hb) /=.
- by move: hus'; rewrite /sem_assert /= assert_allowed_wa /= => ->; eexists.
by move=> x hx _; apply: hd1.
Qed.

(* The variables of [X] are initialised. *)
Lemma mask_inv_var_init X vm1 vm2 (x : var) :
  mask_inv X vm1 vm2 -> Sv.In x X -> is_var_init vm2 x.
Proof.
move=> [hsc _] hx; rewrite /is_var_init.
case ha: (is_arr_var x); first by apply: arr_defined; rewrite ha.
by move/Sv_memP: hx => hx; have := hsc x; rewrite ha hx => /(_ isT).
Qed.

(* The precondition: the parameters of the contract are bound to the
   arguments, its arrays followed by their masks. *)
Lemma explicit_init_preP fn fs1 fs2 :
  mask_fs fs1 fs2 -> sem_pre pm fn fs1 = ok tt -> sem_pre p fn fs2 = ok tt.
Proof using assert_allowed_wa explicit_init_ok mask_fresh_contract mask_inj mask_type.
move=> [hscs hmem hv]; rewrite /sem_pre get_map_prog /=.
case: contracts_checked => //=.
case hfd: get_fundef => [fd | ] //=.
case: fd hfd => fii [ci | ] tin params c tout res fev hfd //=.
have [hXi _ hXpre _] := contract_no_mask hfd erefl.
have [hrd _ hc _] := contract_checkE hfd erefl.
t_xrbindP => vargs htr s1 hw us hpre _.
have [vargs2 -> hv2] := truncate_mask_vals htr hv => /=.
have hst0 : mask_st {| escs := fscs fs1; emem := fmem fs1; evm := Vm.init |}
                    {| escs := fscs fs2; emem := fmem fs2; evm := Vm.init |}.
- by split => //=; apply: mask_vm_init.
have [s2 -> hst] := write_vars_mask hst0 hXi hv2 hw.
have hb : forall x : var_i, Sv.In x (read_easserts [seq a.2 | a <- f_pre ci]) -> is_var_init (evm s2) x.
- by move=> x hx; case: hst => _ _ [_ hinv]; apply: (mask_inv_var_init hinv); move: hx => /hrd; SvD.fsetdec.
by have [us' /= ->] := contract_assertsP hst hXpre hc hb hpre.
Qed.

(* The postcondition: the parameters and the results of the contract are
   bound, its arrays followed by their masks. *)
Lemma explicit_init_postP fn vargs1 vargs2 fr1 fr2 :
  mask_vals vargs1 vargs2 -> mask_fs fr1 fr2 ->
  sem_post pm fn vargs1 fr1 = ok tt -> sem_post p fn vargs2 fr2 = ok tt.
Proof using assert_allowed_wa explicit_init_ok mask_fresh_contract mask_inj mask_type.
move=> hv [hscs hmem hr]; rewrite /sem_post get_map_prog /=.
case: contracts_checked => //=.
case hfd: get_fundef => [fd | ] //=.
case: fd hfd => fii [ci | ] tin params c tout res fev hfd //=.
have [hXi hXr _ hXpost] := contract_no_mask hfd erefl.
have [_ hrd _ hc] := contract_checkE hfd erefl.
t_xrbindP => vargs htr s1 hw s1' hw' us hpost _.
have [vargs2' -> hv2] := truncate_mask_vals htr hv => /=.
have hst0 : mask_st {| escs := fscs fr1; emem := fmem fr1; evm := Vm.init |}
                    {| escs := fscs fr2; emem := fmem fr2; evm := Vm.init |}.
- by split => //=; apply: mask_vm_init.
have [s2 -> hst] := write_vars_mask hst0 hXi hv2 hw.
rewrite /=; have [s2' -> hst'] := write_vars_mask hst hXr hr hw' => /=.
have hb : forall x : var_i, Sv.In x (read_easserts [seq a.2 | a <- f_post ci]) -> is_var_init (evm s2') x.
- by move=> x hx; case: hst' => _ _ [_ hinv]; apply: (mask_inv_var_init hinv); move: hx => /hrd; SvD.fsetdec.
by have [us' /= ->] := contract_assertsP hst' hXpost hc hb hpost.
Qed.

(* The results of a function: an array is followed by its mask. *)
Lemma get_var_is_mask X xs vm1 vm2 vs1 :
  mask_vm X vm1 vm2 -> no_mask (vars_l xs) ->
  get_var_is (sm := total) true vm1 (List.flat_map (with_mask_x mask) xs) = ok vs1 ->
  exists2 vs2, get_var_is (sm := total) true vm2 xs = ok vs2 & mask_vals vs1 vs2.
Proof using ep mask_type spp syscall_state.
move=> hvm; elim: xs vs1 => [ | x xs ih] vs1 /= hX.
- by move=> [<-]; exists [::] => //; constructor.
have hXx : ~ is_mask x by apply: hX; SvD.fsetdec.
have {hX} hXs : no_mask (vars_l xs) by apply: no_maskI hX; SvD.fsetdec.
have hgx : get_var (sm := total) true vm2 x = get_var (sm := total) true vm1 x by rewrite /get_var (hvm.1 _ hXx).
rewrite hgx /with_mask_x; case ha: (is_arr_var x) => /=; t_xrbindP.
- move=> v hv _ m hm vs hvs <- <-; have [vs2 hvs2 hmv] := ih _ hXs hvs.
  move: hv hm; rewrite /get_var; t_xrbindP => _ <- _ <-.
  have hmo := mask_vm_self hvm hXx.
  move: (Vm.getP_mode (sm := total) vm1 x) (Vm.getP_mode (sm := total) vm1 (mask x)) hmo.
  rewrite mask_type; move: ha; rewrite /is_arr_var; case: (vtype x) => //= ws len _.
  move=> /compat_valEl [t ->] /compat_valEl [tm ->] hmo /=.
  by exists (Varr t :: vs2); [rewrite hvs2 | constructor].
move=> v hv vs hvs <-; have [vs2 hvs2 hmv] := ih _ hXs hvs.
exists (v :: vs2); first by rewrite hv hvs2.
move: hv; rewrite /get_var; t_xrbindP => hd hv; subst v.
constructor => //.
move: (Vm.getP_mode (sm := total) vm1 x) ha; rewrite /is_arr_var.
case: (vm1.[x]) => [b | z | len t | ws w | ty h] /compat_valE //=; case: (vtype x) => //.
all: by case: ty h.
Qed.

Lemma finalize_maskP X (fd : ufundef) s1 s2 fr1 :
  mask_st_ex X s1 s2 -> no_mask (vars_l (f_res fd)) ->
  finalize_funcall (sm := total_init) (explicit_init_fd mask fd) s1 = ok fr1 ->
  exists2 fr2, finalize_funcall (sm := total) fd s2 = ok fr2 & mask_fs fr1 fr2.
Proof using mask_type spp.
case: fd => fii ci tin params c tout res fev [hscs hmem hvm] /= hX.
rewrite /finalize_funcall /=; t_xrbindP => vs1 hvs vs1' htr <-.
have {}hvs : get_var_is (sm := total) true (evm s1) (List.flat_map (with_mask_x mask) res) = ok vs1.
- by rewrite -hvs /get_var_is; apply: mapM_ext => x _; apply: get_var_is_totalE.
have [vs2 -> hv2] := get_var_is_mask hvm hX hvs.
rewrite /=.
have [vs2' -> hv2'] := truncate_mask_vals htr hv2.
by eexists.
Qed.

Lemma initialize_maskP (fd : ufundef) fs1 fs2 s1 :
  mask_fs fs1 fs2 -> no_mask (vars_l (f_params fd)) ->
  initialize_funcall pm ev (explicit_init_fd mask fd) fs1 = ok s1 ->
  exists2 s2, initialize_funcall p ev fd fs2 = ok s2 &
    mask_st_ex (vars_l (f_params fd)) s1 s2 /\
    (forall x, ~ Sv.In x (vars_l (f_params fd)) -> (evm s2).[x] = Vm.init.[x]).
Proof using mask_inj mask_type spp.
case: fd => fii ci tin params c tout res fev [hscs hmem hv] /= hX.
rewrite /initialize_funcall /=; t_xrbindP.
move=> vs1 htr hw; have [vs2 -> hv2] := truncate_mask_vals htr hv => /=.
have hst0 : mask_st (estate0 fs1) (estate0 fs2) by split => //=; apply: mask_vm_init.
have [s2 hw2 [? ? [? hinv]]] := write_vars_mask hst0 hX hv2 hw.
exists s2; first by rewrite hw2.
split; first by split => //; split => //; apply: mask_inv_eq hinv => ? _; SvD.fsetdec.
move=> x hx; rewrite -(write_vars_eq_ex hw2) //.
move=> /sv_of_listP; elim: (params) hx => //= y ys ih hx.
rewrite in_cons => /orP [/eqP ? | ]; first by subst x; apply: hx; SvD.fsetdec.
by apply: ih => h; apply: hx; SvD.fsetdec.
Qed.

(* The masks written on entry: a scalar parameter is defined; any other
   variable is undefined, or an array with no initialised cell. *)
Lemma init_masksP X ii (fd : ufundef) s1 s1' s2 :
  mask_st_ex X s1 s2 ->
  (forall x, ~~ is_arr_var x -> Sv.In x X -> x \in Sv.elements (vars_fd fd)) ->
  (forall x, ~~ is_arr_var x -> Sv.In x (vars_l (f_params fd)) -> is_defined (evm s2).[x]) ->
  (forall x, ~ Sv.In x (vars_l (f_params fd)) -> (evm s2).[x] = Vm.init.[x]) ->
  esem (sm := total_init) pm ev (init_masks mask ii fd) s1 = ok s1' -> mask_st s1' s2.
Proof using mask_inj mask_type.
move=> + + hdef hinit; rewrite /init_masks.
elim: (Sv.elements (vars_fd fd)) X s1 => [ | x xs ih] X s1 hst hX /=.
- move=> [<-]; case: hst => ? ? [? hinv]; split => //; split => //.
  by apply: mask_inv_eq hinv => y hy; split => [h | /SvD.F.empty_iff []]; have := hX _ hy h.
rewrite esem_cat; t_xrbindP => s1a ha.
case: hst => hscs hmem [hp hinv].
apply: (ih (Sv.remove x X)); last first.
- move=> y hy /SvD.F.remove_iff [/(hX _ hy)]; rewrite in_cons => /orP [/eqP -> | //].
  by move=> /(_ erefl).
case hx: (vtype x) ha => [ | | ws len | ws]; last 2 first.
- case: Sv_memP => hin.
  + move=> [<-]; split => //; split => //; apply: mask_inv_eq hinv => y hy.
    have : x <> y by move=> ?; subst y; rewrite /is_arr_var hx in hy.
    by SvD.fsetdec.
  rewrite esem_assgn1 /sem_assgn; t_xrbindP => m hm m' htr.
  rewrite (sem_pexpr_is_totalE gd (sm2 := total)) // in hm.
  rewrite /= /write_var; t_xrbindP => vm hsv <-; split => //; split; first exact: (prog_eq_set_mask hsv hp).
  apply: (mask_inv_set_mask_l hinv _ hsv); rewrite /is_arr_var hx /= hinit // => i.
  case/truncate_val_typeE: htr => ? ? ->; subst m; rewrite (sem_eempty hm) Vm.initP hx.
  by rewrite /WArray.is_init /=.
all: rewrite esem_assgn1 /sem_assgn; t_xrbindP => m [<-] m' /= [<-].
all: rewrite /= /write_var; t_xrbindP => vm hsv <-; split => //; split; first exact: (prog_eq_set_mask hsv hp).
all: apply: (mask_inv_set_mask_l hinv _ hsv); rewrite /is_arr_var hx /=.
all: case: Sv_memP => hin; first by rewrite hdef // /is_arr_var hx.
all: by rewrite hinit // Vm.initP hx.
Qed.

(* The counter of a loop: a defined integer, written alike on both sides; its
   mask is written at the start of the body. *)
Lemma for_writeP (x : var_i) i s1 s2 s1' :
  mask_st s1 s2 -> ~ is_mask x -> write_var true x (Vint i) s1 = ok s1' ->
  exists2 s2', write_var true x (Vint i) s2 = ok s2' &
    mask_st_ex (Sv.add x Sv.empty) s1' s2'.
Proof using asm_op mask_inj mask_type p sip spp.
move=> hst hx hw.
have hX : no_mask (vars_lval (Lvar x)) by move=> y; rewrite /vars_lval /=; move=> hy; have <- : v_var x = y by SvD.fsetdec.
have hna : ~~ is_arr_var x.
- by move: hw; rewrite /write_var /is_arr_var; t_xrbindP => vm /set_varP [_ htr _] _; case: (vtype x) htr.
have [s2' hw2 hst'] := same_write_step (lv := Lvar x) (v := Vint i) hst hX isT hna hw.
by exists s2' => //; case: hst' => ? ? [? hinv]; split => //; split => //; apply: mask_inv_eq hinv => ? _ /=; SvD.fsetdec.
Qed.
Context {E E0 : Type -> Type} {wE : with_Error E E0} {rE : EventRels E0}.

Notation wequiv_m := (wequiv_rec (sm1 := total_init) (sm2 := total) pm p ev ev mask_spec).

(* The instructions that make no call: their semantics is [esem]. *)
Definition is_simple_i (i : instr) :=
  if i is MkI _ (Cassgn _ _ _ _ | Copn _ _ _ _ | Csyscall _ _ _) then true else false.

Lemma wequiv_esem1 i1 c2 P Q :
  is_simple_i i1 ->
  wrequiv P (esem (sm := total_init) pm ev [:: i1]) (esem (sm := total) p ev c2) Q ->
  wequiv_m P [:: i1] c2 Q.
Proof.
case: i1 => ii [] //= => [lv tg ty e | lvs tg o es | lvs o es] _ h.
- apply wequiv_assgn_esem.
  by move=> s t s' hP hs; apply: (h s t s' hP); rewrite esem1.
- apply wequiv_opn_esem.
  by move=> s t s' hP hs; apply: (h s t s' hP); rewrite esem1.
apply wequiv_syscall_esem.
by move=> s t s' hP hs; apply: (h s t s' hP); rewrite esem1.
Qed.

Lemma wequiv_esem i1 c1 c2 P Q :
  all is_simple_i (i1 :: c1) ->
  wrequiv P (esem (sm := total_init) pm ev (i1 :: c1)) (esem (sm := total) p ev c2) Q ->
  wequiv_m P (i1 :: c1) c2 Q.
Proof.
elim: c1 i1 P => [ | i2 c1 ih] i1 P /=.
- by rewrite andbT; apply: wequiv_esem1.
move=> /andP [hi1 hc] h.
rewrite -cat1s -(cat0s c2).
apply wequiv_cat with (fun s1' s2 => exists2 s1, P s1 s2 & esem (pT := progUnit) (sm := total_init) pm ev [:: i1] s1 = ok s1').
- apply: wequiv_esem1 => // s1 s2 s1' hP hs1; exists s2 => //.
  by exists s1.
apply: ih => // s1' s2 o [s1 hP hs1] ho; apply: (h s1 s2 o hP).
by rewrite esem_cons -esem1 hs1.
Qed.

(* Instructions of the instrumented program only. *)
Lemma wequiv_esem_l c1 P Q :
  all is_simple_i c1 ->
  (forall s1 s2 s1', P s1 s2 -> esem (pT := progUnit) (sm := total_init) pm ev c1 s1 = ok s1' -> Q s1' s2) ->
  wequiv_m P c1 [::] Q.
Proof.
case: c1 => [ | i1 c1] hall h.
- by apply wequiv_nil => s1 s2 hP; apply: h hP _.
by apply: wequiv_esem => // s1 s2 s1' hP hs; exists s2 => //; apply: h hP hs.
Qed.

Lemma explicit_init_simple i : is_simple_i i -> all is_simple_i (explicit_init_i mask i).
Proof.
case: i => ii [] //= => [lv tg ty e | lvs tg o es | lvs o es] _.
- by rewrite all_cat andbT; case: lv => //= x; case: is_arr_var.
- have hm : forall c, all is_mask_assgn c -> all is_simple_i c by move=> c; apply: sub_all => -[? []].
  have hopn := hm _ (mask_cmd_opn ii lvs (map2 (out_mask es) (tout (get_instr_desc o)) (i_init (get_instr_desc o)))).1.
  repeat match goal with |- context [match ?x with _ => _ end] => destruct x end.
  all: try by rewrite all_cat hopn.
  all: try by [].
repeat match goal with |- context [match ?x with _ => _ end] => destruct x end.
all: by rewrite /set_arr_mask.
Qed.

Lemma explicit_init_cons i : is_simple_i i -> exists i1 c1, explicit_init_i mask i = i1 :: c1.
Proof.
case: i => ii [] //= => [lv tg ty e | lvs tg o es | lvs o es] _.
- by case: explicit_init_assgn => [ | ??] /=; do 2!eexists.
- by repeat match goal with |- context [match ?x with _ => _ end] => destruct x end; rewrite ?cat_cons /=; try case: explicit_init_opn => [ | ??] /=; do 2!eexists.
by repeat match goal with |- context [match ?x with _ => _ end] => destruct x end; do 2!eexists.
Qed.

Lemma simple_instrP i : is_simple_i i -> no_mask (vars_I i) -> check_i gd i = ok tt ->
  wequiv_m mask_st (explicit_init_i mask i) [:: i] mask_st.
Proof using asm_op_tout explicit_init_ok mask_inj mask_type.
move=> hs hX hc; have [i1 [c1 he]] := explicit_init_cons hs.
have hall := explicit_init_simple hs; rewrite he in hall *.
apply: wequiv_esem => // s1 s2 s1' hst; rewrite -he.
case: i hs hX hc {he hall} => ii [] // => [lv tg ty e | lvs tg o es | lvs o es] _ hX /= hc.
- exact: assgnP hX hst.
- apply: opn_caseP hX _ hst => h.
  by move: hc; rewrite h; t_xrbindP.
by apply: syscall_caseP hX _ hst; move: hc; t_xrbindP.
Qed.
(* A call: the arguments carry their masks, the results are variables; the
   masks of its scalar results are written after it. *)
Lemma callP ii lvs fn es :
  no_mask (vars_I (MkI ii (Ccall lvs fn es))) -> all is_var_lv lvs ->
  wequiv_m mask_st (explicit_init_i mask (MkI ii (Ccall lvs fn es))) [:: MkI ii (Ccall lvs fn es)] mask_st.
Proof using assert_allowed_wa explicit_init_ok mask_fresh_contract mask_inj mask_type.
move=> hX hvar.
have hXl : no_mask (vars_lvals lvs) by apply: no_maskI hX; rewrite /vars_I /vars_lvals read_Ii write_Ii read_i_call write_i_call; SvD.fsetdec.
have {hX} hXe : no_mask (read_es es) by apply: no_maskI hX; rewrite /vars_I read_Ii write_Ii read_i_call write_i_call; SvD.fsetdec.
rewrite /= -cat1s -[[:: MkI ii (Ccall lvs fn es)]]cats0.
apply wequiv_cat with (mask_st_ex (Sv.union (vrvs lvs) Sv.empty)).
- apply wequiv_call_wa with (rpreF (eS := mask_spec)) (rpostF (eS := mask_spec)) mask_vals.
  + move=> s1 s2 vs1 hst /=; rewrite (sem_pexprs_is_totalE gd (sm2 := total)) // => h.
    exact: with_mask_esP hst hXe h.
  + by move=> s1 s2 vs1 vs2 [hscs hmem _] hv; apply: explicit_init_preP.
  + by move=> s1 s2 vs1 vs2 [hscs hmem _] hv.
  + by move=> fs1 fs2 fr1 fr2 [_ [_ _ hv]] hr; apply: explicit_init_postP.
  + exact (@wequiv_fun_rec _ _ _ _ progUnit progUnit _ _ _ _ pm p ev ev mask_spec ii ii fn fn).
  move=> fs1 fs2 fr1 fr2 _ [hscs hmem hvr] s1 s2 s1' [_ _ hvm].
  rewrite /upd_estate (write_lvals_is_totalE gd (sm2 := total)) // => hw1.
  have hst : mask_st (with_scs (with_mem s1 (fmem fr1)) (fscs fr1)) (with_scs (with_mem s2 (fmem fr2)) (fscs fr2)).
  + by split.
  exact: (call_lvsP hst hXl hvar hvr hw1).
apply wequiv_esem_l.
- elim: (lvs) => //= lv lvs' ih; rewrite all_cat ih andbT.
  by apply: sub_all (mask_cmd_out ii lv (Pbool true)).1 => -[? []].
move=> s1 s2 s1' hst; apply: (res_masksP hst hvar).
- by move=> y _; SvD.fsetdec.
move=> y _ hy; case: hst => _ _ [_ hinv].
by have := mask_inv_var_init hinv (x := y); apply; SvD.fsetdec.
Qed.
(* An assertion reads the masks in place of the initialisation. *)
Lemma assert_instrP ii lbl a :
  no_mask (vars_I (MkI ii (Cassert (lbl, a)))) -> check_arr_init gd a ->
  wequiv_m mask_st (explicit_init_i mask (MkI ii (Cassert (lbl, a)))) [:: MkI ii (Cassert (lbl, a))] mask_st.
Proof using assert_allowed_wa explicit_init_ok mask_type.
move=> hX hc.
have {hX} hXa : no_mask (read_eassert a) by apply: no_maskI hX; rewrite /vars_I read_Ii write_Ii read_i_assert write_i_assert; SvD.fsetdec.
apply wequiv_assert => _; split => // s1 s2 hst h; split => //.
apply: (explicit_init_aP hst hXa hc _ h) => x _ /=; rewrite /is_var_init.
case ha: (is_arr_var x); first by move=> _; apply: arr_defined; move: ha; rewrite /is_arr_var.
move=> /=; rewrite /get_gvar /= /get_var; t_xrbindP => _ hm.
case: hst => _ _ [_ [hinv _]].
have hxa : ~~ is_arr_var x by rewrite ha.
by have /= := hinv x hxa; rewrite hm => -[<-].
Qed.
Let Pi (i : instr) :=
  no_mask (vars_I i) -> check_i gd i = ok tt -> wequiv_m mask_st (explicit_init_i mask i) [:: i] mask_st.
Let Pr (ir : instr_r) := forall ii, Pi (MkI ii ir).
Let Pc (c : cmd) :=
  no_mask (vars_c c) -> allM (check_i gd) c = ok tt -> wequiv_m mask_st (explicit_init_c mask c) c mask_st.

(* The body of a function. *)
Lemma explicit_init_cP c : Pc c.
Proof using assert_allowed_wa asm_op_tout explicit_init_ok mask_fresh_contract mask_inj mask_type.
apply: (cmd_rect (Pr := Pr) (Pi := Pi) (Pc := Pc)) => //.
- by move=> _ _; apply wequiv_nil.
- move=> i c0 hi hc hX; rewrite /allM /=; t_xrbindP => hci hcc.
  rewrite -cat1s; apply wequiv_cat with mask_st.
  + by apply: hi => //; apply: no_maskI hX; rewrite /vars_c read_c_cons write_c_cons /vars_I; SvD.fsetdec.
  by apply: hc => //; apply: no_maskI hX; rewrite /vars_c read_c_cons write_c_cons; SvD.fsetdec.
1-3: by move=> > ii; apply: simple_instrP.
- by move=> [lbl a] ii hX /= /add_iinfoP /assertP; apply: assert_instrP.
- move=> e c1 c2 hc1 hc2 ii hX; rewrite /= /allM; t_xrbindP => hc1' hc2'.
  have hXe : no_mask (read_e e) by apply: no_maskI hX; rewrite /vars_I read_Ii write_Ii read_i_if write_i_if; SvD.fsetdec.
  have hX1 : no_mask (vars_c c1) by apply: no_maskI hX; rewrite /vars_c /vars_I read_Ii write_Ii read_i_if write_i_if; SvD.fsetdec.
  have {hX} hX2 : no_mask (vars_c c2) by apply: no_maskI hX; rewrite /vars_c /vars_I read_Ii write_Ii read_i_if write_i_if; SvD.fsetdec.
  apply wequiv_if_eq; last by case; [apply: hc1 | apply: hc2].
  move=> s1 s2 v [_ hmem [hp _]] /=; rewrite (prog_eq_sem_pexpr (sm2 := total) _ _ _ hXe hp hmem) //.
  by move=> ->; exists v.
- move=> x dir lo hi c0 hc ii hX /= hcc.
  have hXb : no_mask (read_es [:: lo; hi]) by apply: no_maskI hX; rewrite /vars_I read_Ii write_Ii read_i_for write_i_for !read_es_cons; SvD.fsetdec.
  have hXx : ~ is_mask x by apply: hX; rewrite /vars_I read_Ii write_Ii read_i_for write_i_for; SvD.fsetdec.
  have {hX} hXc : no_mask (vars_c c0) by apply: no_maskI hX; rewrite /vars_c /vars_I read_Ii write_Ii read_i_for write_i_for; SvD.fsetdec.
  apply (wequiv_for_eq (P0 := mask_st) (P := mask_st)
    (Pi := fun s1 s2 => mask_st_ex (Sv.add x Sv.empty) s1 s2 /\ ~~ is_arr_var x)) => //.
  + move=> s1 s2 v [_ hmem [hp _]]; rewrite (prog_eq_sem_pexprs (sm2 := total) _ _ _ hXb hp hmem) //.
    by move=> ->; exists v.
  + move=> i s1 s2 s1' hst hw; have [s2' hw2 hst'] := for_writeP hst hXx hw.
    exists s2' => //; split => //.
    by move: hw; rewrite /write_var /is_arr_var; t_xrbindP => vm /set_varP [_ htr _] _; case: (vtype x) htr.
  rewrite -cat1s -[c0]cat0s; apply wequiv_cat with mask_st; last by apply: hc.
  apply wequiv_esem_l => // s1 s2 s1' [hst hna] hs.
  apply: (res_masksP (ii := ii) (lvs := [:: Lvar x]) hst) => //.
  + move=> y _ hy; case: hst => _ _ [_ hinv]; apply: (mask_inv_var_init hinv).
    by move: hy; rewrite vrvs_cons /= /vrvs /=; SvD.fsetdec.
  by rewrite /= (negbTE hna) /=.
- move=> a c1 e info c2 hc1 hc2 ii hX; rewrite /= /allM; t_xrbindP => hc1' hc2'.
  have hXe : no_mask (read_e e) by apply: no_maskI hX; rewrite /vars_I read_Ii write_Ii read_i_while write_i_while; SvD.fsetdec.
  have hX1 : no_mask (vars_c c1) by apply: no_maskI hX; rewrite /vars_c /vars_I read_Ii write_Ii read_i_while write_i_while; SvD.fsetdec.
  have {hX} hX2 : no_mask (vars_c c2) by apply: no_maskI hX; rewrite /vars_c /vars_I read_Ii write_Ii read_i_while write_i_while; SvD.fsetdec.
  apply wequiv_while_eq; [ | by apply: hc1 | by apply: hc2].
  move=> s1 s2 v [_ hmem [hp _]] /=; rewrite (prog_eq_sem_pexpr (sm2 := total) _ _ _ hXe hp hmem) //.
  by move=> ->; exists v.
by move=> xs f es ii hX hc; apply: (callP hX); move: hc => /= /assertP.
Qed.

(* ------------------------------------------------------------------------- *)
(* Correctness of the pass                                                    *)

(* If the instrumented program runs without failure in the mode [total_init],
   the original program runs in the mode [total] and reaches a related state. *)
Lemma explicit_init_callP fn :
  wiequiv_f (sm1 := total_init) (sm2 := total) p' p ev ev
    (rpreF (eS := mask_spec)) fn fn (rpostF (eS := mask_spec)).
Proof using assert_allowed_wa asm_op_tout explicit_init_ok mask_fresh mask_fresh_contract mask_inj mask_type.
have [-> _ hchk] := explicit_init_okE.
apply wequiv_fun_ind_wa => {}fn _ fs1 fs2 [<- hfs] fd1.
rewrite get_map_prog; case hfd: get_fundef => [fd | ] //= [<-].
exists fd => // hpre; split; first exact: explicit_init_preP hfs hpre.
have hXfd : no_mask (vars_fd fd) := no_maskI (vars_pP hfd) no_mask_vars_p.
move=> s11 hinit.
have hXp : no_mask (vars_l (f_params fd)) by apply: no_maskI hXfd; rewrite /vars_fd; SvD.fsetdec.
have hXr : no_mask (vars_l (f_res fd)) by apply: no_maskI hXfd; rewrite /vars_fd; SvD.fsetdec.
have hXc : no_mask (vars_c (f_body fd)) by apply: no_maskI hXfd; rewrite /vars_fd; SvD.fsetdec.
have hcb : allM (check_i gd) (f_body fd) = ok tt by move: (hchk _ _ hfd); rewrite /check_fd; t_xrbindP.
have [s21 hinit2 [hst hdef]] := initialize_maskP hfs hXp hinit.
exists s21 => //; exists (fun s1 s2 => s1 = s11 /\ s2 = s21), mask_st; split => //.
- have hbody : forall fd0 : ufundef, f_body (explicit_init_fd mask fd0) =
    init_masks mask (if explicit_init_c mask (f_body fd0) is MkI ii _ :: _ then ii else dummy_instr_info) fd0
      ++ explicit_init_c mask (f_body fd0) by case.
  rewrite hbody -[f_body fd]cat0s; apply wequiv_cat with mask_st; last by apply: explicit_init_cP.
  apply wequiv_esem_l; last first.
  + move=> s1 s2 s1' [-> ->]; apply: (init_masksP hst _ _ hdef).
    * move=> x _ hx; apply/Sv_elemsP; rewrite /vars_fd; SvD.fsetdec.
    by move=> x _ hx; case: hst => _ _ [_ hinv]; apply: (mask_inv_var_init hinv).
  rewrite /init_masks; elim: (Sv.elements _) => //= x xs ih; rewrite all_cat ih andbT.
  by rewrite /is_arr_var; case: (vtype x) => // ??; case: Sv.mem.
- by move=> s1 s2 fr1 hst' hfin; apply: finalize_maskP hst' hXr hfin.
by have [_ _ hv] := hfs; move=> fr1 fr2 hfr; apply: explicit_init_postP hv hfr.
Qed.

End EXPLICIT_INIT_PROOF.

#[local] Existing Instance progUnit.
#[local] Existing Instance nosubword.
#[local] Existing Instance indirect_c.

Section DEFS.

Context
  {asm_op syscall_state : Type}
  {ep : EstateParams syscall_state}
  {spp : SemPexprParams}
  {sip : SemInstrParams asm_op syscall_state}.

(* The hypotheses of [explicit_init_callP] on the masks of the variables of
   [p]. *)
Definition mask_ok (mask : var -> var) (p : uprog) : Prop :=
  [/\ injective mask,
      forall x y, Sv.In y (vars_p (p_funcs p)) -> mask x <> y,
      forall x, vtype (mask x) = if is_arr_var x then vtype x else abool
    & forall fn fd ci, get_fundef (p_funcs p) fn = Some fd -> f_contract fd = Some ci ->
      forall x y, Sv.In y (vars_l (f_iparams ci ++ f_ires ci)) -> mask x <> y].

End DEFS.
