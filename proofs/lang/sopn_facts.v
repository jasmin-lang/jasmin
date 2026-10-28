(* * Facts about the semantics of the pseudo-operations.

   [sopn.v] is in the extraction cone and contains definitions only, together
   with the lemmas the fields of the descriptors need.  The equalities between
   the semantics of an instruction and the hand-written function that used to
   define it are needed by the compiler proofs only, and are here. *)

(* ** Imports and settings *)
From mathcomp Require Import ssreflect ssrfun ssrbool seq eqtype ssralg.
From mathcomp Require Import word_ssrZ.
Require Import pseudo_operator slh_ops safety_cond_facts sopn_semi sopn_semi_facts values values_facts sopn psem_defs.
Import Utf8 Lia.

Local Open Scope seq_scope.

(* -------------------------------------------------------------------- *)
(* ** The array copy                                                     *)

(* On a cell that is in bounds, the only possible failure of a read is an
   uninitialised cell. *)
Lemma get8_errE len (a : WArray.array len) i e :
  WArray.in_bound a i -> WArray.get8 partial a i = Error e -> e = ErrAddrUndef.
Proof. by rewrite WArray.get8_partial => -> /=; case: WArray.is_init => //= -[<-]. Qed.

Lemma mapM_get8_errE len (a : WArray.array len) (f : Z -> Z) l e :
  all (fun k => WArray.in_bound a (f k)) l ->
  mapM (fun k => WArray.get8 partial a (f k)) l = Error e -> e = ErrAddrUndef.
Proof.
elim: l e => //= k l ih e /andP [hk hl].
case hg: WArray.get8 => [w|e'] /=; last by move=> [<-]; apply: get8_errE hg.
by case hm: mapM => [?|e2] //= [?]; subst e2; apply: ih hl hm.
Qed.

Lemma get_errE ws len (a : WArray.array len) i e :
  validw a Unaligned (i * mk_scale AAscale ws)%Z ws ->
  WArray.get Unaligned AAscale ws a i = Error e -> e = ErrAddrUndef.
Proof.
rewrite /validw => /andP [] _ hv.
rewrite /WArray.get /CoreMem.read /is_aligned_if.
case hm: mapM => [l|e'] //= [<-].
apply: mapM_get8_errE hm; exact: hv.
Qed.

Lemma copy_validw ws n (a : WArray.array (arr_size ws n)) i :
  (0 <= i < n)%Z -> validw a Unaligned (i * mk_scale AAscale ws)%Z ws.
Proof.
move=> hi; rewrite /validw /is_aligned_if andTb.
apply ziota_ind => //= k ? hk ->; rewrite andbT; apply/WArray.in_boundP.
by rewrite WArray.addE arr_sizeE; Lia.nia.
Qed.

Lemma fcopy_eq ws n (a : WArray.array (arr_size ws n)) l
    (t : WArray.array (arr_size ws n)) :
  all (fun i => (0 <=? i)%Z && (i <? n)%Z) l ->
  foldM (fun i t => Let w := WArray.get Unaligned AAscale ws a i in
                    WArray.set t Unaligned AAscale i w) t l
  = (if all (fun i => is_ok (WArray.get Unaligned AAscale ws a i)) l
     then ok (foldl (fun t i => copy_set t i (@copy_get ws _ a i)) t l)
     else Error ErrAddrUndef).
Proof.
elim: l t => //= i l ih t /andP [] /andP [] /ZleP h1 /ZltP h2 hl.
have hv := @copy_validw ws n t i (conj h1 h2).
have hva := @copy_validw ws n a i (conj h1 h2).
case hg : (WArray.get Unaligned AAscale ws a i) => [w | e] /=; last first.
+ by rewrite (@get_errE _ _ _ _ _ hva hg).
have [t' ht'] : exists t', WArray.set t Unaligned AAscale i w = ok t'.
+ by apply: (writeV (CM:= WArray.array_CM (arr_size ws n))).
have hgt : WArray.get (sm := total) Unaligned AAscale ws a i = ok w.
+ by case/read_partialE: hg.
have ht't : WArray.set (sm := total) t Unaligned AAscale i w = ok t'.
+ by case/write_partialE: ht'.
rewrite ht' /= /copy_set /copy_get hgt ht't /=.
by apply ih.
Qed.

(* [copy] fails exactly when one of the cells it reads is uninitialised, that
   is, exactly when its safety condition does not hold. *)
Lemma array_copy_eq ws n (a : WArray.array (arr_size ws n)) :
  @WArray.copy partial ws n a =
  (if all (fun i => is_ok (WArray.get Unaligned AAscale ws a i)) (ziota 0 n)
   then ok (@copy_total ws _ a) else Error ErrAddrUndef).
Proof.
rewrite /WArray.copy /WArray.fcopy /copy_total; apply fcopy_eq.
apply ziota_ind => //= i l hi ->; rewrite andbT.
by apply/andP; split; [apply/ZleP | apply/ZltP]; Lia.lia.
Qed.

Lemma array_copy_semi_eq ws p :
  sem_prod_eq [:: carr (arr_size ws p)] (@WArray.copy partial ws p)
    (@mk_semi _ [:: carr (arr_size ws p)] [:: carr (arr_size ws p)]
       [:: sc_all_init ws p 0] ErrAddrUndef [:: IBool true] (@copy_total ws p)).
Proof.
move=> t.
have -> : @mk_semi _ [:: carr (arr_size ws p)] [:: carr (arr_size ws p)]
            [:: sc_all_init ws p 0] ErrAddrUndef [:: IBool true] (@copy_total ws p) t
        = (Let _ := check_safe [:: Varr t] [:: sc_all_init ws p 0] ErrAddrUndef in
           ok (@copy_total ws _ t)) by [].
rewrite /check_safe /= andbT (safety_cond_holds_all_init (t := t)) // array_copy_eq.
by case: all.
Qed.

Section COPY_TOTAL.

Local Open Scope Z_scope.

(* The total copy writes every cell of its result. *)
Lemma copy_total_is_init ws n (a : WArray.array (arr_size ws n)) k :
  0 <= k < arr_size ws n -> WArray.is_init (@copy_total ws n a) k.
Proof.
move=> hk.
have hws := wsize_size_pos ws.
have hset : forall (t : WArray.array (arr_size ws n)) i (w : word ws),
  i * wsize_size ws <= k < i * wsize_size ws + wsize_size ws -> WArray.is_init (copy_set t i w) k.
- move=> t i w hi; rewrite /copy_set.
  case h : WArray.set => [t' | e].
  + rewrite (set_total_is_init k h) /= /WArray.in_bound.
    by apply/orP; left; apply/and4P; split; [apply/ZleP | apply/ZltP | apply/ZleP | apply/ZltP]; lia.
  move: h; rewrite /WArray.set.
  have := write_total_ok t Unaligned (i * mk_scale AAscale ws) w.
  by move=> /(_ _ (WArray.array_CM _)) /[swap] ->.
have hmono : forall (t : WArray.array (arr_size ws n)) i (w : word ws),
  WArray.is_init t k -> WArray.is_init (copy_set t i w) k.
- move=> t i w hi; rewrite /copy_set.
  case h : WArray.set => [t' | //].
  by rewrite (set_total_is_init k h) hi orbT.
set i0 := k / wsize_size ws.
have hi0 : i0 * wsize_size ws <= k < i0 * wsize_size ws + wsize_size ws.
- rewrite /i0; have := Z.div_mod k (wsize_size ws); have := Z.mod_pos_bound k (wsize_size ws); lia.
have : i0 \in ziota 0 n.
- rewrite in_ziota; apply/andP; split; [apply/ZleP | apply/ZltP]; rewrite /arr_size in hk; nia.
rewrite /copy_total; move=> hin.
have : forall l (t : WArray.array (arr_size ws n)), (i0 \in l) || WArray.is_init t k ->
  WArray.is_init (foldl (fun t i => copy_set t i (copy_get ws a i)) t l) k.
- elim => [ | j l ih] t //=.
  move=> h; apply: ih; move: h; rewrite in_cons -orbA => /orP [/eqP <- | /orP [-> // | hinit]].
  + by rewrite hset ?orbT.
  by rewrite hmono ?orbT.
by move=> h; apply: h; rewrite hin.
Qed.

End COPY_TOTAL.

(* -------------------------------------------------------------------- *)
(* ** The [total_init] semantics                                         *)

Section EXEC_SOPN.

Context {asm_op syscall_state : Type} {ep : EstateParams syscall_state} {asmop : asmOp asm_op}.

(* An instruction in the [total_init] mode computes what it computes in the
   [total] mode, where every undefined output takes its default value: its
   total semantics gives [undefined_flag], that is [false], to a boolean
   output it leaves undefined ([i_init_dflt]). *)
Lemma exec_sopn_total_initE o vs :
  exec_sopn (sm := total_init) o vs =
  Let vs2 := exec_sopn (sm := total) o vs in ok (map value_dflt vs2).
Proof.
rewrite /exec_sopn /sopn_sem; case: assert => //= _.
rewrite /sopn_sem_ /semi (mk_semi_total_initE _ _ _ (i_init_dflt (get_instr_desc o))).
by case: app_sopn => //= t; rewrite list_ltuple_dflt.
Qed.

Lemma exec_sopn_total_initP o vs vs1 :
  exec_sopn (sm := total_init) o vs = ok vs1 <->
  exists2 vs2, exec_sopn (sm := total) o vs = ok vs2 & vs1 = map value_dflt vs2.
Proof.
rewrite exec_sopn_total_initE; case: exec_sopn => //= [vs2 | e]; split.
+ by move=> [<-]; exists vs2.
+ by move=> [_ [<-] ->].
+ by [].
by case.
Qed.

End EXEC_SOPN.

(* -------------------------------------------------------------------- *)
(* ** Protection of a pointer                                            *)

(* -------------------------------------------------------------------- *)
(* ** The outputs of an instruction                                      *)

Section OUTPUTS.

Context {asm_op syscall_state : Type} {ep : EstateParams syscall_state} {asmop : asmOp asm_op}.

Lemma oto_val_DB t (x : sem_ot t) : DB true (oto_val x).
Proof. by case: t x => //= -[]. Qed.

(* Only a boolean output may be undefined. *)
Lemma list_ltuple_DB ts (t : sem_tuple ts) : all (DB true) (list_ltuple t).
Proof.
elim: ts t => [ | t1 ts ih] //= t.
case: ts ih t => [ | t2 ts] ih t /=; first by rewrite oto_val_DB.
by rewrite oto_val_DB; apply: ih.
Qed.

Lemma exec_sopn_DB {sm : SemMode} o vs vs2 : exec_sopn (sm := sm) o vs = ok vs2 -> all (DB true) vs2.
Proof. by rewrite /exec_sopn; t_xrbindP => _ _ t _ <-; apply: list_ltuple_DB. Qed.

Lemma app_sopn_size T ts (f : sem_prod ts (exec T)) vs t :
  app_sopn ts f vs = ok t -> size vs = size ts.
Proof.
clear.
by elim: ts f vs => [ | ty ts ih] f [ | v vs] //=; t_xrbindP => // x _ /ih ->.
Qed.

Lemma instr_desc_init_wt (d : instruction_desc) :
  all (safety_cond_wt [seq eval_atype i | i <- tin d]) (i_init d).
Proof. by case/and4P: (i_wf d). Qed.

Lemma exec_sopn_size {sm : SemMode} o vs vs2 :
  exec_sopn (sm := sm) o vs = ok vs2 -> size vs = size (tin (get_instr_desc o)).
Proof.
rewrite /exec_sopn /sopn_sem; t_xrbindP => _ _ <- t ht _.
by rewrite (app_sopn_size ht) size_map.
Qed.

Lemma exec_protect_ptr o ws len vs v :
  (o = SLHprotect_ptr ws len \/ o = SLHprotect_ptr_fail ws len) ->
  exec_sopn (sm := total) (Oslh o) vs = ok [:: v] -> v = head v vs.
Proof.
move=> ho; rewrite /exec_sopn /sopn_sem; case: ho => -> /=; t_xrbindP => t.
all: case: vs => [ | a [ | b [ | ? ?]]] /=; try by t_xrbindP.
all: by t_xrbindP => a' /to_arrI -> w _ <- <-.
Qed.

Lemma exec_swapE {sm : SemMode} ws len vs vs' :
  exec_sopn (sm := sm) (Opseudo_op (Oswap (aarr ws len))) vs = ok vs' ->
  exists (a1 a2 : WArray.array (arr_size ws len)), vs = [:: Varr a1; Varr a2] /\ vs' = [:: Varr a2; Varr a1].
Proof.
rewrite /exec_sopn /sopn_sem /=; t_xrbindP => t.
case: vs => [ | v1 [ | v2 [ | ? ?]]] /=; try by t_xrbindP.
t_xrbindP => a1 /to_arrI -> a2 /to_arrI -> _.
by move=> <- <-; exists a1, a2.
Qed.

(* In the total mode a valid instruction runs on defined arguments of its
   types, and gives values of the types of its outputs. *)
Lemma exec_sopn_total_ok o vs : i_valid (get_instr_desc o) ->
  List.Forall2 (fun t v => is_defined v /\ subctype t (type_of_val v))
    (map eval_atype (sopn_tin o)) vs ->
  exists2 vs', exec_sopn (sm := total) o vs = ok vs' &
    List.Forall2 (fun t v => type_of_val v = eval_atype t /\ DB true v) (sopn_tout o) vs'.
Proof.
move=> hv hall; rewrite /exec_sopn /sopn_sem hv /=.
have hf : sem_forall (fun r => is_ok r) _ (sopn_sem_ (sm := total) o).
+ by apply: mk_semi_aux_ok.
have [t ->] := app_sopn_ok hf hall.
eexists; first reflexivity.
have := type_of_val_ltuple t; have := list_ltuple_DB t; rewrite /sopn_tout.
move: (list_ltuple t) => l; clear t hf hall.
elim: l (tout (get_instr_desc o)) => [ | v l ih] [ | ty tys] //= /andP [hdb hdbs] [hty htys].
by constructor; [split | apply: ih].
Qed.

End OUTPUTS.
