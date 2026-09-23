(* * Facts about the semantics of the pseudo-operations.

   [sopn.v] is in the extraction cone and contains definitions only, together
   with the lemmas the fields of the descriptors need.  The equalities between
   the semantics of an instruction and the hand-written function that used to
   define it are needed by the compiler proofs only, and are here. *)

(* ** Imports and settings *)
From mathcomp Require Import ssreflect ssrfun ssrbool seq eqtype ssralg.
From mathcomp Require Import word_ssrZ.
Require Import sopn.
Import Utf8.

Local Open Scope seq_scope.

(* -------------------------------------------------------------------- *)
(* ** The array copy                                                     *)

(* On a cell that is in bounds, the only possible failure of a read is an
   uninitialised cell. *)
Lemma get8_errE len (a : WArray.array len) i e :
  WArray.in_bound a i -> WArray.get8 a i = Error e -> e = ErrAddrUndef.
Proof. by rewrite /WArray.get8 => -> /=; case: WArray.is_init => //= -[<-]. Qed.

Lemma mapM_get8_errE len (a : WArray.array len) (f : Z -> Z) l e :
  all (fun k => WArray.in_bound a (f k)) l ->
  mapM (fun k => WArray.get8 a (f k)) l = Error e -> e = ErrAddrUndef.
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
rewrite ht' /= /copy_set /copy_get hg ht' /=.
by apply ih.
Qed.

(* [copy] fails exactly when one of the cells it reads is uninitialised, that
   is, exactly when its safety condition does not hold. *)
Lemma array_copy_eq ws n (a : WArray.array (arr_size ws n)) :
  @WArray.copy ws n a =
  (if all (fun i => is_ok (WArray.get Unaligned AAscale ws a i)) (ziota 0 n)
   then ok (@copy_total ws _ a) else Error ErrAddrUndef).
Proof.
rewrite /WArray.copy /WArray.fcopy /copy_total; apply fcopy_eq.
apply ziota_ind => //= i l hi ->; rewrite andbT.
by apply/andP; split; [apply/ZleP | apply/ZltP]; Lia.lia.
Qed.

Lemma array_copy_semi_eq ws p :
  sem_prod_eq [:: carr (arr_size ws p)] (@WArray.copy ws p)
    (@mk_semi [:: carr (arr_size ws p)] [:: carr (arr_size ws p)]
       [:: AllInit ws p 0] ErrAddrUndef [:: IBool true] (@copy_total ws p)).
Proof.
move=> t.
have -> : @mk_semi [:: carr (arr_size ws p)] [:: carr (arr_size ws p)]
            [:: AllInit ws p 0] ErrAddrUndef [:: IBool true] (@copy_total ws p) t
        = (Let _ := check_safe_old [:: Varr t] [:: AllInit ws p 0] ErrAddrUndef in
           ok (@copy_total ws _ t)) by [].
rewrite /check_safe_old /= andbT WArray.castK array_copy_eq.
by case: all.
Qed.

(* -------------------------------------------------------------------- *)
(* ** Protection of a pointer                                            *)

Section WITH_PARAMS.

Context {msfsz : MSFsize}.

Definition se_protect_ptr_fail_sem {len:Z} (t: WArray.array len) (msf : wmsf) : exec (WArray.array len) :=
  Let _ := assert (msf == 0%w) ErrSemUndef in
  ok t.

Lemma protect_ptr_fail_eq n :
  sem_prod_eq [:: carr n; cty_msf ] (@se_protect_ptr_fail_sem n)
    (@mk_semi [:: carr n; cty_msf ] [:: carr n] [:: IsZero msf_size 1] ErrSemUndef
       [:: IBool true ] (fun (t : WArray.array n) (_ : wmsf) => t)).
Proof.
  move=> t msf.
  rewrite /mk_semi /= /check_safe_old /= andbT truncate_word_u /se_protect_ptr_fail_sem.
  by rewrite /assert; case: eqP.
Qed.

End WITH_PARAMS.
