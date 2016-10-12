(* -------------------------------------------------------------------- *)
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat ssrint ssralg tuple.
From mathcomp Require Import choice fintype eqtype div seq zmodp.

Require Import strings word dmasm_utils.
Require Import dmasm_type dmasm_var dmasm_expr.
Require Import memory dmasm_sem dmasm_Ssem dmasm_Ssem_props.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* -------------------------------------------------------------------- *)
Axiom fe : forall {T U} (f g : T -> U), (forall x, f x = g x) -> f = g.

(* -------------------------------------------------------------------- *)
Fixpoint st2sst_ty {t : stype} :=
  match t return st2ty t -> sst2ty t with
  | sword     => fun v => v
  | sbool     => fun v => v
  | t1 ** t2  => fun v => (st2sst_ty v.1, st2sst_ty v.2)
  | sarr n st => fun v => 
       (fun i : word => st2sst_ty
          match @Array.get _ n v i with
          | Ok w => w
          | _      => dflt_val st
          end)
  end.

(* -------------------------------------------------------------------- *)
Definition vmap_to_svmap (v : vmap) : svmap :=
  {| Fv.map := fun x : var => st2sst_ty (v.(Fv.map) x); |}.

(* -------------------------------------------------------------------- *)
Coercion estate_to_sestate (s : estate) :=
  {| semem := s.(emem); sevm := vmap_to_svmap s.(evm); |}.

(* -------------------------------------------------------------------- *)
Hint Constructors ssem ssem_i : ssem.

(* -------------------------------------------------------------------- *)
Lemma bindW {T U} (v : exec T) (f : T -> exec U) r :
  v >>= f = ok r -> exists2 a, v = ok a & f a = ok r.
Proof. by case E: v => [a|//] /= <-; exists a. Qed.

(* -------------------------------------------------------------------- *)
Lemma st2sst_pexpr {t} s (p : pexpr t) v : sem_pexpr s p = ok v ->
  ssem_pexpr (vmap_to_svmap s) p = (st2sst_ty v).
Proof.
elim: p v => //=.
+ by move=> x v [<-]. + by move=> n v [<-]. + by move=> n v [<-].
+ move=> st rt op a iha v h; case: (bindW h)=> va /iha -> {a h iha}.
  by case: op v va => //= *; unfold ok in *; congruence.
+ move=> st1 st2 str op a1 ih1 a2 ih2 v h.
  case: (bindW h) => v1 /ih1 -> {h}h; case: (bindW h) => v2 /ih2 -> {h}.
  case: {a1 a2 ih1 ih2} op v v1 v2 => //=; try by move=> ??? [].
  + by move=> v ?? [] ->;case v.
  + by move=> v ?? [] ->;case v.
  + by rewrite /FArray.get /= => ???? ->.
  by move=> ????? [] <-.
+ move=> st1 st2 st3 sr op a1 ih1 a2 ih2 a3 ih3 v h.
  case: (bindW h) => v1 /ih1 -> {h}h;
    case: (bindW h) => v2 /ih2 -> {h}h.
    case: (bindW h) => v3 /ih3 -> {h}.
  case: {a1 a2 a3 ih1 ih2 ih3} op v v1 v2 v3 => //=.
  + by move=> v ??? [] ->;case: v.
  + by move=> v ??? [] ->;case: v.
  move=> n a a' v1 v2.
  rewrite /Array.set /Array.get /FArray.set;case:ifP => //= Hb [] <-;apply fe=> z.
  case: ifP => [/eqP<-|Hne].
  + by rewrite Hb /FArray.get eq_refl.
  by case: ifPn=> //= ?;rewrite /FArray.get Hne.
Qed.

(* -------------------------------------------------------------------- *)
Lemma st2sst_vmap_get (s : vmap) (x : var) :
  (vmap_to_svmap s).[x]%vmap = st2sst_ty s.[x]%vmap.
Proof. by []. Qed.

Lemma st2sst_vmap_set (s : vmap) (x : var) v :
  (vmap_to_svmap s).[x <- st2sst_ty v]%vmap = vmap_to_svmap s.[x <- v]%vmap.
Proof.
apply/Fv.map_ext=> y; rewrite /Fv.get /Fv.set /=.
by case: eqP=> // eq; case: y / eq.
Qed.

(* -------------------------------------------------------------------- *)
Lemma st2sst_write {t} s (x : rval t) (v : st2ty t) :
    vmap_to_svmap (write_rval s x v)
  = swrite_rval (vmap_to_svmap s) x (st2sst_ty v).
Proof.
elim: x s v => /= [x|st1 st2 r1 ih1 r2 ih2] s v; last first.
  by rewrite !(ih1, ih2).
by apply/Fv.map_ext=> y /=; rewrite st2sst_vmap_set.
Qed.

(* -------------------------------------------------------------------- *)
Section SEM.

Lemma st2sst_bcmd s1 c s2 : sem_bcmd s1 c = ok s2 ->
  ssem_bcmd s1 c = ok (s2 : sestate).
Proof.
case: c=> [st r p|r p|p p'] /=.
+ move=> h; case: (bindW h) => v {h} /st2sst_pexpr.
  by move=> -> [<-]; rewrite -st2sst_write.
+ move=> h; case: (bindW h) => v /(@st2sst_pexpr sword) -> {h}.
  by case: (read_mem _ _) => //= w [<-]; rewrite -st2sst_write.
+ move=> h; case: (bindW h) => v /(@st2sst_pexpr sword) -> {h}.
  move=> h; case: (bindW h) => w /(@st2sst_pexpr sword) -> {h}.
  by case: (write_mem _ _ _) => //= m [<-].
Qed.

(*
(* -------------------------------------------------------------------- *)
Lemma st2sst_cmd : forall s1 c s2, sem s1 c s2 -> ssem s1 c s2.
Proof.
pose Pi s1 i s2 := ssem_i s1 i s2.
pose Pf rv d lo hi s1 c s2 := ssem_for rv d lo hi s1 c s2.
pose Pc sta str m1 (fd : fundef sta str) ag m2 res :=
  ssem_fun fd m1 (st2sst_ty ag) m2 (st2sst_ty res).
apply: (@sem_Ind _ Pi Pf Pc); rewrite {}/Pi {}/Pf {}/Pc;
  try by (move=> *; eauto with ssem).
+ by move=> s1 s2 c /st2sst_bcmd h; constructor.
+ move=> s1 s2 pe cd c1 c2 h _; case: (boolP cd) h => cdP h ih.
  * by apply/SEifTrue => //; apply/(@st2sst_pexpr sbool).
  * by apply/SEifFalse=> //; apply/negbT/(@st2sst_pexpr sbool).
+ move=> sta srt m1 vm1 m2 rvr fd a r.
  case E: (sem_pexpr _ _) => /= [va|//] _ _ ih /=.
  rewrite {2}/estate_to_sestate st2sst_write.
  by constructor=> /=; move/st2sst_pexpr: E => ->.
+ move=> s1 s2 iv d lo hi c vlo vhi h1 h2 _ ih.
  case Elo: (sem_pexpr _ lo) h1 => /= [vlo'|//] [vlo'E].
  case Ehi: (sem_pexpr _ hi) h2 => /= [vhi'|//] [vhi'E].
  case: (leqP vlo' vhi') => [le|gt].
  + apply/SEforDone;
      rewrite (st2sst_pexpr (t := sword) Elo) ;
      rewrite (st2sst_pexpr (t := sword) Ehi) //.
    by rewrite vlo'E vhi'E.
  


Admitted.
*)

End SEM.
