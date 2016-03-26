(* * Properties of the dmasm source language *)

(* ** Imports and settings *)
Require Import JMeq ZArith Setoid Morphisms.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat ssrint ssralg tuple finfun.
From mathcomp Require Import choice fintype eqtype div seq zmodp.
Require Import gen_map word dmasm_utils dmasm_type dmasm_var dmasm_sem 
               dmasm_sem_props dmasm_Ssem.

Import GRing.Theory.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope seq_scope.

Lemma surj_SEstate s : {| semem := semem s; sevm := sevm s |} = s.
Proof. by case: s. Qed.

(* -------------------------------------------------------------------------- *)
(* Compute the set of writen variables of a program                           *)
(* -------------------------------------------------------------------------- *)

Fixpoint vrv_rec {t} (s:Sv.t) (rv : rval t)  :=
  match rv with
  | Rvar  x               => Sv.add x s
  | Rpair st1 st2 rv1 rv2 => vrv_rec (vrv_rec s rv1) rv2 
  end.

Definition vrv {t} (rv : rval t) := vrv_rec Sv.empty rv.

Definition write_bcmd_rec (s:Sv.t) bc  := 
  match bc with
  | Assgn _ rv _  => vrv_rec s rv
  | Load rv _     => vrv_rec s rv
  | Store _ _     => s
  end.

Definition write_bcmd := write_bcmd_rec Sv.empty.

Fixpoint write_i_rec s i := 
  match i with
  | Cbcmd bc        => write_bcmd_rec s bc
  | Cif   _ c1 c2   => foldl write_i_rec (foldl write_i_rec s c2) c1
  | Cfor  x _ c     => foldl write_i_rec (vrv_rec s x) c
  | Ccall _ _ x _ _ => vrv_rec s x
  end.

Definition write_i i := write_i_rec Sv.empty i.

Definition write_c_rec s c := foldl write_i_rec s c.

Definition write_c c := write_c_rec Sv.empty c.

Instance vrv_rec_m {t} : Proper (Sv.Equal ==> (@eq (rval t)) ==> Sv.Equal) vrv_rec.
Proof.
  move=> s1 s2 Hs ? r ->.
  elim:r s1 s2 Hs => //= [??? -> // | ?? r1 Hr1 r2 Hr2 ???];auto.
Qed.

Lemma vrv_var (x:var) : Sv.Equal (vrv x) (Sv.singleton x). 
Proof. rewrite /vrv /=;SvD.fsetdec. Qed.

Lemma vrv_recE t (r:rval t) s : Sv.Equal (vrv_rec s r) (Sv.union s (vrv r)).
Proof.
  elim: r s => //= [x | ?? r1 Hr1 r2 Hr2] s.
  + by rewrite vrv_var;SvD.fsetdec.
  rewrite /vrv /= !(Hr1,Hr2);SvD.fsetdec.
Qed.

Lemma vrv_pair t1 t2 (r1:rval t1) (r2:rval t2):
  Sv.Equal (vrv (Rpair r1 r2)) (Sv.union (vrv r1) (vrv r2)).
Proof. rewrite {1}/vrv /= !vrv_recE;SvD.fsetdec. Qed.

Lemma write_bcmdE s bc : Sv.Equal (write_bcmd_rec s bc) (Sv.union s (write_bcmd bc)).
Proof. case: bc=> [? r _ | r _ | _ _] /=;rewrite ?vrv_recE;SvD.fsetdec. Qed.

(* TODO: move this *)
Definition cmd_Ind (P : cmd -> Prop) := 
  @cmd_ind P (fun _ _ _ => True).

Lemma write_c_recE s c : Sv.Equal (write_c_rec s c) (Sv.union s (write_c c)).
Proof.
  apply (@cmd_rect
           (fun i => forall s, Sv.Equal (write_i_rec s i) (Sv.union s (write_i i)))
           (fun c => forall s, Sv.Equal (write_c_rec s c) (Sv.union s (write_c c)))
           (fun _ _ _ => True)) => /= {c s}
    [ |i c1 Hi Hc1|bc|e c1 c2 Hc1 Hc2|x rn c1 Hc1| ?? x f a _|//] s;
    rewrite /write_i /write_c /=.
  + by SvD.fsetdec. 
  + by rewrite !Hc1 !Hi; SvD.fsetdec.  
  + by rewrite !write_bcmdE; SvD.fsetdec.
  + by rewrite -!/(write_c_rec _ c1) -!/(write_c_rec _ c2) !Hc1 !Hc2; SvD.fsetdec.
  + by rewrite -!/(write_c_rec _ c1) !Hc1 vrv_recE; SvD.fsetdec.
  by rewrite !vrv_recE; SvD.fsetdec.
Qed.

Lemma write_i_recE s i : Sv.Equal (write_i_rec s i) (Sv.union s (write_i i)).
Proof. by apply (write_c_recE s [:: i]). Qed.

Lemma write_c_cons i c: Sv.Equal (write_c (i::c)) (Sv.union (write_i i) (write_c c)).
Proof. by rewrite {1}/write_c /= write_c_recE write_i_recE;SvD.fsetdec. Qed.

Lemma write_i_bcmd bc : write_i (Cbcmd bc) = write_bcmd bc.
Proof. done. Qed.

Lemma write_i_if e c1 c2 :
   Sv.Equal (write_i (Cif e c1 c2)) (Sv.union (write_c c1) (write_c c2)).
Proof.
  rewrite /write_i /= -/(write_c_rec _ c1) -/(write_c_rec _ c2) !write_c_recE;SvD.fsetdec.
Qed.

Lemma write_i_for x rn c :
   Sv.Equal (write_i (Cfor x rn c)) (Sv.union (vrv x) (write_c c)).
Proof.
  rewrite /write_i /= -/(write_c_rec _ c) write_c_recE vrv_recE;SvD.fsetdec.
Qed.

Lemma write_i_call t1 t2 (f:fundef t1 t2) x a :
  write_i (Ccall x f a) = vrv x.
Proof. done. Qed.
  
Definition svmap_eq_except (s : Sv.t) (vm1 vm2 : svmap) :=
  forall x, ~Sv.In x s -> vm1.[x]%vmap = vm2.[x]%vmap.

Notation "vm1 = vm2 [\ s ]" := (svmap_eq_except s vm1 vm2) (at level 70, vm2 at next level,
  format "'[hv ' vm1  '/' =  vm2  '/' [\ s ] ']'").

Lemma vrvP t (r:rval t) v s : s = swrite_rval s r v [\ vrv r].
Proof.
  elim: r v s=> [x | ?? r1 Hr1 r2 Hr2] v s /= z; rewrite ?vrv_var ?vrv_pair=> ?.
  + rewrite Fv.setP_neq //;apply /eqP; SvD.fsetdec.
  rewrite -Hr1 -?Hr2//; SvD.fsetdec.
Qed.

Lemma writeP c s1 s2 : 
   ssem s1 c s2 -> s1.(sevm) = s2.(sevm) [\ write_c c].
Proof.
  apply (@cmd_rect
           (fun i => forall s1 s2, ssem_i s1 i s2 -> s1.(sevm) = s2.(sevm) [\ write_i i])
           (fun c => forall s1 s2, ssem   s1 c s2 -> s1.(sevm) = s2.(sevm) [\ write_c c])
           (fun _ _ _ => True)) => /= {c s1 s2}
    [ |i c1 Hi Hc1|bc|e c1 c2 Hc1 Hc2|x rn c1 Hc1| ?? x f a _|//] s1 s2 Hsem;
    inversion Hsem=>{Hsem};subst=> // z.
  + rewrite write_c_cons => Hz;rewrite (Hi _ _ H2) ?(Hc1 _ _ H4) //; SvD.fsetdec. 
  + rewrite write_i_bcmd;case: bc H1 => //= [? r p | r p | ??].
    + by move=> [] <- /=;apply vrvP.
    + by case read_mem => //= w [] <-;apply vrvP.
    by case write_mem => //= ? [] <-.
  + by rewrite write_i_if=> ?;apply Hc1=> //; SvD.fsetdec. 
  + by rewrite write_i_if=> ?;apply Hc2=> //; SvD.fsetdec. 
  + rewrite write_i_for. 
    elim: H5 Hc1=> {w1 w2 H4 e1 e2 dir s1 s2}.
    + move=> i _ w c s1 s2 Hsem Hc Hin.
      by rewrite -(Hc _ _ Hsem) /= -?vrvP //; SvD.fsetdec. 
    move => i dir w1 w2 c s1 s2 s3 _ /= Hsem _ Hrec Hc Hin.    
    by rewrite -Hrec // -(Hc _ _ Hsem) /= -?vrvP //; SvD.fsetdec. 
  by rewrite write_i_call=> Hin; move: H3 H4=> [] ?;subst=> -[] [] ?;subst;apply vrvP.  
Qed.


(* -------------------------------------------------------------------------- *)
(* Properties on swrite_rval                                                  *)
(* -------------------------------------------------------------------------- *)

Lemma swrite_nin  t (rv:rval t) (v:sst2ty t) z s:
  ~Sv.In z (vrv rv) ->
  ((swrite_rval s rv v).[z])%vmap = s.[z]%vmap.
Proof.
  elim: rv v s => /= [x | ??? Hr1 ? Hr2] v s;rewrite ?vrv_var ?vrv_pair => Hin.
  + by rewrite Fv.setP_neq //;apply /eqP; SvD.fsetdec.
  rewrite Hr1 ?Hr2 //;SvD.fsetdec.
Qed.

Lemma ssem_swrite_rval s (r:rval sword) w: 
  ssem_rval (swrite_rval s r w) r = w.
Proof. by case H : sword / r w => //= ?;rewrite Fv.setP_eq. Qed.

Lemma swrite_ssem_rval s (r:rval sword): swrite_rval s r (ssem_rval s r) = s.
Proof.
  apply Fv.map_ext=> x1;case H : sword / (r) => [ x2 | ] //=. 
  case: (x2 =P x1) => [ -> | /eqP ? ];first by rewrite Fv.setP_eq. 
  by rewrite Fv.setP_neq.   
Qed.


(* -------------------------------------------------------------------------- *)
(* Properties on donotdep                                                     *)
(* -------------------------------------------------------------------------- *)

Definition donotdep  (s : Sv.t) t (e:pexpr t) := 
  forall s1 s2, s1 = s2 [\ s] -> ssem_pexpr s1 e = ssem_pexpr s2 e.


