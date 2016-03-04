(* * Prove properties about semantics of dmasm input language *)

(* ** Imports and settings *)
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat ssrint ssralg.
From mathcomp Require Import choice fintype eqtype div seq zmodp.
Require Import Coq.Logic.Eqdep_dec.
Require Import finmap strings  dmasm_utils dmasm_sem.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.

Local Open Scope ring_scope.
Local Open Scope fun_scope.
Local Open Scope fmap.
Local Open Scope fset.

(* ** Variable renaming
 * -------------------------------------------------------------------- *)

Notation renaming := (ident -> ident).

Definition rn_var st (pi : renaming) (v : var st) :=
  let: Var _ n := v in Var st (pi n).

Fixpoint rn_pexpr st (pi : renaming) (pe : pexpr st) :=
  match pe with
  | Pvar   st v           => Pvar (rn_var pi v)
  | Pconst    c           => Pconst c
  | Papp sta ste op pe    => Papp op (rn_pexpr pi pe)
  | Ppair st1 st2 pe1 pe2 => Ppair (rn_pexpr pi pe1) (rn_pexpr pi pe2)
  end.

Fixpoint rn_rval st (pi : renaming) (rv : rval st) : rval st :=
  match rv with
  | Rvar  st v            => Rvar (rn_var pi v)
  | Rpair st1 st2 rv1 rv2 => Rpair (rn_rval pi rv1) (rn_rval pi rv2)
  end.

Definition rn_bcmd (pi : renaming) (bc : bcmd) :=
  match bc with
  | Assgn st rv pe       => Assgn (rn_rval pi rv) (rn_pexpr pi pe)
  | Load rv pe_addr      => Load (rn_rval pi rv) (rn_pexpr pi pe_addr)
  | Store pe_addr pe_val => Store (rn_pexpr pi pe_addr) (rn_pexpr pi pe_val)
  end.

Definition rn_range (pi : renaming) (r : range) :=
  let: (dir,pe1,pe2) := r in (dir,rn_pexpr pi pe1,rn_pexpr pi pe2).

Fixpoint rn_cmd (rec : recurse) (pi : renaming) (c : cmd) :=
  match c with
  | Cskip        => Cskip
  | Cbcmd bc     => Cbcmd (rn_bcmd pi bc)
  | Cseq c1 c2   => Cseq (rn_cmd rec pi c1) (rn_cmd rec pi c2)
  | Cif pe c1 c2 => Cif (rn_pexpr pi pe) (rn_cmd rec pi c1) (rn_cmd rec pi c2)
  | Cfor v rng c => Cfor (rn_var pi v) (rn_range pi rng) (rn_cmd rec pi c)
  | Ccall starg stres rv_farg pe_ret c_body rv_res pe_arg =>
      let: (rv_farg,pe_ret,c_body) :=
        if rec is NoRecurse then (rv_farg,pe_ret,c_body)
        else (rn_rval pi rv_farg, rn_pexpr pi pe_ret, rn_cmd rec pi c_body)
      in
      Ccall rv_farg pe_ret c_body
        (rn_rval pi rv_res) (rn_pexpr pi pe_arg)
  end.

Definition rn_fdef starg stres (pi : renaming) (rv : rval starg) (pe : pexpr stres) (c : cmd) :=
  (rn_rval pi rv, rn_pexpr pi pe, rn_cmd NoRecurse pi c).

Fixpoint rn_fmap_aux st (pi : renaming) (f_in : {fmap ident -> st2ty st}) (ks : seq ident) :=
  match ks with
  | [::]        => fmap0
  | [:: k & ks] =>
    (rn_fmap_aux pi f_in ks) +
    fmap0.[ pi k <- odflt (dflt st) f_in.[? k ]]
  end.

Definition rn_fmap st (pi : renaming) (f : {fmap ident -> st2ty st}) : {fmap ident -> st2ty st} :=
  rn_fmap_aux pi f (fset_keys (domf f)).

Lemma rn_fmap_dom st (pi : renaming) (fm : {fmap ident -> st2ty st}):
  domf (rn_fmap pi fm) = seq_fset [seq pi i | i <- fset_keys (domf fm)].
Proof.
apply /fsetP; rewrite /eq_mem => x.
rewrite in_seq_fsetE /rn_fmap.
have ->: forall xs,
             (x \in domf (rn_fmap_aux pi fm xs))
           = (x \in [seq pi i | i <- xs]) => //.
move=> xs. elim xs.
+ by rewrite //= in_fset0 in_nil. 
+ move=> k ks Hind.
  rewrite //= in_cons in_fsetU in_fset1U in_fset0.
  move: (LEM x (pi k)). elim => [Heq | Hineq].
  + rewrite Heq //=.
    have ->: pi k == pi k = true. admit.
    by rewrite !(Bool.orb_true_l,Bool.orb_true_r).
  + have Hf: x == pi k = false. admit.
    rewrite Hf !(Bool.orb_false_l,Bool.orb_false_r) in_fsetD in_fset1U Hf in_fset0
            !(Bool.orb_false_l,Bool.orb_false_r) //=.
Admitted.

Lemma rn_fmap_get st (pi : renaming) (fm : {fmap ident -> st2ty st}) i:
  fm.[? i] = (rn_fmap pi fm).[? pi i].
Proof.
rewrite /rn_fmap.
Admitted.

Definition rn_vmap (pi : renaming) (vm : vmap) : vmap :=
  fun st => rn_fmap pi (vm st).

Lemma rn_vmap_get {st} pi (vm : vmap) (v : var st):
  (vm st).[? (vname v)] = ((rn_vmap pi vm) st).[? vname (rn_var pi v)].
Proof. by case v; rewrite /= => st_ id_; rewrite (rn_fmap_get pi). Qed.

(* ** Ecall reminder
 * -------------------------------------------------------------------- *)

(* Ecall
     {m1}     : initial memory
     {m2}     : final memory
     {vm1}    : initial vmap
     {vmc1}   : vmap before call
     {vmc2}   : vmap after call
     {starg}  : type of function arg
     {stres}  : type of function result
     {farg}   : formal argument
     {fres}   : formal result
     {fbody}  : function body
     rv_res   : rval for assigning result
     {pe_arg} : given result *)

(* ** Renaming function bodies
 * -------------------------------------------------------------------- *)

Lemma rn_pexpr_eq st (pi : renaming) (vm : vmap) (pe : pexpr st):
  sem_pexpr vm pe = sem_pexpr (rn_vmap pi vm) (rn_pexpr pi pe).
Proof.
elim pe.
+ by move=> st1 v; rewrite //= (rn_vmap_get pi).
+ by rewrite //=.
+ move => st1 st2 pe1 Heq1 pe2 Heq2.
  by rewrite //= -Heq1 -Heq2.
+ move=> sta str sop pe1 Heq.
  by rewrite //= Heq.
Qed.

Lemma rn_write_rval_eq pi vm {st} (rv : rval st) (v : st2ty st):
    (@write_rval st (rn_vmap pi vm) (rn_rval pi rv) v)
  = (@rn_vmap pi (@write_rval st vm rv v)).
Proof.
have vmap_ext: forall (vm1 vm2 : vmap),
                 (forall st k, (vm1 st).[? k] = (vm2 st).[? k]) -> vm1 = vm2.
  admit.
apply vmap_ext => st2 id2.
induction rv.
+ rewrite /write_rval. admit.
+ admit.
Admitted.

Lemma rn_sem_equiv pi m1 m2 vm1 vm2 c:
  bijective pi ->
  sem {| emem := m1; evm := vm1 |} c {| emem := m2; evm := vm2 |} ->
  sem {| emem := m1; evm := rn_vmap pi vm1 |}
      (rn_cmd NoRecurse pi c)
      {| emem := m2; evm := rn_vmap pi vm2 |}.
Proof. Admitted.

Lemma rn_call_equiv starg stres (s1 s2 : estate) pi farg fres fbody rv_res pe_arg:
  bijective pi ->
  sem s1 (@Ccall starg stres farg fres fbody rv_res pe_arg) s2 ->
  let:  (farg,fres,fbody) := rn_fdef pi farg fres fbody in
  sem s1 (@Ccall starg stres farg fres fbody rv_res pe_arg) s2.
Proof.
move=> Hbij Hs //=.
inversion Hs. 
clear pe_arg0 H starg0 H5 fbody0 fres0 H0 Hs H3 s2.
rewrite /vm2 /res0.
apply (inj_pair2_eq_dec _ LEM) in H1.
apply (inj_pair2_eq_dec _ LEM) in H4.
apply (inj_pair2_eq_dec _ LEM) in H6.
apply (inj_pair2_eq_dec _ LEM) in H7.
rewrite -H6.
move : (rn_pexpr_eq pi vmc2 fres1) => WW.
rewrite -H1 -H4 -H7 WW. clear H1 H2 H4 H6.
rewrite /vmc0 in H9.
apply (Ecall (vmc1:=rn_vmap pi vmc1)).
+ done.
+ rewrite (rn_write_rval_eq pi vmc1).
  rewrite -/arg0.  
  by apply rn_sem_equiv.
+ by rewrite -WW.
Qed.

(* ** Variable substitution
 * -------------------------------------------------------------------- *)

Notation subst := (forall st, var st -> pexpr st).

Fixpoint subst_pexpr st (s : subst) (pe : pexpr st) :=
  match pe with
  | Pvar   st v           => s st v
  | Pconst    c           => Pconst c
  | Papp sta ste op pe    => Papp op (subst_pexpr s pe)
  | Ppair st1 st2 pe1 pe2 => Ppair (subst_pexpr s pe1) (subst_pexpr s pe2)
  end.

Definition subst_bcmd (s : subst) (bc : bcmd) :=
  match bc with
  | Assgn st rv pe       => Assgn rv (subst_pexpr s pe)
  | Load rv pe_addr      => Load rv (subst_pexpr s pe_addr)
  | Store pe_addr pe_val => Store (subst_pexpr s pe_addr) (subst_pexpr s pe_val)
  end.

Definition subst_range (s : subst) (r : range) :=
  let: (dir,pe1,pe2) := r in (dir,subst_pexpr s pe1,subst_pexpr s pe2).

Fixpoint subst_cmd (s : subst) (c : cmd) :=
  match c with
  | Cskip        => Cskip
  | Cbcmd bc     => Cbcmd (subst_bcmd s bc)
  | Cseq c1 c2   => Cseq (subst_cmd s c1) (subst_cmd s c2)
  | Cif pe c1 c2 => Cif (subst_pexpr s pe) (subst_cmd s c1) (subst_cmd s c2)
  | Cfor v rng c => Cfor v (subst_range s rng) (subst_cmd s c)
  | Ccall _ _ rv_farg pe_ret c_body rv_res pe_arg =>
      Ccall rv_farg (subst_pexpr s pe_ret)
        (subst_cmd s c_body) rv_res (subst_pexpr s pe_arg)
  end.

(* Assumes that variables in different scopes all disjoint *)
Fixpoint inline_calls (pos : seq nat) (p : seq nat -> bool) (c : cmd) : cmd :=
  match c with
  | Cskip =>
      Cskip
  | Cbcmd bc =>
      Cbcmd bc
  | Cseq c1 c2 =>
      Cseq (inline_calls (0%N :: pos) p c1) (inline_calls (1%N :: pos) p c2)
  | Cif pe c1 c2 =>
      Cif pe (inline_calls (0%N :: pos) p c1) (inline_calls (1%N :: pos) p c2)
  | Cfor v rng c =>
      Cfor v rng (inline_calls (0%N :: pos) p c)
  | Ccall starg stres rv_farg pe_ret c_body rv_res pe_arg =>
      let c_body := inline_calls (0%N :: pos) p c_body in
      if p pos
      then Cseq (assgn rv_farg pe_arg) (Cseq c_body (assgn rv_res pe_ret))
      else Ccall rv_farg pe_ret c_body rv_res pe_arg
  end.

(* ** Definitions: {phi} c {psi} <=> (c <^> phi) <= psi
 * -------------------------------------------------------------------- *)

Notation assn := (estate -> Prop).

Definition post (c : cmd) (Pre: assn) : assn :=
  fun est' => exists est, Pre est /\ sem est c est'.

Notation "c <^> sts" := (post c sts) (at level 40, left associativity).

Parameter rn_pred : renaming -> assn -> assn.

Lemma rn_commutes (pi : renaming) (sts : assn) (c : cmd):
  bijective pi ->
    (rn_cmd NoRecurse pi c) <^> (rn_pred pi sts)
  = rn_pred pi (c <^> sts).
Proof.
move=> Hbij.
Admitted.