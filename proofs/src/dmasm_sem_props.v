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
Local Open Scope vmap.

(* ** Variable occurences
 * -------------------------------------------------------------------- *)

Fixpoint vars_pexpr st (pe : pexpr st) :=
  match pe with
  | Pvar   _ (Var vn)  => [fset (Tvar st vn)]
  | Pconst _           => fset0
  | Papp sta ste _ pe     => vars_pexpr pe
  | Ppair st1 st2 pe1 pe2 => vars_pexpr pe1 `|` vars_pexpr pe2
  end.

Fixpoint vars_rval st (rv : rval st) :=
  match rv with
  | Rvar  st (Var vn)   => [fset (Tvar st vn)]
  | Rpair st1 st2 rv1 rv2 => vars_rval rv1 `|` vars_rval rv2
  end.

Definition vars_bcmd (bc : bcmd) :=
  match bc with
  | Assgn st rv pe       => vars_rval  rv      `|` vars_pexpr pe
  | Load rv pe_addr      => vars_rval  rv      `|` vars_pexpr pe_addr
  | Store pe_addr pe_val => vars_pexpr pe_addr `|` vars_pexpr pe_val
  end.

Definition vars_range (r : range) :=
  let: (_,pe1,pe2) := r in
  vars_pexpr pe1 `|` vars_pexpr pe2.

Inductive recurse := Recurse | NoRecurse.

Definition vars_cmd (rec: recurse) (c:cmd) := 
  Eval lazy beta delta [cmd_rect instr_rect' list_rect] in
  @cmd_rect (fun _ =>  {fset tvar}) (fun _ =>  {fset tvar}) (fun _ _ _ =>  {fset tvar})
    fset0
    (fun _ _ s1 s2 =>  s1 `|` s2)
    vars_bcmd
    (fun e _ _ s1 s2 => vars_pexpr e `|` s1 `|` s2)
    (fun i rn _ s  =>  Tvar sword i.(vname) |` vars_range rn `|` s)
    (fun _ _ x f a s =>  
       (if rec is Recurse then s (* Warning : without "Eval lazy ..." the vars of f are always computed *)
        else fset0) `|` vars_rval x `|` vars_pexpr a)
    (fun _ _ x _ re s => vars_rval x `|` vars_pexpr re `|` s) 
    c.

Definition vars_fdef starg stres (rv : rval starg) (pe : pexpr stres) (c : cmd) :=
  vars_rval rv `|` vars_pexpr pe `|` vars_cmd NoRecurse c.

(* ** Variable renaming
 * -------------------------------------------------------------------- *)

Notation renaming := (ident -> ident).

Definition rn_var st (pi : renaming) (v : var st) :=
  Var st (pi v.(vname)).

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

Fixpoint rn_instr (rec : recurse) (pi : renaming) i :=
  match i with
  | Cbcmd  bc => Cbcmd (rn_bcmd pi bc)
  | Cif pe c1 c2 =>
    Cif (rn_pexpr pi pe)
        [seq rn_instr rec pi i | i <- c1]
        [seq rn_instr rec pi i | i <- c2]
  | Cfor v rng c =>
    Cfor (rn_var pi v) (rn_range pi rng) [seq rn_instr rec pi i | i <- c]
  | Ccall sta str rv fd a =>
    let: fd :=
      if rec is Recurse then rn_fdef rec pi fd else fd
    in
    Ccall (rn_rval pi rv) fd (rn_pexpr pi a)
  end

with rn_fdef sta str (rec : recurse) (pi : renaming) (fd : fundef sta str) :=
  match fd with
  | FunDef _ _ fr fb fa =>
    FunDef (rn_rval pi fr) [seq rn_instr rec pi i | i <- fb] (rn_pexpr pi fa)
  end.

Definition rn_cmd (rec : recurse) (pi : renaming) c :=
  [seq rn_instr rec pi i | i <- c].

Definition rn_vmap (pi : renaming) (vm : vmap) : vmap :=
  Vmap (fun st id => vm.(vm_map) st (pi id)).

Lemma rn_vmap_get {st} pi pi_inv (vm : vmap) (v : var st):
  cancel pi_inv pi ->
  vm.[st, vname v] = (rn_vmap pi vm).[st, pi_inv (vname v)].
Proof. by move => Hcan; case v => id; rewrite /vmap_get //= Hcan. Qed.

Definition rn_tosubst pi (ts : g_tosubst st2ty) :=
  @ToSubst st2ty ts.(ts_t) (pi ts.(ts_id)) ts.(ts_to).

Definition rn_estate pi s :=
  {| emem := s.(emem); evm := rn_vmap pi s.(evm) |}.

(* ** Commuting renamings
 * -------------------------------------------------------------------- *)

Lemma rn_pexpr_eq st (pi pi_inv : renaming) (vm : vmap) (pe : pexpr st):
  cancel pi_inv pi ->
  sem_pexpr vm pe = sem_pexpr (rn_vmap pi vm) (rn_pexpr pi_inv pe).
Proof.
  move => Hcan; elim pe => //.
  + by move=> st1 v; rewrite //= (rn_vmap_get vm _ Hcan).
  + by move => st1 st2 pe1 Heq1 pe2 Heq2; rewrite //= -Heq1 -Heq2.
  + by move=> sta str sop pe1 Heq; rewrite //= Heq.
Qed.

Lemma rn_range_eq (pi pi_inv : renaming) (vm : vmap) (rng : range):
  cancel pi_inv pi ->
  sem_range vm rng = sem_range (rn_vmap pi vm) (rn_range pi_inv rng).
Proof.
  move => Hcan. case rng => rng1; case rng1 => dir pe1 pe2.
  rewrite /sem_range /=.
  by do 2 rewrite -(rn_pexpr_eq _ _ Hcan).
Qed.

Lemma rn_vmap_set_get st pi pi_inv vm vn (v : st2ty st) st' id:
  cancel pi_inv pi ->
  cancel pi     pi_inv ->
  ((rn_vmap pi vm).[pi_inv vn <- v]).[st',id] = (rn_vmap pi vm.[vn <- v]).[st',id].
Proof.
  move=> Hcan1 Hcan2.
  rewrite /rn_vmap /vmap_get //=; case: (eq_stype st st'); [ move=> Heq | done ].
  rewrite /eq_rect //=. case Heq.
  rewrite -(bij_eq (_ : bijective pi)); first by rewrite Hcan1.
  by apply /Bijective.
Qed.

Lemma write_subst_rn_val st pi (rv : rval st) (v : st2ty st):
  forall substs,
    write_subst (rn_rval pi rv) v [seq rn_tosubst pi ts | ts <- substs ]
  = [seq rn_tosubst pi ts | ts <- write_subst rv v substs].
Proof.
  induction rv => substs.
  + by case v0 => vn0 //.
  + by rewrite /= IHrv1 IHrv2.
Qed.    

Lemma write_subst_rn_val_nil st pi (rv : rval st) (v : st2ty st):
    write_subst (rn_rval pi rv) v [::]
  = [seq rn_tosubst pi ts | ts <- write_subst rv v [::] ].
Proof. by rewrite (write_subst_rn_val pi _ _ [::]). Qed.

Lemma rn_write_vmap_eq pi pi_inv vm substs:
  cancel pi_inv pi ->
  cancel pi     pi_inv ->
    write_vmap (rn_vmap pi vm) [seq rn_tosubst pi_inv ts | ts <- substs ]
  = rn_vmap pi (write_vmap vm substs).
Proof.
  move=> Hcan1 Hcan2.
  elim substs; first done.
  move=> sub subs Hind; case sub => ts_t ts_id ts_v //=.
  rewrite Hind.
  apply vmap_ext; rewrite /vmap_ext_eq /vmap_get => st2 id2 //=.
  case (eq_stype ts_t st2); [  move=> Heq | done].
  rewrite /eq_rect //=; case Heq.
  rewrite -(bij_eq (_ : bijective pi)); first by rewrite Hcan1.
  by apply /Bijective.
Qed.

Lemma rn_write_rval_eq pi pi_inv vm {st} (rv : rval st) (v : st2ty st):
  cancel pi_inv pi ->
  cancel pi     pi_inv ->
    write_rval (rn_vmap pi vm) (rn_rval pi_inv rv) v
  = rn_vmap pi (write_rval vm rv v).
Proof.
  move=> Hcan1 Hcan2.
  apply vmap_ext; rewrite /vmap_ext_eq => st2 id2 //=.
  rewrite /write_rval write_subst_rn_val_nil.
  by rewrite (rn_write_vmap_eq _ _ Hcan1 Hcan2).
Qed.

(* ** Commuting renamings
 * -------------------------------------------------------------------- *)

Lemma rn_sem_bcmd_equiv pi pi_inv m1 vm1 bc:
  cancel pi_inv pi ->
  cancel pi     pi_inv ->
    (sem_bcmd {| emem := m1; evm := rn_vmap pi vm1 |} (rn_bcmd pi_inv bc))
  = rmap (fun es => {| emem := es.(emem); evm := rn_vmap pi es.(evm) |})
         (sem_bcmd {| emem := m1; evm := vm1 |} bc).
Proof.
  move=> Hcan1 Hcan2.
  case bc => //=.
  + move=> st r pe.
    rewrite -(rn_pexpr_eq _ _ Hcan1).
    case (sem_pexpr vm1 pe) => st2 //=.
    by rewrite rn_write_rval_eq.
  + move=> rv pe.
    rewrite -(rn_pexpr_eq _ _ Hcan1).
    case (sem_pexpr vm1 pe) => st2 //=.
    case (read_mem m1 st2) => w //=.
    by rewrite rn_write_rval_eq.
  + move => w1 w2.
    rewrite -(rn_pexpr_eq _ _ Hcan1).
    rewrite -(rn_pexpr_eq _ _ Hcan1).
    case (sem_pexpr vm1 w1) => st2 //=.
    case (sem_pexpr vm1 w2) => st3 //=.
    by case (write_mem m1 st2 st3) => //=.
Qed.

Lemma rn_sem_equiv_aux pi pi_inv s1 s2 c:
  cancel pi_inv pi ->
  cancel pi     pi_inv ->
  sem s1 c s2 ->
  sem (rn_estate pi s1) (rn_cmd NoRecurse pi_inv c) (rn_estate pi s2).
Proof.
  move=> Hcan1 Hcan2.
  generalize s1 c s2.
  apply (@sem_Ind _
           (fun s1 i s2 => sem_i (rn_estate pi s1) (rn_instr NoRecurse pi_inv i) (rn_estate pi s2))
           (fun v ws s1 c s2 =>
              sem_for
                (rn_var pi_inv v) ws (rn_estate pi s1) (rn_cmd NoRecurse pi_inv c)
                (rn_estate pi s2))).
  + by move=> s; constructor.
  + move=> s3 s4 s5 ii cc Hsi Hsi_rn Hsc Hsc_rn.
    by apply (Eseq (s2:=rn_estate pi s4)) => //.
  + move=> s3 s4 bc Hbc; apply Ebcmd.
    rewrite (rn_sem_bcmd_equiv _ _ _ Hcan1 Hcan2) /=.
    by move: Hbc; case s3 => m3 vm3 //= -> //.
  + move=> s3 s4 pe cond c1 c2 Hpe Hif Hif_rn => //=.
    apply (Eif (cond:=cond)).
    + by rewrite -(rn_pexpr_eq _ _ Hcan1) /=.
    + by move: Hif_rn; case cond => //=.
  + move=> m1 m2 vm1 vmc1 vmc2 sta str fa fr fb rv_res pe_arg.
    move=> Hok_arg arg vmc Hbody Hbody_rn Hok_fres res vm2.
    rewrite /rn_estate /vm2 /=.
    rewrite -(rn_write_rval_eq _ _ _ Hcan1 Hcan2).
    apply (Ecall (vmc1:=vmc1)) => //.
    + by rewrite -(rn_pexpr_eq _ _ Hcan1).
    + rewrite /vmc /arg /rn_estate /= in Hbody.
      by rewrite -(rn_pexpr_eq _ _ Hcan1).
  + move=> s3 s4 iv rng c_for ws Hsrng Hsc_for Hs_for.
    rewrite /=.
    apply (EFor (ws:=ws)); last done.
    by rewrite -(rn_range_eq _ _ Hcan1).
  + by move=> s3 c_for iv; constructor.
  + move=> s3 s4 s5 c_for w ws iv ac Hsac Hsac_rn Hsfor Hsfor_rn.
    by apply (EForOne (s2:=(rn_estate pi s4))).
Qed.

Lemma rn_sem_equiv pi pi_inv m1 m2 vm1 vm2 c:
  cancel pi_inv pi ->
  cancel pi     pi_inv ->
  sem {| emem := m1; evm := vm1 |} c {| emem := m2; evm := vm2 |} ->
  sem {| emem := m1; evm := rn_vmap pi vm1 |}
      (rn_cmd NoRecurse pi_inv c)
      {| emem := m2; evm := rn_vmap pi vm2 |}.
Proof.
  move=> Hcan1 Hcan2.
  by apply (rn_sem_equiv_aux Hcan1 Hcan2
              (s1:={| emem := m1; evm := vm1 |}) (s2:={| emem := m2; evm := vm2 |}) (c:=c)).
Qed.

Lemma rn_call_equiv starg stres (s1 s2 : estate) pi pi_inv (fd : fundef starg stres) rv_res pe_arg:
  cancel pi_inv pi ->
  cancel pi     pi_inv ->
  sem s1 [:: @Ccall starg stres rv_res fd                  pe_arg] s2 ->
  sem s1 [:: @Ccall starg stres rv_res (rn_fdef NoRecurse pi_inv fd) pe_arg] s2.
Proof.
  move=> Hcan1 Hcan2.
  destruct fd => /= Hsem.
  apply (Eseq (s2:=s2)); last apply Eskip.
  inversion Hsem.
  inversion H4.
  rewrite H7 in H2. clear Hsem H4 H H0 H5 H7 H1 H3 s0 s3 s4.
  inversion H2.
  rewrite /vm2 /res0.
  apply (inj_pair2_eq_dec _ LEM) in H1.
  apply (inj_pair2_eq_dec _ LEM) in H7.
  apply (inj_pair2_eq_dec _ LEM) in H9.
  apply (inj_pair2_eq_dec _ LEM) in H10.
  rewrite -H1 -H7 -H8 -H9 -H10.
  move : (@rn_pexpr_eq stres pi pi_inv vmc2 fres0 Hcan1) => WW.
  rewrite WW.
  apply (Ecall (vmc1:=rn_vmap pi vmc1)) => //.
  + rewrite (rn_write_rval_eq _ _ _ Hcan1 Hcan2).
    by apply (rn_sem_equiv Hcan1 Hcan2); rewrite /vmc0 /arg0 -H8 in H12.
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

(* Bene: Does it make sence ? *)
(*
Definition subst_cmd (s : subst) (c : cmd) :=
  Eval lazy beta delta [cmd_rect instr_rect1 list_rect] in
  @cmd_rect (fun _ => instr) (fun _ => cmd) (fun ta tr _ => fundef ta tr)
  [::]
  (fun _ _ i c => i::c)
  (fun bc => Cbcmd (subst_bcmd s bc))
  (fun e _ _ c1 c2 => Cif (subst_pexpr s e) c1 c2)
  (fun i rn _ c => Cfor i (subst_range s rn) c)
  (fun _ _ x _ a f =>  Ccall  x f (subst_pexpr s a))
  (fun _ _ x _ re c => FunDef x c (subst_pexpr s re)).
*)

(* Assumes that variables in different scopes all disjoint *)
(*
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
*)

(*
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
*)