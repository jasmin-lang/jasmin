(* * Prove properties about semantics of dmasm input language *)

(* ** Imports and settings *)
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat ssrint ssralg.
From mathcomp Require Import choice fintype eqtype div seq zmodp.
Require Import Coq.Logic.Eqdep_dec.
Require Import finmap strings  dmasm_utils dmasm_type dmasm_sem.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.

Local Open Scope ring_scope.
Local Open Scope fun_scope.
Local Open Scope vmap.
Local Open Scope fset.
Local Open Scope seq_scope.

(* ** Equivalence relations on vmaps
 * -------------------------------------------------------------------- *)

Definition vmap_eq_on (s : {fset ident}) (vm1 vm2 : vmap) :=
  forall st k, k \in s -> vmap_get vm1 st k = vmap_get vm2 st k.

Definition vmap_eq_except (s : {fset ident}) (vm1 vm2 : vmap) :=
  forall st k, k \notin s -> vmap_get vm1 st k = vmap_get vm2 st k.

Notation "vm1 = vm2 [&& s ]" := (vmap_eq_on s vm1 vm2) (at level 70, vm2 at next level,
  format "'[hv ' vm1  '/' = vm2  '/' [&&  s ] ']'").

Notation "vm1 = vm2 [\ s ]" := (vmap_eq_except s vm1 vm2) (at level 70, vm2 at next level,
  format "'[hv ' vm1  '/' =  vm2  '/' [\ s ] ']'").

Lemma vmap_eq_except_on vm1 vm2 s1 s2:
  [disjoint s2 & s1] ->
  vm1 = vm2 [\ s1] ->
  vm1 = vm2 [&& s2].
Proof.
  move=> Hdis Hexc.
  rewrite /vmap_eq_on => st id Hin.
  apply Hexc.
  move: Hdis => /fdisjointP Hdis.
  by apply (Hdis id).
Qed.

Lemma vmap_eq_except_on_combine vm1 vm2 s1:
  vm1 = vm2 [\ s1] ->
  vm1 = vm2 [&& s1] ->
  vm1 =v vm2.
Proof.
  move=> Hexc Hon.
  rewrite /vmap_ext_eq => st id.
  elim (Bool.bool_dec (id \in s1) true).
  + apply Hon.
  + by move=> /Bool.eq_true_not_negb; apply (Hexc st id).
Qed.

(* ** Identifier occurences
 * -------------------------------------------------------------------- *)

Fixpoint ids_pexpr st (pe : pexpr st) :=
  match pe with
  | Pvar   _ (Var vn)  => [fset vn]
  | Pconst _           => fset0
  | Papp sta ste _ pe     => ids_pexpr pe
  | Ppair st1 st2 pe1 pe2 => ids_pexpr pe1 `|` ids_pexpr pe2
  end.

Fixpoint ids_rval st (rv : rval st) :=
  match rv with
  | Rvar  st (Var vn)   => [fset vn]
  | Rpair st1 st2 rv1 rv2 => ids_rval rv1 `|` ids_rval rv2
  end.

Definition ids_bcmd (bc : bcmd) :=
  match bc with
  | Assgn st rv pe       => ids_rval  rv      `|` ids_pexpr pe
  | Load rv pe_addr      => ids_rval  rv      `|` ids_pexpr pe_addr
  | Store pe_addr pe_val => ids_pexpr pe_addr `|` ids_pexpr pe_val
  end.

Definition ids_range (r : range) :=
  let: (_,pe1,pe2) := r in
  ids_pexpr pe1 `|` ids_pexpr pe2.

Definition ids_cmd_g (ids_instr : instr -> {fset ident}) : cmd -> {fset ident} :=
  fix ids_cmd_g (c : cmd) :=
    match c with
    | [::] => fset0
    | instr::instrs => ids_instr instr `|` ids_cmd_g instrs
    end.

Fixpoint ids_instr (i : instr) : {fset ident} := 
  match i with
  | Cbcmd  bc             => ids_bcmd bc
  | Cif pe c1 c2          => ids_pexpr pe `|` ids_cmd_g ids_instr c1 `|` ids_cmd_g ids_instr c2
  | Cfor v rng c          => vname v |` ids_range rng `|` ids_cmd_g ids_instr c
  | Ccall sta str rv fd a => ids_rval rv `|` ids_pexpr a
  end.

Notation ids_cmd := (ids_cmd_g ids_instr).

Definition ids_fdef sta str (fd : fundef sta str) :=
  ids_rval (fd_arg fd) `|` ids_pexpr (fd_res fd) `|` ids_cmd (fd_body fd).

(* ** Read and write idents
 * -------------------------------------------------------------------- *)

Definition read_bcmd (bc : bcmd) :=
  match bc with
  | Assgn st rv pe       => ids_pexpr pe
  | Load  rv pe_addr     => ids_pexpr pe_addr
  | Store pe_addr pe_val => ids_pexpr pe_addr `|` ids_pexpr pe_val
  end.

Fixpoint read_instr (i : instr) : {fset ident} := 
  match i with
  | Cbcmd  bc             => read_bcmd bc
  | Cif pe c1 c2          => ids_pexpr pe `|` ids_cmd_g read_instr c1 `|` ids_cmd_g read_instr c2
  | Cfor v rng c          => ids_range rng `|` ids_cmd_g read_instr c
  | Ccall sta str rv fd a => ids_pexpr a
  end.

Notation read_cmd := (ids_cmd_g read_instr).

Definition read_fdef sta str (fd : fundef sta str) :=
  ids_pexpr (fd_res fd) `|` read_cmd (fd_body fd).

Definition write_bcmd (bc : bcmd) :=
  match bc with
  | Assgn st rv pe       => ids_rval  rv
  | Load rv pe_addr      => ids_rval  rv
  | Store pe_addr pe_val => fset0
  end.

Fixpoint write_instr (i : instr) : {fset ident} := 
  match i with
  | Cbcmd  bc             => write_bcmd bc
  | Cif pe c1 c2          => ids_cmd_g write_instr c1 `|` ids_cmd_g write_instr c2
  | Cfor v rng c          => vname v |` ids_cmd_g write_instr c
  | Ccall sta str rv fd a => ids_rval rv
  end.

Notation write_cmd := (ids_cmd_g write_instr).

Definition write_fdef sta str (fd : fundef sta str) :=
  ids_rval (fd_arg fd) `|` write_cmd (fd_body fd).

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

Fixpoint rn_instr (pi : renaming) i :=
  match i with
  | Cbcmd  bc => Cbcmd (rn_bcmd pi bc)
  | Cif pe c1 c2 =>
    Cif (rn_pexpr pi pe)
        [seq rn_instr pi i | i <- c1]
        [seq rn_instr pi i | i <- c2]
  | Cfor v rng c =>
    Cfor (rn_var pi v) (rn_range pi rng) [seq rn_instr pi i | i <- c]
  | Ccall sta str rv fd a =>
    Ccall (rn_rval pi rv) fd (rn_pexpr pi a)
  end

with rn_fdef sta str (pi : renaming) (fd : fundef sta str) :=
    FunDef (rn_rval pi (fd_arg fd)) 
           [seq rn_instr pi i | i <- fd_body fd]
           (rn_pexpr pi (fd_res fd)).

Definition rn_cmd (pi : renaming) c :=
  [seq rn_instr pi i | i <- c].

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
    do 2 rewrite -(rn_pexpr_eq _ _ Hcan1).
    case (sem_pexpr vm1 w1) => st2 //=.
    case (sem_pexpr vm1 w2) => st3 //=.
    by case (write_mem m1 st2 st3) => //=.
Qed.

Lemma rn_sem_equiv_aux pi pi_inv s1 s2 c:
  cancel pi_inv pi ->
  cancel pi     pi_inv ->
  sem s1 c s2 ->
  sem (rn_estate pi s1) (rn_cmd pi_inv c) (rn_estate pi s2).
Proof.
  move=> Hcan1 Hcan2.
  generalize s1 c s2.
  apply (@sem_Ind _
           (fun s1 i s2 => sem_i (rn_estate pi s1) (rn_instr pi_inv i) (rn_estate pi s2))
           (fun v ws s1 c s2 =>
              sem_for
                (rn_var pi_inv v) ws (rn_estate pi s1) (rn_cmd pi_inv c)
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
  + move=> m1 m2 vm1 vmc0 vmc2 sta str fa fr fb rv_res pe_arg.
    move=> Hok_arg arg vmc Hbody Hbody_rn Hok_fres.
    rewrite /rn_estate /=.
    rewrite -(rn_write_rval_eq _ _ _ Hcan1 Hcan2).
    apply (Ecall (vmc0:=vmc0)) => //.
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
      (rn_cmd pi_inv c)
      {| emem := m2; evm := rn_vmap pi vm2 |}.
Proof.
  move=> Hcan1 Hcan2.
  by apply (rn_sem_equiv_aux Hcan1 Hcan2
              (s1:={| emem := m1; evm := vm1 |}) (s2:={| emem := m2; evm := vm2 |}) (c:=c)).
Qed.

Lemma rn_call_equiv sta str (s1 s2 : estate) pi pi_inv (fd : fundef sta str) rv_res pe_arg:
  cancel pi_inv pi ->
  cancel pi     pi_inv ->
  sem s1 [:: Ccall rv_res fd                  pe_arg] s2 ->
  sem s1 [:: Ccall rv_res (rn_fdef pi_inv fd) pe_arg] s2.
Proof.
  move=> Hcan1 Hcan2.
  destruct fd => /= Hsem.
  apply (Eseq (s2:=s2)); last apply Eskip.
  inversion Hsem.
  inversion H4.
  rewrite H7 in H2. clear Hsem H4 H H0 H5 H7 H1 H3 s0 s3 s4.
  inversion H2.
  apply (inj_pair2_eq_dec _ LEM) in H1.
  apply (inj_pair2_eq_dec _ LEM) in H7.
  apply (inj_pair2_eq_dec _ LEM) in H9.
  apply (inj_pair2_eq_dec _ LEM) in H10.
  rewrite -H1 -H7 -H8 -H9 -H10.
  move : (@rn_pexpr_eq stres pi pi_inv vmc2 fres0 Hcan1) => WW.
  rewrite WW.
  apply (Ecall (vmc0:=rn_vmap pi vmc0)) => //.
  + rewrite /= (rn_write_rval_eq _ _ _ Hcan1 Hcan2).
    by apply (rn_sem_equiv Hcan1 Hcan2); rewrite /vmc0 /arg0 -H8 in H12.
  + by rewrite -WW.
Qed.

(* ** Framing for command execution
 * -------------------------------------------------------------------- *)

Lemma eq_except_sub vm1 vm2 s1 s2:
  s1 `<=` s2 ->
  vm1 = vm2 [\ s1 ] ->
  vm1 = vm2 [\ s2 ].
Proof.
  move=> Hsub.
  rewrite /vmap_eq_except => Heq st i Hnot.
  apply Heq.
  Locate "\notin".
  rewrite /fsubset in Hsub.
  move: Hsub => /eqP <-.
  rewrite in_fsetI. apply/nandP.
  by right.
Qed.

Lemma eq_except_trans vm1 vm2 vm3 s:
  vm1 = vm2 [\ s ] ->
  vm2 = vm3 [\ s ] ->
  vm1 = vm3 [\ s ].
Proof.
  (do 3 rewrite /vmap_eq_except) => W1 W2 st k Hnotin.
  by rewrite W1 => //; rewrite W2.  
Qed.

Lemma vmap_set_neq {t1 t2} id x (v : st2ty t1) vm: id <> x ->
    vm.[id <- v].[t2,x] = vm.[t2,x].
Proof.
  rewrite /vmap_set /vmap_get /=; case: eq_stype => //= a.
  move: v; case: _ / a=> v.
  by rewrite /= => /eqP /negPf ->.
Qed.

Lemma vmap_set_neq_t {t1 t2} id x (v : st2ty t1) vm: t2 <> t1 ->
    vm.[id <- v].[t2,x] = vm.[t2,x].
Proof.
  by rewrite /vmap_set /vmap_get /= => /nesym; case: eq_stype.
Qed.

Lemma eq_except_set st vm id (v : st2ty st) :
  vm = vm.[id <- v] [\ [fset id]].
Proof.
  rewrite /vmap_eq_except => st2 id2 Hnotin.
  case_eq (id == id2).
  + by move=> /eqP Heq; move: Hnotin; rewrite Heq fset11.
  + rewrite -Bool.negb_true_iff.
    move=> Hneq. rewrite (vmap_set_neq) => //.
    by apply/eqP.
Qed.

Lemma write_vmap_eq_except_aux vm substs:
  vm = write_vmap vm substs [\ seq_fset [seq ts.(ts_id) | ts <- substs ]].
Proof.
  elim substs => //.
  move=> s ss //=.
  destruct s => /=.
  rewrite fset_cons.
  set ws := (ts_id |` _).
  move=> H1.
  apply (@eq_except_sub _ _ _ ws) in H1; last by apply fsubsetUr.
  have W:  write_vmap vm ss = (write_vmap vm ss).[ts_id <- ts_to] [\ws].
    apply (@eq_except_sub _ _ [fset ts_id]); first by apply fsubsetUl.
    apply eq_except_set.    
  by apply (eq_except_trans H1 W).
Qed.

Lemma write_subst_arg st (rv : rval st) (v : st2ty st) (l : seq (g_tosubst st2ty)):
  write_subst rv v l = (write_subst rv v [::]) ++ l.
Proof.
  generalize l.
  induction rv => /=.
  + by case v0 => vn; move => ls //.
  + move => ls. rewrite IHrv1 IHrv2.
    by rewrite (IHrv2 _ (write_subst rv1 v.1 [::])) catA.
Qed.

Lemma seq_fset_cat (aT : choiceType) (l1 : seq aT) (l2 : seq aT):
  seq_fset (l1 ++ l2) = seq_fset l1 `|` seq_fset l2.
Proof.
  elim l1.
  + by rewrite cat0s (_ : seq_fset [::] = fset0) !(fset0U,seq_fset0).
  + move=> x xs.
    rewrite cat_cons /= !fset_cons; move=> ->.
    by rewrite fsetUA.
Qed.

Lemma ids_rval_write_substs st (rv : rval st) (v : st2ty st):
  ids_rval rv = seq_fset [seq ts.(ts_id) | ts <- write_subst rv v [::] ].
Proof.
  induction rv.
  + by case v0 => vn; rewrite /=.
  + rewrite /= write_subst_arg map_cat seq_fset_cat.
    by rewrite (IHrv1 v.1) (IHrv2 v.2) fsetUC.
Qed.

Lemma write_rval_eq_except st vm (rv : rval st) (v : st2ty st):
  vm = write_rval vm rv v [\ids_rval rv].
Proof.
  rewrite /write_rval (ids_rval_write_substs rv v).
  by apply write_vmap_eq_except_aux.
Qed.

Lemma write_rval_eq_except_imp st vm1 vm2 (rv : rval st) (v : st2ty st) s:
  vm1 = vm2 [\s ] ->
  write_rval vm1 rv v = write_rval vm2 rv v [\ s].
Proof.
  rewrite /write_rval. admit.
Admitted.

Lemma sem_bcmd_eq_except s1 s2 bc:
  sem_bcmd s1 bc = ok s2 ->
  evm s1 = evm s2 [\write_bcmd bc].
Proof.
  elim bc.
  + move=> st r p /=.
    case (sem_pexpr (evm s1) p) => //.
    move=> v /= Heq.
    inversion Heq => /=.
    by apply write_rval_eq_except.
  + move=> rw pe /=.
    case (sem_pexpr (evm s1) pe) => //.
    move=> v /=.
    case (read_mem (emem s1) v) => //.
    move=> w /= Heq.
    inversion Heq => /=.
    by apply write_rval_eq_except.
  + move=> w1 w2 //=.
    case (sem_pexpr (evm s1) w1) => //.
    move=> w3 /=.    
    case (sem_pexpr (evm s1) w2) => //.
    move=> w4 /=.
    case (write_mem _ _ _) => // m' /= Heq.
    inversion Heq => //.
Qed.

Lemma sem_eq_except (s1 s2 : estate) c:
  sem s1 c s2 -> s1.(evm) = s2.(evm) [\ write_cmd c].
Proof.
   apply (@sem_Ind
           (fun s1 c s2 => evm s1 = evm s2 [\ write_cmd c])
           (fun s1 i s2 => s1.(evm) = s2.(evm) [\ write_instr i])
           (fun v ws s1 c s2 => s1.(evm) = s2.(evm) [\ vname v |` write_cmd c])).
  + done.
  + move=> s3 s4 s5 i cc Hi Heq1 Hc Heq2.
    apply (eq_except_sub (s2:=write_cmd (i::cc))) in Heq1;
      last by rewrite /write_cmd; apply (fsubsetUl).
    apply (eq_except_sub (s2:=write_cmd (i::cc))) in Heq2;
      last by rewrite /write_cmd; apply (fsubsetUr).
    by apply (eq_except_trans Heq1 Heq2).
  + move=> s3 s4 cc Hsbc Hsi.
    by apply sem_bcmd_eq_except.
  + move=> s3 s4 pcond cond c1 c2 Hpcond Hs Heq1 Hsi.
    apply (eq_except_sub (s1:=(write_cmd (if cond then c1 else c2)))) => //.
    by rewrite /=; case cond; [ apply fsubsetUl | apply fsubsetUr].
  + move=> m1 m2 vm1 vmc0 vmc2 sta str fa fr fb rv_res pe_arg.
    move=> Hok1 arg vmc1 Hsfb Heq1 Hok2 Hscall k.
    by rewrite /=; apply write_rval_eq_except.   
  + by move=> s3 s4 iv rng cc ws Hrng Hcc_ws Heq1.
  + done.
  + move=> s3 s4 s5 cc w ws iv ac Hac Heq1 Hcc_ws Heq2 Hcc_w_ws.
    apply (eq_except_sub (s2:=vname iv |` write_cmd cc)) in Heq1;
      last by rewrite /ac /=; case iv => ii //=; apply fsubset_refl.
    by apply (eq_except_trans Heq1 Heq2).
Qed.

Lemma sem_ids_unchanged (s1 s1' s2 s2': estate) c:
  s1.(emem) = s1'.(emem) /\ s1.(evm)  = s1'.(evm) [&& read_cmd c] ->
  sem s1  c s2 ->
  sem s1' c s2' ->
  s2.(emem) = s2'.(emem) /\ s2.(evm) = s2'.(evm)  [&& write_cmd c].
Proof.
Admitted.

(* ** Inline call
 * -------------------------------------------------------------------- *)

Definition inlined_call sta str (rv_res : rval str) fd (pe_arg : pexpr sta) :=
  match fd with
  | FunDef sta str fa fc fr =>
      fun pe_arg rv_res => Cbcmd (Assgn fa pe_arg)::(fc++[:: Cbcmd (Assgn rv_res fr)])
  end pe_arg rv_res.

Definition inline_call i :=
  match i with
  | Cbcmd bc                       => None
  | Cfor v rng c                   => None
  | Cif pe c1 c2                   => None
  | Ccall sta str rv_res fd pe_arg => Some (inlined_call rv_res fd pe_arg)
  end.

Lemma eq_except_sym vm1 vm2 s:
  vm1 = vm2 [\ s] -> vm2 = vm1 [\ s].
Proof. rewrite /vmap_eq_except => Heq st id Hnotin. rewrite Heq; done. Qed.

Lemma inline_call_simul sta str (s1 s2 : estate) (fd : fundef sta str) rv_res pe_arg:
  sem s1 (inlined_call rv_res fd pe_arg) s2 ->
  exists s2',
    sem s1 [:: Ccall     rv_res fd pe_arg] s2' /\
    s2.(emem) = s2'.(emem) /\
    s2.(evm) = s2'.(evm) [\ write_fdef fd].
Proof.
  destruct fd=> /= Hic.
  inversion Hic => {Hic}. clear H1 H1 H3 s4 s0 H0 H.
  apply sem_inv_app in H4. elim H4 => {H4} s2_1.
  case => Hsl Hsassgn. inversion Hsassgn => {Hsassgn}.
  inversion H5 => {H5}. rewrite H8 in H3. clear  H H0 H4 H6 H8 s s4 H1 c0 i0 s0 s5 i c.
  inversion H2 => {H2}. clear H4 H H0 s4 s0 c.
  inversion H3 => {H3}. clear H4 H H0 s4 s0 c.
  rewrite /write_fdef /=.
  pose s2' := ({| emem := s2.(emem);
                  evm := write_rval s1.(evm) rv_res (rdflt_ (sem_pexpr s2_1.(evm) p)) |}).
  exists s2'.
  split.
  + apply (Eseq (s2:= s2')); last by apply Eskip.
    rewrite /s2'. move: H1. case s1 => m1 vm1 H1.
    have Hok: isOk (sem_pexpr vm1 pe_arg).
    + by move: H1; rewrite /sem_bcmd /=; case (sem_pexpr vm1 pe_arg).
    have Hok2: isOk (sem_pexpr (evm s2_1) p).
    + by move: H2; rewrite /sem_bcmd /=; case (sem_pexpr (evm s2_1) p). 
    apply (Ecall (vmc0:=vm1)) => //.
    move: H1 Hok => /=. case (sem_pexpr vm1 pe_arg) => v //= Heq Ht {Ht}.
    move: Heq; case => Heq. rewrite -Heq in Hsl.
    move: H2 Hok2 => /=. case (sem_pexpr (evm s2_1) p) => v2 //= Heq2 Ht {Ht}.
    move: Heq2; case. case s2 => m2 vm2; case => Heq3.
    rewrite /= -Heq3 /=.
    have ->: {| emem := emem s2_1; evm := evm s2_1 |} = s2_1. case s2_1; done.
    done. 
  split => //.
  rewrite /=.
  have W: evm s2_1 = evm s1 [\ids_rval r `|` write_cmd l].
    have Q1: evm s1 = evm s3 [\ids_rval r `|` write_cmd l].
      apply (@eq_except_sub _ _ (ids_rval r)). apply fsubsetUl.
      by apply (sem_bcmd_eq_except H1).
    have Q2: evm s3 = evm s2_1 [\ids_rval r `|` write_cmd l].
      apply (@eq_except_sub _ _ (write_cmd l)). apply fsubsetUr.
      by apply (sem_eq_except Hsl).
    apply eq_except_sym.
    by apply (eq_except_trans Q1 Q2).
  have WW: evm s2 = write_rval (evm s1) rv_res (rdflt_ (sem_pexpr (evm s2_1) p))
             [\ids_rval r `|` write_cmd l]. 
    move: H2 => /=. case (sem_pexpr (evm s2_1) p) => v //=. case. case s2 => m2 vm2 /=.
    case => HH <-.  by apply write_rval_eq_except_imp.
  apply WW.
Qed.

(* ** Modify command at given position
 * -------------------------------------------------------------------- *)

Definition pos := seq nat.

Fixpoint map_pos_instr (p : pos) (f : instr -> option cmd) (i : instr) {struct p} : cmd :=
  match p with
  | [::] =>
    match f i with
    | Some i => i
    | None   => [:: i]
    end
  | j::p =>
    match i with
    | Cbcmd bc => [:: Cbcmd bc]
    | Cfor v rng c =>
      [:: Cfor v rng (map_pos_cmd p f c)]
    | Ccall sta str rv_res fd pe_arg =>
      [:: Ccall rv_res fd pe_arg] (* p cannot point into function body *)
    | Cif pe c1 c2 =>
      match j with
      | 0%nat => [:: Cif pe (map_pos_cmd p f c1) c2]
      | 1%nat => [:: Cif pe c1 (map_pos_cmd p f c2)]
      | _     => [:: Cif pe c1 c2]
      end
    end
  end

with map_pos_cmd (p : seq nat) (f : instr -> option cmd) (c : cmd) {struct p}: cmd :=
  match p with
  | [::] => c
  | j::p =>
    (take j c)++
    (match drop j c with
     | inst::insts => (map_pos_instr p f inst)++insts
     | [::]        => [::]
    end)
  end.

Lemma map_pos_equiv (s1 s2 : estate) p f c (Rel : estate -> estate -> Prop):
  (forall s, Rel s s) ->
  (* c ~ f c : s<1> = s<2> ==> Rel s<2> s<2> *)
  (forall s1 s2 s2' i c,
     f i = Some c ->
     sem_i s1 i s2 ->
     sem   s1 c s2' ->
     Rel s2 s2') ->
  (* c ~ c : Rel s<1> s<2> ==> Rel s<1> s<2> *)
  (forall c s1 s2 s1' s2',
     Rel s1 s1' ->
     sem s1  c s2 ->
     sem s1' c s2' ->
     Rel s2 s2') ->
  sem s1 c                   s2  ->
  forall s2',
    sem s1 (map_pos_cmd p f c) s2' ->
    Rel s2 s2'.
Proof.
Admitted.

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