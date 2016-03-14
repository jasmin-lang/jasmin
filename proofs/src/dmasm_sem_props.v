(* * Prove properties about semantics of dmasm input language *)

(* ** Imports and settings *)
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat ssrint ssralg.
From mathcomp Require Import choice fintype eqtype div seq zmodp finset.
Require Import Coq.Logic.Eqdep_dec.
Require Import finmap strings  dmasm_utils dmasm_type dmasm_var dmasm_sem.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.

Local Open Scope ring_scope.
Local Open Scope fun_scope.
Local Open Scope vmap.
Local Open Scope fset.
Local Open Scope seq_scope.

Import W.

(* ** Equivalence relations on vmaps
 * -------------------------------------------------------------------- *)

Definition vmap_eq_on (s : {fset var}) (vm1 vm2 : vmap) :=
  forall k, k \in s -> vm1.[k] = vm2.[k].

Definition vmap_eq_except (s : {fset var}) (vm1 vm2 : vmap) :=
  forall k, k \notin s -> vm1.[k] = vm2.[k].

Notation "vm1 = vm2 [&& s ]" := (vmap_eq_on s vm1 vm2) (at level 70, vm2 at next level,
  format "'[hv ' vm1  '/' = vm2  '/' [&&  s ] ']'").

Notation "vm1 = vm2 [\ s ]" := (vmap_eq_except s vm1 vm2) (at level 70, vm2 at next level,
  format "'[hv ' vm1  '/' =  vm2  '/' [\ s ] ']'").

Lemma vmap_eq_except_on vm1 vm2 s1 s2:
  [disjoint s2 & s1] ->
  vm1 = vm2 [\ s1] ->
  vm1 = vm2 [&& s2].
Proof.
  move=> /fdisjointP Hdis Hexc;rewrite /vmap_eq_on => id Hin.
  by apply Hexc; apply Hdis.
Qed.

Lemma vmap_eq_except_on_combine vm1 vm2 s1:
  vm1 = vm2 [\ s1] ->
  vm1 = vm2 [&& s1] ->
  vm1 =v vm2.
Proof.
  rewrite /Fv.ext_eq => Hexc Hon id.
  by case: (boolP (id \in s1));[apply Hon | apply Hexc].
Qed.

(* ** Identifier occurences
 * -------------------------------------------------------------------- *)

Fixpoint ids_pexpr st (pe : pexpr st) :=
  match pe with
  | Pvar   x                    => [fset x]
  | Pconst _                    => fset0
  | Papp1 _ _ _ pe              => ids_pexpr pe
  | Papp2 _ _ _ _ pe1 pe2       => ids_pexpr pe1 `|` ids_pexpr pe2
  | Papp3 _ _ _ _ _ pe1 pe2 pe3 => ids_pexpr pe1 `|` ids_pexpr pe2 `|` ids_pexpr pe3
  end.

Fixpoint ids_rval st (rv : rval st) :=
  match rv with
  | Rvar  x               => [fset x]
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

Definition ids_cmd_g (ids_instr : instr -> {fset var}) : cmd -> {fset var} :=
  fix ids_cmd_g (c : cmd) :=
    match c with
    | [::] => fset0
    | instr::instrs => ids_instr instr `|` ids_cmd_g instrs
    end.

Fixpoint ids_instr (i : instr) : {fset var} := 
  match i with
  | Cbcmd  bc             => ids_bcmd bc
  | Cif pe c1 c2          => ids_pexpr pe `|` ids_cmd_g ids_instr c1 `|` ids_cmd_g ids_instr c2
  | Cfor v rng c          => ids_rval v `|` ids_range rng `|` ids_cmd_g ids_instr c
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

Fixpoint read_instr (i : instr) : {fset var} := 
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

Fixpoint write_instr (i : instr) : {fset var} := 
  match i with
  | Cbcmd  bc             => write_bcmd bc
  | Cif pe c1 c2          => ids_cmd_g write_instr c1 `|` ids_cmd_g write_instr c2
  | Cfor v rng c          => ids_rval v `|` ids_cmd_g write_instr c
  | Ccall sta str rv fd a => ids_rval rv
  end.

Notation write_cmd := (ids_cmd_g write_instr).

Definition write_fdef sta str (fd : fundef sta str) :=
  ids_rval (fd_arg fd) `|` write_cmd (fd_body fd).

(* ** Variable renaming
 * -------------------------------------------------------------------- *)

Notation renaming := (ident -> ident).

Definition rn_var (pi : renaming) (v : var) :=
  Var v.(vtype) (pi v.(vname)).

Fixpoint rn_pexpr st (pi : renaming) (pe : pexpr st) :=
  match pe in pexpr st0 return pexpr st0 with
  | Pvar          v              => Pvar (rn_var pi v)
  | Pconst        c              => Pconst c
  | Papp1 _ _     op pe1         => Papp1 op (rn_pexpr pi pe1)
  | Papp2 _ _ _   op pe1 pe2     => Papp2 op (rn_pexpr pi pe1) (rn_pexpr pi pe2)
  | Papp3 _ _ _ _ op pe1 pe2 pe3 => 
    Papp3 op (rn_pexpr pi pe1) (rn_pexpr pi pe2) (rn_pexpr pi pe3)
  end.

Fixpoint rn_rval st (pi : renaming) (rv : rval st) : rval st :=
  match rv with
  | Rvar     v            => Rvar (rn_var pi v)
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
    Cfor (rn_rval pi v) (rn_range pi rng) [seq rn_instr pi i | i <- c]
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
  Fv.empty (fun id => vm.[rn_var pi id]%vmap).

Lemma rn_var_can (pi:renaming) pi_inv:
  cancel pi_inv pi -> cancel (rn_var pi_inv) (rn_var pi).
Proof. by move=> Hcan [t id];rewrite /rn_var /= Hcan. Qed.

Lemma rn_vmap_get pi vm x:
  (rn_vmap pi vm).[x] = vm.[rn_var pi x].
Proof. by done. Qed.

Definition rn_tosubst pi (ts : W.tosubst) :=
  {| W.ts_v := rn_var pi ts.(W.ts_v); W.ts_to := ts.(W.ts_to) |}.

Definition rn_estate pi s :=
  {| emem := s.(emem); evm := rn_vmap pi s.(evm) |}.

(* ** Commuting renamings
 * -------------------------------------------------------------------- *)

Lemma rn_pexpr_eq st (pi pi_inv : renaming) (vm : vmap) (pe : pexpr st):
  cancel pi_inv pi ->
  sem_pexpr vm pe = sem_pexpr (rn_vmap pi vm) (rn_pexpr pi_inv pe).
Proof.
  move => Hcan; elim pe => //= [[t id] | ????<-| ?????<-?<-|??????<-?<-?<- ] //.
  by rewrite rn_vmap_get /rn_var /= Hcan. 
Qed.

Lemma rn_range_eq (pi pi_inv : renaming) (vm : vmap) (rng : range):
  cancel pi_inv pi ->
  sem_range vm rng = sem_range (rn_vmap pi vm) (rn_range pi_inv rng).
Proof.
  move => Hcan;case: rng=> -[] dir pe1 pe2.
  by rewrite /sem_range /= -2!(rn_pexpr_eq _ _ Hcan).
Qed.

Lemma rn_vmap_set pi pi_inv vm x (v : st2ty x.(vtype)):
  cancel pi_inv pi ->
  cancel pi     pi_inv ->
  ((rn_vmap pi vm).[rn_var pi_inv x <- v]) = (rn_vmap pi vm.[x <- v]).
Proof.
  move=> Hcan1 Hcan2;apply Fv.map_ext => y.
  rewrite !rn_vmap_get.
  case: (rn_var pi_inv x =P y) => [ <- | /eqP neq].
  + by rewrite Fv.setP_eq /rn_var Hcan1 /=;case:x v => /=???;rewrite Fv.setP_eq.
  rewrite !Fv.setP_neq ?rn_vmap_get //. 
  by apply: contra_neq neq=>->;apply rn_var_can.
Qed.

Lemma write_subst_rn_val st pi (rv : rval st) (v : st2ty st):
  forall substs,
    write_subst (rn_rval pi rv) v [seq rn_tosubst pi ts | ts <- substs ]
  = [seq rn_tosubst pi ts | ts <- write_subst rv v substs].
Proof.
  elim:rv v => [x | st1 st2 r1 Hr1 r2 Hr2] v substs //=.
  by rewrite Hr1 Hr2.
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
  move=> sub subs Hind; case sub => ts_id ts_v //=.
  by rewrite Hind rn_vmap_set.
Qed.

Lemma rn_write_rval_eq pi pi_inv vm {st} (rv : rval st) (v : st2ty st):
  cancel pi_inv pi ->
  cancel pi     pi_inv ->
    write_rval (rn_vmap pi vm) (rn_rval pi_inv rv) v
  = rn_vmap pi (write_rval vm rv v).
Proof.
  move=> Hcan1 Hcan2; apply Fv.map_ext => id2 /=.
  rewrite /write_rval write_subst_rn_val_nil.
  by rewrite (rn_write_vmap_eq _ _ Hcan1 Hcan2).
Qed.

(* ** Cancelling renamings
 * -------------------------------------------------------------------- *)

Lemma rn_vmap_id f vm:
  f =1 id -> rn_vmap f vm = vm.
Proof.
  move=> Hid; apply Fv.map_ext.
  rewrite /Fv.ext_eq /rn_vmap /Fv.get /Fv.map //= => x.
  by case vm=> //= m; rewrite /rn_var Hid; case x.
Qed.

Lemma rn_var_id f (v : var):
  f =1 id -> rn_var f v = v.
Proof.
  move=> Hid. elim v=> vt vn //=.
  by rewrite /rn_var //= Hid.
Qed.

Lemma rn_rval_id st f (rv : rval st):
  f =1 id -> rn_rval f rv = rv.
Proof.
  move=> Hid. elim rv=> //=.
  + by move=> x; elim x => vt vn; rewrite /rn_var //= Hid.
  + by move=> st1 st2 rv1 H1 rv2 H2; rewrite H1 H2.
Qed.

Lemma rn_pexpr_id {st} f (pe : pexpr st):
  f =1 id -> rn_pexpr f pe = pe.
Proof.
  move=> Hid. elim pe => //=.
  + by move=> x; elim x => vt vn; rewrite /rn_var //= Hid.
  + by move=> sta str so1 pe1 ->.
  + by move=> st1 st2 str so2 p1 -> p2 ->.
  + by move=> st1 st2 st3 str so3 p1 -> p2 -> p3 ->.
Qed.

Lemma rn_range_id f (r : range):
  f =1 id -> rn_range f r = r.
Proof.
  move=> Hid. case r => dp1 p2. case dp1 => d p1 //=.
  by rewrite !rn_pexpr_id.
Qed.

Lemma rn_bcmd_id f bc:
  f =1 id -> rn_bcmd f bc = bc.
Proof.
  move=> Hid. elim bc=> //=.
  + by move=> st rv pe; rewrite (rn_rval_id _ Hid) (rn_pexpr_id _ Hid).
  + by move=> rv pe; rewrite (rn_rval_id _ Hid) (rn_pexpr_id _ Hid).
  + by move=> pe1 pe2; rewrite !(rn_pexpr_id _ Hid).
Qed.

Lemma rn_cmd_id f cmd:
  f =1 id ->
  rn_cmd f cmd = cmd.
Proof.
  move=> Hid.
  apply (@cmd_ind
    (fun c => rn_cmd f c = c) (fun sta str fd => true)) => //.
  + move=> i c //= Hi Hc //=.
    by move: Hi; case => ->; rewrite Hc.
  + by move=> bc //=; rewrite rn_bcmd_id.
  + move=> pe c1 c2 H1 H2.
    rewrite /rn_cmd in H1; rewrite /rn_cmd in H2.
    by rewrite /= H1 H2 rn_pexpr_id.
  + move=> i rn c //=; rewrite /rn_cmd => ->.
    by rewrite (rn_rval_id _ Hid) (rn_range_id _ Hid).
  + move=> sta str x fd a //= Hfd.
    by rewrite rn_rval_id // rn_pexpr_id //.
Qed.

Lemma rn_vmap_comp f g vm:
  rn_vmap f (rn_vmap g vm) = rn_vmap (g \o f) vm.
Proof.
  apply Fv.map_ext.
  by rewrite /Fv.ext_eq /rn_vmap /Fv.get /Fv.map //=.
Qed.

Lemma rn_var_comp f g v:
  rn_var f (rn_var g v) = rn_var (f \o g) v.
Proof.
  by case v=> tv tn //=; rewrite /rn_var /=.
Qed.

Lemma rn_rval_comp st f g (rv : rval st):
  rn_rval f (rn_rval g rv) = rn_rval (f \o g) rv.
Proof.
  by elim rv => //=; move=> st1 st2 rv1 -> rv2 ->.
Qed.

Lemma rn_pexpr_comp st f g (pe : pexpr st):
  rn_pexpr f (rn_pexpr g pe) = rn_pexpr (f \o g) pe.
Proof.
  elim pe => //=.
  + by move=> sta str so1 pe1 ->.
  + by move=> st1 st2 str so2 p1 -> p2 ->.
  + by move=> st1 st2 st3 str so3 //= p1 -> p2 -> p3 ->.
Qed.

Lemma rn_range_comp f g r:
  rn_range f (rn_range g r) = rn_range (f \o g) r.
Proof.
  case r => dp1 p2; case dp1=> d p1 //=.
  by rewrite !rn_pexpr_comp.
Qed.

Lemma rn_bcmd_comp f g bc:
  rn_bcmd f (rn_bcmd g bc) = rn_bcmd (f \o g) bc.
Proof.
  elim bc => //=.
  + by move=> st rv pe; rewrite rn_pexpr_comp rn_rval_comp.
  + by move=> rv pe; rewrite rn_pexpr_comp rn_rval_comp.
  + by move=> pe1 pe2; rewrite !rn_pexpr_comp.
Qed.

Lemma rn_cmd_comp f g cmd:
  rn_cmd f (rn_cmd g cmd) = rn_cmd (f \o g) cmd.
Proof.
  apply (@cmd_ind
    (fun c => rn_cmd f (rn_cmd g c) = rn_cmd (f \o g) c) (fun sta str fd => true)) => //.
  + move=> i c //= Hi Hc //=.
    by move: Hi; case => ->; rewrite Hc.
  + by move=> bc //=; rewrite rn_bcmd_comp.
  + move=> pe c1 c2 H1 H2 //=.
    rewrite /rn_cmd in H1; rewrite /rn_cmd in H2.
    by rewrite /= H1 H2 rn_pexpr_comp.
  + move=> i rn c //=; rewrite /rn_cmd => ->.
    by rewrite rn_rval_comp rn_range_comp.
  + move=> sta str x fd a //= Hfd.
    by rewrite rn_rval_comp // rn_pexpr_comp //.
Qed.

Lemma rn_vmap_cancel pi pi_inv vm:
  cancel pi pi_inv -> rn_vmap pi (rn_vmap pi_inv vm) = vm.
Proof.
  by move=> Hcan; rewrite rn_vmap_comp rn_vmap_id.
Qed.

Lemma rn_cmd_cancel pi pi_inv cmd:
  cancel pi_inv pi ->
  rn_cmd pi (rn_cmd pi_inv cmd) = cmd.
Proof.
  by move=> Hcan; rewrite rn_cmd_comp rn_cmd_id.
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
                (rn_rval pi_inv v) ws (rn_estate pi s1) (rn_cmd pi_inv c)
                (rn_estate pi s2))
           (fun sta str m1 m2 fb fa a r => true)).
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
  + move=> sta str m1 vm1 m2 rv_res fd pe_arg res.
    move=> ragr Hok Hscall Htrue.
    rewrite /rn_estate /=.
    rewrite -(rn_write_rval_eq _ _ _ Hcan1 Hcan2).
    apply (Ecall).
    + by rewrite -(rn_pexpr_eq _ _ Hcan1).
    + by rewrite -(rn_pexpr_eq _ _ Hcan1).
  + move=> s3 s4 iv rng c_for ws Hsrng Hsc_for Hs_for.
    rewrite /=.
    apply (EFor (ws:=ws)); last done.
    by rewrite -(rn_range_eq _ _ Hcan1).
  + by move=> s3 c_for iv; constructor.
  + move=> s3 s4 s5 c_for w ws iv ac Hsac Hsac_rn Hsfor Hsfor_rn.
    by apply (EForOne (s2:=(rn_estate pi s4))).
  + done.
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

Lemma rn_sem_eq pi pi_inv m1 m2 vm1 vm2 c:
  cancel pi_inv pi ->
  cancel pi     pi_inv ->
  sem {| emem := m1; evm := vm1 |} c {| emem := m2; evm := vm2 |}
  <->
  sem {| emem := m1; evm := rn_vmap pi vm1 |}
      (rn_cmd pi_inv c)
      {| emem := m2; evm := rn_vmap pi vm2 |}.
Proof.
  move=> Hcan1 Hcan2.
  split.
  + by apply rn_sem_equiv.
  + rewrite -{2}(rn_vmap_cancel vm1 Hcan1).
    rewrite -{2}(rn_vmap_cancel vm2 Hcan1).
    rewrite -{2}(rn_cmd_cancel  c   Hcan1).
    by apply rn_sem_equiv.
Qed.    

Lemma rn_sem_fail_equiv_aux pi pi_inv s1 c:
  cancel pi_inv pi ->
  cancel pi     pi_inv ->
  sem_fail s1 c ->
  sem_fail (rn_estate pi s1) (rn_cmd pi_inv c).
Proof.
  move=> Hcan1 Hcan2; case s1 => m1 vm1.
  rewrite /sem_fail => Hfail s2.
  case s2 => m2 vm2 //=.
  rewrite (rn_sem_eq _ _ _ _ _ Hcan2 Hcan1).
  rewrite (rn_vmap_cancel _ Hcan1) (rn_cmd_cancel c Hcan1).
  by apply Hfail.
Qed.  

Lemma rn_sem_call_equiv {sta str} pi pi_inv m1 m2 l (fres : pexpr str)
    (arg :st2ty sta) (res : st2ty str):
  cancel pi_inv pi ->
  cancel pi     pi_inv ->
  sem_call m1 m2 l fres arg res ->
  sem_call m1 m2 [seq rn_instr pi_inv i | i <- l] (rn_pexpr pi_inv fres) arg res.
Proof.
  move=> Hcan1 Hcan2 Hscall.
  inversion Hscall; subst; clear Hscall.
  rewrite /rres.
  move: (@rn_pexpr_eq str pi pi_inv vm2 fres Hcan1) => WW.
  rewrite WW.
  apply (EcallRun (vm0:=rn_vmap pi vm0) (farg:=rn_rval pi_inv farg0)).
  + move => vm3. move: (H7 (rn_vmap pi_inv vm3)). elim=> m3. elim=> vm4. case => [Hsem Hok]. 
    exists m3. exists (rn_vmap pi vm4).
    rewrite -(rn_vmap_cancel vm3 Hcan2).
    split.
    + rewrite /= (rn_write_rval_eq _ _ _ Hcan1 Hcan2).
      by apply (rn_sem_equiv Hcan1 Hcan2).
    + by rewrite -(@rn_pexpr_eq str pi pi_inv vm4 fres Hcan1).
  + rewrite /vm1 in H8.
    rewrite /= (rn_write_rval_eq _ _ _ Hcan1 Hcan2).
    by apply (rn_sem_equiv Hcan1 Hcan2).
  + by rewrite -WW.
Qed.

Lemma rn_sem_equiv_call sta str (s1 s2 : estate) pi pi_inv (fd : fundef sta str) rv_res pe_arg:
  cancel pi_inv pi ->
  cancel pi     pi_inv ->
  sem s1 [:: Ccall rv_res fd                  pe_arg] s2 ->
  sem s1 [:: Ccall rv_res (rn_fdef pi_inv fd) pe_arg] s2.
Proof.
  move=> Hcan1 Hcan2.
  destruct fd => /= Hsem.
  apply (Eseq (s2:=s2)); last apply Eskip.
  inversion Hsem; subst; clear Hsem.
  inversion H4; subst; clear H4.
  inversion H2; subst; clear H2.
  apply (inj_pair2_eq_dec _ LEM) in H5.
  apply (inj_pair2_eq_dec _ LEM) in H5.
  rewrite H5 //= in H8. clear H5 fd1.
  apply (inj_pair2_eq_dec _ LEM) in H4.
  rewrite H4. clear H4 rv_res1.
  apply (inj_pair2_eq_dec _ LEM) in H6.
  rewrite -H6. clear H6 pe_arg.
  apply (Ecall) => //.
  rewrite /= -/rarg.
  by apply (rn_sem_call_equiv Hcan1 Hcan2).
Qed.

(* ** Upper bound on variables that are changed
 * -------------------------------------------------------------------- *)

Lemma eq_except_sub s1 s2 vm1 vm2:
  s1 `<=` s2 ->
  vm1 = vm2 [\ s1 ] ->
  vm1 = vm2 [\ s2 ].
Proof.
  rewrite /fsubset => /eqP Hsub; rewrite /vmap_eq_except => Heq i Hnot.
  by apply Heq;rewrite -Hsub in_fsetI (negPf Hnot) andbC.
Qed.

Lemma eq_except_trans vm2 vm1 vm3 s:
  vm1 = vm2 [\ s ] ->
  vm2 = vm3 [\ s ] ->
  vm1 = vm3 [\ s ].
Proof.
  (do 3 rewrite /vmap_eq_except) => W1 W2 k Hnotin.
  by rewrite W1 // W2.  
Qed.

Lemma eq_except_set vm id (v : st2ty id.(vtype)) :
  vm = vm.[id <- v] [\ [fset id]].
Proof.
  rewrite /vmap_eq_except => id2;case: (id =P id2)=> [<- | /eqP ?].
  + by rewrite fset11.
  by rewrite Fv.setP_neq.
Qed.

Lemma eq_except_set_imp vm1 vm2 s id (v : st2ty id.(vtype)) :
  vm1 = vm2 [\ s] ->
  vm1.[id <- v] = vm2.[id <- v] [\ s].
Proof.
  rewrite /vmap_eq_except => Heq k1 Hnotin.
  case (id =P k1) => [<- | /eqP neq].
  + by rewrite !Fv.setP_eq.
  by rewrite !Fv.setP_neq //;apply Heq.
Qed.

Lemma write_vmap_eq_except_aux vm substs:
  vm = write_vmap vm substs [\ seq_fset [seq ts.(ts_v) | ts <- substs ]].
Proof.
  elim: substs => //= -[] x v ss Hrec;rewrite fset_cons /= => y.
  rewrite in_fsetU Bool.negb_orb in_fset1 eq_sym => /andP -[??]. 
  by rewrite Fv.setP_neq // Hrec.
Qed.

Lemma write_subst_arg st (rv : rval st) (v : st2ty st) (l : seq tosubst):
  write_subst rv v l = (write_subst rv v [::]) ++ l.
Proof.
  elim: rv v l => /= [// | st1 st2 rv1 Hrv1 rv2 Hrv2] v ls.
  by rewrite Hrv1 Hrv2 catA -Hrv2.
Qed.

Lemma seq_fset_cat (aT : choiceType) (l1 : seq aT) (l2 : seq aT):
  seq_fset (l1 ++ l2) = seq_fset l1 `|` seq_fset l2.
Proof.
  elim: l1 => [ | x xs].
  + by rewrite cat0s !(fset0U,seq_fset0).
  rewrite cat_cons /= !fset_cons; move=> ->.
  by rewrite fsetUA.
Qed.

Lemma ids_rval_write_substs st (rv : rval st) (v : st2ty st):
  ids_rval rv = seq_fset [seq ts.(ts_v) | ts <- write_subst rv v [::] ].
Proof.
  elim: rv v => [x | st1 st2 rv1 Hrv1 rv2 Hrv2] v //=.
  rewrite write_subst_arg map_cat seq_fset_cat.
  by rewrite (Hrv1 v.1) (Hrv2 v.2) fsetUC.
Qed.

Lemma write_rval_eq_except st vm (rv : rval st) (v : st2ty st):
  vm = write_rval vm rv v [\ids_rval rv].
Proof.
  rewrite /write_rval (ids_rval_write_substs rv v).
  by apply write_vmap_eq_except_aux.
Qed.

Lemma write_vmap_eq_except_imp vm1 vm2 s substs:
  vm1 = vm2 [\s ] ->
  write_vmap vm1 substs = write_vmap vm2 substs [\ s].
Proof.
  generalize vm1 vm2. elim substs => //.
  move=> sub subs Hind vm3 vm4 Heq.
  rewrite /=; case sub => st_ id_ v_.
  by apply eq_except_set_imp; apply Hind.
Qed.

Lemma write_rval_eq_except_imp st vm1 vm2 (rv : rval st) (v : st2ty st) s:
  vm1 = vm2 [\s ] ->
  write_rval vm1 rv v = write_rval vm2 rv v [\ s].
Proof.
  by rewrite /write_rval; apply write_vmap_eq_except_imp.
Qed.

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
           (fun v ws s1 c s2 => s1.(evm) = s2.(evm) [\ ids_rval v `|` write_cmd c])
           (fun sta str m1 m2 fb fres arg res => true)).
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
  + move=> sta str m1 vm1 m2 rv_res fd pe_arg res rarg Hok Hscall Htrue.
    by rewrite /=; apply write_rval_eq_except.
  + by move=> s3 s4 iv rng cc ws Hrng Hcc_ws Heq1.
  + done.
  + move=> s3 s4 s5 cc w ws iv ac Hac Heq1 Hcc_ws Heq2 Hcc_w_ws.
    apply (eq_except_sub (s2:=ids_rval iv `|` write_cmd cc)) in Heq1.
    + by apply (eq_except_trans Heq1 Heq2).
    rewrite /ac /= {ac Hac Heq1 Hcc_ws Heq2}; case Heq : _ / iv => //=.
    apply fsubset_refl.
  + done.
Qed.

(* ** Equivalent state leads to equivalent state
 * -------------------------------------------------------------------- *)

Lemma sem_ids_unchanged (s1 s1' s2 s2': estate) c:
  s1.(emem) = s1'.(emem) /\ s1.(evm) = s1'.(evm) [&& read_cmd c] ->
  sem s1  c s2 ->
  exists s2', 
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
Proof. rewrite /vmap_eq_except => Heq id Hnotin. rewrite Heq; done. Qed.

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
    admit.
    (*
    apply (Ecall (vmc0:=vm1)) => //.
    move: H1 Hok => /=. case (sem_pexpr vm1 pe_arg) => v //= Heq Ht {Ht}.
    move: Heq; case => Heq. rewrite -Heq in Hsl.
    move: H2 Hok2 => /=. case (sem_pexpr (evm s2_1) p) => v2 //= Heq2 Ht {Ht}.
    move: Heq2; case. case s2 => m2 vm2; case => Heq3.
    rewrite /= -Heq3 /=.
    have ->: {| emem := emem s2_1; evm := evm s2_1 |} = s2_1. case s2_1; done.
    done. 
    *)
  split => //.
  rewrite /=.
  have W: evm s2_1 = evm s1 [\ids_rval r `|` write_cmd l].
    have Q1: evm s1 = evm s3 [\ids_rval r `|` write_cmd l].
(*      apply (@eq_except_sub _ _ (ids_rval r)). apply fsubsetUl.
      by apply (sem_bcmd_eq_except H1).
    have Q2: evm s3 = evm s2_1 [\ids_rval r `|` write_cmd l].
      apply (@eq_except_sub _ _ (write_cmd l)). apply fsubsetUr.
      by apply (sem_eq_except Hsl).
    apply eq_except_sym.
    by apply (eq_except_trans Q1 Q2).
  have WW: evm s2 = write_rval (evm s1) rv_res (rdflt_ (sem_pexpr (evm s2_1) p))
             [\ids_rval r `|` write_cmd l]. 
    move: H2 => /=. case (sem_pexpr (evm s2_1) p) => v //=. case. case s2 => m2 vm2 /=.
    case => HH <-. rewrite /write_rval.
    by apply write_vmap_eq_except_imp.
  apply WW. *)
Admitted.

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

Notation subst := (forall (x:var), pexpr x.(vtype)).

Fixpoint subst_pexpr st (s : subst) (pe : pexpr st) :=
  match pe in pexpr st_ return pexpr st_ with
  | Pvar          v              => s  v
  | Pconst        c              => Pconst c
  | Papp1 _ _     op pe1         => Papp1 op (subst_pexpr s pe1)
  | Papp2 _ _ _   op pe1 pe2     => Papp2 op (subst_pexpr s pe1) (subst_pexpr s pe2)
  | Papp3 _ _ _ _ op pe1 pe2 pe3 => 
    Papp3 op (subst_pexpr s pe1) (subst_pexpr s pe2) (subst_pexpr s pe3)
  end.

Definition subst_bcmd (s : subst) (bc : bcmd) :=
  match bc with
  | Assgn st rv pe       => Assgn rv (subst_pexpr s pe)
  | Load rv pe_addr      => Load rv (subst_pexpr s pe_addr)
  | Store pe_addr pe_val => Store (subst_pexpr s pe_addr) (subst_pexpr s pe_val)
  end.

Definition subst_range (s : subst) (r : range) :=
  let: (dir,pe1,pe2) := r in (dir,subst_pexpr s pe1,subst_pexpr s pe2).