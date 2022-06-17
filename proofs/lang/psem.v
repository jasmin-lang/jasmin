(* * Jasmin semantics with “partial values”. *)

(* ** Imports and settings *)
From mathcomp Require Import all_ssreflect all_algebra.
Require Import Psatz xseq.
Require Export expr expr_facts low_memory syscall_sem sem.
Import Utf8.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope Z_scope.
Local Open Scope seq_scope.
Local Open Scope vmap_scope.

(* ** Interpretation of types
 * -------------------------------------------------------------------- *)

Record pword s :=
  { pw_size: wsize;
    pw_word : word pw_size;
    pw_proof : (pw_size <= s)%CMP }.

Definition psem_t (t : stype) : Type :=
  match t with
  | sword s => pword s
  | _ => sem_t t
  end.

(* ** Default values
 * -------------------------------------------------------------------- *)

Definition pword_of_word (s:wsize) (w:word s) : pword s :=
  {|pw_word := w; pw_proof := cmp_le_refl s|}.

Definition to_pword (s: wsize) (v: value) : exec (pword s) :=
   match v with
   | Vword s' w =>
    ok (
     if Sumbool.sumbool_of_bool (s' ≤ s)%CMP is left heq
     then {| pw_word := w ; pw_proof := heq |}
     else pword_of_word (zero_extend s w))
   | Vundef (sword _) _ => undef_error
   | _                  => type_error
   end.

Definition pof_val t : value -> exec (psem_t t) :=
  match t return value -> exec (psem_t t) with
  | sword s => to_pword s
  | t0 => of_val t0
  end.

Definition pto_val t : psem_t t -> value :=
  match t return psem_t t -> value with
  | sword s => fun w => Vword (pw_word w)
  | t0 => @to_val t0
  end.

Lemma to_pwordI s v w :
  to_pword s v = ok w → exists s', exists2 w',
    v = @Vword s' w' & w = if Sumbool.sumbool_of_bool (s' ≤ s)%CMP is left heq
        then {| pw_word := w' ; pw_proof := heq |}
        else pword_of_word (zero_extend s w').
Proof. by case: v => // [ | [] // ] s' w' /= [<-]; exists s', w'. Qed.

Lemma to_pword_u ws (w : word ws) :
  to_pword ws (Vword w) = ok (pword_of_word w).
Proof. by rewrite /= sumbool_of_boolET. Qed.

Lemma to_pword_undef w v :
  to_pword w v = undef_error -> v = undef_w.
Proof.
  by case: v => //= -[] // >; rewrite undef_x_vundef.
Qed.

Lemma type_of_val_to_pword sz v w :
  type_of_val v = sword sz → to_pword sz v = ok w →
  ∃ w' : word sz, w = pword_of_word w' ∧ v = Vword w'.
Proof.
  move=> /type_of_valI [] [w' ->] //=.
  by rewrite sumbool_of_boolET => - [<-]; exists w'.
Qed.

Lemma subtype_of_val_to_pword ws v (w : pword ws) :
  subtype (sword ws) (type_of_val v) ->
  to_pword ws v = ok w ->
  exists ws' (w' : word ws'),
    [/\ (ws <= ws')%CMP, w = pword_of_word (zero_extend ws w') & v = Vword w'].
Proof.
  move=> /subtypeEl[ws' hty] /[dup] hle.
  rewrite cmp_le_eq_lt => /orP [].
  + rewrite -cmp_nle_lt => /negPf hlt.
    move=> /to_pwordI[ws'' [w' ? ]]; subst v.
    case: hty => ?; subst ws''.
    rewrite sumbool_of_boolEF => ->.
    by exists ws', w'.
  move=> /eqP ?; subst ws' => hto.
  have [w' [hw hv]] := (type_of_val_to_pword hty hto).
  exists ws, w'; split=> //.
  by rewrite zero_extend_u.
Qed.

(* ** Variable map
 * -------------------------------------------------------------------- *)

#[export] Instance vmr_subtype : VmapRel :=
  {| vm_rel := Basics.flip subtype
   ; vm_relxx := subtype_refl
   ; vm_supeq := fun _ x e => eq_rect _ (subtype x) (subtype_refl x) _ (esym (eqP e))
   ; vm_subcomp := fun x y s => eq_rect _ _ (@subtype_compat y x s) _ (compat_typeC y x) |}.

Lemma compat_typerel_undef t v : compat_type t (type_of_val v) ->
  typerel_undef vm_rel t (rdflt v (truncate_defined_val t v)).
Proof.
  (rewrite /typerel_undef /truncate_defined_val; case: v => >;
    last by rewrite of_val_undef => /[dup]?->)
    => /compat_typeE => [|||/is_swordP[?]] -> //=.
  + by rewrite sumbool_of_boolET /Basics.flip /=.
  case: Result.rmapP => [? _|? /truncate_word_errP/proj2 h]; rewrite /Basics.flip //=.
  exact: cmp_lt_le.
Qed.

Lemma vmap_get_set_get vm vm' x :
  Vmap.set_var vm x (Vmap.get_var vm x) = ok vm' ->
  Vmap.get_var vm' x = Vmap.get_var vm x.
Proof.
  move=> /Vmap.set_varP_eq ->; case: Result.rdfltP => // ? /truncate_defined_valE H.
  case: Vmap.get_var H (Vmap.get_varP vm x) => > []
    => [|||? [? [+ /truncate_wordP[/cmp_le_antisym Ha ->]]]] => -> -> // /typerel_undefE.
  by rewrite /= /Basics.flip /= => /Ha{Ha} ?; subst; f_equal; exact: zero_extend_u.
Qed.

Lemma get_gvar_glob gd x vm : is_glob x -> get_gvar gd vm x = get_global gd (gv x).
Proof. by rewrite /get_gvar /is_lvar /is_glob => /eqP ->. Qed.

Lemma get_gvar_nglob gd x vm :
  ~~is_glob x -> get_gvar gd vm x = ok (Vmap.get_var vm (gv x)).
Proof. by rewrite /get_gvar is_lvar_is_glob => ->. Qed.

(* ** Parameter expressions
 * -------------------------------------------------------------------- *)

Section WITH_POINTER_DATA.
Context {pd: PointerData} {syscall_state : Type} {sc_sem : syscall_sem syscall_state}.

Section SEM_PEXPR.

Context (gd: glob_decls).

Fixpoint sem_pexpr (s:estate) (e : pexpr) : exec value :=
  match e with
  | Pconst z => ok (Vint z)
  | Pbool b  => ok (Vbool b)
  | Parr_init n => ok (Varr (WArray.empty n))
  | Pvar v => get_gvar gd s.(evm) v
  | Pget aa ws x e =>
      Let (n, t) := gd, s.[x] in
      Let i := sem_pexpr s e >>= to_int in
      Let w := WArray.get aa ws t i in
      ok (Vword w)
  | Psub aa ws len x e =>
    Let (n, t) := gd, s.[x] in
    Let i := sem_pexpr s e >>= to_int in
    Let t' := WArray.get_sub aa ws len t i in
    ok (Varr t')
  | Pload sz x e =>
    Let w1 := to_pointer (Vmap.get_var s.(evm) x) in
    Let w2 := sem_pexpr s e >>= to_pointer in
    Let w  := read s.(emem) (w1 + w2)%R sz in
    ok (@to_val (sword sz) w)
  | Papp1 o e1 =>
    Let v1 := sem_pexpr s e1 in
    sem_sop1 o v1
  | Papp2 o e1 e2 =>
    Let v1 := sem_pexpr s e1 in
    Let v2 := sem_pexpr s e2 in
    sem_sop2 o v1 v2
  | PappN op es =>
    Let vs := mapM (sem_pexpr s) es in
    sem_opN op vs
  | Pif t e e1 e2 =>
    Let b := sem_pexpr s e >>= to_bool in
    Let v1 := sem_pexpr s e1 >>= of_val t in
    Let v2 := sem_pexpr s e2 >>= of_val t in
    ok (to_val (if b then v1 else v2))
  end.

Definition sem_pexprs s := mapM (sem_pexpr s).

Definition with_vm (s:estate) vm := 
  {| escs := s.(escs); emem := s.(emem); evm := vm |}.

Definition with_mem (s:estate) m := 
  {| escs := s.(escs); emem := m; evm := s.(evm) |}.

Definition with_scs (s:estate) scs := 
  {| escs := scs; emem := s.(emem); evm := s.(evm) |}.

Definition write_var (x:var_i) (v:value) (s:estate) : exec estate :=
  Let vm := Vmap.set_var s.(evm) x v in
  ok (with_vm s vm).

Definition write_vars xs vs s :=
  fold2 ErrType write_var xs vs s.

Definition write_lval (l:lval) (v:value) (s:estate) : exec estate :=
  match l with
  | Lnone _ ty => if compat_type ty (type_of_val v) then ok s else type_error
  | Lvar x => write_var x v s
  | Lmem sz x e =>
    Let vx := to_pointer (Vmap.get_var (evm s) x) in
    Let ve := sem_pexpr s e >>= to_pointer in
    let p := (vx + ve)%R in (* should we add the size of value, i.e vx + sz * se *)
    Let w := to_word sz v in
    Let m :=  write s.(emem) p w in
    ok (with_mem s m) 
  | Laset aa ws x i =>
    Let (n,t) := s.[x] in
    Let i := sem_pexpr s i >>= to_int in
    Let v := to_word ws v in
    Let t := WArray.set t aa i v in
    write_var x (@to_val (sarr n) t) s
  | Lasub aa ws len x i =>
    Let (n,t) := s.[x] in
    Let i := sem_pexpr s i >>= to_int in
    Let t' := to_arr (Z.to_pos (arr_size ws len)) v in 
    Let t := @WArray.set_sub n aa ws len t i t' in
    write_var x (@to_val (sarr n) t) s
  end.

Definition write_lvals (s:estate) xs vs :=
   fold2 ErrType write_lval xs vs s.

End SEM_PEXPR.

Lemma surj_estate s : s = {| escs := escs s; emem := emem s; evm := evm s |}.
Proof. by case:s. Qed.

Lemma with_vm_same s : with_vm s (evm s) = s.
Proof. by case: s. Qed.

Lemma with_vm_idem s vm1 vm2 : with_vm (with_vm s vm1) vm2 = with_vm s vm2.
Proof. by case: s. Qed.

Lemma with_mem_same s : with_mem s (emem s) = s.
Proof. by case: s. Qed.

Lemma with_mem_idem s m1 m2 : with_mem (with_mem s m1) m2 = with_mem s m2.
Proof. by case: s. Qed.

Lemma with_scs_same s : with_scs s (escs s) = s.
Proof. by case: s. Qed.

Lemma with_scs_idem s scs1 scs2 : with_scs (with_scs s scs1) scs2 = with_scs s scs2.
Proof. by case: s. Qed.

Lemma evm_with_vm s vm : evm (with_vm s vm) = vm.
Proof. by case: s. Qed.

Lemma emem_with_vm s vm : emem (with_vm s vm) = emem s.
Proof. by case: s. Qed.

Lemma escs_with_vm s vm : escs (with_vm s vm) = escs s.
Proof. by case: s. Qed.

Lemma with_vm_inj_vm s vm1 vm2 : with_vm s vm1 = with_vm s vm2 -> vm1 = vm2.
Proof. by rewrite /with_vm => -[]. Qed.

Section WITH_SCS.

  Context (gd: glob_decls) (s1:estate) (scs: syscall_state).

  Let P e : Prop :=
    sem_pexpr gd s1 e = sem_pexpr gd (with_scs s1 scs) e.

  Let Q es : Prop :=
    sem_pexprs gd s1 es = sem_pexprs gd (with_scs s1 scs) es.

  Lemma sem_pexpr_es_with_scs : (∀ e, P e) * (∀ es, Q es).
  Proof.
    apply: pexprs_ind_pair; split; subst P Q => //=; rewrite /sem_pexprs => *;
    repeat match goal with H: _ = _ |- _ => rewrite H // end.
  Qed.

  Definition sem_pexpr_with_scs := fst sem_pexpr_es_with_scs.
  Definition sem_pexprs_with_scs := snd sem_pexpr_es_with_scs.

End WITH_SCS.

(* ** Instructions
 * -------------------------------------------------------------------- *)

Section SEM.

Context `{asmop:asmOp}.
Context {T} {pT:progT T}.

Class semCallParams := SemCallParams {
  init_state : extra_fun_t -> extra_prog_t -> extra_val_t -> estate -> exec estate;
  finalize   : extra_fun_t -> mem -> mem;
  exec_syscall : syscall_state_t -> mem -> syscall_t -> values -> exec (syscall_state_t * mem * values);
  exec_syscallP: forall scs m o vargs vargs' rscs rm vres, 
     exec_syscall scs m o vargs = ok (rscs, rm, vres) ->
     List.Forall2 value_uincl vargs vargs' -> 
     exists2 vres', exec_syscall scs m o vargs' = ok (rscs, rm, vres') & List.Forall2 value_uincl vres vres';
  exec_syscallS: forall scs m o vargs rscs rm vres, 
     exec_syscall scs m o vargs = ok (rscs, rm, vres) ->
     mem_equiv m rm;
}.

Context {sCP : semCallParams}.

Variable P:prog.
Variable ev: extra_val_t.

Notation gd := (p_globs P).

Definition sem_range (s : estate) (r : range) :=
  let: (d,pe1,pe2) := r in
  Let i1 := sem_pexpr gd s pe1 >>= to_int in
  Let i2 := sem_pexpr gd s pe2 >>= to_int in
  ok (wrange d i1 i2).

Definition sem_sopn gd o m lvs args :=
  sem_pexprs gd m args >>= exec_sopn o >>= write_lvals gd m lvs.

Inductive sem : estate -> cmd -> estate -> Prop :=
| Eskip s :
  sem s [::] s

| Eseq s1 s2 s3 i c :
  sem_I s1 i s2 -> sem s2 c s3 -> sem s1 (i::c) s3

with sem_I : estate -> instr -> estate -> Prop :=
| EmkI ii i s1 s2:
  sem_i s1 i s2 ->
  sem_I s1 (MkI ii i) s2

with sem_i : estate -> instr_r -> estate -> Prop :=
| Eassgn s1 s2 (x:lval) tag ty e v v' :
  sem_pexpr gd s1 e = ok v ->
  truncate_val ty v = ok v' →
  write_lval gd x v' s1 = ok s2 ->
  sem_i s1 (Cassgn x tag ty e) s2

| Eopn s1 s2 t o xs es:
  sem_sopn gd o s1 xs es = ok s2 ->
  sem_i s1 (Copn xs t o es) s2

| Esyscall s1 scs m s2 o xs es ves vs:
  sem_pexprs gd s1 es = ok ves →
  exec_syscall s1.(escs) s1.(emem) o ves = ok (scs, m, vs) →
  write_lvals gd (with_scs (with_mem s1 m) scs) xs vs = ok s2 →
  sem_i s1 (Csyscall xs o es) s2

| Eif_true s1 s2 e c1 c2 :
  sem_pexpr gd s1 e = ok (Vbool true) ->
  sem s1 c1 s2 ->
  sem_i s1 (Cif e c1 c2) s2

| Eif_false s1 s2 e c1 c2 :
  sem_pexpr gd s1 e = ok (Vbool false) ->
  sem s1 c2 s2 ->
  sem_i s1 (Cif e c1 c2) s2

| Ewhile_true s1 s2 s3 s4 a c e c' :
  sem s1 c s2 ->
  sem_pexpr gd s2 e = ok (Vbool true) ->
  sem s2 c' s3 ->
  sem_i s3 (Cwhile a c e c') s4 ->
  sem_i s1 (Cwhile a c e c') s4

| Ewhile_false s1 s2 a c e c' :
  sem s1 c s2 ->
  sem_pexpr gd s2 e = ok (Vbool false) ->
  sem_i s1 (Cwhile a c e c') s2

| Efor s1 s2 (i:var_i) d lo hi c vlo vhi :
  sem_pexpr gd s1 lo = ok (Vint vlo) ->
  sem_pexpr gd s1 hi = ok (Vint vhi) ->
  sem_for i (wrange d vlo vhi) s1 c s2 ->
  sem_i s1 (Cfor i (d, lo, hi) c) s2

| Ecall s1 scs2 m2 s2 ii xs f args vargs vs :
  sem_pexprs gd s1 args = ok vargs ->
  sem_call s1.(escs) s1.(emem) f vargs scs2 m2 vs ->
  write_lvals gd (with_scs (with_mem s1 m2) scs2) xs vs = ok s2 ->
  sem_i s1 (Ccall ii xs f args) s2

with sem_for : var_i -> seq Z -> estate -> cmd -> estate -> Prop :=
| EForDone s i c :
  sem_for i [::] s c s

| EForOne s1 s1' s2 s3 i w ws c :
  write_var i (Vint w) s1 = ok s1' ->
  sem s1' c s2 ->
  sem_for i ws s2 c s3 ->
  sem_for i (w :: ws) s1 c s3

with sem_call : syscall_state_t -> mem -> funname -> seq value -> syscall_state_t -> mem -> seq value -> Prop :=
| EcallRun scs1 m1 scs2 m2 fn f vargs vargs' s0 s1 s2 vres :
  get_fundef (p_funcs P) fn = Some f ->
  mapM2 ErrType truncate_val f.(f_tyin) vargs' = ok vargs ->
  init_state f.(f_extra) (p_extra P) ev (Estate scs1 m1 Vmap.empty) = ok s0 ->
  write_vars f.(f_params) vargs s0 = ok s1 ->
  sem s1 f.(f_body) s2 ->
  mapM2 ErrType (fun ty (x:var_i) => truncate_val ty s2.(evm).[x]) f.(f_tyout) f.(f_res) = ok vres ->
  scs2 = s2.(escs) ->
  m2 = finalize f.(f_extra) s2.(emem) ->
  sem_call scs1 m1 fn vargs' scs2 m2 vres.

Lemma semE s c s' :
  sem s c s' ->
  match c with
  | [::] => s' = s
  | i :: c' => exists2 si, sem_I s i si & sem si c' s'
  end.
Proof. by case; eauto. Qed.

Lemma sem_IE s i s' :
  sem_I s i s' ->
  let 'MkI ii r := i in
  sem_i s r s'.
Proof. by case. Qed.

Lemma sem_iE s i s' :
  sem_i s i s' ->
  match i with
  | Cassgn lv _ ty e =>
    ∃ v v',
    [/\ sem_pexpr gd s e = ok v, truncate_val ty v = ok v' & write_lval gd lv v' s = ok s' ]
  | Copn lvs _ op es => sem_sopn gd op s lvs es = ok s'
  | Csyscall xs o es =>
    ∃ scs m ves vs,
    [/\ sem_pexprs gd s es = ok ves, 
        exec_syscall s.(escs) s.(emem) o ves = ok (scs, m, vs) & 
        write_lvals gd (with_scs (with_mem s m) scs) xs vs = ok s']
  | Cif e th el =>
    ∃ b, sem_pexpr gd s e = ok (Vbool b) ∧ sem s (if b then th else el) s'
  | Cfor i (d, lo, hi) c =>
    ∃ vlo vhi,
    [/\ sem_pexpr gd s lo = ok (Vint vlo), sem_pexpr gd s hi = ok (Vint vhi) &
        sem_for i (wrange d vlo vhi) s c s' ]
  | Cwhile a c e c' =>
    ∃ si b,
       [/\ sem s c si, sem_pexpr gd si e = ok (Vbool b) &
                       if b then ∃ sj, sem si c' sj ∧ sem_i sj (Cwhile a c e c') s' else si = s' ]
  | Ccall _ xs f es =>
    ∃ vs scs2 m2 rs,
    [/\ sem_pexprs gd s es = ok vs, 
        sem_call s.(escs) s.(emem) f vs scs2 m2 rs &
        write_lvals gd (with_scs (with_mem s m2) scs2) xs rs = ok s']
  end.
Proof.
  case => {s i s'} //.
  - by move => s s' x _ ty e v v' hv hv' hw; exists v, v'.
  - by move => s scs m s' xs o es ves vs h1 h2 h3; exists scs, m, ves, vs.
  - by move => s s' e th el he hth; exists true.
  - by move => s s' e th el he hel; exists false.
  - by move => s si sj s' c e c' hc he hc' hrec; exists si, true; constructor => //; exists sj.
  - by move => s s' c e c' hc he; exists s', false.
  - by move => s s' i d lo hi c vlo vhi hlo hhi hc; exists vlo, vhi.
  by move => s scs m s' _ xs f es vs rs hvs h hrs; exists vs, scs, m, rs.
Qed.

Lemma sem_forE i ws s c s' :
  sem_for i ws s c s' →
  if ws is w :: ws then
    exists s1 s2,
      [/\
       write_var i (Vint w) s = ok s1,
       sem s1 c s2 &
       sem_for i ws s2 c s' ]
  else s' = s.
Proof.
  case => { i ws s c s' } // s s1 s2 s' i w ws c ok_s1 exec_c ih.
  by exists s1, s2.
Qed.

Lemma sem_callE scs1 m1 fn vargs' scs2 m2 vres :
  sem_call scs1 m1 fn vargs' scs2 m2 vres ->
  ∃ f,
    get_fundef (p_funcs P) fn = Some f ∧
  ∃ vargs s0 s1 s2,
  [/\
    mapM2 ErrType truncate_val f.(f_tyin) vargs' = ok vargs,
    init_state f.(f_extra) (p_extra P) ev (Estate scs1 m1 Vmap.empty) = ok s0 /\
    write_vars f.(f_params) vargs s0 = ok s1,
    sem s1 f.(f_body) s2,
    mapM2 ErrType (fun ty (x:var_i) => truncate_val ty s2.(evm).[x]) f.(f_tyout) f.(f_res) = ok vres &
    scs2 = s2.(escs) /\ m2 = finalize f.(f_extra) s2.(emem) ].
Proof.
  case=> {scs1 m1 fn vargs' scs2 m2 vres} scs1 m1 scs2 m2 fn f vargs vargs' s0 s1 s2 vres.
  move=> hf ha hi hw hc htr hscs hfi.
  exists f; split => //.
  by exists vargs, s0, s1, s2.
Qed.

(* -------------------------------------------------------------------- *)

Section SEM_IND.
  Variables
    (Pc   : estate -> cmd -> estate -> Prop)
    (Pi_r : estate -> instr_r -> estate -> Prop)
    (Pi   : estate -> instr -> estate -> Prop)
    (Pfor : var_i -> seq Z -> estate -> cmd -> estate -> Prop)
    (Pfun : syscall_state_t -> mem -> funname -> seq value -> syscall_state_t -> mem -> seq value -> Prop).

  Definition sem_Ind_nil : Prop :=
    forall s : estate, Pc s [::] s.

  Definition sem_Ind_cons : Prop :=
    forall (s1 s2 s3 : estate) (i : instr) (c : cmd),
      sem_I s1 i s2 -> Pi s1 i s2 -> sem s2 c s3 -> Pc s2 c s3 -> Pc s1 (i :: c) s3.

  Hypotheses
    (Hnil: sem_Ind_nil)
    (Hcons: sem_Ind_cons)
  .

  Definition sem_Ind_mkI : Prop :=
    forall (ii : instr_info) (i : instr_r) (s1 s2 : estate),
      sem_i s1 i s2 -> Pi_r s1 i s2 -> Pi s1 (MkI ii i) s2.

  Hypothesis HmkI : sem_Ind_mkI.

  Definition sem_Ind_assgn : Prop :=
    forall (s1 s2 : estate) (x : lval) (tag : assgn_tag) ty (e : pexpr) v v',
      sem_pexpr gd s1 e = ok v →
      truncate_val ty v = ok v' →
      write_lval gd x v' s1 = ok s2 →
      Pi_r s1 (Cassgn x tag ty e) s2.

  Definition sem_Ind_opn : Prop :=
    forall (s1 s2 : estate) t (o : sopn) (xs : lvals) (es : pexprs),
      sem_sopn gd o s1 xs es = ok s2 →
      Pi_r s1 (Copn xs t o es) s2.

  Definition sem_Ind_syscall : Prop := 
    forall  s1 scs m s2 o xs es ves vs,
      sem_pexprs gd s1 es = ok ves →
      exec_syscall s1.(escs) s1.(emem) o ves = ok (scs, m, vs) →
      write_lvals gd (with_scs (with_mem s1 m) scs) xs vs = ok s2 →
      Pi_r s1 (Csyscall xs o es) s2.

  Definition sem_Ind_if_true : Prop :=
    forall (s1 s2 : estate) (e : pexpr) (c1 c2 : cmd),
    sem_pexpr gd s1 e = ok (Vbool true) ->
    sem s1 c1 s2 -> Pc s1 c1 s2 -> Pi_r s1 (Cif e c1 c2) s2.

  Definition sem_Ind_if_false : Prop :=
    forall (s1 s2 : estate) (e : pexpr) (c1 c2 : cmd),
    sem_pexpr gd s1 e = ok (Vbool false) ->
    sem s1 c2 s2 -> Pc s1 c2 s2 -> Pi_r s1 (Cif e c1 c2) s2.

  Definition sem_Ind_while_true : Prop :=
    forall (s1 s2 s3 s4 : estate) a (c : cmd) (e : pexpr) (c' : cmd),
    sem s1 c s2 -> Pc s1 c s2 ->
    sem_pexpr gd s2 e = ok (Vbool true) ->
    sem s2 c' s3 -> Pc s2 c' s3 ->
    sem_i s3 (Cwhile a c e c') s4 -> Pi_r s3 (Cwhile a c e c') s4 -> Pi_r s1 (Cwhile a c e c') s4.

  Definition sem_Ind_while_false : Prop :=
    forall (s1 s2 : estate) a (c : cmd) (e : pexpr) (c' : cmd),
    sem s1 c s2 -> Pc s1 c s2 ->
    sem_pexpr gd s2 e = ok (Vbool false) ->
    Pi_r s1 (Cwhile a c e c') s2.

  Hypotheses
    (Hasgn: sem_Ind_assgn)
    (Hopn: sem_Ind_opn)
    (Hsyscall: sem_Ind_syscall)
    (Hif_true: sem_Ind_if_true)
    (Hif_false: sem_Ind_if_false)
    (Hwhile_true: sem_Ind_while_true)
    (Hwhile_false: sem_Ind_while_false)
  .

  Definition sem_Ind_for : Prop :=
    forall (s1 s2 : estate) (i : var_i) (d : dir)
           (lo hi : pexpr) (c : cmd) (vlo vhi : Z),
      sem_pexpr gd s1 lo = ok (Vint vlo) ->
      sem_pexpr gd s1 hi = ok (Vint vhi) ->
      sem_for i (wrange d vlo vhi) s1 c s2 ->
      Pfor i (wrange d vlo vhi) s1 c s2 -> Pi_r s1 (Cfor i (d, lo, hi) c) s2.

  Definition sem_Ind_for_nil : Prop :=
    forall (s : estate) (i : var_i) (c : cmd), Pfor i [::] s c s.

  Definition sem_Ind_for_cons : Prop :=
    forall (s1 s1' s2 s3 : estate) (i : var_i)
           (w : Z) (ws : seq Z) (c : cmd),
      write_var i w s1 = Ok error s1' ->
      sem s1' c s2 -> Pc s1' c s2 ->
      sem_for i ws s2 c s3 -> Pfor i ws s2 c s3 -> Pfor i (w :: ws) s1 c s3.

  Hypotheses
    (Hfor: sem_Ind_for)
    (Hfor_nil: sem_Ind_for_nil)
    (Hfor_cons: sem_Ind_for_cons)
  .

  Definition sem_Ind_call : Prop :=
    forall (s1 : estate) (scs2 : syscall_state_t) (m2 : mem) (s2 : estate) 
           (ii : inline_info) (xs : lvals)
           (fn : funname) (args : pexprs) (vargs vs : seq value),
      sem_pexprs gd s1 args = ok vargs →
      sem_call (escs s1) (emem s1) fn vargs scs2 m2 vs → 
      Pfun (escs s1) (emem s1) fn vargs scs2 m2 vs →
      write_lvals gd (with_scs (with_mem s1 m2) scs2) xs vs = ok s2 →
      Pi_r s1 (Ccall ii xs fn args) s2.

  Definition sem_Ind_proc : Prop :=
    forall (scs1 : syscall_state_t) (m1 : mem) (scs2 : syscall_state_t) (m2 : mem)
           (fn:funname) (f : fundef) (vargs vargs': seq value)
           (s0 s1 s2: estate) (vres : seq value),
      get_fundef (p_funcs P) fn = Some f ->
      mapM2 ErrType truncate_val f.(f_tyin) vargs' = ok vargs ->
      init_state f.(f_extra) (p_extra P) ev (Estate scs1 m1 Vmap.empty) = ok s0 ->
      write_vars (f_params f) vargs s0 = ok s1 ->
      sem s1 (f_body f) s2 ->
      Pc s1 (f_body f) s2 ->
      mapM2 ErrType (fun ty (x:var_i) => truncate_val ty s2.(evm).[x]) f.(f_tyout) f.(f_res) = ok vres ->
      scs2 = s2.(escs) -> 
      m2 = finalize f.(f_extra) s2.(emem) ->
      Pfun scs1 m1 fn vargs' scs2 m2 vres.

  Hypotheses
    (Hcall: sem_Ind_call)
    (Hproc: sem_Ind_proc)
  .

  Fixpoint sem_Ind (e : estate) (l : cmd) (e0 : estate) (s : sem e l e0) {struct s} :
    Pc e l e0 :=
    match s in (sem e1 l0 e2) return (Pc e1 l0 e2) with
    | Eskip s0 => Hnil s0
    | @Eseq s1 s2 s3 i c s0 s4 =>
        @Hcons s1 s2 s3 i c s0 (@sem_I_Ind s1 i s2 s0) s4 (@sem_Ind s2 c s3 s4)
    end

  with sem_i_Ind (e : estate) (i : instr_r) (e0 : estate) (s : sem_i e i e0) {struct s} :
    Pi_r e i e0 :=
    match s in (sem_i e1 i0 e2) return (Pi_r e1 i0 e2) with
    | @Eassgn s1 s2 x tag ty e1 v v' h1 h2 h3 => @Hasgn s1 s2 x tag ty e1 v v' h1 h2 h3
    | @Eopn s1 s2 t o xs es e1 => @Hopn s1 s2 t o xs es e1
    | @Esyscall s1 scs m s2 o xs es ves vs h1 h2 h3 => @Hsyscall s1 scs m s2 o xs es ves vs h1 h2 h3
    | @Eif_true s1 s2 e1 c1 c2 e2 s0 =>
      @Hif_true s1 s2 e1 c1 c2 e2 s0 (@sem_Ind s1 c1 s2 s0)
    | @Eif_false s1 s2 e1 c1 c2 e2 s0 =>
      @Hif_false s1 s2 e1 c1 c2 e2 s0 (@sem_Ind s1 c2 s2 s0)
    | @Ewhile_true s1 s2 s3 s4 a c e1 c' s0 e2 s5 s6 =>
      @Hwhile_true s1 s2 s3 s4 a c e1 c' s0 (@sem_Ind s1 c s2 s0) e2 s5 (@sem_Ind s2 c' s3 s5) s6
          (@sem_i_Ind s3 (Cwhile a c e1 c') s4 s6)
    | @Ewhile_false s1 s2 a c e1 c' s0 e2 =>
      @Hwhile_false s1 s2 a c e1 c' s0 (@sem_Ind s1 c s2 s0) e2
    | @Efor s1 s2 i0 d lo hi c vlo vhi e1 e2 s0 =>
      @Hfor s1 s2 i0 d lo hi c vlo vhi e1 e2 s0
        (@sem_for_Ind i0 (wrange d vlo vhi) s1 c s2 s0)
    | @Ecall s1 scs2 m2 s2 ii xs f13 args vargs vs e2 s0 e3 =>
      @Hcall s1 scs2 m2 s2 ii xs f13 args vargs vs e2 s0
        (@sem_call_Ind (escs s1) (emem s1) f13 vargs scs2 m2 vs s0) e3
    end

  with sem_I_Ind (e : estate) (i : instr) (e0 : estate) (s : sem_I e i e0) {struct s} :
    Pi e i e0 :=
    match s in (sem_I e1 i0 e2) return (Pi e1 i0 e2) with
    | @EmkI ii i0 s1 s2 s0 => @HmkI ii i0 s1 s2 s0 (@sem_i_Ind s1 i0 s2 s0)
    end

  with sem_for_Ind (v : var_i) (l : seq Z) (e : estate) (l0 : cmd) (e0 : estate)
         (s : sem_for v l e l0 e0) {struct s} : Pfor v l e l0 e0 :=
    match s in (sem_for v0 l1 e1 l2 e2) return (Pfor v0 l1 e1 l2 e2) with
    | EForDone s0 i c => Hfor_nil s0 i c
    | @EForOne s1 s1' s2 s3 i w ws c e1 s0 s4 =>
      @Hfor_cons s1 s1' s2 s3 i w ws c e1 s0 (@sem_Ind s1' c s2 s0)
         s4 (@sem_for_Ind i ws s2 c s3 s4)
    end

  with sem_call_Ind (scs : syscall_state_t) (m : mem) (f13 : funname) (l : seq value) (scs0 : syscall_state_t) (m0 : mem) 
         (l0 : seq value) (s : sem_call scs m f13 l scs0 m0 l0) {struct s} : Pfun scs m f13 l scs0 m0 l0 :=
    match s with
    | @EcallRun scs1 m1 scs2 m2 fn f vargs vargs' s0 s1 s2 vres Hget Hca Hi Hw Hsem Hvres hscs Hfi=>
      @Hproc scs1 m1 scs2 m2 fn f vargs vargs' s0 s1 s2 vres Hget Hca Hi Hw Hsem (sem_Ind Hsem) Hvres hscs Hfi
    end.

End SEM_IND.

Lemma sem_app l1 l2 s1 s2 s3:
  sem s1 l1 s2 -> sem s2 l2 s3 ->
  sem s1 (l1 ++ l2) s3.
Proof.
  elim: l1 s1;first by move => s1 /semE ->.
  move=> a l Hrec s1 /semE [si h1 hi] h.
  by apply (Eseq h1);apply Hrec.
Qed.

Lemma sem_seq1 i s1 s2:
  sem_I s1 i s2 -> sem s1 [::i] s2.
Proof.
  move=> Hi; apply (Eseq Hi);constructor.
Qed.
 
Lemma sem_seq1_iff (i : instr) s1 s2:
  sem_I s1 i s2 <-> sem s1 [:: i] s2.
Proof.
  split; first by apply sem_seq1.
  by case/semE => ? ? /semE ->.
Qed.

End SEM.

Section ASM_OP.

Context `{asmop:asmOp}.

Lemma sopn_tinP o vs vs' : exec_sopn o vs = ok vs' ->
  all2 subtype (sopn_tin o) (List.map type_of_val vs).
Proof.
  rewrite /exec_sopn /sopn_tin /sopn_sem.
  case (get_instr_desc o) => /= _ tin _ tout _ semi _ _ _.
  t_xrbindP => p hp _.
  elim: tin vs semi hp => /= [ | t tin hrec] [ | v vs] // semi.
  by t_xrbindP => sv /= /of_val_subtype -> /hrec.
Qed.

End ASM_OP.

Lemma truncate_pto_val ty v v':
  truncate_val ty (@pto_val ty v) = ok v' -> is_defined v' -> v' = pto_val v.
Proof.
  case: ty v.
  1,2: by move=> ? [<-].
  + move=> p t1; rewrite /truncate_val /= ifT // => -[<-].
    by f_equal;case: t1.
  rewrite /= /truncate_word => w [] s v /cmp_le_antisym h [<-] /=.
  by case: ifP => // /h{h} <- _ /=; f_equal; exact: zero_extend_u.
Qed.

Lemma is_wconstP gd s sz e w:
  is_wconst sz e = Some w →
  sem_pexpr gd s e >>= to_word sz = ok w.
Proof.
  case: e => // - [] // sz' e /=; case: ifP => // hle /oseq.obindI [z] [h] [<-].
  have := is_constP e; rewrite h => {h} /is_reflect_some_inv -> {e}.
  by rewrite /= /truncate_word hle.
Qed.

Definition eq_on := Vmap.R_on eq.

Notation "vm1 '=[' s ']' vm2" := (eq_on s vm1 vm2) (at level 70, vm2 at next level,
  format "'[hv ' vm1  =[ s ]  '/'  vm2 ']'").

Lemma eq_onT s vm1 vm2 vm3:
  vm1 =[s] vm2 -> vm2 =[s] vm3 -> vm1 =[s] vm3.
Proof. by move=> H1 H2 x Hin;rewrite H1 ?H2. Qed.

Lemma eq_onI s1 s2 vm1 vm2 : Sv.Subset s1 s2 -> vm1 =[s2] vm2 -> vm1 =[s1] vm2.
Proof. move=> Hs Heq x Hin;apply Heq;SvD.fsetdec. Qed.

Lemma eq_onS vm1 s vm2 : vm1 =[s] vm2 -> vm2 =[s] vm1.
Proof. by move=> Heq x Hin;rewrite Heq. Qed.

Global Instance equiv_eq_on s: Equivalence (eq_on s).
Proof.
  constructor=> //.
  move=> ??;apply: eq_onS.
  move=> ???;apply: eq_onT.
Qed.

Global Instance eq_on_impl : Proper (Basics.flip Sv.Subset ==> eq ==> eq ==> Basics.impl) eq_on.
Proof. by move=> s1 s2 H vm1 ? <- vm2 ? <-;apply: eq_onI. Qed.

Global Instance eq_on_m : Proper (Sv.Equal ==> eq ==> eq ==> iff) eq_on.
Proof. by move=> s1 s2 Heq vm1 ? <- vm2 ? <-;split;apply: eq_onI;rewrite Heq. Qed.

Lemma size_wrange d z1 z2 :
  size (wrange d z1 z2) = Z.to_nat (z2 - z1).
Proof. by case: d => /=; rewrite ?size_rev size_map size_iota. Qed.

Lemma nth_wrange z0 d z1 z2 n : (n < Z.to_nat (z2 - z1))%nat ->
  nth z0 (wrange d z1 z2) n =
    if   d is UpTo
    then z1 + Z.of_nat n
    else z2 - Z.of_nat n.
Proof.
case: d => ltn /=;
  by rewrite (nth_map 0%nat) ?size_iota ?nth_iota.
Qed.

Lemma last_wrange_up_ne z0 lo hi :
  lo < hi -> last z0 (wrange UpTo lo hi) = hi - 1.
Proof.
move=> lt; rewrite -nth_last nth_wrange; last rewrite size_wrange prednK //.
rewrite size_wrange -subn1 Nat2Z.inj_sub; first by rewrite Z2Nat.id; lia.
+ apply/leP/ltP; rewrite -Z2Nat.inj_0; apply Z2Nat.inj_lt; lia.
+ apply/ltP; rewrite -Z2Nat.inj_0; apply Z2Nat.inj_lt; lia.
Qed.

Lemma last_wrange_up lo hi : last (hi-1) (wrange UpTo lo hi) = hi - 1.
Proof.
case: (Z_lt_le_dec lo hi) => [lt|le]; first by apply: last_wrange_up_ne.
rewrite -nth_last nth_default // size_wrange.
by rewrite [Z.to_nat _](_ : _ = 0%nat) ?Z_to_nat_le0 //; lia.
Qed.

Lemma wrange_cons lo hi : lo <= hi ->
  lo - 1 :: wrange UpTo lo hi = wrange UpTo (lo - 1) hi.
Proof.
set s1 := wrange _ _ _; set s2 := wrange _ _ _ => /=.
move=> lt; apply/(@eq_from_nth _ 0) => /=.
+ rewrite {}/s1 {}/s2 !size_wrange -Z2Nat.inj_succ; last lia.
  by apply: Nat2Z.inj; rewrite !Z2Nat.id; lia.
rewrite {1}/s1 size_wrange; case => [|i].
+ rewrite /s2 nth_wrange /=; try lia.
  by rewrite -Z2Nat.inj_0; apply/leP/Z2Nat.inj_lt; lia.
move=> lti; rewrite -[nth _ (_ :: _) _]/(nth 0 s1 i) {}/s1 {}/s2.
rewrite !nth_wrange; first lia; last first.
+ by apply/leP; move/leP: lti; lia.
apply/leP/Nat2Z.inj_lt; rewrite Z2Nat.id; last lia.
move/leP/Nat2Z.inj_lt: lti; try rewrite -Z2Nat.inj_succ; last lia.
by rewrite Z2Nat.id; lia.
Qed.

(* -------------------------------------------------------------------- *)

Definition vmap_eq_except := Vmap.R_except eq.

Notation "vm1 = vm2 [\ s ]" := (vmap_eq_except s vm1 vm2) (at level 70, vm2 at next level,
  format "'[hv ' vm1  '/' =  vm2  '/' [\ s ] ']'").

Lemma vmap_eq_exceptT vm2 s vm1 vm3:
  vm1 = vm2 [\s] -> vm2 = vm3 [\s] -> vm1 = vm3 [\s].
Proof. by move=> H1 H2 x Hin;rewrite H1 ?H2. Qed.

Lemma vmap_eq_exceptI s1 s2 vm1 vm2 : Sv.Subset s1 s2 -> vm1 = vm2 [\s1] -> vm1 = vm2 [\s2].
Proof. move=> Hs Heq x Hin;apply Heq;SvD.fsetdec. Qed.

Lemma vmap_eq_exceptTI s1 s2 vm1 vm2 vm3 :
  vm1 = vm2 [\s1] ->
  vm2 = vm3 [\s2] ->
  vm1 = vm3 [\Sv.union s1 s2].
Proof.
  move => h12 h23; apply: vmap_eq_exceptT; apply: vmap_eq_exceptI.
  2: exact: h12.
  3: exact: h23.
  all: SvD.fsetdec.
Qed.

Lemma vmap_eq_exceptS vm1 s vm2 : vm1 = vm2 [\s] -> vm2 = vm1 [\s].
Proof. by move=> Heq x Hin;rewrite Heq. Qed.

Global Instance equiv_vmap_eq_except s: Equivalence (vmap_eq_except s).
Proof.
  constructor=> //.
  move=> ??;apply: vmap_eq_exceptS.
  move=> ???;apply: vmap_eq_exceptT.
Qed.

Global Instance vmap_eq_except_impl :
  Proper (Sv.Subset ==> eq ==> eq ==> Basics.impl) vmap_eq_except.
Proof. by move=> s1 s2 H vm1 ? <- vm2 ? <-;apply: vmap_eq_exceptI. Qed.

Global Instance vmap_eq_except_m : Proper (Sv.Equal ==> eq ==> eq ==> iff) vmap_eq_except.
Proof. by move=> s1 s2 Heq vm1 ? <- vm2 ? <-;split;apply: vmap_eq_exceptI;rewrite Heq. Qed.

Lemma vmap_eq_except_eq_on x y z e o :
  x = y [\e] →
  z =[o] y →
  x =[Sv.diff o e] z.
Proof. by move => he ho j hj; rewrite he ?ho; SvD.fsetdec. Qed.

Lemma vrvP_var (x:var_i) v s1 s2 :
  write_var x v s1 = ok s2 ->
  s1.(evm) = s2.(evm) [\ Sv.add x Sv.empty].
Proof.
  rewrite /write_var; t_xrbindP=> vm /Vmap.set_varP_neq h <- ??.
  by rewrite h //; apply /eqP; SvD.fsetdec.
Qed.

Lemma vrvP gd (x:lval) v s1 s2 :
  write_lval gd x v s1 = ok s2 ->
  s1.(evm) = s2.(evm) [\ vrv x].
Proof.
  case x => /= [ _ ty | ? /vrvP_var| sz y e| aa sz y e | aa sz len y e] //.
  + by case: ifP => // _ [<-].
  + by t_xrbindP=> ptr hptr ptr' ev hev hptr' w hw m hm <-.
  all: by case: Vmap.get_var => //; t_xrbindP => *; apply: vrvP_var; eassumption.
Qed.

Lemma vrvsP gd xs vs s1 s2 :
  write_lvals gd s1 xs vs = ok s2 ->
  s1.(evm) = s2.(evm) [\ vrvs xs].
Proof.
  elim: xs vs s1 s2 => [|x xs Hrec] [|v vs] s1 s2 //=.
  + by move=> [<-].
  apply: rbindP => s /vrvP Hrv /Hrec Hrvs.
  rewrite vrvs_cons;apply: (@vmap_eq_exceptT (evm s)).
  + by apply: vmap_eq_exceptI Hrv;SvD.fsetdec.
  by apply: vmap_eq_exceptI Hrvs;SvD.fsetdec.
Qed.

Lemma write_var_memP x v s1 s2 :
  write_var x v s1 = ok s2 → emem s1 = emem s2.
Proof. by apply: rbindP=> ?? [] <-. Qed.

Lemma lv_write_memP gd (x:lval) v s1 s2:
  ~~ lv_write_mem x ->
  write_lval gd x v s1 = ok s2 ->
  emem s1 = emem s2.
Proof.
  case: x=> //= [v0 t|v0|aa ws v0 p|aa ws len v0 p] _.
  + by case: ifP => // _ [<-].
  + by apply: write_var_memP.
  all: by case: Vmap.get_var => //; t_xrbindP=> *; apply: write_var_memP; eassumption.
Qed.

Lemma write_var_scsP x v s1 s2 : 
  write_var x v s1 = ok s2 → escs s1 = escs s2.
Proof. by apply: rbindP=> ?? [] <-. Qed.

Lemma lv_write_scsP gd (x:lval) v s1 s2:
  write_lval gd x v s1 = ok s2 ->
  escs s1 = escs s2.
Proof.
  case: x=> /= [v0 t|v0|ws x e|aa ws v0 p|aa ws len v0 p].
  + by case: ifP => // _ [<-].
  + by apply: write_var_scsP.
  + by t_xrbindP => *; subst s2.
  all: by case: Vmap.get_var => //; t_xrbindP=> *; apply: write_var_scsP; eassumption.
Qed.

Lemma write_var_with_vm x v s1 s2 :
  write_var x v s1 = ok s2 -> exists vm, s2 = with_vm s1 vm.
Proof. by rewrite /write_var; t_xrbindP=> ? _ <-; eexists. Qed.

Section Write.

Context `{asmop:asmOp}.
Context {T} {pT:progT T} {sCP : semCallParams}.

Variable P : prog.
Variable ev : extra_val_t.

Lemma writeP c s1 s2 :
   sem P ev s1 c s2 -> s1.(evm) = s2.(evm) [\ write_c c].
Proof.
  apply (@sem_Ind _ _ _ _ _ _ _ (fun s1 c s2 => s1.(evm) = s2.(evm) [\ write_c c])
                  (fun s1 i s2 => s1.(evm) = s2.(evm) [\ write_i i])
                  (fun s1 i s2 => s1.(evm) = s2.(evm) [\ write_I i])
                  (fun x ws s1 c s2 =>
                     s1.(evm) = s2.(evm) [\ (Sv.union (Sv.singleton x) (write_c c))])
                  (fun _ _ _ _ _ _ _ => True)) => {c s1 s2} //.
  + move=> s1 s2 s3 i c _ Hi _ Hc z;rewrite write_c_cons => Hnin.
    by rewrite Hi ?Hc //;SvD.fsetdec.
  + move=> s1 s2 x tag ty e v v' ? hty Hw z.
    by rewrite write_i_assgn;apply (vrvP Hw).
  + move=> s1 s2 t o xs es; rewrite /sem_sopn.
    case: (Let _ := sem_pexprs _ _ _ in _) => //= vs Hw z.
    by rewrite write_i_opn;apply (vrvsP Hw).
  + move=> s1 scs m s2 x o es ves vs hes hscs hw.
    by rewrite write_i_syscall; apply (vrvsP hw).
  + by move=> s1 s2 e c1 c2 _ _ Hrec z;rewrite write_i_if => Hnin;apply Hrec;SvD.fsetdec.
  + by move=> s1 s2 e c1 c2 _ _ Hrec z;rewrite write_i_if => Hnin;apply Hrec;SvD.fsetdec.
  + by move=> s1 s2 s3 s4 a c e c' _ Hc _ _ Hc' _ Hw z Hnin; rewrite Hc ?Hc' ?Hw //;
     move: Hnin; rewrite write_i_while; SvD.fsetdec.
  + move=> s1 s2 a c e c' _ Hc _ z Hnin; rewrite Hc //.
    by move: Hnin; rewrite write_i_while; SvD.fsetdec.
  + by move=> s1 s2 i d lo hi c vlo vhi _ _ _ Hrec z;rewrite write_i_for;apply Hrec.
  + move=> s1 s1' s2 s3 i w ws c Hw _ Hc _ Hf z Hnin.
    by rewrite (vrvP_var Hw) ?Hc ?Hf //;SvD.fsetdec.
  move=> s1 scs2 m2 s2 ii xs fn args vargs vs _ _ _ Hw z.
  by rewrite write_i_call;apply (vrvsP Hw).
Qed.

Lemma write_IP i s1 s2 :
   sem_I P ev s1 i s2 -> s1.(evm) = s2.(evm) [\ write_I i].
Proof.
  move=> /sem_seq1 -/writeP.
  have := write_c_cons i [::].
  move=> Heq H x Hx;apply H; SvD.fsetdec.
Qed.

Lemma write_iP i s1 s2 :
   sem_i P ev s1 i s2 -> s1.(evm) = s2.(evm) [\ write_i i].
Proof. by move=> h; have /write_IP := EmkI dummy_instr_info h. Qed.

End Write.

Lemma disjoint_eq_on gd s r s1 s2 v:
  disjoint s (vrv r) ->
  write_lval gd r v s1 = ok s2 ->
  s1.(evm) =[s] s2.(evm).
Proof.
  move=> Hd /vrvP H z Hnin;apply H.
  move:Hd;rewrite /disjoint /is_true Sv.is_empty_spec;SvD.fsetdec.
Qed.

Lemma disjoint_eq_ons gd s r s1 s2 v:
  disjoint s (vrvs r) ->
  write_lvals gd s1 r v = ok s2 ->
  s1.(evm) =[s] s2.(evm).
Proof.
  move=> Hd /vrvsP H z Hnin;apply H.
  move:Hd;rewrite /disjoint /is_true Sv.is_empty_spec;SvD.fsetdec.
Qed.

Lemma get_gvar_eq_on s gd vm' vm v: Sv.Subset (read_gvar v) s -> vm =[s]  vm' ->
  get_gvar gd vm v = get_gvar gd vm' v.
Proof.
  by rewrite /read_gvar /get_gvar; case: ifP => // _ Hin -> //; SvD.fsetdec.
Qed.

Lemma on_arr_var_eq_on s' X s A x (f: ∀ n, WArray.array n → exec A) :
   evm s =[X] evm s' -> Sv.In x X ->
   on_arr_var (ok (Vmap.get_var (evm s) x)) f = on_arr_var (ok (Vmap.get_var (evm s') x)) f.
Proof. by move=> + Hin => -> //. Qed.

Lemma on_arr_gvar_eq_on s' gd X s A x (f: ∀ n, WArray.array n → exec A) :
   evm s =[X] evm s' -> Sv.Subset (read_gvar x) X ->
   on_arr_var (get_gvar gd (evm s) x) f = on_arr_var (get_gvar gd (evm s') x) f.
Proof.
  move=> Heq; rewrite /get_gvar /read_gvar;case:ifP => _ Hin //.
  by apply: (@on_arr_var_eq_on _ X) => //; SvD.fsetdec.
Qed.

Section READ_E_ES_EQ_ON.
  Context (gd: glob_decls) (s1:estate) (vm': Vmap.t).

  Let P e : Prop :=
    ∀ s, evm s1 =[read_e_rec s e]  vm' →
         sem_pexpr gd s1 e = sem_pexpr gd (with_vm s1 vm') e.

  Let Q es : Prop :=
    ∀ s, evm s1 =[read_es_rec s es] vm' →
         sem_pexprs gd s1 es = sem_pexprs gd (with_vm s1 vm') es.

  Lemma read_e_es_eq_on : (∀ e, P e) * (∀ es, Q es).
  Proof.
    apply: pexprs_ind_pair; split; subst P Q => //=.
    - move => e rec es ih s Heq /=.
      have Heq' : evm s1 =[read_e_rec s e] vm'.
      + apply: (eq_onI _ Heq); rewrite /= read_esE; SvD.fsetdec.
      move: rec => /(_ _ Heq') ->.
      case: (sem_pexpr _ _ e) => //= v.
      by move: ih => /(_ _ Heq) ->.
    - by move=> x s /get_gvar_eq_on -> //; SvD.fsetdec.
    - move=> aa sz x e He s Heq; rewrite (He _ Heq) => {He}.
      rewrite (on_arr_gvar_eq_on (s':= with_vm s1 _) _ _ Heq) ?read_eE //.
      by SvD.fsetdec.
    - move=> aa sz len x e He s Heq; rewrite (He _ Heq) => {He}.
      rewrite (on_arr_gvar_eq_on (s':= with_vm s1 _) _ _ Heq) ?read_eE //.
      by SvD.fsetdec.
    - by move=> sz x e He s Hvm; rewrite Hvm ?(He _ Hvm) // read_eE;SvD.fsetdec.
    - by move=> op e He s /He ->.
    - move => op e1 He1 e2 He2 s Heq; rewrite (He1 _ Heq) (He2 s) //.
      by move=> z Hin; apply Heq; rewrite read_eE; SvD.fsetdec.
    - by move => op es Hes s heq; rewrite -!/(sem_pexprs gd s1) (Hes _ heq).
    move=> t e He e1 He1 e2 He2 s Heq; rewrite (He _ Heq) (He1 s) ? (He2 s) //.
    + move=> z Hin;apply Heq;rewrite !read_eE.
      by move: Hin;rewrite read_eE;SvD.fsetdec.
    move=> z Hin;apply Heq;rewrite !read_eE.
    by move: Hin;rewrite read_eE;SvD.fsetdec.
  Qed.

End READ_E_ES_EQ_ON.

Definition read_e_eq_on gd s vm' s1 e :=
  (read_e_es_eq_on gd s1 vm').1 e s.

Definition read_es_eq_on gd es s s1 vm' :=
  (read_e_es_eq_on gd s1 vm').2 es s.

Corollary eq_on_sem_pexpr s' gd s e :
  escs s = escs s' →
  emem s = emem s' →
  evm s =[read_e e] evm s' →
  sem_pexpr gd s e = sem_pexpr gd s' e.
Proof. by move => eq_scs eq_mem /read_e_eq_on -/(_ gd) ->; case: s' eq_scs eq_mem => scs m vm /= <- <-. Qed.

Corollary eq_on_sem_pexprs s' gd s es :
  escs s = escs s' →
  emem s = emem s' →
  evm s =[read_es es] evm s' →
  sem_pexprs gd s es = sem_pexprs gd s' es.
Proof. by move => eq_scs eq_mem /read_es_eq_on -/(_ gd) ->; case: s' eq_scs eq_mem => scs m vm /= <- <-. Qed.

Lemma set_var_eq_on s x v vm1 vm2 vm1':
  Vmap.set_var vm1 x v = ok vm2 ->
  vm1 =[s]  vm1' ->
  exists2 vm2',
     vm2 =[Sv.add x s]  vm2' &
     Vmap.set_var vm1' x v = ok vm2'.
Proof.
  move=> /[dup]Hsv/Vmap.set_varP_eq H; have:= Vmap.get_varP vm2 x.
  rewrite H{H} => /(Vmap.set_var_ok vm1')[?/[dup]Hsv'->] H; eexists; last done.
  intro y; case: (x =P y) => [<- _ | /[dup]/SvD.F.add_3 h /eqP/Vmap.set_varP_neq h'/h{h}/H].
  + by rewrite (Vmap.set_varP_eq Hsv') (Vmap.set_varP_eq Hsv).
  by rewrite (h' _ _ _ Hsv) (h' _ _ _ Hsv').
Qed.

Lemma write_var_eq_on X x v s1 s2 vm1:
  write_var x v s1 = ok s2 ->
  evm s1 =[X] vm1 ->
  exists2 vm2,
    evm s2 =[Sv.add x X]  vm2 &
    write_var x v (with_vm s1 vm1) = ok (with_vm s2 vm2).
Proof.
  rewrite /write_var /=; t_xrbindP => vm2 /set_var_eq_on h <-.
  by move=> /h [vm2' Hvm2 ->]; exists vm2'.
Qed.

Lemma write_lval_eq_on gd X x v s1 s2 vm1 :
  Sv.Subset (read_rv x) X ->
  write_lval gd x v s1 = ok s2 ->
  evm s1 =[X] vm1 ->
  exists2 vm2,
   evm s2 =[Sv.union (vrv x) X] vm2 &
   write_lval gd x v (with_vm s1 vm1) = ok (with_vm s2 vm2).
Proof.
  case:x => [vi ty | x | sz x e | aa sz' x e | aa sz' len x e] /=.
  + by case: ifP => // _ ? [->]; exists vm1.
  + move=> _ /write_var_eq_on h/h{h} [vm2 Hvm2 Hx]; exists vm2 => //.
    by apply: eq_onI Hvm2;SvD.fsetdec.
  + rewrite read_eE => Hsub + Hvm.
    rewrite Hvm; last by SvD.fsetdec.
    rewrite (@read_e_eq_on gd Sv.empty vm1 s1);first last.
    + by apply: eq_onI Hvm;rewrite read_eE;SvD.fsetdec.
    by t_xrbindP=> ? -> > -> /= -> ? -> ? /= -> <-; exists vm1.
  + rewrite read_eE=> Hsub + Hvm.
    rewrite Hvm; last by SvD.fsetdec.
    rewrite (@read_e_eq_on gd (Sv.add x Sv.empty) vm1) /=; first last.
    + by apply: eq_onI Hvm;rewrite read_eE.
    case: Vmap.get_var => // >; t_xrbindP=> > -> /= -> ? -> ? /= -> /= h.
    have [vm2' heq hw]:= write_var_eq_on h Hvm; exists vm2' => //.
    by apply: eq_onI heq;SvD.fsetdec.
  rewrite read_eE=> Hsub Hsem Hvm;move:Hsem.
  rewrite Hvm; last by SvD.fsetdec.
  rewrite (@read_e_eq_on gd (Sv.add x Sv.empty) vm1) /=;first last.
  + by apply: eq_onI Hvm;rewrite read_eE.
  case: Vmap.get_var => // >; t_xrbindP=> > -> /= -> ? -> ? /= -> h.
  have [vm2' heq hw]:= write_var_eq_on h Hvm; exists vm2' => //.
  by apply: eq_onI heq;SvD.fsetdec.
Qed.

Lemma write_lvals_eq_on gd X xs vs s1 s2 vm1 :
  Sv.Subset (read_rvs xs) X ->
  write_lvals gd s1 xs vs = ok s2 ->
  evm s1 =[X] vm1 ->
  exists2 vm2,
    evm s2 =[Sv.union (vrvs xs) X] vm2 &
    write_lvals gd (with_vm s1 vm1) xs vs = ok (with_vm s2 vm2).
Proof.
  elim: xs vs X s1 s2 vm1 => [ | x xs Hrec] [ | v vs] //= X s1 s2 vm1.
  + by move=> _ [<-] ?;exists vm1.
  rewrite read_rvs_cons => Hsub.
  apply: rbindP => s1' Hw Hws /(write_lval_eq_on _ Hw) [ |vm1' Hvm1' ->].
  + by SvD.fsetdec.
  have [ |vm2 Hvm2 /= ->]:= Hrec _ _ _ _ _ _ Hws Hvm1';first by SvD.fsetdec.
  by exists vm2 => //;rewrite vrvs_cons;apply: eq_onI Hvm2;SvD.fsetdec.
Qed.

(* ------------------------------------------ *)

Lemma subtype_type_of_val t (v:psem_t t):
  subtype (type_of_val (pto_val v)) t.
Proof.
  by case: t v => //= s w; exact: pw_proof.
Qed.

Lemma type_of_get_var x vm :
  subtype (type_of_val (Vmap.get_var vm x)) (x.(vtype)).
Proof.
  case: Vmap.get_var (Vmap.get_varP vm x) => //= >.
  by rewrite /typerel_undef /= compat_typeC; exact: is_undef_t_compat_subtype.
Qed.

Lemma type_of_get_gvar x gd vm v :
  get_gvar gd vm x = ok v ->
  subtype (type_of_val v) (vtype x.(gv)).
Proof.
  rewrite /get_gvar;case:ifP => ?.
  + by case=> <-; exact: type_of_get_var.
  by move=> heq; rewrite (type_of_get_global heq).
Qed.

(* We have a more precise result in the non-word cases. *)
Lemma type_of_get_var_not_word vm x :
  ~ is_sword x.(vtype) ->
  type_of_val (Vmap.get_var vm x) = x.(vtype).
Proof.
  by case: (vtype x) (type_of_get_var x vm) => // > /subtypeE /type_of_valI[]
    => [|[?]||[?]|?] ->.
Qed.

Lemma type_of_get_gvar_not_word gd vm x v :
  ~ is_sword x.(gv).(vtype) ->
  get_gvar gd vm x = ok v ->
  type_of_val v = x.(gv).(vtype).
Proof.
  move=> hnword.
  rewrite /get_gvar.
  case: is_lvar.
  + by case=> <-; exact: type_of_get_var_not_word.
  by apply type_of_get_global.
Qed.

(* -------------------------------------------- *)

Lemma pof_val_undef_ok t t' h v:
  pof_val t (Vundef t' h) <> ok v.
Proof. by case: t t' h v => //= [||s] []. Qed.

Lemma value_uincl_pto_val t (vt : psem_t t) v: 
  pof_val t v = ok vt ->
  value_uincl (pto_val vt) v.
Proof.
  case: t vt => // >; try by move=> /of_val_typeE ->.
  move=> /to_pwordI [ws' [w' -> ->]].
  case: Sumbool.sumbool_of_bool => //= h.
  by apply/word_uincl_zero_ext/cmp_lt_le; rewrite -cmp_nle_lt h.
Qed.

Definition pval_uincl (t1 t2:stype) (v1:psem_t t1) (v2:psem_t t2) :=
  value_uincl (pto_val v1) (pto_val v2).

Definition eval_uincl (t1 t2:stype) (v1: exec (psem_t t1)) (v2: exec (psem_t t2)) :=
  match v1, v2 with
  | Ok  v1 , Ok   v2 => pval_uincl v1 v2
  | Error ErrAddrUndef, Ok    _ => True
  | Error x, Error y => x = y
  | _      , _       => False
  end.

Definition vm_uincl := Vmap.R_all value_uincl.

#[ global ] Arguments vm_uincl _%vmap_scope _%vmap_scope.

Lemma pval_uincl_refl t v: @pval_uincl t t v v.
Proof.  by rewrite /pval_uincl. Qed.
Hint Resolve pval_uincl_refl : core.

Lemma eval_uincl_refl t v: @eval_uincl t t v v.
Proof. by case: v=> //= -[]. Qed.
Hint Resolve eval_uincl_refl : core.

Lemma eval_uincl_trans t1 t2 t3
  (v2 : exec (psem_t t2)) (v1: exec (psem_t t1)) (v3: exec (psem_t t3)) :
   eval_uincl v1 v2 -> eval_uincl v2 v3 -> eval_uincl v1 v3.
Proof.
  case: v1 => /= [v1 | ].
  + by case: v2 => //= v2; case: v3 => // v3;apply: value_uincl_trans.
  case: v2 => [v2 [] // _| ];first by case: v3.
  by move=> e1 e2 he;have <- : e2 = e1 by case: e2 he.
Qed.

Lemma vm_uincl_refl vm: @vm_uincl vm vm.
Proof. by done. Qed.
Hint Resolve vm_uincl_refl : core.

Lemma vm_uincl_trans vm2 vm1 vm3 :
  vm_uincl vm1 vm2 → vm_uincl vm2 vm3 → vm_uincl vm1 vm3.
Proof. move => A B x; exact: (value_uincl_trans (A x) (B x)). Qed.

Lemma pof_val_uincl v v' t z:
  value_uincl v v' ->
  pof_val t v = ok z ->
  exists2 z', pof_val t v' = ok z' & pval_uincl z z'.
Proof.
  (case: t z => >; try move=> /of_value_uincl_te h/h{h} /=)
    => [||[?]|/[swap]/to_pwordI[? [? -> ->]/value_uinclE[? [? + /andP[hle /eqP->]]]]]
    => ->; eexists=> //.
  case: Sumbool.sumbool_of_bool => [hle'|/negbT hlt] => //.
  + case: Sumbool.sumbool_of_bool; rewrite /pval_uincl /= /word_uincl => ?.
    + by apply/andP.
    by rewrite hle' zero_extend_idem // eqxx.
  rewrite cmp_nle_lt in hlt; move: (cmp_lt_le_trans hlt hle).
  rewrite -cmp_nle_lt (zero_extend_idem _ (cmp_lt_le hlt)) => /negbTE h.
  by rewrite sumbool_of_boolEF.
Qed.

Lemma get_gvar_uincl_at x gd vm1 vm2 v1:
  (if is_lvar x then value_uincl (Vmap.get_var vm1 (gv x)) (Vmap.get_var vm2 (gv x)) else True)%vmap ->
  get_gvar gd vm1 x = ok v1 ->
  exists2 v2, get_gvar gd vm2 x = ok v2 & value_uincl v1 v2.
Proof.
  rewrite /get_gvar; case:ifP => _.
  + by move=> ? [<-]; eexists.
  by move=> ? ->;exists v1.
Qed.

Corollary get_gvar_uincl x gd vm1 vm2 v1:
  vm_uincl vm1 vm2 ->
  get_gvar gd vm1 x = ok v1 ->
  exists2 v2, get_gvar gd vm2 x = ok v2 & value_uincl v1 v2.
Proof. by move => /(_ x.(gv)) h; apply: get_gvar_uincl_at; case: ifP. Qed.

Lemma vuincl_sem_sop2 o ve1 ve1' ve2 ve2' v1 :
  value_uincl ve1 ve1' -> value_uincl ve2 ve2' ->
  sem_sop2 o ve1 ve2 = ok v1 ->
  sem_sop2 o ve1' ve2' = ok v1.
Proof.
  rewrite /sem_sop2; t_xrbindP=> /of_value_uincl_te h1 /of_value_uincl_te h2
    + /h1{h1} ++ /h2{h2} /=.
  by case: o => /=;
    match goal with
    | |- cmp_kind -> _ => case=> /=
    | |- op_kind -> _ => case=> /=
    | _ => idtac end => > -> > -> ? /=; (move=> -> || case=> ->) => /= ->.
Qed.

Lemma vuincl_sem_sop1 o ve1 ve1' v1 :
  value_uincl ve1 ve1' -> sem_sop1 o ve1 = ok v1 ->
  sem_sop1 o ve1' = ok v1.
Proof.
  rewrite /sem_sop1; t_xrbindP=> /of_value_uincl_te h + /h{h}.
  by case: o; last case; move=> > -> /= ->.
Qed.

Lemma vuincl_sem_opN op vs v vs' :
  sem_opN op vs = ok v →
  List.Forall2 value_uincl vs vs' →
  exists2 v' : value, sem_opN op vs' = ok v' & value_uincl v v'.
Proof.
  rewrite /sem_opN.
  t_xrbindP => q ok_q <-{v} hvs.
  have -> /= := vuincl_sopn _ hvs ok_q.
  + by eauto.
  case: {q ok_q} op => //.
  by move => sz n; rewrite /= all_nseq orbT.
Qed.

(* --------------------------------------------------------- *)
(* VMAP_UINCL_ON *)
Definition vmap_uincl_on := Vmap.R_on value_uincl.

Notation "vm1 '<=[' s ']' vm2" := (vmap_uincl_on s vm1 vm2) (at level 70, vm2 at next level,
  format "'[hv ' vm1  <=[ s ]  '/'  vm2 ']'").

Lemma vmap_uincl_onT vm2 X vm1 vm3 :
  vm1 <=[X] vm2 -> vm2 <=[X] vm3 -> vm1 <=[X] vm3.
Proof. move=> H1 H2 ? hin; exact: value_uincl_trans (H1 _ hin) (H2 _ hin). Qed.

Lemma vmap_uincl_onI s1 s2 vm1 vm2 : Sv.Subset s1 s2 -> vm1 <=[s2] vm2 -> vm1 <=[s1] vm2.
Proof. move=> Hs Heq x Hin;apply Heq;SvD.fsetdec. Qed.

Lemma vmap_uincl_on_refl X vm : vm <=[X] vm.
Proof. done. Qed.

Global Instance vmap_uincl_on_impl : Proper (Basics.flip Sv.Subset ==> eq ==> eq ==> Basics.impl)
              vmap_uincl_on.
Proof. by move=> s1 s2 H vm1 ? <- vm2 ? <-;apply: vmap_uincl_onI. Qed.

Global Instance vmap_uincl_on_m : Proper (Sv.Equal ==> eq ==> eq ==> iff) vmap_uincl_on.
Proof. by move=> s1 s2 Heq vm1 ? <- vm2 ? <-;split;apply: vmap_uincl_onI;rewrite Heq. Qed.

Lemma eq_on_uincl_on X vm1 vm2 : vm1 =[X] vm2 -> vm1 <=[X] vm2.
Proof. by move=> H ? /H ->. Qed.

Lemma vm_uincl_vmap_uincl_on dom vm1 vm2 :
  vm_uincl vm1 vm2 →
  vmap_uincl_on dom vm1 vm2.
Proof. by move => h x _; exact: h. Qed.

#[ global ] Instance vmap_uincl_on_trans dom : Transitive (vmap_uincl_on dom).
Proof. move => x y z xy yz r hr; apply: (value_uincl_trans (xy _ hr)); exact: yz. Qed.

Lemma vmap_uincl_on_empty vm1 vm2 :
  vmap_uincl_on Sv.empty vm1 vm2.
Proof. by move => ?; SvD.fsetdec. Qed.

Hint Resolve vmap_uincl_on_empty : core.

Lemma vmap_uincl_on_union dom dom' vm1 vm2 :
  vmap_uincl_on (Sv.union dom dom') vm1 vm2 ↔
  vmap_uincl_on dom vm1 vm2 ∧ vmap_uincl_on dom' vm1 vm2.
Proof.
  split.
  + by move => h; split => x hx; apply: h; SvD.fsetdec.
  by case => h h' x /Sv.union_spec[]; [ exact: h | exact: h' ].
Qed.

Lemma vmap_uincl_on_vm_uincl vm1 vm2 vm1' vm2' d :
  vm_uincl vm1 vm2 →
  vmap_uincl_on d vm1' vm2' →
  vm1 = vm1' [\ d] →
  vm2 = vm2' [\ d] →
  vm_uincl vm1' vm2'.
Proof.
  move => out on t1 t2 x.
  case: (Sv_memP x d); first exact: on.
  by move => hx; rewrite -!(t1, t2).
Qed.
(* --------------------------------------------------------- *)

Lemma sem_pexpr_uincl_on_rec gd s s1 vm2 es vs1 :
  vmap_uincl_on (read_es_rec s es) s1.(evm) vm2 →
  sem_pexprs gd s1 es = ok vs1 →
  (∀ e : pexpr, List.In e es →
   ∀ v1 : value,
     vmap_uincl_on (read_e e) (evm s1) vm2 →
     sem_pexpr gd s1 e = ok v1 →
   exists2 v2 : value,
   sem_pexpr gd (with_vm s1 vm2) e = ok v2 &
   value_uincl v1 v2) →
   exists2 vs2,
     sem_pexprs gd (with_vm s1 vm2) es = ok vs2 &
     List.Forall2 value_uincl vs1 vs2.
Proof.
  elim: es vs1.
  + by case => //; eauto.
  move => e es ih vs1.
  rewrite read_esE read_es_cons SvP.MP.union_assoc -read_esE
    => /vmap_uincl_on_union[] hvm /ih{ih}ih /=.
  t_xrbindP=> v ok_v vs ok_vs <-{vs1} rec.
  move: ih => /(_ _ ok_vs) [].
  + by move => e' he'; apply: rec; right.
  move => vs' ok_vs' hs.
  move: rec => /(_ e _ _ hvm ok_v) [].
  + by left.
  move => v' ok_v' h.
  exists (v' :: vs').
  + by rewrite ok_v' ok_vs'.
  by constructor.
Qed.

Lemma sem_pexpr_uincl_on gd s s1 vm2 e v1 :
  vmap_uincl_on (read_e_rec s e) s1.(evm) vm2 →
  sem_pexpr gd s1 e = ok v1 →
  exists2 v2, sem_pexpr gd (with_vm s1 vm2) e = ok v2 & value_uincl v1 v2.
Proof.
  elim: e s v1 => /= > => [|||| Hp | Hp | Hp | Hp | He1 e2 He2 | Hes | He e1 He1 e2 He2] >;
    rewrite /read_e /= ?read_eE ?read_eE /read_gvar; t_xrbindP.
  1-3: by move=> ? ->; eauto.
  + by intro Hu; apply: get_gvar_uincl_at; move: Hu; case: ifP => // _; apply; SvD.fsetdec.
  + move=> /vmap_uincl_on_union[] /Hp{Hp}Hp Hu.
    apply on_arr_gvarP => n t Htx; rewrite /on_arr_var => /get_gvar_uincl_at - /(_ vm2) [].
    * by move: Hu; case: ifP => // _; apply; SvD.fsetdec.
    t_xrbindP=> ? -> /value_uinclE[? -> /WArray.uincl_get hg] > /Hp{Hp}
      [? -> ] /[swap] /to_intI -> /value_uinclE -> ? /hg{hg} /= -> /= ->.
    by eauto.
  + move=> /vmap_uincl_on_union[] /Hp{Hp}Hp Hu.
    apply on_arr_gvarP => n t Htx; rewrite /on_arr_var => /get_gvar_uincl_at - /(_ vm2) [].
    * by move: Hu; case: ifP => // _; apply; SvD.fsetdec.
    t_xrbindP=> ? -> /value_uinclE[? -> /WArray.uincl_get_sub h] > /Hp{Hp}
      [? -> ] /[swap] /to_intI -> /value_uinclE -> ? /h{h} /= [? -> ?] /= <-.
    by eexists.
  + by move=> /vmap_uincl_on_union[] /Hp{Hp}Hp Hu >
      /(of_value_uincl_te (ty:= spointer) (Hu _ (SvD.F.add_1 _ erefl))) /= -> >
      /Hp[? ->] /[swap] /to_wordI[? [? -> /word_uincl_truncate h]]
      /value_uinclE[? [? -> /h{h} /= ->]] ? /= -> <-; eexists.
  + by move=> /vmap_uincl_on_union[] /Hp{Hp}Hp Hu
      ve1 /Hp [] ve1' -> /vuincl_sem_sop1 Hvu1 /Hvu1; eauto.
  + by move=> /vmap_uincl_on_union[] /He1{He1}He1
      /vmap_uincl_on_union[] /He2{He2} He2 _
      ? /He1 [? -> /vuincl_sem_sop2 h1] ? /He2 [? -> /h1 h2/h2]; eauto.
  + rewrite -/read_es_rec; move=> /sem_pexpr_uincl_on_rec Hu vs /Hu[] >.
    + by rewrite /read_e; move/Hes; apply.
    by rewrite /sem_pexprs => -> /vuincl_sem_opN h/h.
  move=> /vmap_uincl_on_union[] /He{He}He /vmap_uincl_on_union[]
    /He1{He1}He1 /vmap_uincl_on_union[] /He2{He2}He2 _ b
    > /He[? ->] /[swap] /to_boolI -> /value_uinclE -> ?
    > /He1[? ->] /of_val_uincl h/h{h} [? /= -> ?]
    > /He2 [? ->] /of_val_uincl h/h{h} [? /= -> ?] /= <-.
  by case: b; eauto.
Qed.

Corollary sem_pexpr_uincl gd s1 vm2 e v1 :
  vm_uincl s1.(evm) vm2 →
  sem_pexpr gd s1 e = ok v1 →
  exists2 v2, sem_pexpr gd (with_vm s1 vm2) e = ok v2 & value_uincl v1 v2.
Proof. move => /(@vm_uincl_vmap_uincl_on (read_e e)); exact: sem_pexpr_uincl_on. Qed.

Lemma sem_pexprs_uincl_on gd s s1 vm2 es vs1 :
  vmap_uincl_on (read_es_rec s es) s1.(evm) vm2 →
  sem_pexprs gd s1 es = ok vs1 →
  exists2 vs2, sem_pexprs gd (with_vm s1 vm2) es = ok vs2 &
              List.Forall2 value_uincl vs1 vs2.
Proof.
  move => heq ok_vs.
  apply: (sem_pexpr_uincl_on_rec heq ok_vs) => e he v.
  exact: sem_pexpr_uincl_on.
Qed.

Corollary sem_pexprs_uincl gd s1 vm2 es vs1 :
  vm_uincl s1.(evm) vm2 →
  sem_pexprs gd s1 es = ok vs1 →
  exists2 vs2, sem_pexprs gd (with_vm s1 vm2) es = ok vs2 &
              List.Forall2 value_uincl vs1 vs2.
Proof. move => /(@vm_uincl_vmap_uincl_on (read_es es)); exact: sem_pexprs_uincl_on. Qed.

Lemma disjoint_uincl_on gd s r s1 s2 v:
  disjoint s (vrv r) ->
  write_lval gd r v s1 = ok s2 ->
  s1.(evm) <=[s] s2.(evm).
Proof.
  move=> Hd /vrvP H z Hnin. rewrite (H z). done.
  move:Hd;rewrite /disjoint /is_true Sv.is_empty_spec;SvD.fsetdec.
Qed.

Lemma disjoint_uincl_ons gd s r s1 s2 v:
  disjoint s (vrvs r) ->
  write_lvals gd s1 r v = ok s2 ->
  s1.(evm) <=[s] s2.(evm).
Proof.
  move=> Hd /vrvsP H z Hnin. rewrite (H z). done.
  move:Hd;rewrite /disjoint /is_true Sv.is_empty_spec;SvD.fsetdec.
Qed.

Section ASM_OP.

Context `{asmop:asmOp}.

Lemma vuincl_exec_opn o vs vs' v :
  List.Forall2 value_uincl vs vs' -> exec_sopn o vs = ok v ->
  exists2 v', exec_sopn o vs' = ok v' & List.Forall2  value_uincl v v'.
Proof.
  rewrite /exec_sopn /sopn_sem => vs_vs' ho.
  exact: (get_instr_desc o).(semu) vs_vs' ho.
Qed.

End ASM_OP.

Lemma set_var_uincl vm1 vm1' vm2 vm2' x v v' :
  value_uincl v v' ->
  Vmap.set_var vm1 x v = ok vm1' -> Vmap.set_var vm2 x v' = ok vm2' ->
  value_uincl (Vmap.get_var vm1' x) (Vmap.get_var vm2' x).
Proof.
  move=> Hvu /Vmap.set_varP_eq/[dup]Hrw-> /Vmap.set_varP_eq->.
  case truncate_defined_val eqn: Htdv.
  + by have [? ->] := value_uincl_truncate_defined Hvu Htdv.
  case: v Hrw (typerel_undefE (Vmap.get_varP vm1' x)) Hvu Htdv
    => > -> + /value_uinclE => [|| /subtypeEl-> [? ->] ? _
      | /subtypeEl[? -> ?] [? [? ->]] Hwu _ | ++ _];
    try by move=> _ -> ->.
  + case truncate_defined_val eqn: H => //.
    by have [_ ->] := truncate_defined_valE H.
  + case truncate_defined_val eqn: H => //.
    have {H} [? [? [[?] /truncate_wordP[? ->] ->]]] := truncate_defined_valE H.
    apply/andP; subst; split=> //; rewrite zero_extend_idem => //.
    exact: proj2 (andP Hwu).
  case truncate_defined_val eqn: H => //=.
  by rewrite (truncate_defined_val_has_type H).
Qed.

Lemma set_vmap_uincl_on vm1 vm1' vm2 vm2' x v v' :
  value_uincl v v' ->
  Vmap.set_var vm1 x v = ok vm1' -> Vmap.set_var vm2 x v' = ok vm2' ->
  vmap_uincl_on (Sv.singleton x) vm1' vm2'.
Proof. move=> +++ _/Sv.singleton_spec->; exact: set_var_uincl. Qed.

Lemma set_vm_uincl vm1 vm1' vm2 vm2' x v v' :
  vm_uincl vm1 vm2 -> value_uincl v v' ->
  Vmap.set_var vm1 x v = ok vm1' -> Vmap.set_var vm2 x v' = ok vm2' ->
  vm_uincl vm1' vm2'.
Proof.
  move=> ? Hvu ++ y; case: (x =P y); first by move=> ->; exact: set_var_uincl.
  by move=> /eqP /Vmap.set_varP_neq h /h-> /h-> {h}.
Qed.

Lemma pof_val_error t v:
  pof_val t v = undef_error -> exists h, v = undef_v t h.
Proof.
  case: t => >; try exact: of_val_error.
  move=> /to_pword_undef ->; exists erefl.
  by rewrite /undef_v (undef_x_vundef (_ _)).
Qed.

Lemma pof_val_pto_val t (v:psem_t t): pof_val t (pto_val v) = ok v.
Proof.
  case: t v => // [> | ? w].
  + exact: to_arr_id.
  by rewrite /= (sumbool_of_boolET (pw_proof w)); case: w.
Qed.

Lemma pto_val_pof_val v t :
  pof_val (type_of_val v) v = ok t ->
  pto_val t = v.
Proof.
  case: v t => [|| ?? a | ? w w' |] >.
  + by case=> ->.
  + by case=> ->.
  + by simpl in a; rewrite /type_of_val /pof_val /of_val to_arr_id => -[->].
  + by rewrite /= sumbool_of_boolET => -[<-].
  by simpl=> /pof_val_undef_ok.
Qed.

Lemma value_uincl_pof_val t v1 (v1' v2 : psem_t t):
  pof_val t v1 = ok v1' ->
  value_uincl v1 (pto_val v2) ->
  value_uincl (pto_val v1') (pto_val v2).
Proof.
  case: t v1' v2 => [] >.
  + by move=> /to_boolI ->.
  + by move=> /to_intI ->.
  + by move=> /to_arrI ->.
  case: v1 => //= [ s' w| [] //] [<-].
  case: Sumbool.sumbool_of_bool => //= /negbT hnle.
  have hle := cmp_nle_le hnle; apply: word_uincl_trans.
  exact: word_uincl_zero_ext.
Qed.

Lemma subtype_eval_uincl_pundef t1 t2 :
  subtype t1 t2 ->
  value_uincl (undef_addr t1) (undef_addr t2).
Proof.
  case: t1 => /= [/eqP?|/eqP?|n| s];subst => //=; case: t2 => //=.
  by move=> ? /eqP[<-].
Qed.

Lemma pof_val_bool_undef v : pof_val sbool v = undef_error -> v = undef_b.
Proof. by case: v => //= -[] // e; rewrite (Eqdep_dec.UIP_refl_bool _ e). Qed.

Lemma pof_val_undef v v':
  value_uincl v v' ->
  pof_val sbool v = undef_error ->
  v' = undef_b \/ exists b, v' = Vbool b.
Proof.
  by move=> + /pof_val_bool_undef ?; subst=> /= /eqP/esym/type_of_valI.
Qed.

Lemma set_var_ex_uincl vm1 vm1' vm2 x v v' :
  value_uincl v v' ->
  Vmap.set_var vm1 x v = ok vm2 ->
  exists2 vm2', Vmap.set_var vm1' x v' = ok vm2' &
   value_uincl (Vmap.get_var vm2 x) (Vmap.get_var vm2' x).
Proof.
  move=> Hvu Hsv; case: (@Vmap.set_var_ok _ vm1' x v').
  + move: (Vmap.set_varP_eq Hsv) (Vmap.get_varP vm2 x).
    case: Result.rdfltP => [? /(value_uincl_truncate_defined Hvu)[? H' _ _]
      | _ _ -> /[dup]/(typerel_undef_compat vm_subcomp) Hc].
    + by rewrite H' -(truncate_defined_val_has_type H') (typerel_undef_refl _ vm_relxx).
    case: Result.rdfltP => [? /truncate_defined_val_has_type <- | ?].
    + by rewrite (typerel_undef_refl _ vm_relxx).
    case: v {Hsv} Hvu Hc => [||||? hu] > /value_uinclE => [||[?]|[?[? ->]]|]; try by move=> ->.
    + move=> _ /=/compat_typeE/is_swordP[? ->]; rewrite /truncate_defined_val /=.
      case H: truncate_word => // _ _.
      exact: cmp_lt_le (proj2 (truncate_word_errP H)).
    ((case: v' => >; last by move=> +/compat_type_trans h => /h) => /=/compat_typeE
      => [|||/is_swordP[?]] /= ?; subst) => /compat_typeE => [|||/is_swordP[?]] -> //.
    rewrite /truncate_defined_val /=; case truncate_word eqn: H => // _ _.
    exact: cmp_lt_le (proj2 (truncate_word_errP H)).
  by move=> ? /[dup]/(set_var_uincl Hvu Hsv) Hsv' Hvmu; eauto.
Qed.

Lemma set_vmap_ex_uincl_on vm1 vm1' vm2 x X v v' :
  value_uincl v v' ->
  Vmap.set_var vm1 x v = ok vm2 ->
  vm1 <=[X]  vm1' ->
  exists2 vm2', Vmap.set_var vm1' x v' = ok vm2' & vm2 <=[Sv.add x X] vm2'.
Proof.
  move=> + /[dup] Hsv => /(set_var_ex_uincl vm1') h/h{h}[? Hsv' Hvu] Hvmu.
  eexists; first by eassumption.
  move=> y; case (x =P y) => [<-//| /[dup]/eqP/Vmap.set_varP_neq Hrw /SvD.F.add_3 h/h{h}/Hvmu].
  by rewrite (Hrw _ _ _ Hsv) (Hrw _ _ _ Hsv').
Qed.

Lemma Array_set_uincl n1 n2
   (a1 a1': WArray.array n1) (a2 : WArray.array n2) wz aa i (v:word wz):
  @val_uincl (sarr n1) (sarr n2) a1 a2 ->
  WArray.set a1 aa i v = ok a1' ->
  exists2 a2', WArray.set a2 aa i v = ok a2' &
      @val_uincl (sarr n1) (sarr n2) a1' a2'.
Proof.
  rewrite /val_uincl /= => -[? hu] hs.
  by have [?[]]:= WArray.uincl_set hu hs; eauto.
Qed.

Lemma write_var_uincl_on s1 s2 vm1 v1 v2 x :
  value_uincl v1 v2 ->
  write_var x v1 s1 = ok s2 ->
  exists2 vm2,
    write_var x v2 (with_vm s1 vm1) = ok (with_vm s2 vm2) &
    vmap_uincl_on (Sv.singleton x) (evm s2) vm2.
Proof.
  move=> /set_vmap_ex_uincl_on h; rewrite /write_var.
  t_xrbindP=> vm2 /h{h} /(_ vm1 _ (vmap_uincl_on_empty _ _))[? -> Hrw <-].
  by eexists.
Qed.

(* Cannot be merged with write_var_uincl_on because there is no "everything" set *)
Lemma write_var_uincl_on' s1 s2 vm1 v1 v2 x X :
  value_uincl v1 v2 ->
  write_var x v1 s1 = ok s2 ->
  evm s1 <=[X]  vm1 ->
  exists2 vm2,
    write_var x v2 (with_vm s1 vm1) = ok (with_vm s2 vm2) &
    (evm s2) <=[Sv.add x X] vm2.
Proof.
  move=> /set_vmap_ex_uincl_on h; rewrite /write_var.
  by t_xrbindP=> ? /h{h}h <- /h{h}[? -> ?]; eexists.
Qed.

Corollary write_var_uincl s1 s2 vm1 v1 v2 x :
  vm_uincl s1.(evm) vm1 ->
  value_uincl v1 v2 ->
  write_var x v1 s1 = ok s2 ->
  exists2 vm2,
    write_var x v2 (with_vm s1 vm1) = ok (with_vm s2 vm2) &
    vm_uincl s2.(evm) vm2.
Proof.
  move=> Hvm /(write_var_uincl_on vm1) h /[dup] ok_s2 /h{h} [vm2 ok_vm2 le].
  exists vm2; first exact: ok_vm2; apply: (vmap_uincl_on_vm_uincl Hvm le).
  - exact: (vrvP_var ok_s2).
  exact: (vrvP_var ok_vm2).
Qed.

Lemma write_vars_uincl s1 s2 vm1 vs1 vs2 xs :
  vm_uincl (evm s1) vm1 ->
  List.Forall2 value_uincl vs1 vs2 ->
  write_vars xs vs1 s1 = ok s2 ->
  exists2 vm2,
    write_vars xs vs2 (with_vm s1 vm1) = ok (with_vm s2 vm2) &
    vm_uincl (evm s2) vm2.
Proof.
  elim: xs s1 vm1 vs1 vs2 => /= [ | x xs Hrec] s1 vm1 vs1 vs2 Hvm [] //=.
  + by move=> [] <-;eauto.
  move=> {vs1 vs2} v1 v2 vs1 vs2 Hv Hvs;apply: rbindP => s1'.
  by move=> /(write_var_uincl Hvm Hv) [] vm2 -> Hvm2 /(Hrec _ _ _ _ Hvm2 Hvs).
Qed.

Lemma write_uincl_on gd s1 s2 vm1 r v1 v2:
  vmap_uincl_on (read_rv r) s1.(evm) vm1 ->
  value_uincl v1 v2 ->
  write_lval gd r v1 s1 = ok s2 ->
  exists2 vm2,
    write_lval gd r v2 (with_vm s1 vm1) = ok (with_vm s2 vm2) &
    vmap_uincl_on (vrv r) s2.(evm) vm2.
Proof.
  case: r => [xi ty | x | sz x p | aa sz1 x p | aa sz1 len x p] + Hv;
    rewrite /= ?read_eE; t_xrbindP=> Hvm1.
  + by case: ifP => // /compat_type_trans
      /(_ (subtype_compat (value_uincl_subtype Hv)))-> [->]; eexists.
  + exact: write_var_uincl_on.
  + move: Hvm1 => /vmap_uincl_on_union[] /sem_pexpr_uincl_on Hvme
      /(_ x (SvD.MSetDecideTestCases.test_In_singleton x)) +? /to_wordI[? [? H]].
      rewrite H{H} => /value_uinclE[? [? ->]] /word_uincl_truncate h/h{h} /= ->
        > /Hvme{Hvme} [? ->] /[swap] /to_wordI [? [? -> /word_uincl_truncate h]]
      /value_uinclE[? [? -> /h{h} /= ->]] ? /to_wordI[? [? ? ]].
    subst; move: Hv => /value_uinclE [? [? -> /word_uincl_truncate h]]
      /= /h{h} -> ? /= -> <-.
    by exists vm1.
  + move: Hvm1 => /vmap_uincl_on_union[] /sem_pexpr_uincl_on Hvmp
      /(_ x (SvD.MSetDecideTestCases.test_In_singleton x)) Hvmx.
    apply: on_arr_varP => n a _ h.
    move: h Hvmx => -> /value_uinclE[? -> /WArray.uincl_set hu].
    t_xrbindP=> > /Hvmp{Hvmp} [? ->]
      /[swap] /to_intI -> /value_uinclE -> ? /to_wordI [? [? ? ]].
    subst; move: Hv => /value_uinclE[? [? -> /word_uincl_truncate h]] /h{h}
      /= -> ? /hu{hu} /= [? [-> ?]] /write_var_uincl_on.
    by apply.
  move: Hvm1 => /vmap_uincl_on_union[] /sem_pexpr_uincl_on Hvm1
    /(_ x (SvD.MSetDecideTestCases.test_In_singleton x)) Hvmx.
  apply: on_arr_varP => n a _ h.
  move: h Hvmx => -> /value_uinclE[? -> /WArray.uincl_set_sub hu].
  t_xrbindP=> > /Hvm1{Hvm1} [? ->]
    /[swap] /to_intI -> /value_uinclE -> ? /to_arrI?; subst.
  move: Hv => /value_uinclE[? -> /hu{hu}hu] ? /hu{hu}[?].
  rewrite /= sumbool_of_boolET (Eqdep_dec.UIP_dec Pos.eq_dec (eqP _)) /= => -> ?.
  exact: write_var_uincl_on.
Qed.

Corollary write_uincl gd s1 s2 vm1 r v1 v2:
  vm_uincl s1.(evm) vm1 ->
  value_uincl v1 v2 ->
  write_lval gd r v1 s1 = ok s2 ->
  exists2 vm2,
    write_lval gd r v2 (with_vm s1 vm1) = ok (with_vm s2 vm2) &
    vm_uincl s2.(evm) vm2.
Proof.
  move => hvm hv ok_s2.
  case: (write_uincl_on (vm_uincl_vmap_uincl_on hvm) hv ok_s2) => vm2 ok_vm2 hvm2.
  exists vm2; first exact: ok_vm2.
  apply: (vmap_uincl_on_vm_uincl hvm hvm2).
  - exact: vrvP ok_s2.
  exact: vrvP ok_vm2.
Qed.

Lemma writes_uincl_on gd s1 s2 vm1 r v1 v2:
  vmap_uincl_on (read_rvs r) s1.(evm) vm1 ->
  List.Forall2 value_uincl v1 v2 ->
  write_lvals gd s1 r v1 = ok s2 ->
  exists2 vm2,
    write_lvals gd (with_vm s1 vm1) r v2 = ok (with_vm s2 vm2) &
    vmap_uincl_on (vrvs r) s2.(evm) vm2.
Proof.
  elim: r v1 v2 s1 s2 vm1 => [ | r rs Hrec] ?? s1 s2 vm1 Hvm1 /= [] //=.
  + by case => <-; exists vm1.
  move: Hvm1; rewrite read_rvs_cons => /vmap_uincl_on_union[] hr hrs.
  move=> v1 v2 vs1 vs2 Hv Hforall.
  apply: rbindP => z ok_z ok_s2.
  have [ vm2 ok_vm2 Hvm2 ] := write_uincl_on hr Hv ok_z.
  have h : vmap_uincl_on (read_rvs rs) (evm z) vm2.
  + move => x hx.
    case: (Sv_memP x (vrv r)); first exact: Hvm2.
    move => hxr; rewrite -(vrvP ok_z hxr) -(vrvP ok_vm2 hxr).
    exact: hrs.
  have [ vm3 ok_vm3 h3 ] := Hrec _ _ _ _ vm2 h Hforall ok_s2.
  exists vm3; first by rewrite ok_vm2.
  rewrite vrvs_cons vmap_uincl_on_union; split; last exact: h3.
  move => x hx.
  case: (Sv_memP x (vrvs rs)); first exact: h3.
  move => hxrs; rewrite -(vrvsP ok_vm3 hxrs) -(vrvsP ok_s2 hxrs).
  exact: Hvm2.
Qed.

Corollary writes_uincl gd s1 s2 vm1 r v1 v2:
  vm_uincl s1.(evm) vm1 ->
  List.Forall2 value_uincl v1 v2 ->
  write_lvals gd s1 r v1 = ok s2 ->
  exists2 vm2,
    write_lvals gd (with_vm s1 vm1) r v2 = ok (with_vm s2 vm2) &
    vm_uincl s2.(evm) vm2.
Proof.
  move => hvm hv ok_s2.
  case: (writes_uincl_on (vm_uincl_vmap_uincl_on hvm) hv ok_s2) => vm2 ok_vm2 hvm2.
  exists vm2; first exact: ok_vm2.
  apply: (vmap_uincl_on_vm_uincl hvm hvm2).
  - exact: vrvsP ok_s2.
  exact: vrvsP ok_vm2.
Qed.

Lemma write_vars_lvals gd xs vs s1:
  write_vars xs vs s1 = write_lvals gd s1 [seq Lvar i | i <- xs] vs.
Proof.
  rewrite /write_vars /write_lvals.
  elim: xs vs s1 => [ | x xs Hrec] [ | v vs] //= s1.
  by case: write_var => //=.
Qed.

Lemma sem_pexprs_get_var gd s xs :
  sem_pexprs gd s [seq Pvar (mk_lvar i) | i <- xs] = 
  ok (map (fun x : var_i => Vmap.get_var (evm s) x) xs).
Proof.
  rewrite /sem_pexprs;elim: xs=> //= x xs Hrec.
  rewrite /get_gvar /=.
  by rewrite Hrec.
Qed.

Lemma  get_vars_uincl_on dom (xs: seq var_i) vm1 vm2:
  vmap_uincl_on dom vm1 vm2 ->
  (∀ x, List.In x xs → Sv.mem x dom) →
  List.Forall2 value_uincl (map (fun x => vm1.[v_var x]) xs) (map (fun x => vm2.[v_var x]) xs).
Proof.
  move => hvm; elim: xs => //= x xs Hrec hdom.
  apply: List.Forall2_cons; first exact: hvm (Sv_memP _ _ (hdom _ (List.in_eq _ _))).
  apply: Hrec => ? h; apply: hdom; move: h; rewrite /in_mem /ssrbool.mem.
  by intuition.
Qed.

Lemma get_vars_uincl (xs:seq var_i) vm1 vm2:
  vm_uincl vm1 vm2 ->
  List.Forall2 value_uincl (map (fun x => Vmap.get_var vm1 (v_var x)) xs)
    (map (fun x => Vmap.get_var vm2 (v_var x)) xs).
Proof.
  move => hvm; apply: (@get_vars_uincl_on (sv_of_list v_var xs)).
  + exact: vm_uincl_vmap_uincl_on hvm.
  move => /= y hy; rewrite sv_of_listE; apply/in_map.
  by exists y.
Qed.

Lemma write_lval_uincl_on gd X x v1 v2 s1 s2 vm1 :
  Sv.Subset (read_rv x) X ->
  value_uincl v1 v2 ->
  write_lval gd x v1 s1 = ok s2 ->
  evm s1 <=[X]  vm1 ->
  exists2 vm2, evm s2 <=[Sv.union (vrv x) X]  vm2 &
                     write_lval gd x v2 (with_vm s1 vm1) = ok (with_vm s2 vm2).
Proof.
  move=> hsubset hu hw hsub; pose vm1' := Vmap.update X vm1 (evm s1).
  have heq_on :  evm s1 =[X] vm1'.
  + by move=> ? /Sv_memP; rewrite /vm1' Vmap.updateP => ->.
  have [vm2' heq_on' ]:= write_lval_eq_on hsubset hw heq_on.
  have: vm_uincl vm1' vm1.
  + by move=> ?; rewrite /vm1' Vmap.updateP; case:ifP => // /Sv_memP -/hsub.
  move=> H /(write_uincl _ hu) -/(_ _ H) /= [vm2 -> hvmu];eexists; last reflexivity.
  by move=> ? hin;rewrite heq_on'.
Qed.

Lemma write_lvals_uincl_on gd X x v1 v2 s1 s2 vm1 :
  Sv.Subset (read_rvs x) X ->
  List.Forall2 value_uincl v1 v2 ->
  write_lvals gd s1 x v1 = ok s2 ->
  evm s1 <=[X]  vm1 ->
  exists2 vm2, evm s2 <=[Sv.union (vrvs x) X]  vm2 &
                     write_lvals gd (with_vm s1 vm1) x v2 = ok (with_vm s2 vm2).
Proof.
  move=> hsubset hu hw hsub; pose vm1' := Vmap.update X vm1 (evm s1).
  have heq_on :  evm s1 =[X] vm1'.
  + by move=> ? /Sv_memP; rewrite /vm1' Vmap.updateP => ->.
  have [vm2' heq_on' ]:= write_lvals_eq_on hsubset hw heq_on.
  have: vm_uincl vm1' vm1.
  + by move=> ?; rewrite /vm1' Vmap.updateP; case:ifP => // /Sv_memP -/hsub.
  move=> H /(writes_uincl _ hu) -/(_ _ H) /= [vm2 -> hvmu]; eexists; last reflexivity.
  by move=> ? hin;rewrite heq_on'.
Qed.

(* ---------------------------------------------------------------- *)
(* value inclusion on vmap except on X   *)

Definition vmap_uincl_ex := Vmap.R_except value_uincl.

#[ global ] Arguments vmap_uincl_ex _ _%vmap _%vmap.

Notation "vm1 '<=[\' s ']' vm2" := (vmap_uincl_ex s vm1 vm2) (at level 70, vm2 at next level,
  format "'[hv ' vm1  <=[\ s ]  '/'  vm2 ']'").

Lemma vmap_uincl_exT vm2 X vm1 vm3 :
  vm1 <=[\X] vm2 -> vm2 <=[\X] vm3 -> vm1 <=[\X] vm3.
Proof. move=> H1 H2 ? hnin; exact: value_uincl_trans (H1 _ hnin) (H2 _ hnin). Qed.

Lemma vmap_uincl_exI s1 s2 vm1 vm2 : Sv.Subset s2 s1 -> vm1 <=[\s2] vm2 -> vm1 <=[\s1] vm2.
Proof. move=> Hs Heq x Hin;apply Heq;SvD.fsetdec. Qed.

Lemma vmap_uincl_ex_refl X vm : vm <=[\X] vm.
Proof. done. Qed.
Hint Resolve vmap_uincl_ex_refl : core.

Lemma vmap_eq_except_uincl_ex X vm1 vm2 :
  vm1 = vm2 [\X] -> vm1 <=[\X] vm2.
Proof. by move=> H ? /H ->. Qed.

Lemma vm_uincl_vmap_uincl_ex dom vm1 vm2 :
  vm_uincl vm1 vm2 →
  vm1 <=[\dom] vm2.
Proof. by move => h x _; exact: h. Qed.

Global Instance vmap_uincl_ex_impl : Proper (Sv.Subset ==> eq ==> eq ==> Basics.impl)
              vmap_uincl_ex.
Proof. by move=> s1 s2 H vm1 ? <- vm2 ? <-;apply: vmap_uincl_exI. Qed.

Global Instance vmap_uincl_ex_m : Proper (Sv.Equal ==> eq ==> eq ==> iff) vmap_uincl_ex.
Proof. by move=> s1 s2 Heq vm1 ? <- vm2 ? <-;split;apply: vmap_uincl_exI;rewrite Heq. Qed.

Instance vmap_uincl_ex_trans dom : Transitive (vmap_uincl_ex dom).
Proof. move => x y z xy yz r hr; apply: (value_uincl_trans (xy _ hr)); exact: yz. Qed.

Lemma vmap_uincl_ex_empty vm1 vm2 :
  vm1 <=[\ Sv.empty ] vm2 ↔ vm_uincl vm1 vm2.
Proof.
  split; last exact: vm_uincl_vmap_uincl_ex.
  move => h x; apply/h.
  SvD.fsetdec.
Qed.

(* ---------------------------------------------------------------- *)
Section UNDEFINCL.

Context `{asmop:asmOp}.
Context {T} {pT:progT T} {sCP : semCallParams}.
Variable p : prog.
Variable ev : extra_val_t.

Notation gd:= (p_globs p).

Let Pc s1 c s2 :=
  forall vm1 ,
    vm_uincl (evm s1) vm1 ->
    exists2 vm2,
      sem p ev (with_vm s1 vm1) c (with_vm s2 vm2) &
      vm_uincl (evm s2) vm2.

Let Pi_r s1 i s2 :=
  forall vm1,
    vm_uincl (evm s1) vm1 ->
    exists2 vm2,
      sem_i p ev (with_vm s1 vm1) i (with_vm s2 vm2) &
      vm_uincl (evm s2) vm2.

Let Pi s1 i s2 :=
  forall vm1,
    vm_uincl (evm s1) vm1 ->
    exists2 vm2,
      sem_I p ev (with_vm s1 vm1) i (with_vm s2 vm2) &
      vm_uincl (evm s2) vm2.

Let Pfor (i:var_i) zs s1 c s2 :=
  forall vm1,
    vm_uincl (evm s1) vm1 ->
    exists2 vm2,
      sem_for p ev i zs (with_vm s1 vm1) c (with_vm s2 vm2) &
      vm_uincl (evm s2) vm2.

Let Pfun scs1 m1 fd vargs scs2 m2 vres :=
  forall vargs',
    List.Forall2 value_uincl vargs vargs' ->
    exists2 vres',
      sem_call p ev scs1 m1 fd vargs' scs2 m2 vres' &
      List.Forall2 value_uincl vres vres'.

Local Lemma Hnil : sem_Ind_nil Pc.
Proof. by move=> s vm1 Hvm1;exists vm1=> //;constructor. Qed.

Local Lemma Hcons : sem_Ind_cons p ev Pc Pi.
Proof.
  move=> s1 s2 s3 i c _ Hi _ Hc vm1 /Hi [vm2 Hsi /Hc [vm3 Hsc ?]].
  by exists vm3=>//;econstructor;eauto.
Qed.

Local Lemma HmkI : sem_Ind_mkI p ev Pi_r Pi.
Proof. by move=> ii i s1 s2 _ Hi vm1 /Hi [vm2 Hsi ?];exists vm2. Qed.

Local Lemma Hasgn : sem_Ind_assgn p Pi_r.
Proof.
  move=> s1 s2 x tag ty e v v' hsem hty hwr vm1 Hvm1.
  have [w hsem' hle]:= sem_pexpr_uincl Hvm1 hsem.
  have [w'' hty' hle'] := value_uincl_truncate hle hty.
  have  [vm2 Hw ?]:= write_uincl Hvm1 hle' hwr;exists vm2 => //.
  by econstructor;first exact hsem'; eauto.
Qed.

Local Lemma Hopn : sem_Ind_opn p Pi_r.
Proof.
  move=> s1 s2 t o xs es H vm1 Hvm1; apply: rbindP H => rs;apply: rbindP => vs.
  move=> /(sem_pexprs_uincl Hvm1) [] vs' H1 H2.
  move=> /(vuincl_exec_opn H2) [] rs' H3 H4.
  move=> /(writes_uincl Hvm1 H4) [] vm2 ??.
  exists vm2 => //;constructor.
  by rewrite /sem_sopn H1 /= H3.
Qed.

Local Lemma Hsyscall : sem_Ind_syscall p Pi_r.
Proof.
  move=> s1 scs m s2 xs o es ves vs hes hex hw vm1 hvm1. 
  have [ves' hes' hle] := sem_pexprs_uincl hvm1 hes.
  have [vs' hex' hle']:= exec_syscallP hex hle.
  have  [vm2 Hw ?]:= writes_uincl (s1 := with_scs (with_mem s1 m) scs) hvm1 hle' hw.
  exists vm2 => //; econstructor; eauto.
Qed.

Local Lemma Hif_true : sem_Ind_if_true p ev Pc Pi_r.
Proof.
  move=> s1 s2 e c1 c2 H _ Hc vm1 Hvm1.
  have [v' H1 /value_uinclE ?]:= sem_pexpr_uincl Hvm1 H;subst v'.
  have [vm2 ??]:= Hc _ Hvm1;exists vm2 =>//.
  by apply Eif_true;rewrite // H1.
Qed.

Local Lemma Hif_false : sem_Ind_if_false p ev Pc Pi_r.
Proof.
  move=> s1 s2 e c1 c2 H _ Hc vm1 Hvm1.
  have [v' H1 /value_uinclE ?]:= sem_pexpr_uincl Hvm1 H;subst v'.
  have [vm2 ??]:= Hc _ Hvm1;exists vm2 =>//.
  by apply Eif_false;rewrite // H1.
Qed.

Local Lemma Hwhile_true : sem_Ind_while_true p ev Pc Pi_r.
Proof.
  move=> s1 s2 s3 s4 a c e c' _ Hc H _ Hc' _ Hw vm1 Hvm1.
  have [vm2 Hs2 Hvm2] := Hc _ Hvm1.
  have [v' H1 /value_uinclE ?]:= sem_pexpr_uincl Hvm2 H;subst.
  have [vm3 H4 /Hw [vm4 ??]]:= Hc' _ Hvm2;exists vm4 => //.
  by eapply Ewhile_true;eauto;rewrite H1.
Qed.

Local Lemma Hwhile_false : sem_Ind_while_false p ev Pc Pi_r.
Proof.
  move=> s1 s2 a c e c' _ Hc H vm1 Hvm1.
  have [vm2 Hs2 Hvm2] := Hc _ Hvm1.
  have [v' H1 /value_uinclE ?]:= sem_pexpr_uincl Hvm2 H;subst.
  by exists vm2 => //;apply: Ewhile_false=> //;rewrite H1.
Qed.

Local Lemma Hfor : sem_Ind_for p ev Pi_r Pfor.
Proof.
  move=> s1 s2 i d lo hi c vlo vhi H H' _ Hfor vm1 Hvm1.
  have [? H1 /value_uinclE ?]:= sem_pexpr_uincl Hvm1 H;subst.
  have [? H3 /value_uinclE ?]:= sem_pexpr_uincl Hvm1 H';subst.
  have [vm2 ??]:= Hfor _ Hvm1; exists vm2 =>//.
  by econstructor;eauto;rewrite ?H1 ?H3.
Qed.

Local Lemma Hfor_nil : sem_Ind_for_nil Pfor.
Proof. by move=> s i c vm1 Hvm1;exists vm1 => //;constructor. Qed.

Local Lemma Hfor_cons : sem_Ind_for_cons p ev Pc Pfor.
Proof.
  move=> s1 s1' s2 s3 i w ws c Hi _ Hc _ Hf vm1 Hvm1.
  have [vm1' Hi' /Hc] := write_var_uincl Hvm1 (value_uincl_refl _) Hi.
  move=> [vm2 Hsc /Hf [vm3 Hsf Hvm3]];exists vm3 => //.
  by econstructor;eauto.
Qed.

Local Lemma Hcall : sem_Ind_call p ev Pi_r Pfun.
Proof.
  move=> s1 scs2 m2 s2 ii xs fn args vargs vs Hargs Hcall Hfd Hxs vm1 Hvm1.
  have [vargs' Hsa /Hfd [vs' Hc Hvres]]:= sem_pexprs_uincl Hvm1 Hargs.
  have Hvm1' : vm_uincl (evm (with_scs (with_mem s1 m2) scs2)) vm1 by done.
  have [vm2' ??] := writes_uincl Hvm1' Hvres Hxs.
  by exists vm2' => //; econstructor; eauto.
Qed.

Lemma mapM2_truncate_val_aux vm tys vs :
  mapM2 ErrType (fun ty (x : var_i) => truncate_val ty vm.[x]) tys vs =
    mapM2 ErrType truncate_val tys (map (fun x: var_i => vm.[x]) vs).
Proof. by elim: vs tys => [[]|?] // > hrec []//= >; f_equal; rewrite hrec. Qed.

Local Lemma Hproc : sem_Ind_proc p ev Pc Pfun.
Proof.
  move=> ????? fd > Hget /mapM2_truncate_val Hca
    ? /(write_vars_uincl (vm_uincl_refl _)) Hargs ? Hrec.
  rewrite mapM2_truncate_val_aux => /mapM2_truncate_val Hcr
    ??? /Hca{Hca}[vargs2' hm2 /Hargs{Hargs}].
  rewrite with_vm_same => -[?? /Hrec[? ? /(get_vars_uincl (f_res fd))]]
    /Hcr{Hcr}[vres2' ??].
  by exists vres2' => //; econstructor; eauto; rewrite mapM2_truncate_val_aux.
Qed.

Lemma sem_call_uincl vargs scs1 m1 f scs2 m2 vres vargs':
  List.Forall2 value_uincl vargs vargs' ->
  sem_call p ev scs1 m1 f vargs scs2 m2 vres ->
  exists2 vres', sem_call p ev scs1 m1 f vargs' scs2 m2 vres' & List.Forall2 value_uincl vres vres'.
Proof.
  move=> H1 H2.
  by apply:
    (@sem_call_Ind _ _ _ _ _ p ev Pc Pi_r Pi Pfor Pfun Hnil Hcons HmkI Hasgn Hopn Hsyscall
        Hif_true Hif_false Hwhile_true Hwhile_false Hfor Hfor_nil Hfor_cons Hcall Hproc) H1.
Qed.

Lemma sem_i_uincl s1 i s2 vm1 :
  vm_uincl (evm s1) vm1 ->
  sem_i p ev s1 i s2 ->
  exists2 vm2,
    sem_i p ev (with_vm s1 vm1) i (with_vm s2 vm2) &
    vm_uincl (evm s2) vm2.
Proof.
  move=> H1 H2.
  by apply:
    (@sem_i_Ind _ _ _ _ _ p ev Pc Pi_r Pi Pfor Pfun Hnil Hcons HmkI Hasgn Hopn Hsyscall
        Hif_true Hif_false Hwhile_true Hwhile_false Hfor Hfor_nil Hfor_cons Hcall Hproc) H1.
Qed.

Lemma sem_I_uincl s1 i s2 vm1 :
  vm_uincl (evm s1) vm1 ->
  sem_I p ev s1 i s2 ->
  exists2 vm2,
    sem_I p ev (with_vm s1 vm1) i (with_vm s2 vm2) &
    vm_uincl (evm s2) vm2.
Proof.
  move=> H1 H2.
  by apply:
    (@sem_I_Ind _ _ _ _ _ p ev Pc Pi_r Pi Pfor Pfun Hnil Hcons HmkI Hasgn Hopn Hsyscall
        Hif_true Hif_false Hwhile_true Hwhile_false Hfor Hfor_nil Hfor_cons Hcall Hproc) H1.
Qed.

Lemma sem_uincl s1 c s2 vm1 :
  vm_uincl (evm s1) vm1 ->
  sem p ev s1 c s2 ->
  exists2 vm2,
    sem p ev (with_vm s1 vm1) c (with_vm s2 vm2) &
    vm_uincl (evm s2) vm2.
Proof.
  move=> H1 H2.
  by apply:
    (@sem_Ind _ _ _ _ _ p ev Pc Pi_r Pi Pfor Pfun Hnil Hcons HmkI Hasgn Hopn Hsyscall
        Hif_true Hif_false Hwhile_true Hwhile_false Hfor Hfor_nil Hfor_cons Hcall Hproc) H1.
Qed.

End UNDEFINCL.

Lemma eq_expr_recP gd s (es es': pexprs) :
  (∀ e : pexpr, List.In e es →
   ∀ e' : pexpr, eq_expr e e' → sem_pexpr gd s e = sem_pexpr gd s e') →
  all2 eq_expr es es' →
  sem_pexprs gd s es = sem_pexprs gd s es'.
Proof.
  elim: es es'; first by case.
  move => e es ih [] //= e' es' rec /andP [] he hes.
  rewrite (rec e _ e' he); last by left.
  case: (sem_pexpr _ _ e') => //= v.
  rewrite (ih es') // => q hq q' hq'.
  by apply: rec => //; right.
Qed.

Lemma eq_gvarP gd vm x x' : eq_gvar x x' → get_gvar gd vm x = get_gvar gd vm x'.
Proof. by rewrite /eq_gvar /get_gvar /is_lvar => /andP [] /eqP -> /eqP ->. Qed.

Lemma eq_exprP gd s e1 e2 : eq_expr e1 e2 -> sem_pexpr gd s e1 = sem_pexpr gd s e2.
Proof.
  elim: e1 e2=> [z  | b | n | x | aa sz x e He | aa sz len x e He | sz x e He | o e  He | o e1 He1 e2 He2 | o es Hes | t e He e1 He1 e2 He2]
                [z' | b' | n' | x' | aa' sz' x' e' | aa' sz' len' x' e' | sz' x' e'  | o' e' | o' e1' e2' | o' es' | t' e' e1' e2'] //=.
  + by move=> /eqP ->.   + by move=> /eqP ->.   + by move=> /eqP ->. 
  + by apply: eq_gvarP.
  + by move=> /andP[] /andP []/andP [] /eqP-> /eqP -> /eq_gvarP -> /He ->.
  + by move=> /andP[] /andP[] /andP[] /andP[] /eqP-> /eqP -> /eqP -> /eq_gvarP -> /He ->.
  + by case/andP => /andP [] /eqP -> /eqP -> /He ->.
  + by move=> /andP[]/eqP -> /He ->.
  + by move=> /andP[]/andP[] /eqP -> /He1 -> /He2 ->.
  + rewrite -!/(sem_pexprs _ _).
    by case/andP => /eqP <- /(eq_expr_recP Hes) ->.
  by move=> /andP[]/andP[]/andP[] /eqP -> /He -> /He1 -> /He2 ->.
Qed.

Lemma eq_exprsP gd m es1 es2:
  all2 eq_expr es1 es2 → sem_pexprs gd m es1 = sem_pexprs gd m es2.
Proof.
  apply: eq_expr_recP => e _ e'; exact: eq_exprP.
Qed.

Lemma eq_lvalP gd m lv lv' v :
  eq_lval lv lv' ->
  write_lval gd lv v m = write_lval gd lv' v m.
Proof.
  case: lv lv'=> [ ?? | [??] | sz [??] e | aa sz [??] e | aa sz len [??] e] 
                 [ ?? | [??] | sz' [??] e' | aa' sz' [??] e' | aa' sz' len' [??] e'] //=.
  + by move=> /eqP ->.
  + by move=> /eqP ->.
  + by case/andP => /andP [] /eqP -> /eqP -> /eq_exprP ->.
  + by move=> /andP [] /andP [] /andP [] /eqP -> /eqP -> /eqP -> /eq_exprP ->.
  by move=> /andP [] /andP [] /andP [] /andP [] /eqP -> /eqP -> /eqP -> /eqP -> /eq_exprP ->.
Qed.

Lemma eq_lvalsP gd m ls1 ls2 vs:
  all2 eq_lval ls1 ls2 → write_lvals gd m ls1 vs =  write_lvals gd m ls2 vs.
Proof.
 rewrite /write_lvals.
 elim: ls1 ls2 vs m => [ | l1 ls1 Hrec] [ | l2 ls2] //= [] // v vs m.
 by move=> /andP [] /eq_lvalP -> /Hrec; case: write_lval => /=.
Qed.

Lemma pto_val_inj t (v1 v2:psem_t t) : pto_val v1 = pto_val v2 -> v1 = v2.
Proof.
  case: t v1 v2 => //= [ | | p | sz ] v1 v2 => [ []|[] | /Varr_inj1 | ] //.
  case: v1 v2 => sz1 w1 p1 [sz2 w2 p2] /=.
  move=> /Vword_inj [e];subst => /= <-.
  by rewrite (@eq_irrelevance _ _ _ p1 p2).
Qed.

Lemma pto_val_undef t (v:psem_t t) t' h : pto_val v <> Vundef t' h.
Proof. by case: t v. Qed.

Lemma to_word_to_pword s v w: to_word s v = ok w -> to_pword s v = ok (pword_of_word w).
Proof.
  case: v => //= [ s' w' | [] // ].
  move=> /truncate_wordP [hle] ?; subst w; f_equal.
  case: Sumbool.sumbool_of_bool => //=.
  move=> e;move: (e);rewrite cmp_le_eq_lt in e => e'.
  case /orP: e => [hlt | /eqP ?];first by rewrite -cmp_nlt_le hlt in hle.
  by subst; rewrite /pword_of_word zero_extend_u;do 2 f_equal;apply eq_irrelevance.
Qed.

Lemma pword_of_word_uincl sz (x: word sz) (y: pword sz) :
  @pval_uincl (sword sz) (sword sz) (pword_of_word x) y →
  ∃ e : sz = pw_size y, pw_word y = ecast _ _ e x.
Proof.
  case: y => sz' y sz'_le_sz.
  case/andP => /(cmp_le_antisym sz'_le_sz) ? /=; subst.
  move => /eqP -> {x}; exists erefl.
  by rewrite zero_extend_u.
  Qed.

(* ------------------------------------------------------------------------------ *)
(*Definition apply_undef t (v : exec (psem_t t)) :=
  match v with
  | Error ErrAddrUndef => pundef_addr t
  | _                  => v
  end.

Lemma eval_uincl_undef t1 t2 (v:psem_t t2) :
  subtype t1 t2 ->
  eval_uincl (pundef_addr t1) (ok v).
Proof. 
  case: t1 => //= p; case: t2 v => //= p2 a /ZleP; split => // ??. 
  by rewrite WArray.get_empty; case: ifP.
Qed.

Lemma apply_undef_pundef_addr t : apply_undef (pundef_addr t) = pundef_addr t.
Proof. by case: t. Qed.

Lemma eval_uincl_apply_undef t (v1 v2 : exec (psem_t t)):
  eval_uincl v1 v2 ->
  eval_uincl (apply_undef v1) (apply_undef v2).
Proof.
  case:v1 v2=> [v1 | []] [v2 | e2] //=; try by move=> <-.
  by move=> _; apply eval_uincl_undef.
Qed.*)

(* ------------------------------------------------------------------------------ *)

(* ** Semantic without stack 
 * -------------------------------------------------------------------- *)

Lemma exec_syscallPu scs m o vargs vargs' rscs rm vres :
  sem.exec_syscall scs m o vargs = ok (rscs, rm, vres) → 
  List.Forall2 value_uincl vargs vargs' → 
  exists2 vres' : values,
    sem.exec_syscall scs m o vargs' = ok (rscs, rm, vres') & List.Forall2 value_uincl vres vres'.
Proof.
  rewrite /sem.exec_syscall; case: o => [ p ].
  t_xrbindP => -[scs' v'] /= h ??? hu; subst scs' m v'. 
  move: h; rewrite /exec_getrandom.
  case: hu => // va va' ?? /of_value_uincl_te h [] //.
  t_xrbindP => a /h{h}[? /= -> ?] ra hra ??; subst rscs vres.
  by rewrite hra /=; eexists; eauto.
Qed.

Lemma exec_syscallSu scs m o vargs rscs rm vres :
  sem.exec_syscall scs m o vargs = ok (rscs, rm, vres) → 
  mem_equiv m rm.
Proof.
  rewrite /sem.exec_syscall; case: o => [ p ].
  by t_xrbindP => -[scs' v'] /= _ _ <- _.
Qed.

#[ global ]
Instance sCP_unit : @semCallParams _ progUnit :=
  { init_state := fun _ _ _ s => ok s;
    finalize   := fun _ m => m; 
    exec_syscall  := sem.exec_syscall;
    exec_syscallP := exec_syscallPu;
    exec_syscallS := exec_syscallSu;
}.

(* ** Semantic with stack 
 * -------------------------------------------------------------------- *)

Definition init_stk_state (sf : stk_fun_extra) (pe:sprog_extra) (wrip:pointer) (s:estate) :=
  let scs1 := s.(escs) in
  let m1   := s.(emem) in
  let vm1  := s.(evm) in
  Let m1' := alloc_stack m1 sf.(sf_align) sf.(sf_stk_sz) sf.(sf_stk_extra_sz) in
  write_vars [:: vid pe.(sp_rsp) ; vid pe.(sp_rip)]
             [:: Vword (top_stack m1'); Vword wrip] (Estate scs1 m1' Vmap.empty).

Definition finalize_stk_mem (sf : stk_fun_extra) (m:mem) :=
  free_stack m.

#[ global ]
Instance sCP_stack : @semCallParams _ progStack :=
  { init_state := init_stk_state;
    finalize   := finalize_stk_mem; 
    exec_syscall  := exec_syscall_s;
    exec_syscallP := exec_syscallPs;
    exec_syscallS := exec_syscallSs;
}.

End WITH_POINTER_DATA.

(* We redefine the notations outside the section so that we can use them in other files *)
Notation "'Let' ( n , t ) ':=' s '.[' v ']' 'in' body" :=
  (@on_arr_var _ (ok (Vmap.get_var s.(evm) v)) (fun n (t:WArray.array n) => body)) (at level 25, s at level 0).

Notation "'Let' ( n , t ) ':=' gd ',' s '.[' v ']' 'in' body" :=
  (@on_arr_var _ (get_gvar gd s.(evm) v) (fun n (t:WArray.array n) => body)) (at level 25, gd at level 0, s at level 0).

Notation "vm1 '=[' s ']' vm2" := (eq_on s vm1 vm2) (at level 70, vm2 at next level,
  format "'[hv ' vm1  =[ s ]  '/'  vm2 ']'").

Notation "vm1 = vm2 [\ s ]" := (vmap_eq_except s vm1 vm2) (at level 70, vm2 at next level,
  format "'[hv ' vm1  '/' =  vm2  '/' [\ s ] ']'").

Notation "vm1 '<=[' s ']' vm2" := (vmap_uincl_on s vm1 vm2) (at level 70, vm2 at next level,
  format "'[hv ' vm1  <=[ s ]  '/'  vm2 ']'").

Notation "vm1 '<=[\' s ']' vm2" := (vmap_uincl_ex s vm1 vm2) (at level 70, vm2 at next level,
  format "'[hv ' vm1  <=[\ s ]  '/'  vm2 ']'").

(* Same thing for the hints *)
#[ export ] Hint Resolve
  word_uincl_refl
  value_uincl_refl
  val_uincl_refl
  pval_uincl_refl
  eval_uincl_refl
  vm_uincl_refl
  vmap_uincl_on_empty
  : core.
