(* ** License
 * -----------------------------------------------------------------------
 * Copyright 2016--2017 IMDEA Software Institute
 * Copyright 2016--2017 Inria
 *
 * Permission is hereby granted, free of charge, to any person obtaining
 * a copy of this software and associated documentation files (the
 * "Software"), to deal in the Software without restriction, including
 * without limitation the rights to use, copy, modify, merge, publish,
 * distribute, sublicense, and/or sell copies of the Software, and to
 * permit persons to whom the Software is furnished to do so, subject to
 * the following conditions:
 *
 * The above copyright notice and this permission notice shall be
 * included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
 * EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.
 * IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY
 * CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT,
 * TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE
 * SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 * ----------------------------------------------------------------------- *)

(* * Jasmin semantics with “partial values”. *)

(* ** Imports and settings *)
From mathcomp Require Import all_ssreflect all_algebra.
Require Import Psatz xseq.
Require Export expr low_memory sem.
Require Import x86_variables.
Import Utf8.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope Z_scope.

(* ** Interpretation of types
 * -------------------------------------------------------------------- *)

Record pword s :=
  { pw_size: wsize;
    pw_word : word pw_size;
    pw_proof : (pw_size <= s)%CMP }.

Definition psem_t (t : stype) : Type :=
  match t with
  | sbool   => bool
  | sint    => Z
  | sarr n  => WArray.array n
  | sword s => pword s
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
   | Vundef (sword _) => undef_error
   | _                => type_error
   end.

Definition to_parr (n : positive) v: exec (WArray.array n) :=
  match v with
  | Varr n' t => ok (WArray.inject n t)
  | Vundef (sarr n') => type_error
  | _                => type_error
  end.

Definition pof_val t : value -> exec (psem_t t) :=
  match t return value -> exec (psem_t t) with
  | sbool   => to_bool
  | sint    => to_int
  | sarr n  => to_parr n
  | sword s => to_pword s
  end.

Definition pto_val t : psem_t t -> value :=
  match t return psem_t t -> value with
  | sbool   => Vbool
  | sint    => Vint
  | sarr n  => fun a => Varr a
  | sword s => fun w => Vword (pw_word w)
  end.

Lemma to_pwordI s v w :
  to_pword s v = ok w →
  ∃ s' w',
    v = @Vword s' w' ∧
    w = if Sumbool.sumbool_of_bool (s' ≤ s)%CMP is left heq
        then {| pw_word := w' ; pw_proof := heq |}
        else pword_of_word (zero_extend s w').
Proof. by case: v => // [ | [] // ] s' w' /= [<-]; exists s', w'. Qed.

Lemma type_of_val_to_pword sz v w :
  type_of_val v = sword sz →
  to_pword sz v = ok w →
  ∃ w' : word sz, w = pword_of_word w' ∧ v = Vword w'.
Proof.
  case: v => //= [ s w' [?]| []//]; subst.
  by rewrite sumbool_of_boolET => - [<-]; exists w'.
Qed.

(* ** Variable map
 * -------------------------------------------------------------------- *)

Notation vmap     := (Fv.t (fun t => exec (psem_t t))).

Definition pundef_addr t :=
  match t return exec (psem_t t) with
  | sbool | sint | sword _ => undef_error
  | sarr n => ok (@WArray.empty n)
  end.

Definition vmap0 : vmap :=
  @Fv.empty (fun t => exec (psem_t t)) (fun x => pundef_addr x.(vtype)).

(* An access to a undefined value, leads to an error *)
Definition get_var (m:vmap) x :=
  on_vu (@pto_val (vtype x)) undef_error (m.[x]%vmap).

Definition get_gvar (gd: glob_decls) (vm: vmap) (x:gvar) :=
  if is_lvar x then get_var vm x.(gv)
  else get_global gd x.(gv).

(* Assigning undefined value is allowed only for bool *)
Definition set_var (m:vmap) x v : exec vmap :=
  on_vu (fun v => m.[x<-ok v]%vmap)
        (if is_sbool x.(vtype) then ok m.[x<-pundef_addr x.(vtype)]%vmap
         else type_error)
        (pof_val (vtype x) v).

Lemma set_varP (m m':vmap) x v P :
   (forall t, pof_val (vtype x) v = ok t -> m.[x <- ok t]%vmap = m' -> P) ->
   ( is_sbool x.(vtype) -> pof_val (vtype x) v = undef_error ->
     m.[x<-pundef_addr x.(vtype)]%vmap = m' -> P) ->
   set_var m x v = ok m' -> P.
Proof.
  move=> H1 H2;apply on_vuP => //.
  by case:ifPn => // hb herr []; apply : H2.
Qed.

(* ** Parameter expressions
 * -------------------------------------------------------------------- *)

Record estate := Estate {
  emem : mem;
  evm  : vmap
}.

Notation "'Let' ( n , t ) ':=' s '.[' v ']' 'in' body" :=
  (@on_arr_var _ (get_var s.(evm) v) (fun n (t:WArray.array n) => body)) (at level 25, s at level 0).

Notation "'Let' ( n , t ) ':=' gd ',' s '.[' v ']' 'in' body" :=
  (@on_arr_var _ (get_gvar gd s.(evm) v) (fun n (t:WArray.array n) => body)) (at level 25, gd at level 0, s at level 0).

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
    Let w1 := get_var s.(evm) x >>= to_pointer in
    Let w2 := sem_pexpr s e >>= to_pointer in
    Let w  := read_mem s.(emem) (w1 + w2) sz in
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
    Let v1 := sem_pexpr s e1 >>= truncate_val t in
    Let v2 := sem_pexpr s e2 >>= truncate_val t in
    ok (if b then v1 else v2)
  end.

Definition sem_pexprs s := mapM (sem_pexpr s).

Definition with_vm (s:estate) vm := 
  {| emem := s.(emem); evm := vm |}.

Definition with_mem (s:estate) m := 
  {| emem := m; evm := s.(evm) |}.

Definition write_var (x:var_i) (v:value) (s:estate) : exec estate :=
  Let vm := set_var s.(evm) x v in
  ok (with_vm s vm).

Definition write_vars xs vs s :=
  fold2 ErrType write_var xs vs s.

Definition write_none (s:estate) ty v :=
  on_vu (fun v => s) (if is_sbool ty then ok s else type_error)
          (pof_val ty v).

Definition write_lval (l:lval) (v:value) (s:estate) : exec estate :=
  match l with
  | Lnone _ ty => write_none s ty v
  | Lvar x => write_var x v s
  | Lmem sz x e =>
    Let vx := get_var (evm s) x >>= to_pointer in
    Let ve := sem_pexpr s e >>= to_pointer in
    let p := (vx + ve)%R in (* should we add the size of value, i.e vx + sz * se *)
    Let w := to_word sz v in
    Let m :=  write_mem s.(emem) p sz w in
    ok (with_mem s m) 
  | Laset aa ws x i =>
    Let (n,t) := s.[x] in
    Let i := sem_pexpr s i >>= to_int in
    Let v := to_word ws v in
    Let t := WArray.set t aa i v in
    Let vm := set_var s.(evm) x (@to_val (sarr n) t) in
    ok (with_vm s vm)
  | Lasub aa ws len x i =>
    Let (n,t) := s.[x] in
    Let i := sem_pexpr s i >>= to_int in
    Let t' := to_arr (Z.to_pos (arr_size ws len)) v in 
    Let t := @WArray.set_sub n aa ws len t i t' in
    Let vm := set_var s.(evm) x (@to_val (sarr n) t) in
    ok ({| emem := s.(emem); evm := vm |})
  end.

Definition write_lvals (s:estate) xs vs :=
   fold2 ErrType write_lval xs vs s.

End SEM_PEXPR.

Lemma surj_estate s : s = {| emem := emem s; evm := evm s |}.
Proof. by case:s. Qed.

Lemma with_vm_same s : with_vm s (evm s) = s.
Proof. by case: s. Qed.

Lemma with_vm_idem s vm1 vm2 : with_vm (with_vm s vm1) vm2 = with_vm s vm2.
Proof. by case: s. Qed.

Lemma with_mem_same s : with_mem s (emem s) = s.
Proof. by case: s. Qed.

Lemma with_mem_idem s m1 m2 : with_mem (with_mem s m1) m2 = with_mem s m2.
Proof. by case: s. Qed.

Lemma evm_with_vm s vm : evm (with_vm s vm) = vm.
Proof. by case: s. Qed.

Lemma emem_with_vm s vm : emem (with_vm s vm) = emem s.
Proof. by case: s. Qed.

(* ** Instructions
 * -------------------------------------------------------------------- *)

Section SEM.

Context {T} {pT:progT T}.

Class semCallParams := SemCallParams {
  init_state : extra_fun_t -> extra_prog_t -> extra_val_t -> estate -> exec estate;
  finalize   : extra_fun_t -> mem -> mem;
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

| Ecall s1 m2 s2 ii xs f args vargs vs :
    sem_pexprs gd s1 args = ok vargs ->
    sem_call s1.(emem) f vargs m2 vs ->
    write_lvals gd (with_mem s1 m2) xs vs = ok s2 ->
    sem_i s1 (Ccall ii xs f args) s2

with sem_for : var_i -> seq Z -> estate -> cmd -> estate -> Prop :=
| EForDone s i c :
    sem_for i [::] s c s

| EForOne s1 s1' s2 s3 i w ws c :
    write_var i (Vint w) s1 = ok s1' ->
    sem s1' c s2 ->
    sem_for i ws s2 c s3 ->
    sem_for i (w :: ws) s1 c s3

with sem_call : mem -> funname -> seq value -> mem -> seq value -> Prop :=
| EcallRun m1 m2 fn f vargs vargs' s0 s1 s2 vres vres' :
    get_fundef (p_funcs P) fn = Some f ->
    mapM2 ErrType truncate_val f.(f_tyin) vargs' = ok vargs ->
    init_state f.(f_extra) (p_extra P) ev (Estate m1 vmap0) = ok s0 ->
    write_vars f.(f_params) vargs s0 = ok s1 ->
    sem s1 f.(f_body) s2 ->
    mapM (fun (x:var_i) => get_var s2.(evm) x) f.(f_res) = ok vres ->
    mapM2 ErrType truncate_val f.(f_tyout) vres = ok vres' ->
    m2 = finalize f.(f_extra) s2.(emem)  ->
    sem_call m1 fn vargs' m2 vres'.

Lemma semE s c s' :
  sem s c s' ->
  match c with
  | [::] => s' = s
  | i :: c' => exists si, sem_I s i si /\ sem si c' s'
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
    ∃ vs m2 rs,
    [/\ sem_pexprs gd s es = ok vs, sem_call s.(emem) f vs m2 rs &
       write_lvals gd (with_mem s m2) xs rs = ok s' ]
  end.
Proof.
  case => {s i s'} //.
  - by move => s s' x _ ty e v v' hv hv' hw; exists v, v'.
  - by move => s s' e th el he hth; exists true.
  - by move => s s' e th el he hel; exists false.
  - by move => s si sj s' c e c' hc he hc' hrec; exists si, true; constructor => //; exists sj.
  - by move => s s' c e c' hc he; exists s', false.
  - by move => s s' i d lo hi c vlo vhi hlo hhi hc; exists vlo, vhi.
  by move => s m s' _ xs f es vs rs hvs h hrs; exists vs, m, rs.
Qed.

Lemma sem_callE m1 fn vargs' m2 vres' :
  sem_call m1 fn vargs' m2 vres' ->
  ∃ f,
    get_fundef (p_funcs P) fn = Some f ∧
  ∃ vargs s0 s1 s2 vres,
  [/\    
    mapM2 ErrType truncate_val f.(f_tyin) vargs' = ok vargs,
    init_state f.(f_extra) (p_extra P) ev (Estate m1 vmap0) = ok s0 /\
    write_vars f.(f_params) vargs s0 = ok s1,
    sem s1 f.(f_body) s2,
    mapM (fun (x:var_i) => get_var s2.(evm) x) f.(f_res) = ok vres /\
    mapM2 ErrType truncate_val f.(f_tyout) vres = ok vres' &
    m2 = finalize f.(f_extra) s2.(emem) ].
Proof.
  case => { m1 fn vargs' m2 vres' } m1 m2 fn f vargs vargs' s0 s1 s2 vres vres'.
  move => hf ha hi hw hc hr ht hfi.
  exists f; split => //.
  by exists vargs, s0, s1, s2, vres.
Qed.

(* -------------------------------------------------------------------- *)

Section SEM_IND.
  Variables
    (Pc   : estate -> cmd -> estate -> Prop)
    (Pi_r : estate -> instr_r -> estate -> Prop)
    (Pi : estate -> instr -> estate -> Prop)
    (Pfor : var_i -> seq Z -> estate -> cmd -> estate -> Prop)
    (Pfun : mem -> funname -> seq value -> mem -> seq value -> Prop).

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
    forall (s1 : estate) (m2 : mem) (s2 : estate)
           (ii : inline_info) (xs : lvals)
           (fn : funname) (args : pexprs) (vargs vs : seq value),
      sem_pexprs gd s1 args = ok vargs →
      sem_call (emem s1) fn vargs m2 vs -> Pfun (emem s1) fn vargs m2 vs →
      write_lvals gd (with_mem s1 m2) xs vs = ok s2 →
      Pi_r s1 (Ccall ii xs fn args) s2.

  Definition sem_Ind_proc : Prop :=
    forall (m1 m2 : mem) (fn:funname) (f : fundef) (vargs vargs': seq value)
           (s0 s1 s2: estate) (vres vres': seq value),
      get_fundef (p_funcs P) fn = Some f ->
      mapM2 ErrType truncate_val f.(f_tyin) vargs' = ok vargs ->
      init_state f.(f_extra) (p_extra P) ev (Estate m1 vmap0) = ok s0 ->
      write_vars (f_params f) vargs s0 = ok s1 ->
      sem s1 (f_body f) s2 ->
      Pc s1 (f_body f) s2 ->
      mapM (fun x : var_i => get_var s2.(evm) x) (f_res f) = ok vres ->
      mapM2 ErrType truncate_val f.(f_tyout) vres = ok vres' ->
      m2 = finalize f.(f_extra) s2.(emem) ->
      Pfun m1 fn vargs' m2 vres'.

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
    | @Ecall s1 m2 s2 ii xs f13 args vargs vs e2 s0 e3 =>
      @Hcall s1 m2 s2 ii xs f13 args vargs vs e2 s0
        (@sem_call_Ind (emem s1) f13 vargs m2 vs s0) e3
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

  with sem_call_Ind (m : mem) (f13 : funname) (l : seq value) (m0 : mem)
         (l0 : seq value) (s : sem_call m f13 l m0 l0) {struct s} : Pfun m f13 l m0 l0 :=
    match s with
    | @EcallRun m1 m2 fn f vargs vargs' s0 s1 s2 vres vres' Hget Hca Hi Hw Hsem Hvres Hcr Hfi=>
       @Hproc m1 m2 fn f vargs vargs' s0 s1 s2 vres vres' Hget Hca Hi Hw Hsem (sem_Ind Hsem) Hvres Hcr Hfi
    end.

End SEM_IND.

Lemma sem_app l1 l2 s1 s2 s3:
  sem s1 l1 s2 -> sem s2 l2 s3 ->
  sem s1 (l1 ++ l2) s3.
Proof.
  elim: l1 s1;first by move => s1 /semE ->.
  move=> a l Hrec s1 /semE [si] [h1 hi] h.
  by apply (Eseq h1);apply Hrec.
Qed.

Lemma sem_seq1 i s1 s2:
  sem_I s1 i s2 -> sem s1 [::i] s2.
Proof.
  move=> Hi; apply (Eseq Hi);constructor.
Qed.

End SEM.

(* -------------------------------------------------------------------- *)
(* Proving some properties                                              *)
(* -------------------------------------------------------------------- *)

Lemma truncate_word_u s (a : word s): truncate_word s a = ok a.
Proof. by rewrite /truncate_word cmp_le_refl zero_extend_u. Qed.

Lemma truncate_wordP s1 s2 (w1:word s1) (w2:word s2) :
  truncate_word s1 w2 = ok w1 →
  (s1 <= s2)%CMP /\ w1 = zero_extend s1 w2.
Proof. by rewrite /truncate_word;case:ifP => // Hle []. Qed.

Lemma truncate_word_errP s1 s2 (w: word s2) e :
  truncate_word s1 w = Error e →
  e = ErrType ∧ (s2 < s1)%CMP.
Proof.
by rewrite /truncate_word; case: ifP => // /negbT; rewrite cmp_nle_lt => ? [].
Qed.

Lemma of_val_type_of_val (v: value) :
  (if v is Vundef _ then false else true) →
  exists2 x, of_val (type_of_val v) v = ok x & to_val x = v.
Proof.
case: v => //=; eauto.
+ move=> n a _;rewrite /WArray.cast.
  exists a => //; case: ifP => /ZleP; last by lia.
  by move=> _; f_equal;case: a.
by move => sz w; rewrite truncate_word_u; eauto.
Qed.

Lemma to_boolI x b :
  to_bool x = ok b →
  x = b.
Proof. case: x => //=; last by case. by move => ? /(@ok_inj _ _ _ _) ->. Qed.

Lemma of_val_int v z: of_val sint v = ok z -> v = Vint z.
Proof. by case v=> //= [? [->] | []]. Qed.

Lemma to_wordI sz v w:
  to_word sz v = ok w →
  ∃ sz' (w': word sz'), [/\ (sz <= sz')%CMP, v = Vword w' & w = zero_extend sz w'].
Proof.
 case: v => //=.
 + by move=> s w' /truncate_wordP [];exists s, w'.
 by case => // ?;case: ifP => //.
Qed.

Corollary of_val_word sz v w :
  of_val (sword sz) v = ok w →
  ∃ sz' (w': word sz'), [/\ (sz <= sz')%CMP, v = Vword w' & w = zero_extend sz w'].
Proof. exact: to_wordI. Qed.

Lemma to_intI v n: to_int v = ok n → v = n.
Proof. by case: v => //= [? [<-] | [] ]. Qed.

Lemma to_arrI n v t : to_arr n v = ok t -> exists n' (t':WArray.array n'), [/\ v = Varr t', (n <= n')%Z & t = {| WArray.arr_data := WArray.arr_data t'|}].
Proof.
  case: v => //= [n' t' | [] //].
  rewrite /WArray.cast;case:ZleP => // ? [<-].
  by exists n', t'.
Qed.

Lemma of_val_subtype t v sv : of_val t v = ok sv -> subtype t (type_of_val v).
Proof.
  case: t sv => /= [ | |p|ws] sv.
  + by move=> /to_boolI ->.
  + by move=> /to_intI ->.
  + by move=> /to_arrI [n' [t' [-> /ZleP hle ?]]] /=.
  by move=> /to_wordI [ws' [w [? -> ?]]] /=.
Qed.

Lemma sopn_tinP o vs vs' : exec_sopn o vs = ok vs' ->
  all2 subtype (sopn_tin o) (List.map type_of_val vs).
Proof.
  rewrite /exec_sopn /sopn_tin /sopn_sem.
  case (get_instr o) => /= _ tin _ tout _ semi _ _ _.
  t_xrbindP => p hp _.
  elim: tin vs semi hp => /= [ | t tin hrec] [ | v vs] // semi.
  by t_xrbindP => sv /= /of_val_subtype -> /hrec.
Qed.

Lemma on_arr_varP A (f : forall n, WArray.array n -> exec A) v vm x P:
  (forall n t, vtype x = sarr n -> 
               get_var vm x = ok (@Varr n t) ->
               f n t = ok v -> P) ->
  on_arr_var (get_var vm x) f = ok v -> P.
Proof.
  rewrite /on_arr_var /= => H;apply: rbindP => vx.
  case: x H => -[ | | n | sz ] /= nx;rewrite /get_var => H;
    case Heq : (vm.[_])%vmap => [v' | e] //=; rewrite /= in H.
  + by move=> [<-]. + by case: (e) => // -[<-].
  + by move=> [<-]. + by case: (e) => // -[<-].
  + by move=> [<-]; apply: H => //=; rewrite Heq /=.
  + by case: (e) => // -[<-].
  by move=> [<-]. + by case: (e) => // -[<-].
Qed.

Lemma on_arr_gvarP A (f : forall n, WArray.array n -> exec A) v gd vm x P0:
  (forall n t, vtype x.(gv) = sarr n ->
       get_gvar gd vm x = ok (@Varr n t) ->
       f n t = ok v -> P0) ->
  on_arr_var (get_gvar gd vm x) f = ok v -> P0.
Proof.
  rewrite /get_gvar; case: ifP => heq; first by apply: on_arr_varP.
  move=> H; apply: rbindP => vx hx.
  have h := type_of_get_global hx; case: vx h hx => // len t h.
  by apply: H;rewrite -h.
Qed.

Definition Varr_inj := Varr_inj.

Definition Varr_inj1 := Varr_inj1.

Definition Vword_inj sz sz' w w' (e: @Vword sz w = @Vword sz' w') :
  ∃ e : sz = sz', eq_rect sz (λ s, (word s)) w sz' e = w' :=
  let 'Logic.eq_refl := e in (ex_intro _ erefl erefl).

Lemma ok_word_inj E sz sz' w w' :
  ok (@Vword sz w) = Ok E (@Vword sz' w') →
  ∃ e : sz = sz', eq_rect sz word w sz' e = w'.
Proof. by move => h; have /Vword_inj := ok_inj h. Qed.

Lemma truncate_val_subtype ty v v' :
  truncate_val ty v = ok v' →
  subtype ty (type_of_val v).
Proof.
  case: ty v => [ | | n | sz ] [] //; try by case.
  - move => n' t; rewrite /truncate_val /=.
    by rewrite /WArray.cast; case: ifP.
  by move => sz' w; rewrite /truncate_val /=; t_xrbindP => w' /truncate_wordP [].
Qed.

Lemma truncate_val_has_type ty v v' :
  truncate_val ty v = ok v' →
  type_of_val v' = ty.
Proof.
  case: ty v => [ | | n | sz ] [] //; try by case.
  - by move => b [<-].
  - by move => z [<-].
  - move => n' t; rewrite /truncate_val /= /WArray.cast.
    by case: ifP => h //= [<-].
  by move => sz' w; rewrite /truncate_val /=; t_xrbindP => w' /truncate_wordP [] ? -> <-.
Qed.

Lemma truncate_val_wordI ty v sz w :
  truncate_val ty v = ok (@Vword sz w) →
  ∃ sz' (w': word sz'), ty = sword sz /\ v = Vword w' ∧ (sz ≤ sz')%CMP /\ w = zero_extend sz w'.
Proof.
case: ty v => [ | | n | s ] [] //; try by case.
- by move => n' t; rewrite /truncate_val /= /WArray.cast; case: ifP.
move => sz' w'; rewrite /truncate_val /=.
apply: rbindP => w'' /truncate_wordP [] => hle -> h.
have := ok_inj h => {h} /Vword_inj [] ?; subst => /= ?; subst.
by exists sz', w'.
Qed.

Lemma truncate_val_int ty (z: Z) v :
  truncate_val ty z = ok v →
  ty = sint ∧ v = z.
Proof. by case: ty => // - []. Qed.

Lemma truncate_val_word ty sz (w: word sz) v :
  truncate_val ty (Vword w) = ok v →
  ∃ sz',
    [/\
    ty = sword sz',
    (sz' ≤ sz)%CMP &
    v = Vword (zero_extend sz' w) ].
Proof.
by case: ty => // sz'; apply: rbindP => w' /truncate_wordP [] hle -> [<-]; exists sz'.
Qed.

Lemma truncate_val_bool t (b:bool) v : truncate_val t b = ok v -> t = sbool /\ v = b.
Proof. by case: t => //= -[] <-. Qed.

Lemma truncate_val_boolI t (b:bool) v : truncate_val t v = ok (Vbool b) -> t = sbool /\ v = b.
Proof.
  move=> h; have /= ? := truncate_val_has_type h;subst t.
  by case: v h => //= [ b' [->] | []].
Qed.

Lemma truncate_pto_val ty v v':
  truncate_val ty (@pto_val ty v) = ok v' →
  v' = pto_val v.
Proof.
case: ty v.
+ by move=> ? [<-]. + by move=> ? [<-].
+ move=> p t1; rewrite /truncate_val /= /WArray.cast Z.leb_refl /= => -[<-].
  by f_equal;case: t1.
move => w [] // s v /= hle; apply: rbindP => w' /truncate_wordP [hle'] -> [<-].
by rewrite -(cmp_le_antisym hle hle') zero_extend_u.
Qed.

Lemma is_wconstP gd s sz e w:
  is_wconst sz e = Some w →
  sem_pexpr gd s e >>= to_word sz = ok w.
Proof.
  case: e => // - [] // sz' e /=; case: ifP => // hle /oseq.obindI [z] [h] [<-].
  have := is_constP e; rewrite h => {h} /is_reflect_some_inv -> {e}.
  by rewrite /= /truncate_word hle.
Qed.

Definition eq_on (s : Sv.t) (vm1 vm2 : vmap) :=
  forall x, Sv.In x s -> vm1.[x]%vmap = vm2.[x]%vmap.

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

Lemma wrange_cons lo hi : lo < hi ->
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

Definition vmap_eq_except (s : Sv.t) (vm1 vm2 : vmap) :=
  forall x, ~Sv.In x s -> vm1.[x]%vmap = vm2.[x]%vmap.

Notation "vm1 = vm2 [\ s ]" := (vmap_eq_except s vm1 vm2) (at level 70, vm2 at next level,
  format "'[hv ' vm1  '/' =  vm2  '/' [\ s ] ']'").

Lemma vmap_eq_exceptT vm2 s vm1 vm3:
  vm1 = vm2 [\s] -> vm2 = vm3 [\s] -> vm1 = vm3 [\s].
Proof. by move=> H1 H2 x Hin;rewrite H1 ?H2. Qed.

Lemma vmap_eq_exceptI s1 s2 vm1 vm2 : Sv.Subset s1 s2 -> vm1 = vm2 [\s1] -> vm1 = vm2 [\s2].
Proof. move=> Hs Heq x Hin;apply Heq;SvD.fsetdec. Qed.

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
Proof. move => he ho j hj; rewrite he ?ho; SvD.fsetdec. Qed.

Lemma vrvP_var (x:var_i) v s1 s2 :
  write_var x v s1 = ok s2 ->
  s1.(evm) = s2.(evm) [\ Sv.add x Sv.empty].
Proof.
  rewrite /write_var;t_xrbindP => vm.
  by apply: set_varP => [t | _] => ? <- <- z Hz; rewrite Fv.setP_neq //;apply /eqP; SvD.fsetdec.
Qed.

Lemma write_noneP s s' ty v:
  write_none s ty v = ok s' ->
  s' = s /\
  ((exists u, pof_val ty v = ok u) \/ pof_val ty v = undef_error ∧ ty = sbool).
Proof.
  apply: on_vuP => [u ? -> | ?].
  + by split => //;left;exists u.
  by case:ifPn => // /eqP ? [->];split => //;right.
Qed.

Lemma vrvP gd (x:lval) v s1 s2 :
  write_lval gd x v s1 = ok s2 ->
  s1.(evm) = s2.(evm) [\ vrv x].
Proof.
  case x => /= [ _ ty | ? /vrvP_var| sz y e| aa sz y e | aa sz len y e] //.
  + by move=> /write_noneP [->].
  + by t_xrbindP => ptr yv hyv hptr ptr' ev hev hptr' w hw m hm <-.
  + apply: on_arr_varP => n t; case: y => -[] ty yn yi /= -> hget.
    apply: rbindP => we;apply: rbindP => ve He Hve.
    apply: rbindP => v0 Hv0;apply rbindP => t' Ht'.
    rewrite /set_var /= => -[<-].
    by move=> z Hz; rewrite Fv.setP_neq //;apply /eqP;SvD.fsetdec.
  apply: on_arr_varP => n t; case: y => -[] ty yn yi /= -> hget.
  apply: rbindP => we;apply: rbindP => ve He Hve.
  apply: rbindP => v0 Hv0;apply rbindP => t' Ht'.
  rewrite /set_var /= => -[<-].
  by move=> z Hz; rewrite Fv.setP_neq //;apply /eqP;SvD.fsetdec.
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

Section Write.

Context {T} {pT:progT T} {sCP : semCallParams}.

Variable P : prog.
Variable ev : extra_val_t.

Lemma writeP c s1 s2 :
   sem P ev s1 c s2 -> s1.(evm) = s2.(evm) [\ write_c c].
Proof.
  apply (@sem_Ind _ _ sCP P ev (fun s1 c s2 => s1.(evm) = s2.(evm) [\ write_c c])
                  (fun s1 i s2 => s1.(evm) = s2.(evm) [\ write_i i])
                  (fun s1 i s2 => s1.(evm) = s2.(evm) [\ write_I i])
                  (fun x ws s1 c s2 =>
                     s1.(evm) = s2.(evm) [\ (Sv.union (Sv.singleton x) (write_c c))])
                  (fun _ _ _ _ _ => True)) => {c s1 s2} //.
  + move=> s1 s2 s3 i c _ Hi _ Hc z;rewrite write_c_cons => Hnin.
    by rewrite Hi ?Hc //;SvD.fsetdec.
  + move=> s1 s2 x tag ty e v v' ? hty Hw z.
    by rewrite write_i_assgn;apply (vrvP Hw).
  + move=> s1 s2 t o xs es; rewrite /sem_sopn.
    case: (Let _ := sem_pexprs _ _ _ in _) => //= vs Hw z.
    by rewrite write_i_opn;apply (vrvsP Hw).
  + by move=> s1 s2 e c1 c2 _ _ Hrec z;rewrite write_i_if => Hnin;apply Hrec;SvD.fsetdec.
  + by move=> s1 s2 e c1 c2 _ _ Hrec z;rewrite write_i_if => Hnin;apply Hrec;SvD.fsetdec.
  + by move=> s1 s2 s3 s4 a c e c' _ Hc _ _ Hc' _ Hw z Hnin; rewrite Hc ?Hc' ?Hw //;
     move: Hnin; rewrite write_i_while; SvD.fsetdec.
  + move=> s1 s2 a c e c' _ Hc _ z Hnin; rewrite Hc //.
    by move: Hnin; rewrite write_i_while; SvD.fsetdec.
  + by move=> s1 s2 i d lo hi c vlo vhi _ _ _ Hrec z;rewrite write_i_for;apply Hrec.
  + move=> s1 s1' s2 s3 i w ws c Hw _ Hc _ Hf z Hnin.
    by rewrite (vrvP_var Hw) ?Hc ?Hf //;SvD.fsetdec.
  move=> s1 m2 s2 ii xs fn args vargs vs _ _ _ Hw z.
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
Proof. by move=> h; have /write_IP := EmkI 1%positive h. Qed.

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

Lemma get_var_eq_on s vm' vm v: Sv.In v s -> vm =[s]  vm' -> get_var vm v = get_var vm' v.
Proof. by move=> Hin Hvm;rewrite /get_var Hvm. Qed.

Lemma get_gvar_eq_on s gd vm' vm v: Sv.Subset (read_gvar v) s -> vm =[s]  vm' -> get_gvar gd vm v = get_gvar gd vm' v.
Proof. 
  rewrite /read_gvar /get_gvar; case: ifP => // _ Hin.
  by apply: get_var_eq_on; SvD.fsetdec.
Qed.

Lemma on_arr_var_eq_on s' X s A x (f: ∀ n, WArray.array n → exec A) :
   evm s =[X] evm s' -> Sv.In x X ->
   on_arr_var (get_var (evm s) x) f = on_arr_var (get_var (evm s') x) f.
Proof.
  by move=> Heq Hin;rewrite /on_arr_var;rewrite (get_var_eq_on Hin Heq).
Qed.

Lemma on_arr_gvar_eq_on s' gd X s A x (f: ∀ n, WArray.array n → exec A) :
   evm s =[X] evm s' -> Sv.Subset (read_gvar x) X ->
   on_arr_var (get_gvar gd (evm s) x) f = on_arr_var (get_gvar gd (evm s') x) f.
Proof.
  move=> Heq; rewrite /get_gvar /read_gvar;case:ifP => _ Hin //.
  by apply: (@on_arr_var_eq_on _ X) => //; SvD.fsetdec.
Qed.

Section READ_E_ES_EQ_ON.
  Context (gd: glob_decls) (s1:estate) (vm': vmap).

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
      rewrite (@on_arr_gvar_eq_on (with_vm s1 vm') _ _ s1 _ _ _ Heq) ?read_eE //.
      by SvD.fsetdec.
    - move=> aa sz len x e He s Heq; rewrite (He _ Heq) => {He}.
      rewrite (@on_arr_gvar_eq_on (with_vm s1 vm') _ _ s1 _ _ _ Heq) ?read_eE //.
      by SvD.fsetdec.
    - by move=> sz x e He s Hvm; rewrite (get_var_eq_on _ Hvm) ?(He _ Hvm) // read_eE;SvD.fsetdec.
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
  emem s = emem s' →
  evm s =[read_e e] evm s' →
  sem_pexpr gd s e = sem_pexpr gd s' e.
Proof. by move => eq_mem /read_e_eq_on -/(_ gd) ->; case: s' eq_mem => m vm /= <-. Qed.

Corollary eq_on_sem_pexprs s' gd s es :
  emem s = emem s' →
  evm s =[read_es es] evm s' →
  sem_pexprs gd s es = sem_pexprs gd s' es.
Proof. by move => eq_mem /read_es_eq_on -/(_ gd) ->; case: s' eq_mem => m vm /= <-. Qed.

Lemma set_var_eq_on s x v vm1 vm2 vm1':
  set_var vm1 x v = ok vm2 ->
  vm1 =[s]  vm1' ->
  exists vm2' : vmap,
     vm2 =[Sv.union (Sv.add x Sv.empty) s]  vm2' /\
     set_var vm1' x v = ok vm2'.
Proof.
  (apply: set_varP;rewrite /set_var) => [t | ->] -> <- hvm /=.
  + exists (vm1'.[x <- ok t])%vmap;split => // z hin.
    case: (x =P z) => [<- | /eqP Hxz];first by rewrite !Fv.setP_eq.
    by rewrite !Fv.setP_neq ?hvm //;move/eqP:Hxz; SvD.fsetdec.
  exists (vm1'.[x <- pundef_addr (vtype x)])%vmap;split => // z Hin.
  case: (x =P z) => [<- | /eqP Hxz];first by rewrite !Fv.setP_eq.
  by rewrite !Fv.setP_neq ?hvm //;move/eqP:Hxz; SvD.fsetdec.
Qed.

Lemma write_var_eq_on X x v s1 s2 vm1:
  write_var x v s1 = ok s2 ->
  evm s1 =[X] vm1 ->
  exists vm2 : vmap,
    evm s2 =[Sv.add x X]  vm2 /\
    write_var x v (with_vm s1 vm1) = ok (with_vm s2 vm2).
Proof.
  rewrite /write_var /=;t_xrbindP => vm2 Hset <-.
  move=> /(set_var_eq_on Hset) [vm2' [Hvm2 ->]];exists vm2';split=>//=.
  by apply: eq_onI Hvm2;SvD.fsetdec.
Qed.

Lemma write_lval_eq_on gd X x v s1 s2 vm1 :
  Sv.Subset (read_rv x) X ->
  write_lval gd x v s1 = ok s2 ->
  evm s1 =[X] vm1 ->
  exists vm2 : vmap,
   evm s2 =[Sv.union (vrv x) X] vm2 /\
   write_lval gd x v (with_vm s1 vm1) = ok (with_vm s2 vm2).
Proof.
  case:x => [vi ty | x | sz x e | aa sz' x e | aa sz' len x e] /=.
  + move=> ? /write_noneP [->];rewrite /write_none=> H ?;exists vm1;split=>//.
    by case:H => [[u ->] | [->] ->].
  + move=> _ Hw /(write_var_eq_on Hw) [vm2 [Hvm2 Hx]];exists vm2;split=>//.
    by apply: eq_onI Hvm2;SvD.fsetdec.
  + rewrite read_eE => Hsub Hsem Hvm;move:Hsem.
    rewrite -(get_var_eq_on _ Hvm);last by SvD.fsetdec.
    rewrite (get_var_eq_on _ Hvm);last by SvD.fsetdec.
    rewrite (@read_e_eq_on gd Sv.empty vm1 s1);first last.
    + by apply: eq_onI Hvm;rewrite read_eE;SvD.fsetdec.
    apply: rbindP => vx ->;apply: rbindP => ve ->;apply: rbindP => w /= ->.
    by apply: rbindP => m /= -> [<-] /=;exists vm1.
  + rewrite read_eE=> Hsub Hsem Hvm;move:Hsem.
    rewrite (@on_arr_var_eq_on (with_vm s1 vm1) X s1 _ _ _ Hvm);
      last by SvD.fsetdec.
    rewrite (@read_e_eq_on gd (Sv.add x Sv.empty) vm1) /=;first last.
    + by apply: eq_onI Hvm;rewrite read_eE.
    apply: on_arr_varP => n t Htx; rewrite /on_arr_var => -> /=.
    apply: rbindP => i -> /=;apply: rbindP => ? -> /=;apply: rbindP => ? -> /=.
    apply: rbindP => ? /set_var_eq_on -/(_ _ _ Hvm) [vm2' [Heq' ->]] [] <-.
    by exists vm2'.
  rewrite read_eE=> Hsub Hsem Hvm;move:Hsem.
  rewrite (@on_arr_var_eq_on (with_vm s1 vm1) X s1 _ _ _ Hvm);
      last by SvD.fsetdec.
  rewrite (@read_e_eq_on gd (Sv.add x Sv.empty) vm1) /=;first last.
  + by apply: eq_onI Hvm;rewrite read_eE.
  apply: on_arr_varP => n t Htx; rewrite /on_arr_var => -> /=.
  apply: rbindP => i -> /=;apply: rbindP => ? -> /=;apply: rbindP => ? -> /=.
  apply: rbindP => ? /set_var_eq_on -/(_ _ _ Hvm) [vm2' [Heq' ->]] [] <-.
  by exists vm2'.
Qed.

Lemma write_lvals_eq_on gd X xs vs s1 s2 vm1 :
  Sv.Subset (read_rvs xs) X ->
  write_lvals gd s1 xs vs = ok s2 ->
  evm s1 =[X] vm1 ->
  exists vm2 : vmap,
    evm s2 =[Sv.union (vrvs xs) X] vm2 /\
    write_lvals gd (with_vm s1 vm1) xs vs = ok (with_vm s2 vm2).
Proof.
  elim: xs vs X s1 s2 vm1 => [ | x xs Hrec] [ | v vs] //= X s1 s2 vm1.
  + by move=> _ [<-] ?;exists vm1.
  rewrite read_rvs_cons => Hsub.
  apply: rbindP => s1' Hw Hws /(write_lval_eq_on _ Hw) [ |vm1' [Hvm1' ->]].
  + by SvD.fsetdec.
  have [ |vm2 [Hvm2 /= ->]]:= Hrec _ _ _ _ _ _ Hws Hvm1';first by SvD.fsetdec.
  by exists vm2;split => //;rewrite vrvs_cons;apply: eq_onI Hvm2;SvD.fsetdec.
Qed.

Definition word_uincl sz1 sz2 (w1:word sz1) (w2:word sz2) :=
  (sz1 <= sz2)%CMP && (w1 == zero_extend sz1 w2).

Lemma word_uincl_refl s (w : word s): word_uincl w w.
Proof. by rewrite /word_uincl zero_extend_u cmp_le_refl eqxx. Qed.
Hint Resolve word_uincl_refl.

Lemma word_uincl_eq s (w w': word s):
  word_uincl w w' → w = w'.
Proof. by move=> /andP [] _ /eqP; rewrite zero_extend_u. Qed.

Lemma word_uincl_trans s2 w2 s1 s3 w1 w3 :
   @word_uincl s1 s2 w1 w2 -> @word_uincl s2 s3 w2 w3 -> word_uincl w1 w3.
Proof.
  rewrite /word_uincl => /andP [hle1 /eqP ->] /andP [hle2 /eqP ->].
  by rewrite (cmp_le_trans hle1 hle2) zero_extend_idem // eqxx.
Qed.

(* ------------------------------------------ *)

Definition value_uincl (v1 v2:value) :=
  match v1, v2 with
  | Vbool b1, Vbool b2 => b1 = b2
  | Vint n1, Vint n2   => n1 = n2
  | Varr n1 t1, Varr n2 t2 => WArray.uincl t1 t2
  | Vword sz1 w1, Vword sz2 w2 => word_uincl w1 w2
  | Vundef t, _     => compat_type t (type_of_val v2)
  | _, _ => False
  end.

Lemma value_uinclE v1 v2 :
  value_uincl v1 v2 →
  match v1 with
  | Vbool _ | Vint _ => v2 = v1
  | Varr n1 t1 =>
    exists n2,
      exists2 t2, v2 = @Varr n2 t2 & WArray.uincl t1 t2
  | Vword sz1 w1 => ∃ sz2 w2, v2 = @Vword sz2 w2 ∧ word_uincl w1 w2
  | Vundef t => compat_type t (type_of_val v2)
  end.
Proof.
  case: v1 v2 => [ b1 | n1 | n1 t1 | sz1 w1 | t1 ] [] //=; eauto; try by move => ? <-.
Qed.

Lemma subtype_compat t1 t2 : subtype t1 t2 -> compat_type t1 t2.
Proof.
  by case: t1 => [/eqP ->| /eqP -> | p | w] // ; case: t2.
Qed.

Lemma compat_type_undef t : compat_type t (vundef_type t).
Proof. by case t. Qed.

Lemma compat_subtype_undef t1 t2 : compat_type t1 t2 → subtype (vundef_type t1) t2.
Proof.
  case: t1 => [/eqP ->|/eqP ->|?|?] //=; case: t2 => // *.
  + by apply /ZleP;lia.
  by apply wsize_le_U8.
Qed.

Lemma subtype_type_of_val t (v:psem_t t):
  subtype (type_of_val (pto_val v)) t.
Proof.
  case: t v => //= s w.
  + by apply Z.leb_refl.
  by apply pw_proof.
Qed.

Lemma subtype_vundef_type t : subtype (vundef_type t) t.
Proof. by apply compat_subtype_undef. Qed.

Lemma vundef_type_idem v : vundef_type v = vundef_type (vundef_type v).
Proof. by case: v. Qed.

(* -------------------------------------------- *)
Lemma value_uincl_refl v: @value_uincl v v.
Proof. by case: v => //=; apply compat_type_undef. Qed.

Hint Resolve value_uincl_refl.

Lemma value_uincl_trans v2 v1 v3 :
  value_uincl v1 v2 ->
  value_uincl v2 v3 ->
  value_uincl v1 v3.
Proof.
  case: v1; case: v2 => //=; last (by
   move=> ?? h; apply:compat_type_trans;
   apply : (compat_type_trans h); rewrite compat_typeC compat_type_undef);
  case:v3=> //=.
  + by move=> ??? ->.
  + by move=> ??? ->.
  + by move=> ?? ?? ??; apply: WArray.uincl_trans.
  by move=> //= ??????;apply word_uincl_trans.
Qed.

(* -------------------------------------------- *)

Lemma value_uincl_int1 z v : value_uincl (Vint z) v -> v = Vint z.
Proof. by case: v => //= ? ->. Qed.

Lemma value_uincl_int ve ve' z :
  value_uincl ve ve' -> to_int ve = ok z -> ve = z /\ ve' = z.
Proof. by case: ve => // [ b' /value_uincl_int1 -> [->]| []//]. Qed.

Lemma value_uincl_bool1 b v : value_uincl (Vbool b) v -> v = Vbool b.
Proof. by case: v => //= ? ->. Qed.

Lemma value_uincl_bool ve ve' b :
  value_uincl ve ve' -> to_bool ve = ok b -> ve = b /\ ve' = b.
Proof. by case: ve => // [ b' /value_uincl_bool1 -> [->]| []//]. Qed.

Lemma value_uincl_word ve ve' sz (w: word sz) :
  value_uincl ve ve' →
  to_word sz ve  = ok w →
  to_word sz ve' = ok w.
Proof.
case: ve ve' => //=;last by case.
move => sz' w' [] // sz1 w1 /andP [] hle /eqP -> /truncate_wordP [] hle'.
by rewrite zero_extend_idem // => -> /=; rewrite /truncate_word (cmp_le_trans hle' hle).
Qed.

Lemma value_uincl_arr ve ve' len (t: WArray.array len) :
  value_uincl ve ve' →
  to_arr len ve  = ok t →
  exists2 t', to_arr len ve' = ok t' & WArray.uincl t t'.
Proof.
case: ve ve' => //=; last by case.
move=> len' a [] // len1 a1 hle; rewrite /= /WArray.cast. 
case: hle => ? hget.
case: ZleP => //= heq [<-]; exists {| WArray.arr_data := WArray.arr_data a1 |}.
+ by case: ZleP => //; lia.
split;first by apply Z.le_refl.
move=> i v hi; apply: hget; lia.
Qed.

Lemma value_uincl_subtype v1 v2 :
  value_uincl v1 v2 ->
  subtype (type_of_val v1) (type_of_val v2).
Proof.
case: v1 v2 => [ b | i | n t | s w | ty ]; try by case.
+ by case => //= n' t' [] /ZleP.
+ by case => //= s' w' /andP[].
by move => /= v2; apply compat_subtype_undef.
Qed.

Lemma value_uincl_is_defined x y :
  value_uincl x y →
  is_defined x →
  is_defined y.
Proof. by case: y => //=; case; case: x. Qed.

Lemma value_uincl_compat_type v1 v1' v2 v2':
  value_uincl v1 v1' -> value_uincl v2 v2' ->
  compat_type (type_of_val v1) (type_of_val v2) ->
  compat_type (type_of_val v1') (type_of_val v2').
Proof.
  move=> /value_uincl_subtype -/subtype_compat h1.
  move=> /value_uincl_subtype -/subtype_compat h2 hc.
  apply: compat_type_trans h2; apply: compat_type_trans hc.
  by rewrite compat_typeC.
Qed.

Lemma word_uincl_zero_ext sz sz' (w':word sz') : (sz ≤ sz')%CMP -> word_uincl (zero_extend sz w') w'.
Proof. by move=> ?;apply /andP. Qed.

Lemma word_uincl_zero_extR sz sz' (w: word sz) :
  (sz ≤ sz')%CMP →
  word_uincl w (zero_extend sz' w).
Proof.
  move => hle; apply /andP; split; first exact: hle.
  by rewrite zero_extend_idem // zero_extend_u.
Qed.

Lemma value_uincl_zero_ext sz sz' (w':word sz') : (sz ≤ sz')%CMP ->
  value_uincl (Vword (zero_extend sz w')) (Vword w').
Proof. apply word_uincl_zero_ext. Qed.

Lemma pof_val_undef_ok t t' v:
  pof_val t (Vundef t') <> ok v.
Proof. by case: t t' v => //= [||p|s][]. Qed.

Lemma of_val_Vword t s1 (w1:word s1) w2 : of_val t (Vword w1) = ok w2 ->
  exists s2 (e:t = sword s2),
    (s2 <= s1)%CMP /\  eq_rect t sem_t w2 _ e = zero_extend s2 w1.
Proof.
  case: t w2 => //= s2 w2 /truncate_wordP [] hle ->.
  by exists s2, erefl.
Qed.

Lemma truncate_value_uincl ty x y x' :
  value_uincl x y →
  truncate_val ty x = ok x' →
  exists2 y', truncate_val ty y = ok y' & value_uincl x' y'.
Proof.
case: ty x y => //.
- by case => // [ b | [] ] // [] //= ? <- [<-]; exists (Vbool b).
- by case => // [ z | [] ] // [] //= ? <- [<-]; exists (Vint z).
- move => n; case => // [ n' t' | [] // ] [] //=.
  move => n'' t [hle hget]; rewrite /truncate_val /= /WArray.cast.
  case: ifPn => /ZleP //= h1 [<-].
  case: ifPn => /ZleP //= h2;last by lia.
  eexists; split => //=; first by apply Z.le_refl.
  by move=> ??? /hget h3;apply h3;lia.
(move => sz; case => // [ sz' w | [] // sz' ];
case) => // sz'' w' /=.
case/andP => hsz' /eqP -> {w}; rewrite /truncate_val /= /truncate_word.
case: ifP => // hsz [<-].
rewrite (cmp_le_trans hsz hsz') /=; eexists; first reflexivity.
by rewrite/= zero_extend_idem.
Qed.

Lemma mapM2_truncate_val tys vs1' vs1 vs2' :
  mapM2 ErrType truncate_val tys vs1' = ok vs1 ->
  List.Forall2 value_uincl vs1' vs2' ->
  exists2 vs2, mapM2 ErrType truncate_val tys vs2' = ok vs2 &
    List.Forall2 value_uincl vs1 vs2.
Proof.
  elim: tys vs1' vs1 vs2' => [ | t tys hrec] [|v1' vs1'] //=.
  + by move => ? ? [<-] /List_Forall2_inv_l ->; eauto.
  move=> vs1 vs2';t_xrbindP => v1 htr vs2 htrs <- /List_Forall2_inv_l [v] [vs] [->] [hv hvs].
  have [v2 -> hv2 /=]:= truncate_value_uincl hv htr.
  by have [vs2'' -> hvs2 /=] := hrec _ _ _ htrs hvs;eauto.
Qed.

Lemma value_uincl_truncate_val t v1 v2 : truncate_val t v1 = ok v2 -> value_uincl v2 v1.
Proof.
  rewrite /truncate_val;case: t; t_xrbindP => /=.
  + by move=> b /to_boolI -> <-.
  + by move=> b /to_intI -> <-.
  + by move=> n t/ to_arrI [n' [t' [-> ? -> <-]]]; split.
  move=> sz w /to_wordI [sz' [w' [? -> -> <-]]] => /=.
  by apply word_uincl_zero_ext.
Qed.

Definition val_uincl (t1 t2:stype) (v1:sem_t t1) (v2:sem_t t2) :=
  value_uincl (to_val v1) (to_val v2).

Definition pval_uincl (t1 t2:stype) (v1:psem_t t1) (v2:psem_t t2) :=
  value_uincl (pto_val v1) (pto_val v2).

Definition eval_uincl (t1 t2:stype) (v1: exec (psem_t t1)) (v2: exec (psem_t t2)) :=
  match v1, v2 with
  | Ok  v1 , Ok   v2 => pval_uincl v1 v2
  | Error ErrAddrUndef, Ok    _ => True
  | Error x, Error y => x = y
  | _      , _       => False
  end.

Definition vm_uincl (vm1 vm2:vmap) :=
  forall x, eval_uincl (vm1.[x])%vmap (vm2.[x])%vmap.

Lemma val_uincl_refl t v: @val_uincl t t v v.
Proof. by rewrite /val_uincl. Qed.
Hint Resolve val_uincl_refl.

Lemma pval_uincl_refl t v: @pval_uincl t t v v.
Proof.  by rewrite /pval_uincl. Qed.
Hint Resolve pval_uincl_refl.

Lemma eval_uincl_refl t v: @eval_uincl t t v v.
Proof. by case: v=> //= -[]. Qed.
Hint Resolve eval_uincl_refl.

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
Hint Resolve vm_uincl_refl.

Lemma val_uincl_array n (a a' : WArray.array n) :
  (∀ (i : Z) (v : u8),
    0 <= i ∧ i < n →
    Mz.get (WArray.arr_data a) i = Some v → Mz.get (WArray.arr_data a') i = Some v) ->
  @val_uincl (sarr n) (sarr n) a a'.
Proof.
  by move=> H;rewrite /val_uincl /=;split => //; apply Z.le_refl.
Qed.

Lemma of_val_uincl v v' t z:
  value_uincl v v' ->
  of_val t v = ok z ->
  exists z', of_val t v' = ok z' /\ val_uincl z z'.
Proof.
  case: v v'=> [b | n | n a | sz w | tv] [b' | n' | n' a' | sz' w' | tv'] //=;
    try by move=> _ /of_val_undef_ok.
  + by move=> <- ->;eauto.
  + by move=> <- ->;eauto.
  + move=> [h1 h2]; case: t z => //= p a1.
    rewrite /WArray.cast; case: ifPn => /ZleP h // [<-].
    case: ifPn => /ZleP ?;last by lia.
    eexists;split; first by reflexivity.
    split => //=; first by apply Z.le_refl.
    by move=> ???; apply h2; lia.
  move=> /andP []hsz /eqP -> /of_val_Vword [] s2 [] ?;subst => /= -[] hle ->.
  rewrite /truncate_word (cmp_le_trans hle hsz) zero_extend_idem //.
  by eexists;split;first reflexivity.
Qed.

Lemma pof_val_uincl v v' t z:
  value_uincl v v' ->
  pof_val t v = ok z ->
  exists z', pof_val t v' = ok z' /\ pval_uincl z z'.
Proof.
  case: v v'=> [b | n | n a | sz w | tv] [b' | n' | n' a' | sz' w' | tv'] //=;
    try by move=> _ /pof_val_undef_ok.
  + by move=> <- ?;exists z.
  + by move=> <- ?;exists z.
  + move=> [h1 h2]; case: t z => //= p a1 [<-].
    eexists;split;first by reflexivity.
    split; first by apply Z.le_refl.
    move=> i v [h0i hip]; rewrite !WArray.zget_inject //; case: ifP => //= /ZltP hn.
    by case: ifPn => /ZltP hn'; [apply h2 | lia].
  move=> /andP []hsz /eqP ->;rewrite /pof_val /pval_uincl /=.
  case: t z => //= s z.
  case: (Sumbool.sumbool_of_bool (sz ≤ s)%CMP).
  + move=> e [<-].
    case: (Sumbool.sumbool_of_bool (sz' ≤ s)%CMP).
    + move=> ?; eexists;split;first reflexivity => /=.
      by rewrite /word_uincl /= hsz eqxx.
    move => /negbT hle; eexists; split; first reflexivity.
    by rewrite /word_uincl /= e zero_extend_idem // eqxx.
  move => /negbT hlt1 [<-]; eexists; split; first reflexivity.
  have hnle: (sz' <= s)%CMP = false.
  + apply negbTE; rewrite cmp_nle_lt.
    by apply: cmp_lt_le_trans hsz; rewrite -cmp_nle_lt.
  have hle := cmp_nle_le hlt1.
  by rewrite /= zero_extend_idem // (sumbool_of_boolEF hnle).
Qed.

Lemma get_var_uincl_at x vm1 vm2 v1 :
  (eval_uincl vm1.[x] vm2.[x])%vmap ->
  get_var vm1 x = ok v1 ->
  exists2 v2, get_var vm2 x = ok v2 & value_uincl v1 v2.
Proof.
  rewrite /get_var=> H; apply: on_vuP => //.
  move=> z1 Heq1 <-.
  move: H;rewrite Heq1=> {Heq1}.
  case: (vm2.[x])%vmap => //= z2 Hz2.
  by exists (pto_val z2) => //;apply pval_uinclP.
Qed.

Corollary get_var_uincl x vm1 vm2 v1:
  vm_uincl vm1 vm2 ->
  get_var vm1 x = ok v1 ->
  exists2 v2, get_var vm2 x = ok v2 & value_uincl v1 v2.
Proof. by move => /(_ x); exact: get_var_uincl_at. Qed.

Lemma  get_vars_uincl (xs:seq var_i) vm1 vm2 vs1:
  vm_uincl vm1 vm2 ->
  mapM (fun x => get_var vm1 (v_var x)) xs = ok vs1 ->
  exists2 vs2,
    mapM (fun x => get_var vm2 (v_var x)) xs = ok vs2 & List.Forall2 value_uincl vs1 vs2.
Proof.
  move=> Hvm;elim: xs vs1 => [ | x xs Hrec] /= ?.
  + move=> [<-]; exists [::] => //; constructor.
  apply: rbindP => v1 /(get_var_uincl Hvm) [v2 -> ?].
  apply: rbindP => vs1 /Hrec [vs2 -> ?] [] <- /=; exists (v2::vs2) => //.
  by constructor.
Qed.

Lemma get_gvar_uincl_at x gd vm1 vm2 v1:
  (if is_lvar x then eval_uincl vm1.[gv x] vm2.[gv x] else True)%vmap ->
  get_gvar gd vm1 x = ok v1 ->
  exists2 v2, get_gvar gd vm2 x = ok v2 & value_uincl v1 v2.
Proof.
  rewrite /get_gvar; case:ifP => _.
  + exact: get_var_uincl_at.
  by move=> ? ->;exists v1.
Qed.

Corollary get_gvar_uincl x gd vm1 vm2 v1:
  vm_uincl vm1 vm2 ->
  get_gvar gd vm1 x = ok v1 ->
  exists2 v2, get_gvar gd vm2 x = ok v2 & value_uincl v1 v2.
Proof. by move => /(_ x.(gv)) h; apply: get_gvar_uincl_at; case: ifP. Qed.

Lemma val_uincl_eq t (x y: sem_t t) :
  val_uincl x y →
  ~~is_sarr t ->
  y = x.
Proof.
  case: t x y => //.
  by move => sz /= x y /andP [] _ /eqP ->; rewrite zero_extend_u.
Qed.

Lemma vuincl_sem_sop2 o ve1 ve1' ve2 ve2' v1 :
  value_uincl ve1 ve1' -> value_uincl ve2 ve2' ->
  sem_sop2 o ve1 ve2 = ok v1 ->
  sem_sop2 o ve1' ve2' = ok v1.
Proof.
  move => h1 h2; rewrite /sem_sop2 /=; t_xrbindP => w1 ok_w1 w2 ok_w2 w3 ok_w3 <-.
  have {ok_w1} [z1 [-> /= hz1]] := of_val_uincl h1 ok_w1.
  have {ok_w2} [z2 [-> /= hz2]] := of_val_uincl h2 ok_w2.
  case: o w1 w2 w3 ok_w3 z1 hz1 z2 hz2 => /=
   [||[|s]|[|s]|[|s]| [|u s]|[|u s]| s|s|s|s|s|s| [|s]|[|s]| [|u s]|[|u s]|[|u s]|[|u s]
    | ve s | ve s | ve s | ve s | ve s | ve s ] /=.
  10, 12: by rewrite /mk_sem_divmod => w1 w2 w3; case: ifP => // h [<-] z1 /val_uincl_eq -> // z2 /val_uincl_eq /(_ erefl) ->; rewrite h.
  all: by move => ??? [<-] ? /val_uincl_eq -> // ? /val_uincl_eq ->.
Qed.

Lemma val_uincl_sword s (z z':sem_t (sword s)) : val_uincl z z' -> z = z'.
Proof.
  by rewrite /val_uincl /= /word_uincl cmp_le_refl zero_extend_u => /eqP.
Qed.

Lemma vuincl_sem_sop1 o ve1 ve1' v1 :
  value_uincl ve1 ve1' ->
  sem_sop1 o ve1 = ok v1 ->
  sem_sop1 o ve1' = ok v1.
Proof.
  case: o => [ sz | sz | szo szi | szo szi | | sz | [| sz] ].
  - by move => h; apply: rbindP => /= z1 /(value_uincl_int h) [??][?]; subst.
  - move => h; apply: rbindP => /= z1 /(value_uincl_word h) {h}h [?]; subst.
    by rewrite /sem_sop1 /= h.
  1-2:
    case: ve1 => // [ | [] // ] sz1 w1 /value_uinclE [sz2] [w2] [-> {ve1'}] /andP [] hle /eqP -> {w1};
    rewrite /sem_sop1 /=; t_xrbindP => /= y /truncate_wordP [hle'] -> <-;
    by rewrite /truncate_word (cmp_le_trans hle' hle) /= (zero_extend_idem _ hle').
  all:
    move => Hu;
    apply: rbindP => z Hz;
    rewrite /sem_sop1 /= => [<-].
  2, 4: by have [z' [/= -> /val_uincl_sword ->]] := of_val_uincl Hu Hz.
  all: by have [z' [/= -> ->]] := of_val_uincl Hu Hz.
Qed.

Lemma vuincl_sopn T ts o vs vs' (v: T) :
  all is_not_sarr ts ->
  List.Forall2 value_uincl vs vs' ->
  app_sopn ts o vs = ok v ->
  app_sopn ts o vs' = ok v.
Proof.
  elim: ts o vs vs' => /= [ | t ts Hrec] o [] //.
  + by move => vs' _ /List_Forall2_inv_l -> ->; eauto using List_Forall2_refl.
  move => n vs vs'' /andP [] ht hts /List_Forall2_inv_l [v'] [vs'] [->] {vs''} [hv hvs].
  case: t o ht => //= [ | | sz ] o _; apply: rbindP.
  + by move=> b /(value_uincl_bool hv) [] _ -> /= /(Hrec _ _ _ hts hvs).
  + by move=> z /(value_uincl_int hv) [] _ -> /= /(Hrec _ _ _ hts hvs).
  by move=> w /(value_uincl_word hv) -> /= /(Hrec _ _ _ hts hvs).
Qed.

Lemma vuincl_sem_opN op vs v vs' :
  sem_opN op vs = ok v →
  List.Forall2 value_uincl vs vs' →
  exists2 v' : value, sem_opN op vs' = ok v' & value_uincl v v'.
Proof.
  rewrite /sem_opN.
  apply: rbindP => q ok_q [<-{v}] hvs.
  have -> /= := vuincl_sopn _ hvs ok_q.
  + by eauto.
  case: {q ok_q} op => //.
  by move => sz n; rewrite /= all_nseq orbT.
Qed.

(* --------------------------------------------------------- *)
(* VMAP_UINCL_ON *)
Definition vmap_uincl_on (dom: Sv.t) : relation vmap :=
  λ vm1 vm2,
  ∀ x : var, Sv.In x dom → (eval_uincl vm1.[x] vm2.[x])%vmap.

Lemma eq_on_vmap_uincl_on dom vm1 vm2 :
  vm1 =[dom] vm2 →
  vmap_uincl_on dom vm1 vm2.
Proof. by move => heq x /heq ->. Qed.

Lemma vm_uincl_vmap_uincl_on dom vm1 vm2 :
  vm_uincl vm1 vm2 →
  vmap_uincl_on dom vm1 vm2.
Proof. by move => h x _; exact: h. Qed.

Instance vmap_uincl_on_m : Proper (Sv.Equal ==> eq ==> eq ==> iff) vmap_uincl_on.
Proof. by move => d d' hd vm1 _ <- vm2 _ <-; split => h x hx; apply: h; rewrite ?hd // -hd. Qed.

Lemma vmap_uincl_onI d d' vm1 vm2 :
  Sv.Subset d d' →
  vmap_uincl_on d' vm1 vm2 →
  vmap_uincl_on d vm1 vm2.
Proof. by move => hd h x hx; apply: h; SvD.fsetdec. Qed.

Instance vmap_uincl_on_refl dom : Reflexive (vmap_uincl_on dom).
Proof. by do 2 red. Qed.

Instance vmap_uincl_on_trans dom : Transitive (vmap_uincl_on dom).
Proof. move => x y z xy yz r hr; apply: (eval_uincl_trans (xy _ hr)); exact: yz. Qed.

Lemma vmap_uincl_on_union dom dom' vm1 vm2 :
  vmap_uincl_on (Sv.union dom dom') vm1 vm2 →
  vmap_uincl_on dom vm1 vm2 ∧ vmap_uincl_on dom' vm1 vm2.
Proof. by move => h; split => x hx; apply: h; SvD.fsetdec. Qed.
(* --------------------------------------------------------- *)

Lemma sem_pexpr_uincl_on_rec gd s1 vm2 es vs1 :
  vmap_uincl_on (read_es es) s1.(evm) vm2 →
  sem_pexprs gd s1 es = ok vs1 →
  (∀ e : pexpr, e \in es →
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
  rewrite read_es_cons => /vmap_uincl_on_union[] hvm /ih{ih}ih /=.
  t_xrbindP => v ok_v vs ok_vs <-{vs1} rec.
  move: ih => /(_ _ ok_vs) [].
  + by move => e' he'; apply: rec; rewrite in_cons he' orbT.
  move => vs' ok_vs' hs.
  move: rec => /(_ e _ _ hvm ok_v) [].
  + by rewrite in_cons eqxx.
  move => v' ok_v' h.
  exists (v' :: vs').
  + by rewrite ok_v' ok_vs'.
  by constructor.
Qed.

Lemma sem_pexpr_uincl_on gd s1 vm2 e v1 :
  vmap_uincl_on (read_e e) s1.(evm) vm2 →
  sem_pexpr gd s1 e = ok v1 →
  exists2 v2, sem_pexpr gd (with_vm s1 vm2) e = ok v2 & value_uincl v1 v2.
Proof.
  elim: e v1=>//=[z|b|n|x|aa ws x p Hp|aa ws len x p Hp|sz x p Hp|o e He|o e1 He1 e2 He2 | op es Hes | t e He e1 He1 e2 He2 ] v1 Hu.
  + by move=> [] <-;exists z.
  + by move=> [] <-;exists b.
  + by case => <-; eauto.
  + apply: get_gvar_uincl_at; move: Hu; rewrite /read_e /= /read_gvar.
    case: ifP => // _; apply; SvD.fsetdec.
  + move: Hu; rewrite /read_e /= read_eE => /vmap_uincl_on_union[] /Hp{Hp}Hp Hu.
    apply on_arr_gvarP => n t Htx; rewrite /on_arr_var => /get_gvar_uincl_at - /(_ vm2) [ |  v2 -> ].
    * move: Hu; rewrite /read_gvar; case: ifP => // _; apply; SvD.fsetdec.
    case: v2 => //= n' t' hu.
    apply: rbindP => z; apply: rbindP => vp /Hp [] vp' -> /= Hvu Hto.
    case: (value_uincl_int Hvu Hto) => ??;subst.
    apply: rbindP=> w Hget [] <- /=.
    by rewrite (WArray.uincl_get hu Hget) /=;eexists; eauto=> //=.
  + move: Hu; rewrite /read_e /= read_eE => /vmap_uincl_on_union[] /Hp{Hp}Hp Hu.
    apply on_arr_gvarP => n t Htx; rewrite /on_arr_var => /get_gvar_uincl_at - /(_ vm2) [ | v2 -> ].
    * move: Hu; rewrite /read_gvar; case: ifP => // _; apply; SvD.fsetdec.
    case: v2 => //= n' t' hu.
    apply: rbindP => z;apply: rbindP => vp /Hp [] vp' -> /= Hvu Hto.
    case: (value_uincl_int Hvu Hto) => ??;subst.
    apply: rbindP=> w Hget [] <- /=.
    have [w' -> ? /=]:= WArray.uincl_get_sub hu Hget.
    by eexists; eauto=> //=.
  + move: Hu; rewrite /read_e /= read_eE => /vmap_uincl_on_union[] /Hp{Hp}Hp Hu.
    apply: rbindP => w1; apply: rbindP => vx /get_var_uincl_at - /(_ vm2) [ | vx' -> ].
    * apply: Hu; SvD.fsetdec.
    move=> /value_uincl_word H/H{H} /= -> /=.
    apply: rbindP => wp;apply: rbindP => vp /Hp [] vp' ->.
    by move=> /value_uincl_word Hvu/Hvu {Hvu} /= -> /= ->; eauto.
  + move: Hu; rewrite /read_e /= read_eE => /vmap_uincl_on_union[] /He{He}He Hu.
    apply: rbindP => ve1 /He [] ve1' -> /vuincl_sem_sop1 Hvu1 /Hvu1.
    by exists v1.
  + move: Hu; rewrite /read_e /= read_eE => /vmap_uincl_on_union[] /He1{He1}He1 /He2{He2} He2.
    apply: rbindP => ve1 /He1 [] ve1' -> /vuincl_sem_sop2 Hvu1.
    apply: rbindP => ve2 /He2 [] ve2' -> /Hvu1 Hvu2 /Hvu2.
    by exists v1.
  + t_xrbindP => vs ok_vs ok_v1; rewrite -/(sem_pexprs gd _).
    have [vs' -> /=] := sem_pexpr_uincl_on_rec Hu ok_vs Hes.
    exact: vuincl_sem_opN.
  move: Hu. rewrite /read_e /= !read_eE => /vmap_uincl_on_union [] /He{He}He /vmap_uincl_on_union[] /He1{He1}He1.
  rewrite SvP.MP.empty_union_2; last exact: Sv.empty_spec.
  move => /He2{He2}He2.
  t_xrbindP => b ve /He [] ve' -> Hue' /value_uincl_bool -/(_ _ Hue')[??]; subst ve ve'.
  move=> vte1 ve1 /He1 [] ve1' -> /= Hue1' /(truncate_value_uincl Hue1') [] vte1' -> Huvte1.
  move=> vte2 ve2 /He2 [] ve2' -> /= Hue2' /(truncate_value_uincl Hue2') [] vte2' -> Huvte2 /= <-.
  eexists;first by reflexivity.
  by case: (b).
Qed.

Corollary sem_pexpr_uincl gd s1 vm2 e v1 :
  vm_uincl s1.(evm) vm2 →
  sem_pexpr gd s1 e = ok v1 →
  exists2 v2, sem_pexpr gd (with_vm s1 vm2) e = ok v2 & value_uincl v1 v2.
Proof. move => /(@vm_uincl_vmap_uincl_on (read_e e)); exact: sem_pexpr_uincl_on. Qed.

Lemma sem_pexprs_uincl_on gd s1 vm2 es vs1 :
  vmap_uincl_on (read_es es) s1.(evm) vm2 →
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

Lemma value_uincl_is_word v v' sz u :
  value_uincl v v' →
  is_word sz v = ok u →
  is_word sz v' = ok tt.
Proof.
move => /value_uinclE; case: v => // [ sz' w | [] // sz' ].
+ by case => ? [] ? [] ->.
by case: v' => // - [].
Qed.

Lemma vuincl_exec_opn_eq o vs vs' v :
  List.Forall2 value_uincl vs vs' -> exec_sopn o vs = ok v ->
  exec_sopn o vs' = ok v.
Proof.
rewrite /exec_sopn /sopn_sem => h1; t_xrbindP => vs1 h2 h3.
by have -> /= := vuincl_sopn (tin_narr _) h1 h2;rewrite h3.
Qed.

Lemma vuincl_exec_opn o vs vs' v :
  List.Forall2 value_uincl vs vs' -> exec_sopn o vs = ok v ->
  exists v', exec_sopn o vs' = ok v' /\ List.Forall2  value_uincl v v'.
Proof. move => /vuincl_exec_opn_eq h /h {h}; eauto using List_Forall2_refl. Qed.

Lemma set_vm_uincl vm vm' x z z' :
  vm_uincl vm vm' ->
  eval_uincl z z' ->
  vm_uincl (vm.[x <- z])%vmap (vm'.[x <- z'])%vmap.
Proof.
  move=> Hvm Hz y; case( x =P y) => [<- | /eqP Hneq];by rewrite ?Fv.setP_eq ?Fv.setP_neq.
Qed.

Lemma of_val_error t v:
  of_val t v = undef_error -> exists2 t', v = Vundef t' & subtype t t'.
Proof.
case: t v => [||p|sz] [] //=.
+ by case => //; eauto.
+ by case => //; eauto.
+ by move => n a; rewrite /WArray.cast; case: ifPn.
+ by case => // ?;case:ifP => // ? _; eexists; first by reflexivity.
+ by move=> ??;rewrite /truncate_word;case:ifP.
by case => // sz'; case: ifP => // hle _; eauto.
Qed.

Lemma pof_val_error t v:
  pof_val t v = undef_error -> exists t', subtype (vundef_type t) t' /\ v = Vundef t'.
Proof.
case: t v => [||p|sz] [] //=.
+ by case => //;eauto.
+ by case => //;eauto.
+ by move => [].
case => // s _;eexists;split;last reflexivity.
by apply wsize_le_U8.
Qed.

Lemma subtype_pof_val_ok t1 t2 v v1 :
  subtype t1 t2 ->
  pof_val t1 v = ok v1 ->
  exists2 v2, pof_val t2 v = ok v2 & value_uincl (pto_val v1) (pto_val v2).
Proof.
  case: t1 v1 => /= [v1 /eqP<-|v1 /eqP<-|n v1 |s1 v1];
   try by move=> h; eexists; [apply h | done].
  + case: t2 => // p' /ZleP hle /=.
    case: v => //=; last by case.
    move=> len a [<-]; eexists;first by reflexivity.
    by split => // i v hi; rewrite !WArray.zget_inject //; lia.
  case: t2 => //= s2 hle;case: v => //=;last by case.
  move=> s' w [<-]; eexists; first reflexivity.
  case: Sumbool.sumbool_of_bool => e /=.
  + by rewrite (sumbool_of_boolET (cmp_le_trans e hle)).
  case: Sumbool.sumbool_of_bool => e' /=.
  + move: e => /negbT e.
    apply/andP; split => //; exact: cmp_nle_le.
  rewrite -(zero_extend_idem _ hle).
  exact: word_uincl_zero_ext.
Qed.

Lemma pof_val_pto_val t (v:psem_t t): pof_val t (pto_val v) = ok v.
Proof.
  case: t v => [b | z | n a | s w] //=.
  + by f_equal; rewrite /WArray.inject Z.ltb_irrefl; case: a.
  case: Sumbool.sumbool_of_bool => e.
  + f_equal;case: w e => /= ????;f_equal; apply eq_irrelevance.
  by have := pw_proof w;rewrite e.
Qed.

Lemma value_uincl_pof_val t v1 (v1' v2 : psem_t t):
  pof_val t v1 = ok v1' ->
  value_uincl v1 (pto_val v2) ->
  value_uincl (pto_val v1') (pto_val v2).
Proof.
  case: t v1' v2 => /= [||n|s] v1' v2.
  + by move=> /to_boolI ->.
  + by move=> h1 h2;have [? [<-]]:= value_uincl_int h2 h1.
  + case: v1 => //= [ len a| []//] [<-] [hlen hget].
    apply: val_uincl_array => i v hi.
    by rewrite WArray.zget_inject //; case:ZltP => // ?; apply hget; lia.
  case: v1 => //= [ s' w| [] //] [<-].
  case: Sumbool.sumbool_of_bool => //= /negbT hnle.
  have hle := cmp_nle_le hnle; apply: word_uincl_trans.
  exact: word_uincl_zero_ext.
Qed.

Lemma subtype_eval_uincl_pundef t1 t2 :
  subtype t1 t2 ->
  eval_uincl (pundef_addr t1) (pundef_addr t2).
Proof.
  case: t1 => /= [/eqP?|/eqP?|n| s];subst => //=; case: t2 => //=.
  by move=> ? /ZleP ?.
Qed.

Lemma to_bool_undef v :
  to_bool v = undef_error -> v = Vundef sbool.
Proof. by case: v => //= -[]. Qed.

Lemma type_of_val_bool v : type_of_val v = sbool ->
  v = Vundef sbool \/ exists b, v = Vbool b.
Proof.
  case: v => //=; first by eauto.
  by move=> [] //=;auto.
Qed.

Lemma to_int_undef v :
  to_int v = undef_error -> v = Vundef sint.
Proof. by case: v => //= -[]. Qed.

Lemma type_of_val_int v : type_of_val v = sint ->
  v = Vundef sint \/ exists n, v = Vint n.
Proof.
  case: v => //=;first eauto.
  by move=> [] //=;auto.
Qed.

Lemma to_arr_undef p v : to_arr p v = undef_error ->
  exists p', v = Vundef (sarr p') /\ (p <= p').
Proof.
  case:v => //=.
  + by move=> ??; rewrite /WArray.cast; case: ifP.
  case => //= p'; case: ifPn => //= /ZleP hle _;eauto.
Qed.

Lemma to_parr_undef p v : to_parr p v <> undef_error.
Proof. by case:v => //= -[]. Qed.

Lemma type_of_val_arr n v : type_of_val v = sarr n ->
  (exists p, v = Vundef (sarr p)) \/ exists (a:WArray.array n), v = Varr a.
Proof.
  case: v => //=.
  + by move=> ? a [<-]; eauto.
   move=> [] //= ??;eauto.
Qed.

Lemma to_pword_undef w v :
  to_pword w v = undef_error -> exists w', v = Vundef (sword w').
Proof. case: v => //= -[] // w' _;eauto. Qed.

Lemma compat_type_word w t : compat_type (sword w) t -> exists w', t = sword w'.
Proof. case: t => //; eauto. Qed.

Lemma type_of_val_word v wz :
  type_of_val v = sword wz ->
  exists wz',
   v = Vundef (sword wz') \/ exists (w:word wz'), v = Vword w.
Proof.
  case: v => //=;first by eauto.
  by case => //; eauto.
Qed.

Lemma pof_val_bool_undef v : pof_val sbool v = undef_error -> v = Vundef sbool.
Proof. by case: v => //= -[]. Qed.

Lemma pof_val_undef v v':
  value_uincl v v' ->
  pof_val sbool v = undef_error ->
  v' = Vundef sbool \/ exists b, v' = Vbool b.
Proof.
  by move=> hv hp;move: hp hv => /pof_val_bool_undef -> /= /eqP /type_of_val_bool.
Qed.

Lemma set_var_uincl vm1 vm1' vm2 x v v' :
  vm_uincl vm1 vm1' ->
  value_uincl v v' ->
  set_var vm1 x v = ok vm2 ->
  exists2 vm2', set_var vm1' x v' = ok vm2' & vm_uincl vm2 vm2'.
Proof.
  (move=> Hvm Hv;apply set_varP;rewrite /set_var) => [t | hb].
  + move=> /(pof_val_uincl Hv) [z' [-> ?]] <- /=.
    by exists (vm1'.[x <- ok z'])%vmap => //; apply set_vm_uincl.
  by rewrite hb;case: x hb => /= xt xn /eqP -> /(pof_val_undef Hv) [->| [b ->]] /= <-;
    (eexists;first reflexivity); apply set_vm_uincl.
Qed.

Lemma Array_set_uincl n1 n2
   (a1 a1': WArray.array n1) (a2 : WArray.array n2) wz aa i (v:word wz):
  @val_uincl (sarr n1) (sarr n2) a1 a2 ->
  WArray.set a1 aa i v = ok a1' ->
  exists2 a2', WArray.set a2 aa i v = ok a2' &
      @val_uincl (sarr n1) (sarr n2) a1' a2'.
Proof.
  rewrite /val_uincl /= => hu hs.
  by have [?[]]:= WArray.uincl_set hu hs; eauto.
Qed.

Lemma write_var_uincl s1 s2 vm1 v1 v2 x :
  vm_uincl (evm s1) vm1 ->
  value_uincl v1 v2 ->
  write_var x v1 s1 = ok s2 ->
  exists2 vm2 : vmap,
    write_var x v2 (with_vm s1 vm1) = ok (with_vm s2 vm2) & 
    vm_uincl (evm s2) vm2.
Proof.
  move=> Hvm1 Hv;rewrite /write_var;t_xrbindP => vm1' Hmv1' <- /=.
  by have [vm2' -> ? /=] := set_var_uincl Hvm1 Hv Hmv1'; exists vm2'.
Qed.

Lemma write_vars_uincl s1 s2 vm1 vs1 vs2 xs :
  vm_uincl (evm s1) vm1 ->
  List.Forall2 value_uincl vs1 vs2 ->
  write_vars xs vs1 s1 = ok s2 ->
  exists2 vm2 : vmap,
    write_vars xs vs2 (with_vm s1 vm1) = ok (with_vm s2 vm2) & 
    vm_uincl (evm s2) vm2.
Proof.
  elim: xs s1 vm1 vs1 vs2 => /= [ | x xs Hrec] s1 vm1 vs1 vs2 Hvm [] //=.
  + by move=> [] <-;eauto.
  move=> {vs1 vs2} v1 v2 vs1 vs2 Hv Hvs;apply: rbindP => s1'.
  by move=> /(write_var_uincl Hvm Hv) [] vm2 -> Hvm2 /(Hrec _ _ _ _ Hvm2 Hvs).
Qed.

Lemma is_sword_subtype t1 t2 : subtype t1 t2 -> is_sword t1 = is_sword t2.
Proof.
  by case: t1 => //= [/eqP <-|/eqP <-|?|?] //;case:t2.
Qed.

Lemma uincl_write_none s2 v1 v2 s s' t:
  value_uincl v1 v2 ->
  write_none s t v1 = ok s' ->
  write_none s2 t v2 = ok s2.
Proof.
  move=> Hv /write_noneP [_] H;rewrite /write_none.
  case: H.
  + by move=> [w1] /(pof_val_uincl Hv) [w2 [->]].
  by move=> [] H1 ?;subst t;move /(pof_val_undef Hv): H1 => [ | [b]] ->.
Qed.

Lemma write_uincl gd s1 s2 vm1 r v1 v2:
  vm_uincl s1.(evm) vm1 ->
  value_uincl v1 v2 ->
  write_lval gd r v1 s1 = ok s2 ->
  exists2 vm2,
    write_lval gd r v2 (with_vm s1 vm1) = ok (with_vm s2 vm2) &
    vm_uincl s2.(evm) vm2.
Proof.
  move=> Hvm1 Hv;case:r => [xi ty | x | sz x p | aa sz1 x p | aa sz1 len x p] /=.
  + move=> H; have [-> _]:= write_noneP H.
    by rewrite (uincl_write_none _ Hv H);exists vm1.
  + by apply write_var_uincl.
  + apply: rbindP => vx1; apply: rbindP => vx /(get_var_uincl Hvm1) [vx2 -> Hvx].
    move=> /= /(value_uincl_word Hvx) -> {Hvx vx} /=.
    apply: rbindP => ve; apply: rbindP => ve' /(sem_pexpr_uincl Hvm1) [ve''] -> Hve.
    move=> /(value_uincl_word Hve) /= -> /=.
    apply: rbindP => w /(value_uincl_word Hv) -> /=.
    by apply: rbindP => m' -> [] <- /=; exists vm1.
  + apply: on_arr_varP => n a Htx /(get_var_uincl Hvm1).
    rewrite /on_arr_var => -[] vx /= -> /=.
    case: vx => //= n0 t0 hu.
    t_xrbindP => i vp /(sem_pexpr_uincl Hvm1) [vp' -> Hvp] /=.
    move=>  /(value_uincl_int Hvp) [] _ -> /= v /(value_uincl_word Hv) -> /=.
    move=> t /(WArray.uincl_set hu) [] t' [-> htt'] vm'.
    have ht : value_uincl (Varr t) (Varr t') by apply htt'.
    by move=> /(set_var_uincl Hvm1 ht) /= [vm2' -> ?] <- /=;exists vm2'.
  apply: on_arr_varP => n a Htx /(get_var_uincl Hvm1).
  rewrite /on_arr_var => -[] vx /= -> /=.
  case: vx => //= n0 t0 hu.
  t_xrbindP => i vp /(sem_pexpr_uincl Hvm1) [vp' -> Hvp] /=.
  move=>  /(value_uincl_int Hvp) [] _ -> /= t.
  move=> /(value_uincl_arr Hv) [t' ->] htt' t1 /(WArray.uincl_set_sub hu htt').
  move=> [t2 /= -> hu2] vm'.
  have ht : value_uincl (Varr t1) (Varr t2) by apply hu2.
  by move=> /(set_var_uincl Hvm1 ht) /= [vm2' -> ?] <- /=;exists vm2'.
Qed.

Lemma writes_uincl gd s1 s2 vm1 r v1 v2:
  vm_uincl s1.(evm) vm1 ->
  List.Forall2 value_uincl v1 v2 ->
  write_lvals gd s1 r v1 = ok s2 ->
  exists2 vm2,
    write_lvals gd (with_vm s1 vm1) r v2 = ok (with_vm s2 vm2) &
    vm_uincl s2.(evm) vm2.
Proof.
  elim: r v1 v2 s1 s2 vm1 => [ | r rs Hrec] ?? s1 s2 vm1 Hvm1 /= [] //=.
  + by move=> [] <-;eauto.
  move=> v1 v2 vs1 vs2 Hv Hforall.
  apply: rbindP => z /(write_uincl Hvm1 Hv) [] vm2 -> Hvm2.
  by move=> /(Hrec _ _ _ _ _ Hvm2 Hforall).
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
  mapM (fun x : var_i => get_var (evm s) x) xs.
Proof.
  rewrite /sem_pexprs;elim: xs=> //= x xs Hrec.
  rewrite /get_gvar /=.
  by case: get_var => //= v;rewrite Hrec.
Qed.

Section UNDEFINCL.

Context {T} {pT:progT T} {sCP : semCallParams}.
Variable p : prog.
Variable ev : extra_val_t.

Notation gd:= (p_globs p).

Let Pc s1 c s2 :=
  forall vm1 ,
    vm_uincl (evm s1) vm1 ->
    exists vm2,
      sem p ev (with_vm s1 vm1) c (with_vm s2 vm2) /\
      vm_uincl (evm s2) vm2.

Let Pi_r s1 i s2 :=
  forall vm1,
    vm_uincl (evm s1) vm1 ->
    exists vm2,
      sem_i p ev (with_vm s1 vm1) i (with_vm s2 vm2) /\
      vm_uincl (evm s2) vm2.

Let Pi s1 i s2 :=
  forall vm1,
    vm_uincl (evm s1) vm1 ->
    exists vm2,
      sem_I p ev (with_vm s1 vm1) i (with_vm s2 vm2) /\
      vm_uincl (evm s2) vm2.

Let Pfor (i:var_i) zs s1 c s2 :=
  forall vm1,
    vm_uincl (evm s1) vm1 ->
    exists vm2,
      sem_for p ev i zs (with_vm s1 vm1) c (with_vm s2 vm2) /\
      vm_uincl (evm s2) vm2.

Let Pfun m1 fd vargs m2 vres :=
  forall vargs',
    List.Forall2 value_uincl vargs vargs' ->
    exists vres',
      sem_call p ev m1 fd vargs' m2 vres' /\
      List.Forall2 value_uincl vres vres'.

Local Lemma Hnil : sem_Ind_nil Pc.
Proof. by move=> s vm1 Hvm1;exists vm1;split=> //;constructor. Qed.

Local Lemma Hcons : sem_Ind_cons p ev Pc Pi.
Proof.
  move=> s1 s2 s3 i c _ Hi _ Hc vm1 /Hi [vm2 []] Hsi /Hc [vm3 []] Hsc ?.
  by exists vm3;split=>//;econstructor;eauto.
Qed.

Local Lemma HmkI : sem_Ind_mkI p ev Pi_r Pi.
Proof. by move=> ii i s1 s2 _ Hi vm1 /Hi [vm2 []] Hsi ?;exists vm2. Qed.

Local Lemma Hasgn : sem_Ind_assgn p Pi_r.
Proof.
  move=> s1 s2 x tag ty e v v' hsem hty hwr vm1 Hvm1.
  have [w hsem' hle]:= sem_pexpr_uincl Hvm1 hsem.
  have [w'' hty' hle'] := truncate_value_uincl hle hty.
  have  [vm2 Hw ?]:= write_uincl Hvm1 hle' hwr;exists vm2;split=> //.
  by econstructor;first exact hsem'; eauto.
Qed.

Local Lemma Hopn : sem_Ind_opn p Pi_r.
Proof.
  move=> s1 s2 t o xs es H vm1 Hvm1; apply: rbindP H => rs;apply: rbindP => vs.
  move=> /(sem_pexprs_uincl Hvm1) [] vs' H1 H2.
  move=> /(vuincl_exec_opn H2) [] rs' [] H3 H4.
  move=> /(writes_uincl Hvm1 H4) [] vm2 ??.
  exists vm2;split => //;constructor.
  by rewrite /sem_sopn H1 /= H3.
Qed.

Local Lemma Hif_true : sem_Ind_if_true p ev Pc Pi_r.
Proof.
  move=> s1 s2 e c1 c2 H _ Hc vm1 Hvm1.
  have [v' H1 /value_uincl_bool1 ?]:= sem_pexpr_uincl Hvm1 H;subst v'.
  have [vm2 [??]]:= Hc _ Hvm1;exists vm2;split=>//.
  by apply Eif_true;rewrite // H1.
Qed.

Local Lemma Hif_false : sem_Ind_if_false p ev Pc Pi_r.
Proof.
  move=> s1 s2 e c1 c2 H _ Hc vm1 Hvm1.
  have [v' H1 /value_uincl_bool1 ?]:= sem_pexpr_uincl Hvm1 H;subst v'.
  have [vm2 [??]]:= Hc _ Hvm1;exists vm2;split=>//.
  by apply Eif_false;rewrite // H1.
Qed.

Local Lemma Hwhile_true : sem_Ind_while_true p ev Pc Pi_r.
Proof.
  move=> s1 s2 s3 s4 a c e c' _ Hc H _ Hc' _ Hw vm1 Hvm1.
  have [vm2 [Hs2 Hvm2]] := Hc _ Hvm1.
  have [v' H1 /value_uincl_bool1 ?]:= sem_pexpr_uincl Hvm2 H;subst.
  have [vm3 [H4 /Hw [vm4] [??]]]:= Hc' _ Hvm2;exists vm4;split => //.
  by eapply Ewhile_true;eauto;rewrite H1.
Qed.

Local Lemma Hwhile_false : sem_Ind_while_false p ev Pc Pi_r.
Proof.
  move=> s1 s2 a c e c' _ Hc H vm1 Hvm1.
  have [vm2 [Hs2 Hvm2]] := Hc _ Hvm1.
  have [v' H1 /value_uincl_bool1 ?]:= sem_pexpr_uincl Hvm2 H;subst.
  by exists vm2;split=> //;apply: Ewhile_false=> //;rewrite H1.
Qed.

Local Lemma Hfor : sem_Ind_for p ev Pi_r Pfor.
Proof.
  move=> s1 s2 i d lo hi c vlo vhi H H' _ Hfor vm1 Hvm1.
  have [? H1 /value_uincl_int1 ?]:= sem_pexpr_uincl Hvm1 H;subst.
  have [? H3 /value_uincl_int1 ?]:= sem_pexpr_uincl Hvm1 H';subst.
  have [vm2 []??]:= Hfor _ Hvm1; exists vm2;split=>//.
  by econstructor;eauto;rewrite ?H1 ?H3.
Qed.

Local Lemma Hfor_nil : sem_Ind_for_nil Pfor.
Proof. by move=> s i c vm1 Hvm1;exists vm1;split=> //;constructor. Qed.

Local Lemma Hfor_cons : sem_Ind_for_cons p ev Pc Pfor.
Proof.
  move=> s1 s1' s2 s3 i w ws c Hi _ Hc _ Hf vm1 Hvm1.
  have [vm1' Hi' /Hc] := write_var_uincl Hvm1 (value_uincl_refl _) Hi.
  move=> [vm2 [Hsc /Hf]] [vm3 [Hsf Hvm3]];exists vm3;split => //.
  by econstructor;eauto.
Qed.

Local Lemma Hcall : sem_Ind_call p ev Pi_r Pfun.
Proof.
  move=> s1 m2 s2 ii xs fn args vargs vs Hargs Hcall Hfd Hxs vm1 Hvm1.
  have [vargs' Hsa /Hfd [vs' [Hc Hvres]]]:= sem_pexprs_uincl Hvm1 Hargs.
  have Hvm1' : vm_uincl (evm (with_mem s1 m2)) vm1 by done.
  have [vm2' ??] := writes_uincl Hvm1' Hvres Hxs.
  exists vm2';split=>//.
  econstructor;eauto.
Qed.

Lemma check_ty_val_uincl v1 x v2 :
  check_ty_val x v1 → value_uincl v1 v2 → check_ty_val x v2.
Proof.
  rewrite /check_ty_val => h /value_uincl_subtype.
  by apply: subtype_trans.
Qed.

Lemma all2_check_ty_val v1 x v2 :
  all2 check_ty_val x v1 → List.Forall2 value_uincl v1 v2 → all2 check_ty_val x v2.
Proof.
  move=> /all2P H1 H2;apply /all2P;apply: Forall2_trans H1 H2;apply check_ty_val_uincl.
Qed.

Local Lemma Hproc : sem_Ind_proc p ev Pc Pfun.
Proof.
  move=> m1 m2 fn fd vargs vargs' s0 s1 s2 vres vres' Hget Hca hi Hargs Hsem Hrec Hmap Hcr Hfi vargs1' Uargs.
  have [vargs2' hm2 Uargs']:= mapM2_truncate_val Hca Uargs.
  have := write_vars_uincl (vm_uincl_refl _) Uargs' Hargs.
  rewrite with_vm_same => -[vm1 Hargs' Hvm1].
  have [vm2' /= [] Hsem' Uvm2]:= Hrec _ Hvm1.
  have [vs2 Hvs2 Hsub] := get_vars_uincl Uvm2 Hmap.
  have [vres2' hmr2 Ures']:= mapM2_truncate_val Hcr Hsub.
  by exists vres2';split=>//;econstructor;eauto.
Qed.

Lemma sem_call_uincl vargs m1 f m2 vres vargs':
  List.Forall2 value_uincl vargs vargs' ->
  sem_call p ev m1 f vargs m2 vres ->
  exists vres', sem_call p ev m1 f vargs' m2 vres' /\ List.Forall2 value_uincl vres vres'.
Proof.
  move=> H1 H2.
  by apply:
    (@sem_call_Ind _ _ _ p ev Pc Pi_r Pi Pfor Pfun Hnil Hcons HmkI Hasgn Hopn
        Hif_true Hif_false Hwhile_true Hwhile_false Hfor Hfor_nil Hfor_cons Hcall Hproc) H1.
Qed.

Lemma sem_i_uincl s1 i s2 vm1 :
  vm_uincl (evm s1) vm1 ->
  sem_i p ev s1 i s2 ->
  exists vm2,
    sem_i p ev (with_vm s1 vm1) i (with_vm s2 vm2) /\
    vm_uincl (evm s2) vm2.
Proof.
  move=> H1 H2.
  by apply:
    (@sem_i_Ind _ _ _ p ev Pc Pi_r Pi Pfor Pfun Hnil Hcons HmkI Hasgn Hopn
        Hif_true Hif_false Hwhile_true Hwhile_false Hfor Hfor_nil Hfor_cons Hcall Hproc) H1.
Qed.

Lemma sem_I_uincl s1 i s2 vm1 :
  vm_uincl (evm s1) vm1 ->
  sem_I p ev s1 i s2 ->
  exists vm2,
    sem_I p ev (with_vm s1 vm1) i (with_vm s2 vm2) /\
    vm_uincl (evm s2) vm2.
Proof.
  move=> H1 H2.
  by apply:
    (@sem_I_Ind _ _ _ p ev Pc Pi_r Pi Pfor Pfun Hnil Hcons HmkI Hasgn Hopn
        Hif_true Hif_false Hwhile_true Hwhile_false Hfor Hfor_nil Hfor_cons Hcall Hproc) H1.
Qed.

Lemma sem_uincl s1 c s2 vm1 :
  vm_uincl (evm s1) vm1 ->
  sem p ev s1 c s2 ->
  exists vm2,
    sem p ev (with_vm s1 vm1) c (with_vm s2 vm2) /\
    vm_uincl (evm s2) vm2.
Proof.
  move=> H1 H2.
  by apply:
    (@sem_Ind _ _ _ p ev Pc Pi_r Pi Pfor Pfun Hnil Hcons HmkI Hasgn Hopn
        Hif_true Hif_false Hwhile_true Hwhile_false Hfor Hfor_nil Hfor_cons Hcall Hproc) H1.
Qed.

End UNDEFINCL.

Lemma eq_expr_recP gd s (es es': pexprs) :
  (∀ e : pexpr, e \in es →
   ∀ e' : pexpr, eq_expr e e' → sem_pexpr gd s e = sem_pexpr gd s e') →
  all2 eq_expr es es' →
  sem_pexprs gd s es = sem_pexprs gd s es'.
Proof.
  elim: es es'; first by case.
  move => e es ih [] //= e' es' rec /andP [] he hes.
  rewrite (rec e _ e' he); last by rewrite in_cons eqxx.
  case: (sem_pexpr _ _ e') => //= v.
  rewrite (ih es') // => q hq q' hq'.
  by apply: rec => //; rewrite in_cons hq orbT.
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

Lemma to_val_inj t (v1 v2:sem_t t) : to_val v1 = to_val v2 -> v1 = v2.
Proof.
  by case: t v1 v2 => //= [ | | p | sz ] v1 v2 => [ []|[] |/Varr_inj1 |[] ] ->.
Qed.

Lemma pto_val_inj t (v1 v2:psem_t t) : pto_val v1 = pto_val v2 -> v1 = v2.
Proof.
  case: t v1 v2 => //= [ | | p | sz ] v1 v2 => [ []|[] | /Varr_inj1 | ] //.
  case: v1 v2 => sz1 w1 p1 [sz2 w2 p2] /=.
  move=> /Vword_inj [e];subst => /= <-.
  by rewrite (@eq_irrelevance _ _ _ p1 p2).
Qed.

Lemma to_val_undef  t (v:sem_t t) : to_val v <> Vundef t.
Proof. by case: t v. Qed.

Lemma pto_val_undef  t (v:psem_t t) : pto_val v <> Vundef t.
Proof. by case: t v. Qed.

(* TODO: move *)
Lemma to_word_to_pword s v w: to_word s v = ok w -> to_pword s v = ok (pword_of_word w).
Proof.
  case: v => //= [ s' w' | [] // ].
  move=> /truncate_wordP [hle] ?; subst w; f_equal.
  case: Sumbool.sumbool_of_bool => //=.
  move=> e;move: (e);rewrite cmp_le_eq_lt in e => e'.
  case /orP: e => [hlt | /eqP ?];first by rewrite -cmp_nlt_le hlt in hle.
  by subst; rewrite /pword_of_word zero_extend_u;do 2 f_equal;apply eq_irrelevance.
Qed.

(* ------------------------------------------------------------------------------ *)
Definition apply_undef t (v : exec (psem_t t)) :=
  match v with
  | Error ErrAddrUndef => pundef_addr t
  | _                  => v
  end.

Lemma eval_uincl_undef t1 t2 (v:psem_t t2) :
  subtype t1 t2 ->
  eval_uincl (pundef_addr t1) (ok v).
Proof. by case: t1 => //= p; case: t2 v => //= p2 a /ZleP. Qed.

Lemma apply_undef_pundef_addr t : apply_undef (pundef_addr t) = pundef_addr t.
Proof. by case: t. Qed.

Lemma eval_uincl_apply_undef t (v1 v2 : exec (psem_t t)):
  eval_uincl v1 v2 ->
  eval_uincl (apply_undef v1) (apply_undef v2).
Proof.
  case:v1 v2=> [v1 | []] [v2 | e2] //=; try by move=> <-.
  by move=> _; apply eval_uincl_undef.
Qed.

(* ------------------------------------------------------------------------------ *)

(* ** Semantic without stack 
 * -------------------------------------------------------------------- *)


Instance sCP_unit : @semCallParams _ progUnit := 
  {| init_state := fun _ _ _ s => ok s;
     finalize   := fun _ m => m; |}.

(* ** Semantic with stack 
 * -------------------------------------------------------------------- *)

Notation vid ident := {|v_var := {|vtype := sword Uptr; vname := ident|}; v_info := xH|}.

Definition init_stk_state (sf : stk_fun_extra) (pe:sprog_extra) (wrip:pointer) (s:estate) :=
  let m1   := s.(emem) in
  let vm1  := s.(evm) in
  Let m1' := alloc_stack m1 sf.(sf_align) sf.(sf_stk_sz) in
  write_vars [:: vid (string_of_register RSP) ; vid pe.(sp_rip)]
             [:: Vword (top_stack m1'); Vword wrip] (Estate m1' vmap0).

Definition finalize_stk_mem (sf : stk_fun_extra) (m:mem) := 
  free_stack m (sf_stk_sz sf).

Instance sCP_stack : @semCallParams _ progStack := 
  {| init_state := init_stk_state;
     finalize   := finalize_stk_mem; |}.

(* -------------------------------------------------------------------- *)

(* FIXME : MOVE THIS, this should be an invariant in vmap *)
Section WF.

  Context {T:eqType} {pT:progT T} {sCP: semCallParams}.

  Definition wf_vm (vm:vmap) :=
    forall x,
      match vm.[x]%vmap, vtype x with
      | Ok _   , _      => True
      | Error ErrAddrUndef, sarr _ => False
      | Error ErrAddrUndef, _ => True
      | _, _ => false
      end.

  Lemma wf_set_var x ve vm1 vm2 :
    wf_vm vm1 -> set_var vm1 x ve = ok vm2 -> wf_vm vm2.
  Proof.
    move=> Hwf;apply: set_varP => [v | _ ] ? <- /= z.
    + case: (x =P z) => [ <- | /eqP Hne];first by rewrite Fv.setP_eq.
      by rewrite Fv.setP_neq //;apply (Hwf z).
    case: (x =P z) => [ <- | /eqP Hne].
    + by rewrite Fv.setP_eq; case (vtype x).
    by rewrite Fv.setP_neq //;apply (Hwf z).
  Qed.

  Lemma wf_write_var x ve s1 s2 :
    wf_vm (evm s1) -> write_var x ve s1 = ok s2 -> wf_vm (evm s2).
  Proof.
    by move=> HWf; apply: rbindP => vm Hset [<-] /=;apply: wf_set_var Hset.
  Qed.

  Lemma wf_write_vars x ve s1 s2 :
    wf_vm (evm s1) -> write_vars x ve s1 = ok s2 -> wf_vm (evm s2).
  Proof.
    elim: x ve s1 s2=> [ | x xs Hrec] [ | e es] //= s1 s2.
    + by move=> ? [<-].
    by move=> Hwf; apply: rbindP => vm /(wf_write_var Hwf) -/Hrec H/H.
  Qed.

  Lemma wf_write_lval gd x ve s1 s2 :
    wf_vm (evm s1) -> write_lval gd x ve s1 = ok s2 -> wf_vm (evm s2).
  Proof.
    case: x => [vi t|v|sz v e|aa sz v e|aa sz len v e] /= Hwf.
    + by move=> /write_noneP [->]. + by apply wf_write_var. + by t_rbindP => -[<-].
    + apply: on_arr_varP => n t ? ?.
      apply:rbindP => ??;apply:rbindP => ??;apply:rbindP => ??.
      by apply:rbindP=>? Hset [<-] /=;apply: wf_set_var Hset.
    apply: on_arr_varP => n t ? ?.
    apply:rbindP => ??;apply:rbindP => ??;apply:rbindP => ??.
    by apply:rbindP=>? Hset [<-] /=;apply: wf_set_var Hset.
  Qed.

  Lemma wf_write_lvals gd xs vs s1 s2 :
    wf_vm (evm s1) -> write_lvals gd s1 xs vs = ok s2 -> wf_vm (evm s2).
  Proof.
    elim: xs vs s1 => [ | x xs Hrec] [ | v vs] s1 //= Hwf => [[<-]//| ].
    apply: rbindP => s1' /(wf_write_lval Hwf);apply Hrec.
  Qed.

  Lemma wf_sem p ev s1 c s2 :
    sem p ev s1 c s2 -> wf_vm (evm s1) -> wf_vm (evm s2).
  Proof.
    apply (@cmd_rect
             (fun i => forall s1 s2, sem_i p ev s1 i s2 -> wf_vm (evm s1) -> wf_vm (evm s2))
             (fun i => forall s1 s2, sem_I p ev s1 i s2 -> wf_vm (evm s1) -> wf_vm (evm s2))
             (fun c => forall s1 s2, sem   p ev s1 c s2 -> wf_vm (evm s1) -> wf_vm (evm s2)))=>
      {s1 s2 c}.
    + by move=> i ii Hrec s1 s2 /sem_IE; apply: Hrec.
    + by move => s1 s2 /semE ->.
    + by move=> i c Hi Hc s1 s2 /semE [si] [] /Hi {Hi} Hi ? /Hi; apply: Hc.
    + move=> x t ty e s1 s2 /sem_iE [v] [v'] [hv hv' ok_s2] hw.
      by apply: wf_write_lval ok_s2.
    + move=> xs t o es s1 s2 /sem_iE.
      by apply:rbindP => ?? Hw ?;apply: wf_write_lvals Hw.
    + move=> e c1 c2 Hc1 Hc2 s1 s2 /sem_iE [b] [_]; case: b; [apply Hc1 | apply Hc2].
    + move=> i dir lo hi c Hc s1 s2 /sem_iE [vlo] [vhi] [hlo hhi hfor].
      elim: hfor Hc => // ???? ???? Hw Hsc Hsf Hrec Hc.
      by move=> /wf_write_var -/(_ _ _ _ Hw) -/(Hc _ _ Hsc);apply: Hrec Hc.
    + move=> a c e c' Hc Hc' s1 s2 H.
      move: {1 2}(Cwhile a c e c') H (refl_equal (Cwhile a c e c'))=> i;elim=> //=.
      move=> ???????? Hsc ? Hsc' Hsw Hrec [????];subst.
      move=> /(Hc _ _ Hsc).
      by move=> /(Hc' _ _ Hsc'); apply Hrec.
    + move=> ?????? Hsc ? [????];subst.
      exact: (Hc _ _ Hsc).
    move=> i xs f es s1 s2 /sem_iE [vs] [m2] [rs] [_ _ ok_s2] hw.
    by apply: wf_write_lvals ok_s2.
  Qed.

  Lemma wf_vm_uincl vm : wf_vm vm -> vm_uincl vmap0 vm.
  Proof.
    move=> Hwf x;have := Hwf x;rewrite /vmap0 Fv.get0.
    case: vm.[x]%vmap => [a _ | ];first by apply eval_uincl_undef.
    move=> [] //=;case:(vtype x) => //=.
  Qed.

  Lemma wf_vmap0 : wf_vm vmap0.
  Proof. by move=> x;rewrite /vmap0 Fv.get0;case:vtype. Qed.

  Definition wf_init := forall fe pe ev s1 s2,
    init_state fe pe ev s1 = ok s2 ->
    wf_vm (evm s1) -> wf_vm (evm s2).

End WF.

Arguments wf_init { T pT }.

Lemma wf_initu : wf_init sCP_unit.
Proof. by move=> ????? [->]. Qed.

Lemma wf_inits : wf_init sCP_stack.
Proof. 
  move=> ????? => /=; rewrite /init_stk_state; t_xrbindP => ?? h1 h2.
  apply: wf_write_vars h1; apply wf_vmap0.
Qed.


