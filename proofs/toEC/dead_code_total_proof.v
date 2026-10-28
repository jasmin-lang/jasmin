(* * The pass dead_code in the modes of the extraction to EasyCrypt.

   The extraction for safety runs [dead_code] on programs whose assertions
   are evaluated. Its correctness is stated in both directions, with equal
   results: from the source to the transformed program in the partial mode
   ([dead_code_proof] proves this direction with [values_uincl] on the
   results, without assertions), from the transformed program to the source
   in the total modes, [total_init] being that of EasyCrypt.

   [dead_code] keeps the assertions, the system calls and the calls, and
   removes assignments and operators whose results are dead. The direction
   from the transformed program to the source therefore needs these removed
   instructions not to fail; [dead_args] also removes arguments,
   destinations, parameters and results, which the source passes and
   writes. [total_ok p] states that, from any state, these never fail in
   the total mode: the assignments and the operators of [p] run; the
   arguments of a call evaluate to values of the types of the parameters of
   the callee, and each destination accepts, on every state, any value of
   the type of its result; each parameter of a function accepts any value of
   its type, and its results, read from any state, have their types. The
   conditions are stated destination by destination and parameter by
   parameter, so that they hold of the calls and the functions that
   [dead_args] leaves with fewer destinations and parameters.

   [total_ok p] amounts to [p] being well typed. In the total mode the
   memory accesses, the array accesses and the operators do not fail, and a
   variable never written reads the default value of its type; what is left
   to fail is a value that does not have the type that its destination, the
   parameter or the result expects. *)

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.
Require Import compiler_util psem psem_facts.
Require Import sopn_semi_facts sopn_facts dead_code.
Require dead_code_proof.

#[local] Existing Instance progUnit.
#[local] Existing Instance nosubword.
#[local] Existing Instance indirect_c.

Section DEFS.

Context
  {asm_op syscall_state : Type} {ep : EstateParams syscall_state}
  {spp : SemPexprParams} {sip : SemInstrParams asm_op syscall_state}.

(* In the total mode, on every state, the assignments and the operators of [p]
   run, the arguments of its calls evaluate to values of the types of the
   parameters, and each of their destinations accepts, on every state, the
   values of the type of the corresponding result. *)
Fixpoint total_ok_i (p : uprog) (i : instr) : Prop :=
  let total_ok_c :=
    fix total_ok_c (c : cmd) : Prop :=
      if c is i :: c then total_ok_i p i /\ total_ok_c c else True in
  let 'MkI _ ir := i in
  match ir with
  | Cassgn x tg ty e => forall s, is_ok (sem_assgn (sm := total) p x tg ty e s)
  | Copn xs tg o es => forall s, is_ok (sem_sopn (sm := total) (p_globs p) o s xs es)
  | Ccall xs f es =>
    if get_fundef (p_funcs p) f is Some fd then
      (forall s,
         is_ok (Let vs := sem_pexprs (sm := total) true (p_globs p) s es in
                mapM2 ErrType dc_truncate_val (map eval_atype fd.(f_tyin)) vs))
      /\ List.Forall2 (fun x ty =>
           forall s v v', dc_truncate_val ty v = ok v' ->
             is_ok (write_lval (sm := total) true (p_globs p) x v' s))
         xs (map eval_atype fd.(f_tyout))
    else forall s, is_ok (sem_pexprs (sm := total) true (p_globs p) s es)
  | Csyscall _ _ _ | Cassert _ => True
  | Cif _ c1 c2 | Cwhile _ c1 _ _ c2 => total_ok_c c1 /\ total_ok_c c2
  | Cfor _ _ c => total_ok_c c
  end.

(* Each parameter of [fd] accepts, on every state, any value of its type; its
   results, read in the total mode from any state, have their types. *)
Definition total_ok_fd (fd : ufundef) : Prop :=
  List.Forall2 (fun x ty =>
      forall s v v', dc_truncate_val ty v = ok v' -> is_ok (write_var true x v' s))
    fd.(f_params) (map eval_atype fd.(f_tyin))
  /\ forall s,
     is_ok (Let vs := get_var_is (sm := total) true (evm s) fd.(f_res) in
            mapM2 ErrType dc_truncate_val (map eval_atype fd.(f_tyout)) vs).

Definition total_ok (p : uprog) : Prop :=
  forall fn fd, get_fundef (p_funcs p) fn = Some fd ->
    total_ok_fd fd /\ forall i, List.In i fd.(f_body) -> total_ok_i p i.

(* The results of [fn] that [onfun] keeps. *)
Definition dc_keep_res (onfun : funname -> option (seq bool)) (fn : funname) (fr : fstate) :=
  {| fscs := fscs fr; fmem := fmem fr; fvals := fn_keep_only onfun fn (fvals fr) |}.

(* Same arguments; the results of the transformed program are those of the
   source that [onfun] keeps. *)
Definition dc_src_tgt_spec onfun : EquivSpec :=
  {| rpreF_ := fun fn1 fn2 fs1 fs2 => fn1 = fn2 /\ fs1 = fs2;
     rpostF_ := fun fn1 _ _ _ fr1 fr2 => fr2 = dc_keep_res onfun fn1 fr1 |}.

Definition dc_tgt_src_spec onfun : EquivSpec :=
  {| rpreF_ := fun fn1 fn2 fs1 fs2 => fn1 = fn2 /\ fs1 = fs2;
     rpostF_ := fun fn1 _ _ _ fr1 fr2 => fr1 = dc_keep_res onfun fn1 fr2 |}.

End DEFS.

Section COMMON.

Context
  {asm_op syscall_state : Type} {ep : EstateParams syscall_state}
  {spp : SemPexprParams} {sip : SemInstrParams asm_op syscall_state}.

(* ** The instructions that [dead_code] removes *)

(* An assignment [x = x] leaves the state as it is, but for [x], which takes
   the value read in the mode: its own in the partial mode, possibly the
   default value in the total modes, which then defines [x]. *)

Lemma sem_assgn_nop {sm : SemMode} (p : uprog) x tag ty e s s' :
  check_nop x e ->
  sem_assgn p x tag ty e s = ok s' ->
  [/\ escs s' = escs s, emem s' = emem s &
      forall y, Vm.get (sm := partial) (evm s') y =
        if Sv.mem y (vrv x) then Vm.get (sm := sm) (evm s) y else Vm.get (sm := partial) (evm s) y].
Proof.
case: x e => // xi [] // [[y yi] [] ] //= /eqP /= ?; subst y.
rewrite /sem_assgn /= /get_gvar /=; t_xrbindP => v /get_varP [-> /= hdef hcomp] v' htr.
move=> /write_varP [-> hdb htrb] /=.
have hty : type_of_val (evm s).[xi] = eval_atype (vtype xi).
+ by move: hcomp; rewrite /compat_val /= hdef /= => /eqP.
have heq : v' = (evm s).[xi].
+ move: (evm s).[xi] hty hdef htr htrb => w.
  case: w => [b | z | len a | ws w | //] /= <- _ /truncate_valE.
  1-3: by move=> [_ ->].
  move=> [ws' [w' [_ /truncate_wordP [hle ->] ->]]] /= hle'.
  by have ? := cmp_le_antisym hle hle'; subst ws'; rewrite zero_extend_u.
rewrite heq; split => // y; rewrite Vm.setP; case: eqP => [<- | hne].
+ by rewrite (vm_truncate_val_eq hty) SvP.add_mem_1.
case: Sv_memP => // hin; elim hne; SvD.fsetdec.
Qed.

(* Writes that do not touch the memory change only the variables written. *)

Lemma write_lvals_dead {sm : SemMode} wdb gd xs vs s s' :
  ~~ has lv_write_mem xs ->
  write_lvals wdb gd s xs vs = ok s' ->
  [/\ escs s' = escs s, emem s' = emem s & evm s =[\ vrvs xs] evm s'].
Proof.
move=> hnm hw; split; last exact: vrvsP hw.
+ elim: xs vs s hw {hnm} => [ | x xs ih] [ | v vs] s //=; first by move=> [<-].
  by t_xrbindP => s1 /lv_write_scsP -> /ih.
elim: xs vs s hw hnm => [ | x xs ih] [ | v vs] s //=; first by move=> [<-].
by t_xrbindP => s1 hw /ih{}ih /norP [/lv_write_memP -/(_ _ _ _ _ _ hw) -> /ih].
Qed.

(* The total modes. [total_ok] is stated in the mode [total]. An assignment
   runs alike in every total mode; an operator that runs in [total] runs in
   [total_init], where its undefined outputs, which are booleans, take their
   default value, read alike by the total modes. *)

Lemma get_total_sm {sm : SemMode} vm y :
  is_total (sm := sm) -> Vm.get (sm := sm) vm y = Vm.get (sm := total) vm y.
Proof. by move=> h; rewrite [LHS]Vm.get_modeE [RHS]Vm.get_modeE h. Qed.

Lemma eq_on_total_sm {sm : SemMode} X vm1 vm2 :
  is_total (sm := sm) -> eq_on (sm := total) X vm1 vm2 -> eq_on (sm := sm) X vm1 vm2.
Proof. by move=> h heq y hy; rewrite !(get_total_sm _ _ h); apply heq. Qed.

Lemma get_total_defined vm y : is_defined (Vm.get (sm := total) vm y).
Proof.
rewrite Vm.get_modeE /=; case: ifPn => [_ | ]; last by rewrite negbK.
by case: (eval_atype (vtype y)).
Qed.

Lemma sem_assgn_total_sm {sm : SemMode} (pp : uprog) x tg ty e s :
  is_total (sm := sm) ->
  sem_assgn (sm := sm) pp x tg ty e s = sem_assgn (sm := total) pp x tg ty e s.
Proof.
move=> h; rewrite /sem_assgn (sem_pexpr_is_totalE _ (sm1 := sm) (sm2 := total)) ?h //.
case: sem_pexpr => //= v; case: truncate_val => //= v'.
by rewrite (write_lval_is_totalE _ (sm1 := sm) (sm2 := total)) ?h.
Qed.

Lemma write_lval_dflt gd x v a a' c :
  escs a = escs c -> emem a = emem c -> DB true v ->
  (forall y, Vm.get (sm := total) (evm a) y = Vm.get (sm := total) (evm c) y) ->
  write_lval (sm := total) true gd x v a = ok a' ->
  exists2 c', write_lval (sm := total) true gd x (value_dflt v) c = ok c' &
    [/\ escs a' = escs c', emem a' = emem c' &
        forall y, Vm.get (sm := total) (evm a') y = Vm.get (sm := total) (evm c') y].
Proof.
move=> hscs hmem hdb h hw.
have heq : eq_on (sm := total) (read_rv x) (evm a) (evm c) by move=> y _; apply h.
rewrite /value_dflt; case: ifP => [_ | hd].
+ have [vm2 hw2 /(eq_on_mode (sm := total)) heq2] := write_lval_eq_on1 heq hw.
  rewrite with_vm_evm // in hw2.
  exists (with_vm a' vm2) => //; split => //= y.
  case: (Sv_memP y (vrv x)) => hyv; first by apply: heq2.
  by rewrite -(get_total_eq_ex (vrvP hw)) // -(get_total_eq_ex (vrvP hw2)).
case: v hd hdb hw => // t ht _; rewrite /DB /= => /eqP ?; subst t.
case: x heq => [vi ty | xi | al ws vi e | al aa ws xi e | aa ws len xi e] /= heq.
+ move=> /write_noneP [-> htr _]; exists c; last by split.
  by rewrite /write_none; case: (eval_atype ty) htr.
+ rewrite /write_var; t_xrbindP => vm1 /set_varP [_ htr ->] <-.
  have hty : eval_atype (vtype xi) = cbool by case: (eval_atype (vtype xi)) htr.
  rewrite (set_var_truncate (wdb := true) (x := xi) (v := Vbool false)) //=; last by rewrite hty.
  eexists; first reflexivity.
  split => //= y; case: (v_var xi =P y) => [<- | hne].
  + by rewrite [LHS]Vm.get_modeE [RHS]Vm.get_modeE !Vm.setP_eq hty.
  have h1 : forall vm w, Vm.get (sm := total) vm.[xi <- w] y = Vm.get (sm := total) vm y.
  + by move=> vm w; apply: (Vm.get_eq_mode erefl); rewrite Vm.setP_neq //; apply/eqP.
  by rewrite !h1; apply: h.
+ by t_xrbindP.
+ by apply: on_arr_varP => n t _ _; t_xrbindP.
by apply: on_arr_varP => n t _ _; t_xrbindP => ? ? _ _ ? /to_arrI.
Qed.

Lemma write_lvals_dflt gd xs vs a a' c :
  escs a = escs c -> emem a = emem c -> all (DB true) vs ->
  (forall y, Vm.get (sm := total) (evm a) y = Vm.get (sm := total) (evm c) y) ->
  write_lvals (sm := total) true gd a xs vs = ok a' ->
  exists2 c', write_lvals (sm := total) true gd c xs (map value_dflt vs) = ok c' &
    [/\ escs a' = escs c', emem a' = emem c' &
        forall y, Vm.get (sm := total) (evm a') y = Vm.get (sm := total) (evm c') y].
Proof.
elim: xs vs a c => [ | x xs ih] [ | v vs] //= a c hscs hmem.
+ by move=> _ h [<-]; exists c.
move=> /andP [hdb hdbs] h; t_xrbindP => a1 hw1 hws.
have [c1 -> [hscs1 hmem1 h1]] := write_lval_dflt hscs hmem hdb h hw1.
exact: ih hscs1 hmem1 hdbs h1 hws.
Qed.

Lemma sem_sopn_total_ok {sm : SemMode} gd o s xs es :
  is_total (sm := sm) ->
  is_ok (sem_sopn (sm := total) gd o s xs es) -> is_ok (sem_sopn (sm := sm) gd o s xs es).
Proof.
case: sm => -[] // _; rewrite /sem_sopn.
rewrite (sem_pexprs_is_totalE gd (sm1 := total_init) (sm2 := total)) //.
case: sem_pexprs => //= vs; rewrite exec_sopn_total_initE.
case h: exec_sopn => [vs2 | ] //=.
rewrite (write_lvals_is_totalE gd (sm1 := total_init) (sm2 := total)) //.
case hw: write_lvals => [a' | ] // _.
by have [c' -> _] := write_lvals_dflt erefl erefl (exec_sopn_DB h) (fun _ => erefl) hw.
Qed.

(* Destinations that each accept the values of their types, on every state,
   accept them in sequence. *)
Lemma total_ok_writes gd xs tys vs vs' :
  List.Forall2 (fun x ty =>
      forall s v v', dc_truncate_val ty v = ok v' ->
        is_ok (write_lval (sm := total) true gd x v' s)) xs tys ->
  mapM2 ErrType dc_truncate_val tys vs = ok vs' ->
  forall s, is_ok (write_lvals (sm := total) true gd s xs vs').
Proof.
move=> h; elim: h vs vs' => {xs tys} [ | x ty xs tys hx _ ih] [ | v vs] vs' //=; first by move=> [<-].
t_xrbindP => v' hv vs1 /ih{}ih <- s.
case: (write_lval _ _ _ _ s) (hx s _ _ hv) => //= s1 _; apply: ih.
Qed.

(* ** The results kept *)

Lemma get_var_is_keep_only {sm : SemMode} wdb vm (res : seq var_i) vres tokeep :
  get_var_is wdb vm res = ok vres ->
  get_var_is wdb vm (keep_only res tokeep) = ok (keep_only vres tokeep).
Proof.
elim: tokeep res vres => // b tokeep ih [ | x res] //= vres; first by move=> [<-].
t_xrbindP => v hv vres1 /ih{}ih <-; case: b => //=.
by rewrite hv /= ih.
Qed.

Lemma mapM2_keep_only {A : Type} (f : A -> value -> exec value) tys vs vs' tokeep :
  mapM2 ErrType f tys vs = ok vs' ->
  mapM2 ErrType f (keep_only tys tokeep) (keep_only vs tokeep) = ok (keep_only vs' tokeep).
Proof.
elim: tokeep tys vs vs' => // b tokeep ih [ | ty tys] [ | v vs] //= vs'; first by move=> [<-].
t_xrbindP => v' hv' vs1 /ih{}ih <-; case: b => //=.
by rewrite hv' /= ih.
Qed.

Lemma map_keep_only {A B : Type} (f : A -> B) l tokeep :
  map f (keep_only l tokeep) = keep_only (map f l) tokeep.
Proof. by elim: tokeep l => // b tokeep ih [ | x l] //=; case: b; rewrite /= ih. Qed.

Lemma get_var_is_eq_on {sm : SemMode} wdb X (xs : seq var_i) vm1 vm2 :
  Sv.Subset (vars_l xs) X -> eq_on (sm := sm) X vm1 vm2 ->
  get_var_is wdb vm1 xs = get_var_is wdb vm2 xs.
Proof using ep sip spp.
move=> hsub heq; elim: xs hsub => //= x xs ih hsub.
rewrite (get_var_eq_on _ _ heq) ?ih //; SvD.fsetdec.
Qed.

(* ** The destinations of a call: the source writes all the results, the
   transformed program those kept. A relation that the writes of the kept
   destinations preserve, and those of the removed ones, which are dead,
   relates the states after the call. *)

Section KEEP.

Context {sm : SemMode} (gd : glob_decls) (R : Sv.t -> estate -> estate -> Prop).
Hypothesis R_sub : forall X X' s t, Sv.Subset X' X -> R X s t -> R X' s t.
Hypothesis R_write : forall X x v s t s',
  Sv.Subset (read_rv x) X -> R X s t -> write_lval true gd x v s = ok s' ->
  exists2 t', write_lval true gd x v t = ok t' & R (Sv.union (vrv x) X) s' t'.
Hypothesis R_dead : forall X x v s t s',
  disjoint X (vrv x) -> ~~ lv_write_mem x -> R X s t ->
  write_lval true gd x v s = ok s' -> R X s' t.

Lemma check_keep_onlyP tokeep xs I O xs' vs s t s' :
  check_keep_only xs tokeep O = ok (I, xs') ->
  R I s t ->
  write_lvals true gd s xs vs = ok s' ->
  exists2 t', write_lvals true gd t xs' (keep_only vs tokeep) = ok t' & R O s' t'.
Proof using sip R_dead R_sub R_write.
elim: tokeep xs xs' I vs s t => [ | b tokeep ih] [ | x xs] //= xs' I [ | v vs] s t //.
+ by move=> [<- <-] hR [<-]; exists t.
t_xrbindP => -[I1 xs1] hc; case: b.
+ move=> [<- <-] hR s1 hw hws.
  have [ | t1 hw' hR1] := R_write _ hR hw; first by rewrite read_rvE; SvD.fsetdec.
  have [ | t2 hws' hR2] := ih _ _ _ _ _ t1 hc _ hws.
  + by apply: R_sub hR1; rewrite read_rvE; SvD.fsetdec.
  by exists t2 => //=; rewrite hw'.
case: andP => // -[hd hnm] [<- <-] hR s1 hw hws.
exact: ih hc (R_dead hd hnm hR hw) hws.
Qed.

End KEEP.

(* ** From the source to the transformed program, in the partial mode: the
   two states agree on the live variables ([st_eq_on]). *)

Lemma st_eq_on_dead gd X x v s t s' :
  disjoint X (vrv x) -> ~~ lv_write_mem x -> st_eq_on X s t ->
  write_lval true gd x v s = ok s' -> st_eq_on X s' t.
Proof using sip.
move=> hd hnm [hscs hmem hvm] hw; split.
+ by rewrite -(lv_write_scsP hw).
+ by rewrite -(lv_write_memP hnm hw).
move=> z hz; rewrite -hvm // -(vrvP hw) //.
by move: hd; rewrite /disjoint /is_true Sv.is_empty_spec; SvD.fsetdec.
Qed.

Lemma st_eq_on_nop (pp : uprog) X x tag ty e s t s' :
  check_nop x e -> st_eq_on X s t ->
  sem_assgn (sm := partial) pp x tag ty e s = ok s' -> st_eq_on X s' t.
Proof using sip.
move=> hnop [hscs hmem hvm] /(sem_assgn_nop hnop) [h1 h2 hget].
split; [by rewrite h1 | by rewrite h2 |].
by move=> z hz; rewrite hget -hvm //; case: Sv.mem.
Qed.

Lemma st_eq_on_write gd X x v s t s' :
  Sv.Subset (read_rv x) X -> st_eq_on X s t -> write_lval true gd x v s = ok s' ->
  exists2 t', write_lval true gd x v t = ok t' & st_eq_on (Sv.union (vrv x) X) s' t'.
Proof using sip.
move=> hsub [hscs hmem hvm] hw.
have [vm2 hw2 hvm2] := write_lval_eq_on hsub hw hvm.
have -> : t = with_vm s (evm t) by case: s t hscs hmem {hvm hw hw2} => ??? [???] /= <- <-.
by exists (with_vm s' vm2) => //; split.
Qed.

Lemma dc_finalize_src_tgt onfun fn (fd fd' : ufundef) :
  f_tyout fd' = fn_keep_only onfun fn (f_tyout fd) ->
  f_res fd' = fn_keep_only onfun fn (f_res fd) ->
  f_extra fd' = f_extra fd ->
  wrequiv (st_eq_on (vars_l (f_res fd'))) (finalize_funcall fd) (finalize_funcall fd')
    (fun fr1 fr2 => fr2 = dc_keep_res onfun fn fr1).
Proof using ep sip spp.
move=> hty hres hex s t fr1 [hscs hmem hvm]; rewrite /finalize_funcall /=.
t_xrbindP => vres hget vres' htr <-.
rewrite -(get_var_is_eq_on _ _ hvm) // hres hty -hscs -hmem /dc_keep_res /fn_keep_only.
case: (onfun fn) => [tokeep | ]; last by rewrite hget /= htr /=; eexists.
rewrite (get_var_is_keep_only _ hget) /= map_keep_only (mapM2_keep_only _ htr) /=.
by eexists.
Qed.

(* ** From the transformed program to the source, in a total mode: on the
   live variables, the two states agree on the values that the total modes
   read, and a variable defined in the transformed program is defined in the
   source. The source runs the assignments [x = x] that the transformed
   program removes, which may define [x]; the assertions observe the
   definition of the variables, and only positively. *)

Definition vm_dc (X : Sv.t) (vm1 vm2 : Vm.t) :=
  eq_on (sm := total) X vm1 vm2 /\
  forall x, Sv.In x X -> is_var_init vm1 x -> is_var_init vm2 x.

Definition st_dc X := st_rel vm_dc X.

Lemma vm_dc_sub X X' vm1 vm2 : Sv.Subset X' X -> vm_dc X vm1 vm2 -> vm_dc X' vm1 vm2.
Proof. by move=> hsub [h1 h2]; split; [apply: eq_onI h1 | move=> x hx; apply: h2; apply: hsub]. Qed.

Lemma st_dc_sub X X' t s : Sv.Subset X' X -> st_dc X t s -> st_dc X' t s.
Proof. by move=> hsub; apply: st_rel_weaken => ??; apply: vm_dc_sub. Qed.

Lemma write_lval_same {sm : SemMode} wdb gd x v a a' c :
  escs a = escs c -> emem a = emem c -> eq_on (sm := sm) (read_rv x) (evm a) (evm c) ->
  write_lval wdb gd x v a = ok a' ->
  exists2 c', write_lval wdb gd x v c = ok c' &
    [/\ escs a' = escs c', emem a' = emem c' & evm a' =[vrv x] evm c'].
Proof.
move=> hscs hmem heq hw.
have [vm2 hw2 heq2] := write_lval_eq_on1 heq hw.
by rewrite with_vm_evm // in hw2; exists (with_vm a' vm2).
Qed.

Lemma vm_dc_union X W vm1 vm2 vm1' vm2' :
  vm_dc X vm1 vm2 -> vm1 =[\ W] vm1' -> vm2 =[\ W] vm2' -> vm1' =[W] vm2' ->
  vm_dc (Sv.union W X) vm1' vm2'.
Proof using ep sip spp.
move=> [h1 h2] he1 he2 hW; split => y hy; case: (Sv_memP y W) => hyW.
+ by apply: (Vm.get_eq_mode erefl); apply: hW.
+ rewrite -(get_total_eq_ex he1) // -(get_total_eq_ex he2) //; apply: h1; SvD.fsetdec.
+ by rewrite /is_var_init (hW y hyW).
by rewrite /is_var_init -(he1 y hyW) -(he2 y hyW); apply: h2; SvD.fsetdec.
Qed.

Lemma st_dc_write {sm : SemMode} wdb gd X x v t s t' :
  is_total (sm := sm) -> Sv.Subset (read_rv x) X -> st_dc X t s ->
  write_lval (sm := sm) wdb gd x v t = ok t' ->
  exists2 s', write_lval (sm := sm) wdb gd x v s = ok s' & st_dc (Sv.union (vrv x) X) t' s'.
Proof using ep sip spp.
move=> hsm hsub [hscs hmem [heq hinit]] hw.
have [s' hw' [h1 h2 h3]] := write_lval_same hscs hmem (eq_on_total_sm hsm (eq_onI hsub heq)) hw.
by exists s' => //; split => //; apply: vm_dc_union (conj heq hinit) (vrvP hw) (vrvP hw') h3.
Qed.

Lemma st_dc_write_rev {sm : SemMode} wdb gd X x v t s s' :
  is_total (sm := sm) -> Sv.Subset (read_rv x) X -> st_dc X t s ->
  write_lval (sm := sm) wdb gd x v s = ok s' ->
  exists2 t', write_lval (sm := sm) wdb gd x v t = ok t' & st_dc (Sv.union (vrv x) X) t' s'.
Proof using ep sip spp.
move=> hsm hsub [hscs hmem [heq hinit]] hw.
have [t' hw' [h1 h2 h3]] :=
  write_lval_same (esym hscs) (esym hmem) (eq_onS (eq_on_total_sm hsm (eq_onI hsub heq))) hw.
exists t' => //; split => //; apply: vm_dc_union (conj heq hinit) (vrvP hw') (vrvP hw) _.
by move=> y hy; rewrite h3.
Qed.

Lemma st_dc_writes {sm : SemMode} wdb gd X xs vs t s t' :
  is_total (sm := sm) -> Sv.Subset (read_rvs xs) X -> st_dc X t s ->
  write_lvals (sm := sm) wdb gd t xs vs = ok t' ->
  exists2 s', write_lvals (sm := sm) wdb gd s xs vs = ok s' & st_dc (Sv.union (vrvs xs) X) t' s'.
Proof using ep sip spp.
move=> hsm; elim: xs vs X t s => [ | x xs ih] [ | v vs] //= X t s.
+ by move=> _ h [<-]; exists s => //; apply: st_dc_sub h; SvD.fsetdec.
rewrite read_rvs_cons => hsub h; t_xrbindP => t1 hw hws.
have [ | s1 -> /= h1] := st_dc_write hsm _ h hw; first by SvD.fsetdec.
have [ | s' -> h'] := ih _ _ _ _ _ h1 hws; first by SvD.fsetdec.
by exists s' => //; apply: st_dc_sub h'; rewrite vrvs_cons; SvD.fsetdec.
Qed.

Lemma st_dc_deads {sm : SemMode} wdb gd X xs vs t s s' :
  disjoint X (vrvs xs) -> ~~ has lv_write_mem xs -> st_dc X t s ->
  write_lvals (sm := sm) wdb gd s xs vs = ok s' -> st_dc X t s'.
Proof using ep sip spp.
move=> hd hnm [hscs hmem [heq hinit]] /(write_lvals_dead hnm) [h1 h2 hex].
have hX : forall y, Sv.In y X -> ~ Sv.In y (vrvs xs).
+ by move: hd; rewrite /disjoint /is_true Sv.is_empty_spec => hd y hy hy'; SvD.fsetdec.
split; [by rewrite h1 | by rewrite h2 | split] => y hy.
+ by rewrite -(get_total_eq_ex hex) ?heq //; apply: hX.
by rewrite /is_var_init -(hex y (hX _ hy)); apply: hinit.
Qed.

Lemma st_dc_dead {sm : SemMode} wdb gd X x v t s s' :
  disjoint X (vrv x) -> ~~ lv_write_mem x -> st_dc X t s ->
  write_lval (sm := sm) wdb gd x v s = ok s' -> st_dc X t s'.
Proof using ep sip spp.
move=> hd hnm h hw; apply: (st_dc_deads (wdb := wdb) (gd := gd) (xs := [:: x]) (vs := [:: v])) h _.
+ by rewrite /vrvs /= -/(vrv x).
+ by rewrite /= orbF.
by rewrite /= hw.
Qed.

Lemma st_dc_nop {sm : SemMode} (pp : uprog) X x tg ty e t s s' :
  is_total (sm := sm) -> check_nop x e -> st_dc X t s ->
  sem_assgn (sm := sm) pp x tg ty e s = ok s' -> st_dc X t s'.
Proof.
move=> hsm hnop [hscs hmem [heq hinit]] /(sem_assgn_nop hnop) [h1 h2 hget].
split; [by rewrite h1 | by rewrite h2 | split] => y hy.
+ rewrite heq // [RHS]Vm.get_modeE hget; case: Sv.mem; last by rewrite -Vm.get_modeE.
  by rewrite (get_total_sm _ _ hsm) get_total_defined.
rewrite /is_var_init hget; case: Sv.mem; last by apply: hinit.
by rewrite (get_total_sm _ _ hsm) get_total_defined.
Qed.

Lemma st_dc_eassert gd X a t s :
  Sv.Subset (read_eassert a) X -> st_dc X t s ->
  sem_eassert gd t a = ok true -> sem_eassert gd s a = ok true.
Proof using ep sip spp.
move=> + [hscs hmem [heq hinit]]; elim: a => /=.
+ move=> e; rewrite read_eassert_Pexpr => hsub.
  by rewrite (eq_on_sem_pexpr (sm := total) true gd hmem (eq_onI hsub heq)).
+ move=> o es; rewrite read_eassert_PappN => hsub.
  have := eq_on_sem_pexprs (sm := total) true gd hmem (eq_onI hsub heq).
  by rewrite /sem_pexprs => ->.
+ by move=> x; rewrite read_eassert_Pis_var_init => hsub [] /hinit -> //; SvD.fsetdec.
+ move=> e1 e2; rewrite read_eassert_Pis_mem_init => hsub.
  rewrite !(eq_on_sem_pexpr (sm := total) true gd hmem) ?hmem //; apply: eq_onI heq; SvD.fsetdec.
move=> a1 ih1 a2 ih2; rewrite read_eassert_Pand => hsub.
t_xrbindP => b1 h1 b2 h2 /andP [hb1 hb2]; move: h1 h2; rewrite hb1 hb2 => h1 h2.
by rewrite (ih1 _ h1) ?(ih2 _ h2) //; SvD.fsetdec.
Qed.

Lemma check_esP_R_st_dc X es1 es2 X' :
  check_es_st_eq_on X es1 es2 X' -> forall t s, st_dc X t s -> st_dc X' t s.
Proof. by move=> [h _ _] t s; apply: st_dc_sub. Qed.

Definition checker_st_dc : Checker_e (st_rel vm_dc) :=
  {| check_es := check_es_st_eq_on;
     check_lvals := check_lvals_st_eq_on;
     check_esP_rel := check_esP_R_st_dc |}.

Lemma checker_st_dcP {sm : SemMode} (pp1 pp2 : uprog) :
  is_total (sm := sm) -> p_globs pp1 = p_globs pp2 ->
  Checker_eq (sm1 := sm) (sm2 := sm) pp1 pp2 checker_st_dc.
Proof.
move=> hsm hg; constructor; rewrite -hg.
+ move=> wdb _ d es1 es2 d' /wdb_ok_eq <- [_ <- hsub] t s v [hscs hmem [heq _]] h.
  exists v => //; rewrite -h; symmetry; apply: eq_on_sem_pexprs => //.
  by apply: eq_on_total_sm hsm (eq_onI hsub heq).
move=> wdb _ d xs1 xs2 d' /wdb_ok_eq <- [hsub <- hread] vs t s t' h hw.
have [s' -> h'] := st_dc_writes hsm hread h hw.
by exists s' => //; apply: st_dc_sub h'.
Qed.

(* The source runs an operator that the transformed program removes. *)

Lemma wequiv_opn_right {wa1 wa2 : WithAssert} {sm1 sm2 : SemMode}
  {E' E0' : Type -> Type} {sem_F1 sem_F2 : sem_Fun E'} {wE' : with_Error E' E0'}
  {rE0 : EventRels E0'}
  (p1 p2 : uprog) ev1 ev2 (P Q : rel_c) ii xs tg o es :
  (forall s t, P s t -> exists2 t', sem_sopn (sm := sm2) (p_globs p2) o t xs es = ok t' & Q s t') ->
  wequiv (wa1 := wa1) (wa2 := wa2) (sm1 := sm1) (sm2 := sm2) (sem_F1 := sem_F1) (sem_F2 := sem_F2)
    p1 p2 ev1 ev2 P [::] [:: MkI ii (Copn xs tg o es)] Q.
Proof. by move=> h; rewrite /wequiv /=; apply/wkequiv_bind_ret_right/wkequiv_iresult_right. Qed.

(* [total_ok] on the instructions of a block. *)

Lemma total_ok_cP (pp : uprog) c :
  (fix total_ok_c (c : cmd) : Prop :=
     if c is i :: c then total_ok_i pp i /\ total_ok_c c else True) c ->
  forall i, List.In i c -> total_ok_i pp i.
Proof. by elim: c => //= i c ih [hi hc] j [<- // | /(ih hc)]. Qed.

End COMMON.

Section PROOF.

Context
  {asm_op syscall_state : Type} {ep : EstateParams syscall_state}
  {spp : SemPexprParams} {sip : SemInstrParams asm_op syscall_state}
  {LC : LoopCounter} {E E0 : Type -> Type} {wE : with_Error E E0} {rE : EventRels E0}.

#[local] Existing Instance withassert_nocontract.

Context (onfun : funname -> option (seq bool)) (p p' : uprog) (ev : extra_val_t).

Hypothesis dc_ok :
  dead_code_prog_tokeep (fun _ => false) (fun _ fi => fi) false onfun p = ok p'.

Notation dc_i := (dead_code_i (fun _ => false) false onfun).
Notation dc_fd := (dead_code_fd (fun _ => false) (fun _ fi => fi) false onfun).

Lemma dc_globs : p_globs p' = p_globs p.
Proof using dc_ok. by move: dc_ok; rewrite /dead_code_prog_tokeep; t_xrbindP => ? _ <-. Qed.

Lemma dc_funcs : map_cfprog_name dc_fd (p_funcs p) = ok (p_funcs p').
Proof using dc_ok. by move: dc_ok; rewrite /dead_code_prog_tokeep; t_xrbindP => ? ? <-. Qed.

Section SRC_TGT.

Let Pi (i : instr) :=
  forall I c' O, dc_i i O = ok (I, c') ->
  wequiv_rec p p' ev ev (dc_src_tgt_spec onfun) (st_eq_on I) [:: i] c' (st_eq_on O).

Let Pi_r (i : instr_r) := forall ii, Pi (MkI ii i).

Let Pc (c : cmd) :=
  forall I c' O, dead_code_c dc_i c O = ok (I, c') ->
  wequiv_rec p p' ev ev (dc_src_tgt_spec onfun) (st_eq_on I) c c' (st_eq_on O).

Lemma dc_src_tgt_body c : Pc c.
Proof using dc_ok.
have hg : p_globs p = p_globs p' by rewrite dc_globs.
have hcu := checker_st_eq_onP hg (sm := partial).
have hca := checker_a_st_eq_onP hg.
move: c; apply (cmd_rect (Pr := Pi_r) (Pi := Pi) (Pc := Pc)) => //; rewrite /Pi_r /Pi /Pc.
+ by move=> _ _ O [<- <-]; apply wequiv_nil.
+ move=> i c hi hc I c_ O /=; t_xrbindP => -[R c'] /hc{}hc [I' i'] /hi{}hi /= ??; subst I' c_.
  by rewrite -cat1s; apply wequiv_cat with (st_eq_on R).
+ move=> x tg ty e ii I c' O /=.
  have hkeep : wequiv_rec p p' ev ev (dc_src_tgt_spec onfun)
    (st_eq_on (read_rv_rec (read_e_rec (Sv.diff O (vrv x)) e) x))
    [:: MkI ii (Cassgn x tg ty e)] [:: MkI ii (Cassgn x tg ty e)] (st_eq_on O).
  + apply wequiv_assgn_rel_eq with checker_st_eq_on
      (read_rv_rec (read_e_rec (Sv.diff O (vrv x)) e) x) => //=.
    + by split => //; rewrite /read_es /= read_rvE !read_eE; SvD.fsetdec.
    by split => //; rewrite /read_rvs /vrvs /= !read_rvE ?read_eE; SvD.fsetdec.
  rewrite write_i_assgn; case: ifP => _; last by move=> [<- <-].
  case: ifP => hrm; last by move=> [<- <-].
  move=> [<- <-]; apply wequiv_assgn_esem => s t s' hst hs; exists t => //.
  case/orP: hrm => [/andP [hd hnm] | /andP [_ hnop]]; last exact: st_eq_on_nop hnop hst hs.
  by move: hs; rewrite /sem_assgn; t_xrbindP => v _ v' _; apply: st_eq_on_dead hd hnm hst.
+ move=> xs tg o es ii I c' O /=.
  have hkeep : wequiv_rec p p' ev ev (dc_src_tgt_spec onfun)
    (st_eq_on (read_es_rec (read_rvs_rec (Sv.diff O (vrvs xs)) xs) es))
    [:: MkI ii (Copn xs tg o es)] [:: MkI ii (Copn xs tg o es)] (st_eq_on O).
  + apply wequiv_opn_rel_eq with checker_st_eq_on
      (read_es_rec (read_rvs_rec (Sv.diff O (vrvs xs)) xs) es) => //=.
    + by split => //; rewrite read_esE read_rvsE; SvD.fsetdec.
    by split => //; rewrite read_esE read_rvsE; SvD.fsetdec.
  have -> : check_nop_opn (fun _ => false) xs o es = false.
  + by move: (xs) (o) (es) => [ | x [ | ??]] [] // ? [ | ? [ | ??]].
  case: ifP => _; last by move=> [<- <-].
  case: ifP => hrm; last by move=> [<- <-].
  move=> [<- <-]; apply wequiv_opn_esem => s t s' hst hs; exists t => //.
  move: hs hrm; rewrite /sem_sopn; t_xrbindP => vs vs' _ _ hw /andP [hd hnm].
  have [h1 h2 hvm'] := write_lvals_dead hnm hw.
  case: hst => hscs hmem hvm; split; [by rewrite h1 | by rewrite h2 | ].
  move=> z hz; rewrite -hvm // -hvm' //.
  by move: hd; rewrite /disjoint /is_true Sv.is_empty_spec; SvD.fsetdec.
+ move=> xs o es ii I c' O /= [<- <-].
  set X := read_es_rec _ es.
  apply wequiv_syscall_rel_eq_core with checker_st_eq_on X => //=.
  + by split => //; rewrite /X read_esE read_rvsE; SvD.fsetdec.
  + by split => //; rewrite /X read_esE read_rvsE; SvD.fsetdec.
  exact: wrequiv_eq.
+ move=> a ii I c' O /= [<- <-].
  apply wequiv_assert_rel_eq with checker_a_st_eq_on => //=.
  by split => //; rewrite read_eassertE; SvD.fsetdec.
+ move=> e c1 c2 hc1 hc2 ii I c' O /=; t_xrbindP.
  move=> [I1 c1'] /hc1{}hc1 [I2 c2'] /hc2{}hc2 [??]; subst I c'.
  apply wequiv_if_rel_eq with checker_st_eq_on (read_e_rec (Sv.union I1 I2) e) O O => //=.
  + by split => //; rewrite /read_es /= !read_eE; SvD.fsetdec.
  + apply wequiv_weaken with (st_eq_on I1) (st_eq_on O) => //.
    by apply st_rel_weaken => ??; apply eq_onI; rewrite read_eE; SvD.fsetdec.
  apply wequiv_weaken with (st_eq_on I2) (st_eq_on O) => //.
  by apply st_rel_weaken => ??; apply eq_onI; rewrite read_eE; SvD.fsetdec.
+ move=> x dir lo hi c hc ii I c_ O /=.
  case Hloop: loop => [[sv1 sc1] /=|//] [??]; subst I c_.
  have [H1 [sv2 [/hc{}hc H2']]] := dead_code_proof.loopP Hloop.
  apply wequiv_weaken with (st_eq_on (read_e_rec (read_e_rec sv1 hi) lo)) (st_eq_on sv1) => //.
  + by apply st_rel_weaken => ??; apply eq_onI.
  apply wequiv_for_rel_eq with checker_st_eq_on (read_e_rec (read_e_rec sv1 hi) lo) sv2 => //.
  + by split => //; rewrite /read_es /= !read_eE; SvD.fsetdec.
  + by move=> ??; apply eq_onI; rewrite !read_eE; SvD.fsetdec.
  by split => //; rewrite /vrvs /read_rvs /=; SvD.fsetdec.
+ move=> a c1 e ii' c2 hc1 hc2 ii I c_ O /=.
  set dobody := (X in wloop X).
  case Hloop: wloop => [[sv1 [c1' c2']] /=|//] [??]; subst sv1 c_.
  have [sv2 [sv2' [H1 [heq H2]]]] := dead_code_proof.wloopP Hloop.
  move: (heq); rewrite /dobody; t_xrbindP.
  move=> [Ic1 c1_] /hc1{}hc1.
  case heq1 : dead_code_c => [[Ic2 c2_]/= | //] [????]; subst sv2' Ic1 c1_ c2_.
  have {}hc2 := hc2 _ _ _ heq1.
  apply wequiv_weaken with (st_eq_on I) (st_eq_on (read_e_rec sv2 e)) => //.
  + by apply st_rel_weaken => ??; apply eq_onI; rewrite read_eE; SvD.fsetdec.
  apply wequiv_while_rel_eq with checker_st_eq_on (read_e_rec sv2 e) => //.
  + by split => //; rewrite /read_es /= !read_eE; SvD.fsetdec.
  apply wequiv_weaken with (st_eq_on Ic2) (st_eq_on I) => //.
  by apply st_rel_weaken => ??; apply eq_onI; rewrite read_eE; SvD.fsetdec.
move=> xs f es ii I_ c_ O /=.
set sxs := (X in Let sxs := X in _).
case heq: sxs => [[I xs'] | ] //= [??]; subst c_ I_.
apply wequiv_call_wa with (Pf := rpreF (eS := dc_src_tgt_spec onfun))
  (Qf := rpostF (eS := dc_src_tgt_spec onfun)) (Rv := eq).
+ by rewrite dc_globs; apply read_es_st_eq_on; rewrite read_esE; SvD.fsetdec.
+ by [].
+ by move=> s1 s2 vs _ [hscs hmem _] <-; rewrite /mk_fstate hscs hmem.
+ by [].
+ exact: (@wequiv_fun_rec _ _ _ _ _ _ _ _ _ _ p p' ev ev (dc_src_tgt_spec onfun) ii ii f f).
move=> fs1 fs2 fr1 fr2 _ /= ->.
rewrite dc_globs /upd_estate => s t s' [hscs hmem hvm] /= hw.
have hst : st_eq_on I (with_scs (with_mem s (fmem fr1)) (fscs fr1))
                      (with_scs (with_mem t (fmem fr1)) (fscs fr1)).
+ by split => //=; apply: eq_onI hvm; rewrite read_esE; SvD.fsetdec.
move: heq hw; rewrite /sxs /fn_keep_only; case: (onfun f) => [tokeep | [??]]; last first.
+ subst I xs' => hw.
  have hsub : Sv.Subset (read_rvs xs) (read_rvs_rec (Sv.diff O (vrvs xs)) xs).
  + by rewrite read_rvsE; SvD.fsetdec.
  have [t' -> hst'] := write_lvals_st_eq_on hsub hst hw.
  exists t' => //; apply: st_rel_weaken hst' => ??; apply eq_onI.
  by rewrite read_rvsE; SvD.fsetdec.
t_xrbindP => hc hw.
have hsub : forall X X' s t, Sv.Subset X' X -> st_eq_on X s t -> st_eq_on X' s t.
+ by move=> X X' ?? h; apply st_rel_weaken => ??; apply eq_onI.
have {}hc : check_keep_only xs tokeep O = ok (I, xs').
+ by move: hc; rewrite /add_iinfo; case: check_keep_only => // ? [->].
apply: (check_keep_onlyP hsub _ _ hc hst hw).
+ by move=> ??????; apply: st_eq_on_write.
by move=> ??????; apply: st_eq_on_dead.
Qed.

Lemma dc_src_tgt_callP fn :
  wiequiv_f p p' ev ev (rpreF (eS := dc_src_tgt_spec onfun)) fn fn
    (rpostF (eS := dc_src_tgt_spec onfun)).
Proof using dc_ok.
apply wequiv_fun_ind_wa => {}fn _ fs _ [<- <-] fd hget.
have [fd' hfd' hget'] := get_map_cfprog_name_gen dc_funcs hget.
exists fd' => // _; split => // s hinit.
move: hfd'; rewrite /dead_code_fd; t_xrbindP => -[I c'] hc ?; subst fd'.
exists s; first by rewrite -hinit.
exists (st_eq_on I), (st_eq_on (read_es [seq Plvar i | i <- fn_keep_only onfun fn (f_res fd)])).
split => //=.
+ exact: dc_src_tgt_body hc.
apply: wrequiv_weaken (dc_finalize_src_tgt _ _ _) => //=.
by apply st_rel_weaken => ??; apply eq_onI; rewrite vars_l_read_es.
by [].
Qed.

End SRC_TGT.

Section TGT_SRC.

Context {sm : SemMode} (hsm : is_total (sm := sm)) (hok : total_ok p).

(* As [dc_tgt_src_spec], and the results of the source are truncated to the
   types of the results of its callee: the source writes them to the
   destinations that the transformed program removes, which accept such
   values by [total_ok]. *)
Definition dc_ts_spec : EquivSpec :=
  {| rpreF_ := fun fn1 fn2 fs1 fs2 => fn1 = fn2 /\ fs1 = fs2;
     rpostF_ := fun fn1 _ _ _ fr1 fr2 =>
       fr1 = dc_keep_res onfun fn1 fr2 /\
       exists2 fd, get_fundef (p_funcs p) fn1 = Some fd &
         exists vs,
           mapM2 ErrType dc_truncate_val (map eval_atype fd.(f_tyout)) vs = ok (fvals fr2) |}.

Let Qi (i : instr) :=
  total_ok_i p i ->
  forall I c' O, dc_i i O = ok (I, c') ->
  wequiv_rec (sm1 := sm) (sm2 := sm) p' p ev ev dc_ts_spec (st_dc I) c' [:: i] (st_dc O).

Let Qi_r (i : instr_r) := forall ii, Qi (MkI ii i).

Let Qc (c : cmd) :=
  (forall i, List.In i c -> total_ok_i p i) ->
  forall I c' O, dead_code_c dc_i c O = ok (I, c') ->
  wequiv_rec (sm1 := sm) (sm2 := sm) p' p ev ev dc_ts_spec (st_dc I) c' c (st_dc O).
Lemma dc_tgt_src_body c : Qc c.
Proof using dc_ok hsm.
have hg : p_globs p' = p_globs p by rewrite dc_globs.
have hcu := checker_st_dcP hsm hg.
move: c; apply (cmd_rect (Pr := Qi_r) (Pi := Qi) (Pc := Qc)) => //; rewrite /Qi_r /Qi /Qc.
+ by move=> _ _ _ O [<- <-]; apply wequiv_nil.
+ move=> i c hi hc hok' I c_ O /=.
  t_xrbindP => -[R c'] /(hc (fun j hj => hok' j (or_intror hj))){}hc [I' i'].
  move=> /(hi (hok' i (or_introl erefl))){}hi /= ??; subst I' c_.
  by rewrite -cat1s; apply wequiv_cat with (st_dc R).
+ move=> x tg ty e ii /= hoki I c' O.
  have hkeep : wequiv_rec (sm1 := sm) (sm2 := sm) p' p ev ev dc_ts_spec
    (st_dc (read_rv_rec (read_e_rec (Sv.diff O (vrv x)) e) x))
    [:: MkI ii (Cassgn x tg ty e)] [:: MkI ii (Cassgn x tg ty e)] (st_dc O).
  + apply wequiv_assgn_rel_eq with checker_st_dc
      (read_rv_rec (read_e_rec (Sv.diff O (vrv x)) e) x) => //=.
    + by split => //; rewrite /read_es /= read_rvE !read_eE; SvD.fsetdec.
    by split => //; rewrite /read_rvs /vrvs /= !read_rvE ?read_eE; SvD.fsetdec.
  rewrite write_i_assgn; case: ifP => _; last by move=> [<- <-].
  case: ifP => hrm; last by move=> [<- <-].
  move=> [<- <-]; apply wequiv_assign_right => t s hts.
  case hs: (sem_assgn (sm := sm) p x tg ty e s) => [s' | err]; last first.
  + by have := hoki s; rewrite -(sem_assgn_total_sm _ _ _ _ _ _ hsm) hs.
  exists s' => //.
  case/orP: hrm => [/andP [hd hnm] | /andP [_ hnop]]; last exact: st_dc_nop hsm hnop hts hs.
  by move: hs; rewrite /sem_assgn; t_xrbindP => v _ v' _; apply: st_dc_dead hd hnm hts.
+ move=> xs tg o es ii /= hoki I c' O.
  have hkeep : wequiv_rec (sm1 := sm) (sm2 := sm) p' p ev ev dc_ts_spec
    (st_dc (read_es_rec (read_rvs_rec (Sv.diff O (vrvs xs)) xs) es))
    [:: MkI ii (Copn xs tg o es)] [:: MkI ii (Copn xs tg o es)] (st_dc O).
  + apply wequiv_opn_rel_eq with checker_st_dc
      (read_es_rec (read_rvs_rec (Sv.diff O (vrvs xs)) xs) es) => //=.
    + by split => //; rewrite read_esE read_rvsE; SvD.fsetdec.
    by split => //; rewrite read_esE read_rvsE; SvD.fsetdec.
  have -> : check_nop_opn (fun _ => false) xs o es = false.
  + by move: (xs) (o) (es) => [ | x [ | ??]] [] // ? [ | ? [ | ??]].
  case: ifP => _; last by move=> [<- <-].
  case: ifP => hrm; last by move=> [<- <-].
  move=> [<- <-]; apply wequiv_opn_right => t s hts.
  case hs: (sem_sopn (sm := sm) (p_globs p) o s xs es) => [s' | err]; last first.
  + by have := sem_sopn_total_ok hsm (hoki s); rewrite hs.
  exists s' => //; move: hs hrm; rewrite /sem_sopn; t_xrbindP => vs vs' _ _ hw /andP [hd hnm].
  exact: st_dc_deads hd hnm hts hw.
+ move=> xs o es ii _ I c' O /= [<- <-].
  set X := read_es_rec _ es.
  apply wequiv_syscall_rel_eq_core with checker_st_dc X => //=.
  + by split => //; rewrite /X read_esE read_rvsE; SvD.fsetdec.
  + by split => //; rewrite /X read_esE read_rvsE; SvD.fsetdec.
  exact: wrequiv_eq.
+ move=> a ii _ I c' O /= [<- <-].
  apply wequiv_assert => _; split => // t s hts; rewrite hg => ha; split.
  + by apply: st_dc_eassert hts ha; rewrite read_eassertE; SvD.fsetdec.
  by apply: st_dc_sub hts; rewrite read_eassertE; SvD.fsetdec.
+ move=> e c1 c2 hc1 hc2 ii /= [/total_ok_cP /hc1{}hc1 /total_ok_cP /hc2{}hc2] I c' O; t_xrbindP.
  move=> [I1 c1'] /hc1{}hc1 [I2 c2'] /hc2{}hc2 [??]; subst I c'.
  apply wequiv_if_rel_eq with checker_st_dc (read_e_rec (Sv.union I1 I2) e) O O => //=.
  + by split => //; rewrite /read_es /= !read_eE; SvD.fsetdec.
  + apply wequiv_weaken with (st_dc I1) (st_dc O) => //.
    by move=> ??; apply: st_dc_sub; rewrite read_eE; SvD.fsetdec.
  apply wequiv_weaken with (st_dc I2) (st_dc O) => //.
  by move=> ??; apply: st_dc_sub; rewrite read_eE; SvD.fsetdec.
+ move=> x dir lo hi c hc ii /= /total_ok_cP /hc{}hc I c_ O.
  case Hloop: loop => [[sv1 sc1] /=|//] [??]; subst I c_.
  have [H1 [sv2 [/hc{}hc H2']]] := dead_code_proof.loopP Hloop.
  apply wequiv_weaken with (st_dc (read_e_rec (read_e_rec sv1 hi) lo)) (st_dc sv1) => //.
  + by move=> ??; apply: st_dc_sub.
  apply wequiv_for_rel_eq with checker_st_dc (read_e_rec (read_e_rec sv1 hi) lo) sv2 => //.
  + by split => //; rewrite /read_es /= !read_eE; SvD.fsetdec.
  + by move=> ??; apply: vm_dc_sub; rewrite !read_eE; SvD.fsetdec.
  by split => //; rewrite /vrvs /read_rvs /=; SvD.fsetdec.
+ move=> a c1 e ii' c2 hc1 hc2 ii /= [/total_ok_cP /hc1{}hc1 /total_ok_cP /hc2{}hc2] I c_ O.
  set dobody := (X in wloop X).
  case Hloop: wloop => [[sv1 [c1' c2']] /=|//] [??]; subst sv1 c_.
  have [sv2 [sv2' [H1 [heq H2]]]] := dead_code_proof.wloopP Hloop.
  move: (heq); rewrite /dobody; t_xrbindP.
  move=> [Ic1 c1_] /hc1{}hc1.
  case heq1 : dead_code_c => [[Ic2 c2_]/= | //] [????]; subst sv2' Ic1 c1_ c2_.
  have {}hc2 := hc2 _ _ _ heq1.
  apply wequiv_weaken with (st_dc I) (st_dc (read_e_rec sv2 e)) => //.
  + by move=> ??; apply: st_dc_sub; rewrite read_eE; SvD.fsetdec.
  apply wequiv_while_rel_eq with checker_st_dc (read_e_rec sv2 e) => //.
  + by split => //; rewrite /read_es /= !read_eE; SvD.fsetdec.
  apply wequiv_weaken with (st_dc Ic2) (st_dc I) => //.
  by move=> ??; apply: st_dc_sub; rewrite read_eE; SvD.fsetdec.
move=> xs f es ii hoki I_ c_ O /=.
set sxs := (X in Let sxs := X in _).
case heq: sxs => [[I xs'] | ] //= [??]; subst c_ I_.
apply wequiv_call_wa with (Pf := rpreF (eS := dc_ts_spec)) (Qf := rpostF (eS := dc_ts_spec))
  (Rv := eq).
+ rewrite hg => t s vs [_ hmem [heq' _]] h; exists vs => //; rewrite -h; symmetry.
  apply: eq_on_sem_pexprs => //; apply: eq_on_total_sm hsm (eq_onI _ heq').
  by rewrite read_esE; SvD.fsetdec.
+ by [].
+ by move=> t s vs _ [hscs hmem _] <-; rewrite /mk_fstate hscs hmem.
+ by [].
+ exact: (@wequiv_fun_rec _ _ _ _ _ _ _ _ _ _ p' p ev ev dc_ts_spec ii ii f f).
move=> fs1 fs2 fr1 fr2 _ /= [-> [fd hfd [vs htr]]].
rewrite hg /upd_estate => t s t' [hscs hmem hvm] /= hw.
set t1 := with_scs (with_mem t (fmem fr2)) (fscs fr2).
set s1 := with_scs (with_mem s (fmem fr2)) (fscs fr2).
have hts : st_dc I t1 s1.
+ by split => //=; apply: vm_dc_sub hvm; rewrite read_esE; SvD.fsetdec.
move: heq hw; rewrite /sxs /fn_keep_only; case: (onfun f) => [tokeep | [??]]; last first.
+ subst I xs' => hw.
  have [ | s' -> hst'] := st_dc_writes hsm _ hts hw; first by rewrite read_rvsE; SvD.fsetdec.
  by exists s' => //; apply: st_dc_sub hst'; rewrite read_rvsE; SvD.fsetdec.
move=> hc hw.
have {}hc : check_keep_only xs tokeep O = ok (I, xs').
+ by move: hc; rewrite /add_iinfo; case: check_keep_only => // ? [->].
move: hoki; rewrite /= hfd => -[_ /total_ok_writes /(_ htr s1)].
rewrite -(write_lvals_is_totalE _ _ _ _ _ (sm1 := sm) (sm2 := total)) ?hsm //.
case hws: write_lvals => [s' | ] // _; exists s' => //.
have [ | | | t'' hw' hR] := check_keep_onlyP (R := fun X a b => st_dc X b a) _ _ _ hc hts hws.
+ by move=> X X' a b hsub; apply: st_dc_sub.
+ by move=> X x v a b a' hsub h1 h2; apply: st_dc_write_rev hsm hsub h1 h2.
+ by move=> X x v a b a' hd hnm h1 h2; apply: st_dc_dead hd hnm h1 h2.
by move: hw'; rewrite /t1 hw => -[->].
Qed.

Lemma dc_tgt_src_callP fn :
  wiequiv_f (sm1 := sm) (sm2 := sm) p' p ev ev (rpreF (eS := dc_ts_spec)) fn fn
    (rpostF (eS := dc_ts_spec)).
Proof using dc_ok hsm hok.
apply wequiv_fun_ind_wa => {}fn _ fs _ [<- <-] fd' hget'.
have [fd hfd hget] := get_map_cfprog_name_gen' dc_funcs hget'.
exists fd => // _; split => // t hinit.
have [[_ hres] hokb] := hok hget.
move: hfd hinit; rewrite /dead_code_fd; t_xrbindP => -[I c'] hc ? hinit; subst fd'.
exists t; first by rewrite -hinit.
exists (st_dc I), (st_dc (read_es [seq Plvar i | i <- fn_keep_only onfun fn (f_res fd)])).
split => //=.
+ exact: dc_tgt_src_body hokb _ _ _ hc.
move=> t' s' fr1 [hscs hmem [heq _]]; rewrite /finalize_funcall /=.
t_xrbindP => vres1 hget1 vres1' htr1 <-.
have hgv : forall vm (xs : seq var_i),
  get_var_is (sm := sm) true vm xs = get_var_is (sm := total) true vm xs.
+ move=> vm; elim => //= x xs ->.
  by rewrite (get_var_is_totalE (sm1 := sm) (sm2 := total)) ?hsm.
move: (hres s'); rewrite -hgv.
case hgs: get_var_is => [vres | ] //=; case htrs: mapM2 => [vres' | ] //= _.
eexists; first reflexivity.
split; last by exists fd => //; exists vres.
rewrite (get_var_is_eq_on _ _ (eq_on_total_sm hsm heq)) in hget1; last by rewrite vars_l_read_es.
rewrite /dc_keep_res /= hscs hmem; move: hget1 htr1; rewrite /fn_keep_only.
case: (onfun fn) => [tokeep | ]; last by rewrite hgs => -[<-]; rewrite htrs => -[<-].
rewrite (get_var_is_keep_only _ hgs) => -[<-].
by rewrite map_keep_only (mapM2_keep_only _ htrs) => -[<-].
Qed.

End TGT_SRC.

End PROOF.

(* When the source runs without failure, in the partial mode with its
   assertions evaluated, the transformed program runs with the same results,
   but those removed. The contracts are not evaluated: they read the results
   that are removed. The statement does not hold in a total mode: [dead_code]
   removes an assignment [x = x] tagged [AT_rename] even when [x] is live;
   from a state where [x] is undefined, the source defines [x], so that an
   assertion [is_var_init x] that follows holds in the source and fails in
   the transformed program. *)
Lemma dead_code_src_tgt :
  forall {asm_op syscall_state : Type} {ep : EstateParams syscall_state}
    {spp : SemPexprParams} {sip : SemInstrParams asm_op syscall_state}
    {LC : LoopCounter}
    {E E0 : Type -> Type} {wE : with_Error E E0} {rE : EventRels E0}
    (onfun : funname -> option (seq bool)) (p p' : uprog) (ev : extra_val_t),
  dead_code_prog_tokeep (fun _ => false) (fun _ fi => fi) false onfun p = ok p' ->
  forall fn,
  wiequiv_f (sm1 := partial) (sm2 := partial)
    (wa1 := withassert_nocontract) (wa2 := withassert_nocontract)
    p p' ev ev (rpreF (eS := dc_src_tgt_spec onfun)) fn fn
    (rpostF (eS := dc_src_tgt_spec onfun)).
Proof.
move=> asm_op syscall_state ep spp sip LC E E0 wE rE onfun p p' ev hdc fn.
exact: (dc_src_tgt_callP (rE := rE) ev hdc).
Qed.

(* When the transformed program runs without failure, in a total mode
   ([total] or [total_init]) with its assertions evaluated, the source runs
   with the same results, but those removed. *)
Lemma dead_code_tgt_src :
  forall {asm_op syscall_state : Type} {ep : EstateParams syscall_state}
    {spp : SemPexprParams} {sip : SemInstrParams asm_op syscall_state}
    {sm : SemMode} {LC : LoopCounter}
    {E E0 : Type -> Type} {wE : with_Error E E0} {rE : EventRels E0}
    (onfun : funname -> option (seq bool)) (p p' : uprog) (ev : extra_val_t),
  is_total (sm := sm) ->
  total_ok p ->
  dead_code_prog_tokeep (fun _ => false) (fun _ fi => fi) false onfun p = ok p' ->
  forall fn,
  wiequiv_f (sm1 := sm) (sm2 := sm)
    (wa1 := withassert_nocontract) (wa2 := withassert_nocontract)
    p' p ev ev (rpreF (eS := dc_tgt_src_spec onfun)) fn fn
    (rpostF (eS := dc_tgt_src_spec onfun)).
Proof.
move=> asm_op syscall_state ep spp sip sm LC E E0 wE rE onfun p p' ev hsm hok hdc fn.
apply: wkequiv_io_weaken (dc_tgt_src_callP (rE := rE) ev hdc hsm hok (fn := fn)) => //.
by move=> > _ [-> _].
Qed.
