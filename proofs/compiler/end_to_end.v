From Coq Require Import Lia.
From HB Require Import structures.

From mathcomp Require Import
  ssreflect
  ssralg
  ssrfun
  ssrbool
  ssrnum
  ssrnat
  choice
  distr
  eqtype
  fintype
  matrix
  order
  reals
  seq
  word
  word_ssrZ
.
From mathcomp Require boolp.

From ITree Require Import
  Basics
  ITree
  ITreeDefinition
  ITreeFacts
  Rutt
  RuttFacts
  Exception
.
Import ITree.

Require Import
  rutt_extras
  xrutt
  xrutt_facts
  it_exec
.
Require Import
  it_sems_core
  psem
  psem_facts
  relational_logic
  hoare_logic
.
Require Import
  compiler
  core_logics
  distr_extra
  itree_safety_facts
  utils
  values
  word
  wseq
.
Require Import
  arch_decl
  arch_extra
  arch_sem
  arch_params
  sem_params_of_arch_extra
.
Require Import
  arch_params_proof
  stack_alloc_proof_1
  stack_alloc_proof_2
  compiler_proof
  it_compiler_proof
  it_compiler_proof_2
.
Require allocation.

Require Import
  cil
  dinterp
.

Import Order.TTheory.

#[local] Open Scope ring_scope.
#[local] Open Scope Z.
#[local] Open Scope order_scope.

#[local] Coercion Pos.to_nat : positive >-> nat.

#[local] Notation "'let*' p ':=' c1 'in' c2" :=
  (@ITree.bind _ _ _ c1 (fun p => c2))
    (at level 61, p as pattern, c1 at next level, right associativity).

#[local] Notation "x |> f" := (f x) (only parsing, at level 25).

Section CHOICEOF.

  Context (T : Type).

  Definition choiceof : Type := T.

  Lemma choiceof_comparable : comparable choiceof.
  Proof. by move=> ??; apply/boolp.pselect. Qed.

  #[export] HB.instance Definition choiceof_eqType :=
    hasDecEq.Build choiceof (compareP choiceof_comparable).
  #[export] HB.instance Definition choiceof_choiceType :=
    boolp.gen_choiceMixin choiceof.
End CHOICEOF.

Notation "{ 'choice' T }" := (choiceof T)
  (format "{ 'choice'  T }").

Section WSEQ_EP.

Context {syscall_state : Type} {ep : EstateParams syscall_state}.

Lemma wseq_in_mem m n (a : WArray.array n) p :
  arr_is_def a ->
  value_in_mem m (Varr a) (Vword p) ->
  wseq_of_arr a = read_wseq m p n.
Proof.
move=> hdef [_ [[/= <- h]]].
rewrite /wseq_of_arr /read_wseq.
have {}hdef :
  forall i : Z,
    i \in ziota 0 n ->
    exists2 w,
      WArray.get8 a i = ok w &
      read m Aligned (p + wrepr Uptr i)%R U8 = ok w.
- move=> i hi.
  have [|w hw] := elimT (valid_getP a i).
  + apply/andP; split; last by move: hdef => /allP /(_ _ hi).
    apply/WArray.in_boundP; rewrite in_ziota in hi; lia.
  exists w => //; apply: h.
  by rewrite /read /= is_align8 /= add_0 hw /= decode_u8.
f_equal; elim: ziota hdef => //= x xs hind hdef.
move: (hdef x); rewrite in_cons eqxx /read8 => /(_ erefl) [w -> ->].
rewrite hind // => i hi; apply: hdef; by rewrite in_cons hi orbT.
Qed.

Lemma write_wseq_wf_ptr_arg
  {gsz rip ms mt p bytes wptrs vs vt writable ws v p' i} :
  let: mt' := write_wseq mt p bytes in
  wf_arg_pointer gsz rip ms mt wptrs vs vt writable ws v p' i ->
  wf_arg_pointer gsz rip ms mt' wptrs vs vt writable ws v p' i.
Proof.
rewrite /write_wseq; case h: fill_mem => [m'|] //=.
move=> [?? hvalid ???]; split=> // w hw.
by rewrite -(fill_mem_validw_eq h) (hvalid _ hw).
Qed.

Lemma write_wseq_wf_arg {gsz rip ms mt p bytes wptrs vs vt ws i} :
  wf_arg gsz rip ms mt wptrs ws vs vt i ->
  wf_arg gsz rip ms (write_wseq mt p bytes) wptrs ws vs vt i.
Proof.
rewrite /wf_arg; case: nth => // b [p' [-> h]]; exists p'; split=> //.
exact: write_wseq_wf_ptr_arg.
Qed.

Lemma write_wseq_it_wf_args {gsz rip ms mt p bytes wptrs vs vt ws} :
  wf_args gsz rip ms mt wptrs ws vs vt ->
  wf_args gsz rip ms (write_wseq mt p bytes) wptrs ws vs vt.
Proof. move=> h i; exact: write_wseq_wf_arg (h i). Qed.

Lemma write_wseq_extend_mem ms mt rip gd p a :
  let: n := Z.of_nat (size a) in
  n <= wbase Uptr ->
  disjoint_zrange p n rip (Z.of_nat (size gd)) ->
  (forall w, validw ms Aligned w U8 -> disjoint_zrange p n w 1) ->
  extend_mem ms mt rip gd ->
  extend_mem ms (write_wseq mt p a) rip gd.
Proof.
move=> hsz hrip hdisj; rewrite /write_wseq; case hm': fill_mem => [m'|//] /=.
move=> [?? hold ? hv hgd]; split=> //.
- move=> x hx; rewrite (hold _ hx) (fill_mem_disjoint hm') //; exact: hdisj hx.
- move=> x /hv; by rewrite (fill_mem_validw_eq hm').
move=> x hx; rewrite -(hgd _ hx); apply: (fill_mem_disjoint hm').
exact: disjoint_zrange_byte hrip hx.
Qed.

End WSEQ_EP.

Section MAIN.

Context
  {R : realType}
  (advmem : Type) (* Adversary's memory. *)
.

Notation distr := (distr R).
Notation Rnd := (Rnd (R := R)).

Instance sc_sem : syscall.syscall_sem unit :=
  {| syscall.get_random := fun _ _ => (tt, [::]); |}.

Definition E := ErrEvent +' RndEvent unit.
Existing Instance with_Error0.
Existing Instance RndE00.

Definition handleE : Handler (RndEvent unit) Rnd :=
  fun _ '(it_sems_core.Rnd _ len) =>
    let* bs := unif_rV (Z.to_nat len) in
    Ret (tt, wseq_of_wvec bs).

Definition translateE : itree (RndEvent unit) ~> itree Rnd :=
  fun _ t => interp handleE t.

Context
  {reg regx xreg rflag cond asm_op extra_op : Type}
  {asm_e : asm_extra reg regx xreg rflag cond asm_op extra_op}
  {call_conv : calling_convention}
  {asm_scsem : asm_syscall_sem}
  {lowering_options : Type}
  (aparams : architecture_params lowering_options)
  (haparams : h_architecture_params aparams)
  (cparams : compiler_params lowering_options)
  (print_uprogP : forall s p, cparams.(print_uprog) s p = p)
  (print_sprogP : forall s p, cparams.(print_sprog) s p = p)
.

(* Not all of the implicits are always needed. *)
Let isemS (p : uprog) :=
  isem_fun
    (asm_op := extended_op)
    (ep := ep_of_asm_e)
    (spp := spp_of_asm_e)
    (wa := withassert)
    (sip := sip_of_asm_e)
    (scP := sCP_unit)
    (E := E)
    (wsw := nosubword)
    (dc := indirect_c)
    (pT := progUnit)
    p tt.

Let isemT (q : asm_prog) :=
  iasmsem_exportcall
    (asm_d := _asm asm_e)
    (call_conv := call_conv)
    (sc_sem :=
    (E := E)
    q.

Section DEFS.

Context
  (p : uprog)
  (entries : seq funname)
  (mI : mem)
.

Definition _Mo : choiceType := {choice mem}.

Record export_funname :=
  {
    _fn :> funname;
    _export : _fn \in entries;
  }.

Definition _No : choiceType := {choice export_funname}.

(* TODO Do we want to restrict the number of arguments?
  if get_fundef (p_funcs p) o is Some fd then
    {choice ltuple (nseq (size (f_tyin fd)) wseq)}
  else void.
  or use [sem_t]?
*)
Definition _In (o : _No) : choiceType := seq wseq.

Definition _Out (o : _No) : choiceType := seq wseq.

Definition val_of_wseq (t : atype) (a : wseq) : value.
Admitted.

Definition wseq_of_val (v : value) : wseq.
Admitted.

Definition mkfsS (fn : funname) (m : mem) (args : seq wseq) : fstate :=
  let vs :=
    if get_fundef (p_funcs p) fn is Some fd then
      [seq val_of_wseq p.1 p.2 | p <- zip (f_tyin fd) args ]
    else [::] (* absurd *)
  in
  {| fscs := tt; fmem := m; fvals := vs; |}.

Definition unmkfsS (fs : fstate) : seq wseq * mem :=
  ([seq wseq_of_val v | v <- fs.(fvals) ], fs.(fmem)).

(* TODO Why doesn't [|>] work for [translateE]? *)
Definition _OoS (o : _No) (i : _In o) (m : _Mo) : itree Rnd (_Out o * _Mo) :=
  let fs := mkfsS o m i in
  let* ofs' := translateE (isemS p o fs |> interp_Err) in
  if ofs' is ESok fs' then Ret (unmkfsS fs')
  else Ret ([::], mI) (* absurd *).

Definition _OoT (o : _No) (i : _In o) (m : _Mo) : itree Rnd (_Out o * _Mo) :=
  let fs := mkfsT o m i in
  let* ofs' := translateE (isemT q o fs |> interp_Err) in
  if ofs' is ESok fs' then Ret (unmkfsS fs')
  else Ret ([::], mI) (* absurd *).

Instance SourceI : OracleSystemInterface :=
  {|
    Mo := _Mo;
    No := _No;
    In := _In;
    Out := _Out;
    mi := mS;
  |}.

Instance Source : OracleSystem SourceI :=
  {| Oo := _OoS; |}.

Instance TargetI : OracleSystemInterface :=
  {|
    Mo := _Mo;
    No := _No;
    In := _In;
    Out := _Out;
    mi := mT;
  |}.

Instance Target : OracleSystem TargetI :=
  {| Oo := _OoT; |}.

End DEFS.
End MAIN.
