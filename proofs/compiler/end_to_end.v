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

Context {R : realType}.

Notation distr := (distr R).
Notation Rnd := (Rnd (R := R)).

Instance sc_sem : syscall.syscall_sem unit :=
  {| syscall.get_random := fun _ _ => (tt, [::]); |}.

Definition E := ErrEvent +' RndEvent unit.

#[local] Existing Instance wE.
#[local] Existing Instance RndE00.

Definition handleE : Handler (RndEvent unit) Rnd :=
  fun _ '(it_sems_core.Rnd _ len) =>
    let* bs := unif_rV (Z.to_nat len) in
    Ret (tt, wseq_of_wvec bs).

Definition translateE : itree (RndEvent unit) ~> itree Rnd :=
  fun _ t => interp handleE t.

Lemma eutt_translateE T (RR : T -> T -> Prop) :
  Proper (eutt RR ==> eutt RR) (translateE (T := T)).
Proof. exact: eutt_interp'. Qed.

Context
  {reg regx xreg rflag cond asm_op extra_op : Type}
  {asm_e : asm_extra reg regx xreg rflag cond asm_op extra_op}
  {call_conv : calling_convention}
  {asm_scsem : asm_syscall_sem}
.

Definition isem_asm (q : asm_prog) :=
  iasmsem_exportcall
    (asm_d := _asm)
    (call_conv := call_conv)
    (asm_scsem := asm_scsem)
    (E := E)
    (wE := wE)
    q.

Definition val_of_wseq (t : atype) (a : wseq) : value.
Proof using. Admitted.

Definition wseq_of_val (v : value) : wseq.
Proof using. Admitted.

Definition xm_with_mem (mem : mem) (m : asmmem) : asmmem :=
  {|
    asm_rip := m.(asm_rip);
    asm_scs := m.(asm_scs);
    asm_mem := mem;
    asm_reg := m.(asm_reg);
    asm_regx := m.(asm_regx);
    asm_xreg := m.(asm_xreg);
    asm_flag := m.(asm_flag);
  |}.

Section DEFS.

Class JazzIParams :=
  {
    entries : seq funname;
    mI : mem;
    ripI : pointer;
    rmI : regmap;
    rxmI : regxmap;
    xrmI : xregmap;
    rfmI : rflagmap;
  }.

Context
  (p : uprog)
  (q : asm_prog)
  {JP : JazzIParams}
.

(* Source needs a memory, target needs all the rest except syscall_state. *)
Definition _Mo : choiceType := {choice asmmem}.

Definition _mi : _Mo :=
  {|
    asm_rip := ripI;
    asm_scs := tt;
    asm_mem := mI;
    asm_reg := rmI;
    asm_regx := rxmI;
    asm_xreg := xrmI;
    asm_flag := rfmI;
  |}.

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

Instance JazzI : OracleSystemInterface :=
  {|
    Mo := _Mo;
    No := _No;
    In := _In;
    Out := _Out;
    mi := _mi;
  |}.

(* -------------------------------------------------------------------------- *)
(* Source oracle system *)

Definition mkfs (fn : funname) (m : mem) (args : seq wseq) : fstate :=
  let vs :=
    if get_fundef (p_funcs p) fn is Some fd then
      [seq val_of_wseq p.1 p.2 | p <- zip (f_tyin fd) args ]
    else [::] (* absurd *)
  in
  {| fscs := tt; fmem := m; fvals := vs; |}.

Definition unmkfs (fs : fstate) : seq wseq * mem :=
  ([seq wseq_of_val v | v <- fs.(fvals) ], fs.(fmem)).

Definition isem_unit_res
  (o : _No) (i : _In o) (m : _Mo) : itree E (_Out o * _Mo) :=
  let fs := mkfs o m.(asm_mem) i in
  let* fs' := isem_unit p o fs in
  let (r, m') := unmkfs fs' in
  Ret (r, xm_with_mem m' m).
Arguments isem_unit_res : clear implicits.

(* TODO Why doesn't [|>] work for [translateE]? *)
Definition _OoS (o : _No) (i : _In o) (m : _Mo) : itree Rnd (_Out o * _Mo) :=
  let* ores := translateE (isem_unit_res o i m |> interp_Err) in
  if ores is ESok res then Ret res
  else Ret ([::], _mi) (* absurd *).

Instance Source : OracleSystem JazzI := {| Oo := _OoS; |}.

(* -------------------------------------------------------------------------- *)
(* Target oracle system *)

Definition xm_writes
  (m : asmmem) (xs : seq asm_typed_reg) (args : seq wseq) : exec asmmem.
Proof using. Admitted.

Definition mkxm (fn : funname) (m : asmmem) (args : seq wseq) : asmmem :=
  if get_fundef (asm_funcs q) fn is Some xfd then
    rdflt _mi (xm_writes m xfd.(asm_fd_arg) args)
  else _mi. (* absurd *)

Definition xm_read (m : asmmem) (x : asm_typed_reg) : value.
Proof using. Admitted.

Definition xget_res (fn : funname) (m : asmmem) : seq wseq :=
  if get_fundef (asm_funcs q) fn is Some xfd then
    [seq wseq_of_val (xm_read m x) | x <- xfd.(asm_fd_res) ]
  else [::]. (* absurd *)

Definition isem_asm_res
  (o : _No) (i : _In o) (m : _Mo) : itree E (_Out o * _Mo) :=
  let xm := mkxm o m i in
  let* xm' := isem_asm q o xm in
  Ret (xget_res o xm', xm').
Arguments isem_asm_res : clear implicits.

Definition _OoT (o : _No) (i : _In o) (m : _Mo) : itree Rnd (_Out o * _Mo) :=
  let* ores := translateE (isem_asm_res o i m |> interp_Err) in
  if ores is ESok res then Ret res
  else Ret ([::], _mi) (* absurd *).

Instance Target : OracleSystem JazzI := {| Oo := _OoT; |}.

(* -------------------------------------------------------------------------- *)
(* Proof. *)

Context
  {lowering_options : Type}
  (aparams : architecture_params lowering_options)
  (haparams : h_architecture_params aparams)
  (cparams : compiler_params lowering_options)
  (print_uprogP : forall s p, cparams.(print_uprog) s p = p)
  (print_sprogP : forall s p, cparams.(print_sprog) s p = p)
  (print_linearP : forall s p, cparams.(print_linear) s p = p)
  (hcomp : compile_prog_to_asm aparams cparams entries p = ok q)
.

Definition inv_mo : _Mo -> _Mo -> Prop.
Proof using. Admitted.

Definition inv_eq {X : Type} (x y : X * _Mo) : Prop :=
  [/\ x.1 = y.1 & inv_mo x.2 y.2 ].

Lemma inv_mo_mi : inv_mo _mi _mi.
Proof using. Admitted.

Definition post_isem : funname -> mem -> asmmem -> fstate -> asmmem -> Prop.
Proof using. Admitted.

Lemma post_isemP fn ms mt fs xm :
  inv_mo ms mt ->
  post_isem fn (asm_mem ms) mt fs xm ->
  inv_eq
    ([seq wseq_of_val v | v <- fvals fs], xm_with_mem (fmem fs) ms)
    (xget_res fn xm, xm).
Proof using. Admitted.

Lemma eutt_isem_post fn ms mt i :
  eutt (post_isem fn (asm_mem ms) mt)
    (isem_unit p fn (mkfs fn (asm_mem ms) i))
    (isem_asm q fn (mkxm fn mt i)).
Proof using. Admitted.

Lemma eutt_isem_res o i ms mt :
  inv_mo ms mt ->
  eutt inv_eq (isem_unit_res o i ms) (isem_asm_res o i mt).
Proof.
move=> hm; apply: eutt_clo_bind; first exact: eutt_isem_post.
move=> fs xm h; apply eutt_Ret; exact/(post_isemP hm h).
Qed.

Theorem compiler_preserves o i m1 m2 :
  inv_mo m1 m2 ->
  eutt inv_eq (Source.(Oo) o i m1) (Target.(Oo) o i m2).
Proof.
move: o i => [fn hfn] /= i hm.
have [xfd [hgetq _ heq]] :=
  [elaborate it_compile_prog_to_asmP
    haparams print_uprogP print_sprogP print_linearP hcomp hfn].
(* TODO we could prove that we always get OK instead of using exec_rel *)
apply: (eutt_clo_bind _ (UU := exec_rel inv_eq)).
- exact/eutt_translateE/interp_exec_eutt/eutt_isem_res/hm.
move=> /= [[rs ms]|?] [[rt mt]|?] //=; last first.
- move=> _; apply eutt_Ret; split=> //=; exact: inv_mo_mi.
move=> [/= -> hm']; apply eutt_Ret; split=> //; exact: hm'.
Qed.

End DEFS.

(* -------------------------------------------------------------------------- *)
(* Instantiation to KEMs and IND-CCA. *)

Section INSTANTIATION.

Context
  {JP : JazzIParams}
  (msgbytes : positive)
  (fn_genkey fn_encap fn_decap : funname)
  (export_genkey : fn_genkey \in entries)
  (export_encap : fn_encap \in entries)
  (export_decap : fn_decap \in entries)
.

Notation OracleSystem := (OracleSystem (R := R)) (only parsing).

#[local] Instance KEMP_of_JP : KEMParams :=
  {|
    M := _Mo;
    M0 := _mi;
    pkey := wseq;
    skey := wseq;
    ctxt := wseq;
    msg := wvec msgbytes;
    dummy_ct := [::];
    dummy_msg := dummy_wvec msgbytes;
  |}.

Definition efn_kg : export_funname := {| _export := export_genkey; |}.
Definition efn_encap : export_funname := {| _export := export_encap; |}.
Definition efn_decap : export_funname := {| _export := export_decap; |}.

Section JKEM.
  (* The KEM induced by a Jasmin program. *)

  Context (P : OracleSystem JazzI).

  Notation InK := (@In KEM) (only parsing).
  Notation OutK := (@Out KEM) (only parsing).

  Let Oo_JKEM_GenKey
    (i : InK OGenKey) (m : M) : itree Rnd (OutK OGenKey * M) :=
    let* (rs, m') := @Oo _ _ P efn_kg [::] m in
    if rs is [:: pk; sk ] then Ret ((pk, sk), m')
    else Ret (([::], [::]), m). (* absurd *)

  Let Oo_JKEM_Encap
    (i : InK OEncap) (m : M) : itree Rnd (OutK OEncap * M) :=
    let* (rs, m') := @Oo _ _ P efn_encap [:: i ] m in
    if rs is [:: ct; msg ] then Ret ((ct, mkwvec _ msg), m')
    else Ret ((dummy_ct, dummy_msg), m). (* absurd *)

  Let Oo_JKEM_Decap
    (i : InK ODecap) (m : M) : itree Rnd (OutK ODecap * M) :=
    let* (rs, m') := @Oo _ _ P efn_decap [:: i.1; i.2 ] m in
    if rs is [:: msg ] then Ret (mkwvec _ msg, m')
    else Ret (dummy_msg, m). (* absurd *)

  Definition _Oo_KEM
    (o : kem_oracle_name) : InK o -> M -> itree Rnd (OutK o * M) :=
    match o with
    | OGenKey => Oo_JKEM_GenKey
    | OEncap => Oo_JKEM_Encap
    | ODecap => Oo_JKEM_Decap
    end.

  Instance KEM_of_Jazz : OracleSystem KEM := {| Oo := fun o i => _Oo_KEM i; |}.

End JKEM.

Lemma equivalent_JKEM P Q :
  equivalent P Q ->
  equivalent (KEM_of_Jazz P) (KEM_of_Jazz Q).
Proof using. Admitted.

Theorem mlkem_end_to_end p q :
  indcca_reduction (KEM_of_Jazz (Source p)) (KEM_of_Jazz (Target q)).
Proof using. Admitted.

End INSTANTIATION.

End MAIN.
