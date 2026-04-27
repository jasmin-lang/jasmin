From Coq Require Import Lia JMeq.
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

Section MOVE.

Context
  {reg regx xreg rflag cond asm_op extra_op syscall_state : Type}
  {sc_sem : syscall.syscall_sem syscall_state}
  {asm_e : asm_extra reg regx xreg rflag cond asm_op extra_op}
  {call_conv : calling_convention}
  {asm_scsem : asm_syscall_sem}
.

Definition safe_uprog (p : uprog) (fn : funname) (fs : fstate) : Prop :=
  safe (is_error wE) (isem_unit p fn fs).

Definition val_is_def (v : value) : bool :=
  if v is Varr _ a then arr_is_def a else is_defined v.

Definition res_defined (p : uprog) (fn : funname) (fs : fstate) : Prop :=
  lutt
    (fun T e => True)
    (fun T e r => True)
    (fun fs => all val_is_def (fvals fs))
    (isem_unit p fn fs).

End MOVE.

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

Notation E := (ErrEvent +' RndEvent unit).

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

Definition mkfs (m : mem) (vs : values) : fstate :=
  {| fscs := tt; fmem := m; fvals := vs; |}.

Definition safe_on p fn m vs :=
  forall m',
    mem_equiv m m' ->
    safe_uprog p fn (mkfs m' vs).

Definition res_defined_on p fn m vs :=
  forall m',
    mem_equiv m m' ->
    res_defined p fn (mkfs m' vs).

Definition isem_asm (q : asm_prog) :=
  iasmsem_exportcall
    (asm_d := _asm)
    (call_conv := call_conv)
    (asm_scsem := asm_scsem)
    (E := E)
    (wE := wE)
    q.

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

Record export_fn :=
  {
    _fn :> funname;
    efn_export : _fn \in entries;
    efn_fd : fundef;
    efn_fd_ok : get_fundef (p_funcs p) _fn = Some efn_fd;
  }.

Definition _No : choiceType := {choice export_fn}.

(* Safety should be proven assuming only that the shape coincides with initial
   memory. *)
Record valid_input o :=
  {
    _args :> values;
    vi_safe : safe_on p o mI _args;
    vi_def : res_defined_on p o mI _args;
    (* for each array, give me an address with enough space *)
  }.

Definition _In (o : _No) : choiceType := {choice valid_input o}.

Definition _Out (o : _No) : choiceType := seq wseq.

Instance JazzI : OracleSystemInterface :=
  {|
    No := _No;
    In := _In;
    Out := _Out;
  |}.

(* -------------------------------------------------------------------------- *)
(* Source oracle system *)

Definition wseq_of_val (v : value) : wseq :=
  match v with
  | Varr _ a => wseq_of_arr a
  | Vword _ w => split_vec 8 w
  | _ => [::]
  end.

Definition unmkfs (fs : fstate) : seq wseq * mem :=
  ([seq wseq_of_val v | v <- fs.(fvals) ], fs.(fmem)).

Definition isem_unit_res
  (o : _No) (i : _In o) (m : _Mo) : itree E (_Out o * _Mo) :=
  let fs := mkfs m.(asm_mem) i in
  let* fs' := isem_unit p o fs in
  let (r, m') := unmkfs fs' in
  Ret (r, xm_with_mem m' m).

#[global] Arguments isem_unit_res : clear implicits.

(* TODO Why doesn't [|>] work for [translateE]? *)
Definition _OoS (o : _No) (i : _In o) (m : _Mo) : itree Rnd (_Out o * _Mo) :=
  let* ores := translateE (isem_unit_res o i m |> interp_Err) in
  if ores is ESok res then Ret res
  else Ret ([::], _mi). (* absurd *)

Instance Source : OracleSystem JazzI :=
  {|
    Mo := _Mo;
    Oo := _OoS;
    mi := _mi;
  |}.

(* -------------------------------------------------------------------------- *)
(* Target oracle system *)

Definition xm_writes
  (m : asmmem) (xs : seq asm_typed_reg) (args : values) : exec asmmem.
Proof using. Admitted.

Definition mkxm (fn : funname) (m : asmmem) (args : values) : asmmem :=
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

Instance Target : OracleSystem JazzI :=
  {|
    Mo := _Mo;
    Oo := _OoT;
    mi := _mi;
  |}.

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

(* TODO can these be automatic? *)

Lemma export_funname_in_entries o : _fn o \in entries.
Proof. exact: efn_export o. Qed.

Lemma export_funname_get_fundef o :
  get_fundef p.(p_funcs) (_fn o) = Some (efn_fd o).
Proof. exact: efn_fd_ok o. Qed.

#[local] Hint Resolve
  export_funname_in_entries
  export_funname_get_fundef
  : core.

Definition inv_mo : _Mo -> _Mo -> Prop.
Proof using. Admitted.

Definition inv_eq {X : Type} (x y : X * _Mo) : Prop :=
  [/\ x.1 = y.1 & inv_mo x.2 y.2 ].

Lemma inv_mo_mi : inv_mo _mi _mi.
Proof using. Admitted.

Lemma inv_mo_mem_equiv_mi ms mt :
  inv_mo ms mt ->
  mem_equiv mI ms.(asm_mem).
Proof using. Admitted.

Definition post_isem
  (fn : funname) (ms mt : asmmem) (fs' : fstate) (xm' : asmmem) : Prop :=
  exists xfd i,
    let: fs := mkfs ms.(asm_mem) i in
    let: xm := mkxm fn mt i in
    [/\ get_fundef q.(asm_funcs) fn = Some xfd
      , full_pre p q fn xfd fs xm
      & full_post cparams p q fn xfd fs xm fs' xm' ].

Lemma post_isemP fn ms mt fs xm :
  inv_mo ms mt ->
  post_isem fn ms mt fs xm ->
  inv_eq
    ([seq wseq_of_val v | v <- fvals fs], xm_with_mem (fmem fs) ms)
    (xget_res fn xm, xm).
Proof using. Admitted.

(* MOVE *)
Let REeq {E : Type -> Type} A1 A2 (e1: E A1) (e2: E A2) :=
  exists h : A2 = A1, e1 = eq_rect A2 E e2 A1 h.

(* MOVE *)
Let RAeq {E : Type -> Type} A1 A2 (e1: E A1) (a1: A1) (e2: E A2) (a2: A2) :=
  JMeq a1 a2.

(* MOVE *)
Lemma correct_comp fn fd :
  fn \in entries ->
  get_fundef p.(p_funcs) fn = Some fd ->
  exists2 xfd,
    get_fundef q.(asm_funcs) fn = Some xfd
    & forall s t,
        safe_uprog p fn s ->
        res_defined p fn s ->
        full_pre p q fn xfd s t ->
        eutt
          (full_post cparams p q fn xfd s t)
          (isem_unit p fn s) (isem_asm q fn t).
Proof.
move=> hfn hfd.
have [xfd [hxfd _ heq]] := [elaborate
  it_compile_prog_to_asmP
    haparams print_uprogP print_sprogP print_linearP hcomp hfn ].
exists xfd; first exact: hxfd.
move=> s t hsafe hdef hpre.
apply/simple_rutt_eutt/(EPreRel_safe_xrutt_rutt hsafe).
apply: (lutt_xrutt_trans_l'
  (REv := EPreRel_safe (is_error wE) REeq)
  (RAns := RAeq)
  (RR := fun s' t' =>
           [/\ all val_is_def (fvals s')
             & full_post cparams p q fn xfd s t s' t' ]));
  cycle -2.
- exact: (isem_fun_finalize (wa := withassert) (scP := sCP_unit)) hfd.
- apply: lutt_xrutt_trans_l'; cycle -2.
  + exact: hdef.
  + exact: heq hpre.
  + move=> T1 T2 [|[[] n1]]; first by left.
    move=> [//|[[] _]] _ [_ <-]; right; by exists erefl.
  + move=> T1 T2 [//|e1] r1 [//|e2] r2 _ _ [] _.
    destruct e1 as [[] n1]; destruct e2 as [[] n2].
    by move=> /(JMeq_eq (x := r1)) <-.
  done.
- done.
- done.
by move=> s' t' hfin [].
Qed.

(* TODO missing hypotheses *)
Lemma inv_mo_full_pre fn xfd i ms mt :
  get_fundef (asm_funcs q) fn = Some xfd ->
  inv_mo ms mt ->
  full_pre p q fn xfd (mkfs ms.(asm_mem) i) (mkxm fn mt i).
Proof using. Admitted.

Lemma eutt_isem_post fn fd ms mt i :
  fn \in entries ->
  get_fundef p.(p_funcs) fn = Some fd ->
  safe_uprog p fn (mkfs ms.(asm_mem) i) ->
  res_defined p fn (mkfs ms.(asm_mem) i) ->
  inv_mo ms mt ->
  eutt (post_isem fn ms mt)
    (isem_unit p fn (mkfs (asm_mem ms) i))
    (isem_asm q fn (mkxm fn mt i)).
Proof.
move=> hfn hfd hsafe hdef hm.
have [xfd hxfd heq] := correct_comp hfn hfd.
have hpre := inv_mo_full_pre i hxfd hm.
apply: eutt_subrel; last first.
- apply: heq; first exact: hsafe.
  + exact: hdef.
  exact: hpre.
move=> fs xm hpost; by exists xfd, i.
Qed.

Lemma eutt_isem_res o i ms mt :
  inv_mo ms mt ->
  eutt inv_eq (isem_unit_res o i ms) (isem_asm_res o i mt).
Proof.
move=> hm; apply: eutt_clo_bind.
- apply: eutt_isem_post => //.
  + exact/vi_safe/inv_mo_mem_equiv_mi/hm.
  exact/vi_def/inv_mo_mem_equiv_mi/hm.
move=> fs xm h; apply eutt_Ret; exact/(post_isemP hm h).
Qed.

Theorem compiler_preserves o i m1 m2 :
  inv_mo m1 m2 ->
  eutt inv_eq (Source.(Oo) o i m1) (Target.(Oo) o i m2).
Proof.
move=> hm.
have [xfd [hgetq _ heq]] := [elaborate
  it_compile_prog_to_asmP haparams print_uprogP print_sprogP print_linearP
    hcomp (efn_export o)].
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
  (pkbytes skbytes ctbytes msgbytes : positive)
  (fn_genkey fn_encap fn_decap : funname)
  (fd_genkey fd_encap fd_decap : ufundef)
  (export_genkey : fn_genkey \in entries)
  (export_encap : fn_encap \in entries)
  (export_decap : fn_decap \in entries)
  (p : uprog)
  (fd_genkey_ok : get_fundef (p_funcs p) fn_genkey = Some fd_genkey)
  (fd_encap_ok : get_fundef (p_funcs p) fn_encap = Some fd_encap)
  (fd_decap_ok : get_fundef (p_funcs p) fn_decap = Some fd_decap)
  (genkey_ok :
    let: pk := WArray.empty pkbytes in
    let: sk := WArray.empty skbytes in
    safe_on p fn_genkey mI [:: Varr pk; Varr sk ]
    /\ res_defined_on p fn_genkey mI [:: Varr pk; Varr sk ])
  (encap_ok :
    forall (pk : WArray.array pkbytes) (msg : WArray.array msgbytes),
      arr_is_def pk ->
      arr_is_def msg ->
      safe_on p fn_encap mI [:: Varr pk; Varr msg ]
      /\ res_defined_on p fn_encap mI [:: Varr pk; Varr msg ])
  (decap_ok :
    forall (sk : WArray.array skbytes) (ct : WArray.array ctbytes),
      arr_is_def sk ->
      arr_is_def ct ->
      safe_on p fn_decap mI [:: Varr sk; Varr ct ]
      /\ res_defined_on p fn_decap mI [:: Varr sk; Varr ct ])
.

Notation OracleSystem := (OracleSystem (R := R)) (only parsing).

Definition pk0 := mkwvec pkbytes [::].
Definition sk0 := mkwvec skbytes [::].
Definition ct0 := mkwvec ctbytes [::].
Definition msg0 := mkwvec msgbytes [::].

#[local] Instance KEMP_of_JP : KEMParams :=
  {|
    pkey := wvec pkbytes;
    skey := wvec skbytes;
    ctxt := wvec ctbytes;
    msg := wvec msgbytes;
    dummy_ct := ct0;
    dummy_msg := msg0;
  |}.

Definition efn_kg : export_fn p :=
  {| efn_export := export_genkey; efn_fd_ok := fd_genkey_ok; |}.
Definition efn_encap : export_fn p :=
  {| efn_export := export_encap; efn_fd_ok := fd_encap_ok; |}.
Definition efn_decap : export_fn p :=
  {| efn_export := export_decap; efn_fd_ok := fd_decap_ok; |}.

Section JKEM.
  (* The KEM induced by a Jasmin program. *)

  Context (J : OracleSystem (JazzI p)).

  Notation InK := (In (I := KEM)).
  Notation OutK := (Out (I := KEM)).

  Definition vi_GenKey : valid_input p efn_kg :=
    {| vi_safe := genkey_ok.1; vi_def := genkey_ok.2; |}.
  Definition vi_Encap (i : InK OEncap) : valid_input p efn_encap.
  Admitted.
  Definition vi_Decap (i : InK ODecap) : valid_input p efn_decap.
  Admitted.

  Let Oo_JKEM_GenKey
    (i : InK OGenKey) (m : Mo) : itree Rnd (OutK OGenKey * Mo) :=
    let* (rs, m') := J.(Oo) efn_kg vi_GenKey m in
    if rs is [:: pk; sk ] then Ret ((mkwvec _ pk, mkwvec _ sk), m')
    else Ret ((pk0, sk0), m). (* absurd *)

  Let Oo_JKEM_Encap
    (i : InK OEncap) (m : Mo) : itree Rnd (OutK OEncap * Mo) :=
    let* (rs, m') := J.(Oo) efn_encap (vi_Encap i) m in
    if rs is [:: ct; msg ] then Ret ((mkwvec _ ct, mkwvec _ msg), m')
    else Ret ((ct0, msg0), m). (* absurd *)

  Let Oo_JKEM_Decap
    (i : InK ODecap) (m : Mo) : itree Rnd (OutK ODecap * Mo) :=
    let* (rs, m') := J.(Oo) efn_decap (vi_Decap i) m in
    if rs is [:: msg ] then Ret (mkwvec _ msg, m')
    else Ret (msg0, m). (* absurd *)

  Definition _Oo_KEM
    (o : kem_oracle_name) : InK o -> Mo -> itree Rnd (OutK o * Mo) :=
    match o with
    | OGenKey => Oo_JKEM_GenKey
    | OEncap => Oo_JKEM_Encap
    | ODecap => Oo_JKEM_Decap
    end.

  Instance KEM_of_Jazz : OracleSystem KEM :=
    {|
      Mo := Mo;
      Oo := fun o i => _Oo_KEM i;
      mi := mi;
    |}.

End JKEM.

Lemma simulating_JKEM P Q :
  simulating P Q ->
  simulating (KEM_of_Jazz P) (KEM_of_Jazz Q).
Proof using. Admitted.

Theorem mlkem_end_to_end q :
  indcca_reduction (KEM_of_Jazz (Source p)) (KEM_of_Jazz (Target p q)).
Proof using. Admitted.

End INSTANTIATION.

End MAIN.
