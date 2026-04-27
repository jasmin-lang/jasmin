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
  equiv_extras
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
  asm_gen_proof
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

Definition to_Rnd : itree (RndEvent unit) ~> itree Rnd :=
  fun _ t => interp handleE t.

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
    mS : mem;
    mT : mem;
    ripT : pointer;
    rmT : regmap;
    rxmT : regxmap;
    xrmT : xregmap;
    rfmT : rflagmap;
  }.

Context
  (p : uprog)
  (q : asm_prog)
  {JP : JazzIParams}
.

Record export_fn :=
  {
    _fn :> funname;
    efn_export : _fn \in entries;
    efn_fd : fundef;
    efn_fd_ok : get_fundef (p_funcs p) _fn = Some efn_fd;
  }.

Definition JNo : choiceType := {choice export_fn}.

(* Safety should be proven assuming only that the shape coincides with initial
   memory. *)
Record valid_input o :=
  {
    _args :> values;
    vi_safe : safe_on p o mS _args;
    vi_def : res_defined_on p o mS _args;
    vi_ptrs : seq pointer;
    (*vi_ptrs_ok :
       forall i,
         oseq.onth _args i = Some (Varr _ _) ->
         exists2 p,
           seq.onth vi_ptrs i = Some p
           & ;*)
  }.

Definition JIn (o : JNo) : choiceType := {choice valid_input o}.

Definition JOut (o : JNo) : choiceType := seq wseq.

Instance JazzI : OracleSystemInterface :=
  {|
    No := JNo;
    In := JIn;
    Out := JOut;
  |}.

(* -------------------------------------------------------------------------- *)
(* Source oracle system *)

Definition MoS : choiceType := {choice mem}.

Definition wseq_of_val (v : value) : wseq :=
  match v with
  | Varr _ a => wseq_of_arr a
  | Vword _ w => split_vec 8 w
  | _ => [::]
  end.

Definition unmkfs (fs : fstate) : seq wseq * mem :=
  ([seq wseq_of_val v | v <- fs.(fvals) ], fs.(fmem)).

Definition isem_unit_res
  (o : JNo) (i : JIn o) (m : MoS) : itree E (JOut o * MoS) :=
  let fs := mkfs m i in
  let* fs' := isem_unit p o fs in
  let (r, m') := unmkfs fs' in
  Ret (r, m').

#[global] Arguments isem_unit_res : clear implicits.

(* TODO Why doesn't [|>] work for [to_Rnd]? *)
Definition OoS (o : JNo) (i : JIn o) (m : MoS) : itree Rnd (JOut o * MoS) :=
  let* ores := to_Rnd (isem_unit_res o i m |> interp_Err) in
  if ores is ESok res then Ret res
  else Ret ([::], mS). (* absurd *)

Instance Source : OracleSystem JazzI :=
  {|
    Mo := MoS;
    Oo := OoS;
    mi := mS;
  |}.

(* -------------------------------------------------------------------------- *)
(* Target oracle system *)

Definition MoT : choiceType := {choice asmmem}.

Definition xmT : asmmem :=
  {|
    asm_rip := ripT;
    asm_scs := tt;
    asm_mem := mT;
    asm_reg := rmT;
    asm_regx := rxmT;
    asm_xreg := xrmT;
    asm_flag := rfmT;
  |}.

Definition xm_write
  (x : asm_typed_reg) (v : value) (ptr : pointer) (xm : asmmem) : exec asmmem :=
  match x with
  | ARReg r =>
      if v is Varr _ a then
        let m' := write_wseq xm.(asm_mem) ptr (wseq_of_arr a) in
        ok (xm_with_mem m' xm)
      else
        Let w := to_word reg_size v in
        ok (mem_write_reg MSB_CLEAR r w xm)
  | ARegX rx =>
      Let w := to_word reg_size v in
      ok (mem_write_regx MSB_CLEAR rx w xm)
  | AXReg xr =>
      Let w := to_word xreg_size v in
      ok (mem_write_xreg MSB_CLEAR xr w xm)
  | ABReg f =>
      Let b := to_bool v in
      ok (mem_write_rflag xm f (Some b))
  end.

Definition xm_writes
  (m : asmmem)
  (xs : seq asm_typed_reg)
  (args : values)
  (ptrs : seq pointer) :
  exec asmmem :=
  foldM (fun x => xm_write x.1.1 x.1.2 x.2) m (zip (zip xs args) ptrs).

Definition mkxm
  (fn : funname) (m : asmmem) (args : values) (ptrs : seq pointer) : asmmem :=
  if get_fundef (asm_funcs q) fn is Some xfd then
    rdflt xmT (xm_writes m xfd.(asm_fd_arg) args ptrs)
  else xmT. (* absurd *)

Definition xm_read
  (xm : asmmem) (x : asm_typed_reg) (ty : atype) (ptr : pointer) : wseq :=
  if ty is aarr ws len then
    let len' := Z.to_pos (arr_size ws len) in
    read_wseq xm.(asm_mem) ptr len'
  else wseq_of_val (get_typed_reg_value xm x).

Definition xget_res
  (fn : funname) (m : asmmem) (ptrs : seq pointer) : seq wseq :=
  if get_fundef p.(p_funcs) fn is Some fd then
    if get_fundef q.(asm_funcs) fn is Some xfd then
      [seq xm_read m x.1.1 x.1.2 x.2
      | x <- zip (zip xfd.(asm_fd_res) fd.(f_tyout)) ptrs ]
    else [::] (* absurd *)
  else [::]. (* absurd *)

Definition isem_asm_res
  (o : JNo) (i : JIn o) (m : MoT) : itree E (JOut o * MoT) :=
  let xm := mkxm o m i (vi_ptrs i) in
  let* xm' := isem_asm q o xm in
  Ret (xget_res o xm' (vi_ptrs i), xm').
Arguments isem_asm_res : clear implicits.

Definition OoT (o : JNo) (i : JIn o) (m : MoT) : itree Rnd (JOut o * MoT) :=
  let* ores := to_Rnd (isem_asm_res o i m |> interp_Err) in
  if ores is ESok res then Ret res
  else Ret ([::], xmT). (* absurd *)

Instance Target : OracleSystem JazzI :=
  {|
    Mo := MoT;
    Oo := OoT;
    mi := xmT;
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

Definition sim : MoS -> MoT -> Prop.
Proof using. Admitted.

Definition inv_eq {X : Type} : X * MoS -> X * MoT -> Prop :=
  eqR (X := X) sim.

Lemma sim_mS_xmT : sim mS xmT.
Proof using. Admitted.

Lemma sim_mem_equiv_mi ms mt :
  sim ms mt ->
  mem_equiv mS ms.
Proof using. Admitted.

Definition post_isem
  (fn : funname)
  (ptrs : seq pointer)
  (ms : mem)
  (mt : asmmem)
  (fs' : fstate)
  (xm' : asmmem) :
  Prop :=
  exists xfd vs,
    let: fs := mkfs ms vs in
    let: xm := mkxm fn mt vs ptrs in
    [/\ get_fundef q.(asm_funcs) fn = Some xfd
      , full_pre p q fn xfd fs xm
      & full_post cparams p q fn xfd fs xm fs' xm' ].

Lemma post_isemP fn ptrs ms mt fs xm :
  sim ms mt ->
  post_isem fn ptrs ms mt fs xm ->
  inv_eq
    ([seq wseq_of_val v | v <- fvals fs], fmem fs)
    (xget_res fn xm ptrs, xm).
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
Lemma sim_full_pre fn xfd i ptrs ms mt :
  get_fundef (asm_funcs q) fn = Some xfd ->
  sim ms mt ->
  full_pre p q fn xfd (mkfs ms i) (mkxm fn mt i ptrs).
Proof using. Admitted.

Lemma eutt_isem_post fn fd ms mt i ptrs :
  fn \in entries ->
  get_fundef p.(p_funcs) fn = Some fd ->
  safe_uprog p fn (mkfs ms i) ->
  res_defined p fn (mkfs ms i) ->
  sim ms mt ->
  eutt (post_isem fn ptrs ms mt)
    (isem_unit p fn (mkfs ms i))
    (isem_asm q fn (mkxm fn mt i ptrs)).
Proof.
move=> hfn hfd hsafe hdef hm.
have [xfd hxfd heq] := correct_comp hfn hfd.
have hpre := sim_full_pre i ptrs hxfd hm.
apply: eutt_subrel; last first.
- apply: heq; first exact: hsafe.
  + exact: hdef.
  exact: hpre.
move=> fs xm hpost; by exists xfd, i.
Qed.

Lemma eutt_isem_res o i ms mt :
  sim ms mt ->
  eutt inv_eq (isem_unit_res o i ms) (isem_asm_res o i mt).
Proof.
move=> hm; apply: eutt_clo_bind.
- apply: eutt_isem_post => //.
  + exact/vi_safe/sim_mem_equiv_mi/hm.
  exact/vi_def/sim_mem_equiv_mi/hm.
move=> fs xm h; apply eutt_Ret; exact: post_isemP hm h.
Qed.

Theorem compiler_preserves : simulating Source Target.
Proof.
exists sim; split; first exact: sim_mS_xmT.
move=> o i m1 m2 hm.
have [xfd [hgetq _ heq]] := [elaborate
  it_compile_prog_to_asmP haparams print_uprogP print_sprogP print_linearP
    hcomp (efn_export o)].
(* TODO we could prove that we always get OK instead of using exec_rel *)
apply (eutt_clo_bind _ (UU := exec_rel inv_eq)).
- apply/eutt_interp_RR/interp_exec_eutt_gen/eutt_isem_res/hm.
move=> /= [[rs ms]|?] [[rt mt]|?] //=; last first.
- move=> _; apply eutt_Ret; split=> //=; exact/sim_mS_xmT.
move=> [/= -> hm']; apply eutt_Ret; split=> //; exact/hm'.
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
.

Definition pk0 := mkwvec pkbytes [::].
Definition sk0 := mkwvec skbytes [::].
Definition ct0 := mkwvec ctbytes [::].
Definition msg0 := mkwvec msgbytes [::].

Definition dummyp := WArray.empty pkbytes.
Definition dummys := WArray.empty skbytes.
Definition dummyc := WArray.empty ctbytes.
Definition dummym := WArray.empty msgbytes.

Context
  (fd_genkey_ok : get_fundef (p_funcs p) fn_genkey = Some fd_genkey)
  (fd_encap_ok : get_fundef (p_funcs p) fn_encap = Some fd_encap)
  (fd_decap_ok : get_fundef (p_funcs p) fn_decap = Some fd_decap)
  (ppk psk pct pmsg : pointer)
  (genkey_ok :
    let: args := [:: Varr dummyp; Varr dummys ] in
    safe_on p fn_genkey mS args /\ res_defined_on p fn_genkey mS args)
  (encap_ok :
    forall (pk : WArray.array pkbytes),
      let: args := [:: Varr dummyc; Varr dummym; Varr pk ] in
      arr_is_def pk ->
      safe_on p fn_encap mS args /\ res_defined_on p fn_encap mS args)
  (decap_ok :
    forall (ct : WArray.array ctbytes) (sk : WArray.array skbytes),
      let: args := [:: Varr dummym; Varr sk; Varr ct ] in
      arr_is_def ct ->
      arr_is_def sk ->
      safe_on p fn_decap mS args /\ res_defined_on p fn_decap mS args)
.

Notation OracleSystem := (OracleSystem (R := R)) (only parsing).


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
    {|
      _args := [:: Varr dummyp; Varr dummys ];
      vi_safe := genkey_ok.1;
      vi_def := genkey_ok.2;
      vi_ptrs := [::];
    |}.

  Let mk_arr {n : positive} (s : wvec n) :=
    Varr (rdflt (WArray.empty _) (WArray.fill n (wseq_of_wvec s))).

  (* MOVE *)
  Lemma fill_ok (n : positive) bytes :
    Pos.to_nat n = size bytes ->
    exists a, WArray.fill n bytes = ok a.
  Proof.
  move=> h; rewrite /WArray.fill -h eqxx /=.
  suff : exists z a, WArray.fill_aux n bytes = ok (z, a).
  - by move=> [z [a {}h]]; rewrite h; exists a.
  have := WArray.fill_aux_ok (len := n) (bytes := bytes).
  rewrite h => /(_ (le_n _)).
  by case: WArray.fill_aux => // [[z a] ?] /=; exists z, a.
  Qed.

  Lemma arr_is_def_mk_arr (n : positive) (s : wvec n) :
    arr_is_def (rdflt (WArray.empty _) (WArray.fill n (wseq_of_wvec s))).
  Proof using.
    have : Pos.to_nat n = size (s : wseq) by admit.
    move=> /fill_ok [a h]; rewrite h /=.
    rewrite /arr_is_def.
  Admitted.

  Definition vi_Encap (i : InK OEncap) : valid_input p efn_encap :=
    {|
      _args := [:: Varr dummyc; Varr dummym; mk_arr i ];
      vi_ptrs := [:: pmsg ];
      vi_safe := (encap_ok (arr_is_def_mk_arr i)).1;
      vi_def := (encap_ok (arr_is_def_mk_arr i)).2;
    |}.

  Definition vi_Decap (i : InK ODecap) : valid_input p efn_decap :=
    {|
      _args := [:: Varr dummym; mk_arr i.1; mk_arr i.2 ];
      vi_ptrs := [:: pmsg; psk; pct ];
      vi_safe := (decap_ok (arr_is_def_mk_arr i.2) (arr_is_def_mk_arr i.1)).1;
      vi_def := (decap_ok (arr_is_def_mk_arr i.2) (arr_is_def_mk_arr i.1)).2;
    |}.

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
Proof.
move=> [sim hsim]; exists sim; split; first exact/hsim.(sim_mi).
move=> [[] | pk | [sk ct]] m1 m2 hm.
- apply: eutt_clo_bind; first exact: hsim.(sim_Oo) hm.
  move=> [r m1'] [_ m2'] [/= <-] hm'.
  by case: r => [| pk [| sk [|??]]]; apply eutt_Ret.
- apply: eutt_clo_bind; first exact: hsim.(sim_Oo) hm.
  move=> [r m1'] [_ m2'] [/= <-] hm'.
  by case: r => [| ct [| msg [|??]]]; apply eutt_Ret.
apply: eutt_clo_bind; first exact: hsim.(sim_Oo) hm.
move=> [r m1'] [_ m2'] [/= <-] hm'.
by case: r => [| msg [|??]]; apply eutt_Ret.
Qed.

Context
  (q : asm_prog)
  {lowering_options : Type}
  (aparams : architecture_params lowering_options)
  (haparams : h_architecture_params aparams)
  (cparams : compiler_params lowering_options)
  (print_uprogP : forall s p, cparams.(print_uprog) s p = p)
  (print_sprogP : forall s p, cparams.(print_sprog) s p = p)
  (print_linearP : forall s p, cparams.(print_linear) s p = p)
  (hcomp : compile_prog_to_asm aparams cparams entries p = ok q)
.

Theorem mlkem_end_to_end :
  indcca_reduction (KEM_of_Jazz (Source p)) (KEM_of_Jazz (Target p q)).
Proof. by apply/sim_indcca_adv/simulating_JKEM/compiler_preserves; eauto. Qed.

End INSTANTIATION.

End MAIN.
