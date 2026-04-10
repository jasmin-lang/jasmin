From Coq Require Import Program.Equality.
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

From Paco Require paco.

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
  compiler
  core_logics
  distr
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
  rutt_extras
  xrutt
  xrutt_facts
.
Require Import
  arch_params_proof
  stack_alloc_proof_1
  stack_alloc_proof_2
  compiler_proof
  it_compiler_proof
.
Require allocation.

Require Import
  indcca
  it_sems_core
  psem
  psem_facts
  relational_logic
  hoare_logic
.

Require Import it_exec.

Import Order.TTheory.

#[local] Open Scope ring_scope.
#[local] Open Scope Z.
#[local] Open Scope order_scope.

Coercion Pos.to_nat : positive >-> nat.

Notation "'let*' p ':=' c1 'in' c2" :=
  (@ITree.bind _ _ _ c1 (fun p => c2))
    (at level 61, p as pattern, c1 at next level, right associativity).

Notation "x |> f" := (f x) (only parsing, at level 25).

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

Instance sc_sem : syscall.syscall_sem unit :=
  {| syscall.get_random := fun _ _ => (tt, [::]); |}.

Definition E := ErrEvent +' RndEvent unit.
Existing Instance with_Error0.
Existing Instance RndE00.

Definition handleE : RndEvent unit ~> itree (distr.Rnd (R := R)) :=
  fun _ '(Rnd _ len) =>
    let* bs := unif_rV (Z.to_nat len) in
    Ret (tt, wseq_of_wvec bs).

Definition translateE : itree (RndEvent unit) ~> itree distr.Rnd :=
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

Let isemT (q : sprog) (rip : pointer) :=
  isem_fun
    (asm_op := extended_op)
    (ep := ep_of_asm_e)
    (spp := spp_of_asm_e)
    (wa := noassert)
    (sip := sip_of_asm_e)
    (scP := sCP_stack)
    (E := E)
    (wsw := withsubword)
    (dc := direct_c)
    (pT := progStack)
    q rip.

Context (
  pkbytes (* MLKEM_INDCPA_PUBLICKEYBYTES *)
  skbytes (* KYBER_INDCPA_SECRETKEYBYTES *)
  ctbytes (* KYBER_INDCPA_BYTES *)
  msgbytes (* MLKEM_INDCPA_MSGBYTES *)
  : positive
).

Notation KEM_Challenger :=
  (Challenger
     (R := R)
     (pkey := wseq)
     (skey := wseq)
     (ciphert := wseq)
     (msg := wvec msgbytes)).

Notation KEM_Adversary :=
  (Adversary
     (R := R)
     (pkey := wseq)
     (advmem := advmem)
     (ciphert := wseq)
     (msg := wvec msgbytes)).

Section DEFS.

Context
  (p : uprog)
  (q : sprog)
  (rip : word Uptr)
  (fn_genkey fn_encap fn_decap : funname)
.

(* Abstractly, the signatures are as follows:
   genkey : () -> u8[MLKEM_INDCPA_PUBLICKEYBYTES] * u8[KYBER_INDCPA_SECRETKEYBYTES]
   encap : u8[MLKEM_INDCPA_PUBLICKEYBYTES] -> u8[KYBER_INDCPA_BYTES] * u8[MLKEM_INDCPA_MSGBYTES]
   decap : u8[KYBER_INDCPA_SECRETKEYBYTES] -> u8[KYBER_INDCPA_BYTES] -> u8[KYBER_INDCPA_MSGBYTES]
  *)

Definition pubkey := WArray.array pkbytes.
Definition seckey := WArray.array skbytes.
Definition ciphert := WArray.array ctbytes.
Definition msg := WArray.array msgbytes.

Definition pk_of_w := WArray.fill pkbytes.
Definition sk_of_w := WArray.fill skbytes.
Definition ct_of_w := WArray.fill ctbytes.

Definition dummyp := WArray.empty pkbytes.
Definition dummys := WArray.empty skbytes.
Definition dummyc := WArray.empty ctbytes.
Definition dummym := WArray.empty msgbytes.

Definition dummy2 : wseq * wseq := (dummy_wseq, dummy_wseq).
Definition dummymsg : wvec msgbytes := dummy_wvec _.

Section SEM.
  Context (m : mem).

  Let fs_of_vals vs : fstate := {| fscs := tt; fmem := m; fvals := vs; |}.

  Definition fsS_GenKey := fs_of_vals [:: Varr dummyp; Varr dummys ].
  Definition fsS_Encap (pk : pubkey) :=
    fs_of_vals [:: Varr dummyc; Varr dummym; Varr pk ].
  Definition fsS_Decap (sk : seckey) (ct : ciphert) :=
    fs_of_vals [:: Varr dummym; Varr ct; Varr sk ].

  Definition fsT_GenKey (ppk psk : pointer) :=
    fs_of_vals [:: Vword ppk; Vword psk ].
  Definition fsT_Encap (ppk pct pmsg : pointer) (pk : wseq) :=
    {|
      fscs := tt;
      fmem := write_wseq m ppk pk;
      fvals := [:: Vword pct; Vword pmsg; Vword ppk ];
    |}.
  Definition fsT_Decap (psk pct pmsg : pointer) (sk ct : wseq) :=
    let m' := write_wseq m psk sk in
    {|
      fscs := tt;
      fmem := write_wseq m' pct ct;
      fvals := [:: Vword pmsg; Vword pct; Vword psk ];
    |}.

  Definition get_res (n : positive) (vs : seq value) (i : nat) : wvec n :=
    nth (Vint 0) vs i |> wvec_of_val n.

  (* Implementation signature:
       (u8[pkbytes], u8[skbytes]) -> u8[pkbytes], u8[skbytes] *)
  Definition semS_GenKey :=
    let* fs' := isemS p fn_genkey fsS_GenKey |> interp_Err in
    if fs' is ESok fs' then
      let p := get_res pkbytes (fvals fs') 0 in
      let s := get_res skbytes (fvals fs') 1 in
      Ret (p : wseq, s : wseq)
    else Ret (dummy_wseq, dummy_wseq).

  (* Implementation signature:
       (u8[ctbytes], u8[msgbytes], u8[pkbytes]) -> u8[ctbytes], u8[msgbytes] *)
  Definition semS_Encap pk :=
    if pk_of_w pk is Ok pk then
      let fs := fsS_Encap pk in
      let* fs' := isemS p fn_encap fs |> interp_Err in
      if fs' is ESok fs' then
        let m := get_res msgbytes (fvals fs') 1 in
        let c := get_res ctbytes (fvals fs') 0 in
        Ret (c : wseq, m)
      else Ret (dummy_wseq, dummymsg)
    else Ret (dummy_wseq, dummymsg).

  (* Implementation signature:
       (u8[msgbytes], u8[ctbytes], u8[skbytes]) -> u8[msgbytes] *)
  Definition semS_Decap sk ct :=
    match sk_of_w sk, ct_of_w ct with
    | Ok sk, Ok ct =>
        let fs := fsS_Decap sk ct in
        let* fs' := isemS p fn_decap fs |> interp_Err in
        if fs' is ESok fs' then Ret (get_res msgbytes (fvals fs') 0)
        else Ret dummymsg
    | _, _ => Ret dummymsg
    end.

  Definition semT_GenKey ppk psk :=
    let fs := fsT_GenKey ppk psk in
    let* fs' := isemT q rip fn_genkey fs |> interp_Err in
    if fs' is ESok fs' then
      let pk := read_wvec (fmem fs') ppk pkbytes in
      let sk := read_wvec (fmem fs') psk skbytes in
      Ret (pk : wseq, sk : wseq)
    else Ret (dummy_wseq, dummy_wseq).

  Definition semT_Encap ppk pct pmsg pk :=
    if pk_of_w pk is Error _ then Ret (dummy_wseq, dummymsg)
    else
      let fs := fsT_Encap ppk pct pmsg pk in
      let* fs' := isemT q rip fn_encap fs |> interp_Err in
      if fs' is ESok fs' then
        let ct := read_wvec (fmem fs') pct ctbytes in
        let msg := read_wvec (fmem fs') pmsg msgbytes in
        Ret (ct : wseq, msg)
      else Ret (dummy_wseq, dummymsg).

  Definition semT_Decap psk pct pmsg sk ct :=
    if sk_of_w sk is Error _ then Ret dummymsg
    else if ct_of_w ct is Error _ then Ret dummymsg
    else
      let fs := fsT_Decap psk pct pmsg sk ct in
      let* fs' := isemT q rip fn_decap fs |> interp_Err in
      if fs' is ESok fs' then Ret (read_wvec (fmem fs') pmsg msgbytes)
      else Ret dummymsg.

  Definition Challenger_of_S : KEM_Challenger :=
    {|
      GenKey := translateE semS_GenKey;
      Encap := fun pk => translateE (semS_Encap pk);
      Decap := fun sk ct => translateE (semS_Decap sk ct);
    |}.

  Definition Challenger_of_T ppk psk pct pmsg : KEM_Challenger :=
    {|
      GenKey := translateE (semT_GenKey ppk psk);
      Encap := fun pk => translateE (semT_Encap ppk pct pmsg pk);
      Decap := fun sk ct => translateE (semT_Decap psk pct pmsg sk ct);
    |}.

End SEM.

(* Safety means:
 1. Jasmin safety (defined with lutt).
 2. Output arrays are defined (can be added to lutt).
 3. There exists a target memory and some pointers that can fit all the
    arguments, results, and global variables
    (a statement on the program and what the compiler decides about its stack
    usage, typically shouldn't be called "safety" but a different requirement
    on the compiler theorem to apply). *)

Definition safe_uprog fn fs := safe (is_error (with_Error0)) (isemS p fn fs).

Definition val_is_def (v : value) : bool :=
  if v is Varr _ a then arr_is_def a else is_defined v.

Definition res_defined fn fs :=
  lutt
    (E := E)
    (fun T e => True)
    (fun T e r => True)
    (fun fs => all val_is_def (fvals fs))
    (isemS p fn fs).

Definition total_stack fd :=
  let: e := fd.(f_extra) in
  e.(sf_stk_max) + wsize_size e.(sf_align) - 1.

Record ok_fun fn ufd sfd ms mt args argt :=
  {
    (* [ufd] is the definition of [fn]. *)
    ok_fun_ufd : get_fundef (p_funcs p) fn = Some ufd;

    (* [sfd] is the definition of the compilation of [fn]. *)
    ok_fun_sfd : get_fundef (p_funcs q) fn = Some sfd;

    (* There's enough stack space in the target memory. *)
    ok_fun_space :
      let: stk_sz := wunsigned (top_stack mt) - wunsigned (stack_limit mt) in
      (0 <= total_stack sfd <= stk_sz)%Z;

    (* The arguments are well formed. *)
    ok_fun_args : it_wf_args p q rip fn ms mt args argt;

    (* The return address is not on the stack or in a register. *)
    ok_fun_ra : is_RAnone (sf_return_address (f_extra sfd));
  }.

End DEFS.

Section THEOREM.

Context
  (entries : seq funname)
  (up : uprog)
  (sp : sprog) (rip : pointer)
  (fn_genkey fn_encap fn_decap : funname)
  (ufd_genkey ufd_encap ufd_decap : ufundef)
  (sfd_genkey sfd_encap sfd_decap : sfundef)
  (ms mt : mem)
  (ppk psk pct pmsg : pointer)
.

Context
  (* These are necessary to be able to write the values in memory. *)
  (small_pkbytes : (pkbytes : Z) <= wbase Uptr)
  (small_skbytes : (skbytes : Z) <= wbase Uptr)
  (small_ctbytes : (ctbytes : Z) <= wbase Uptr)

  (hcomp : compiler_front_end aparams cparams entries up = ok sp)

  (export_genkey : fn_genkey \in entries)
  (export_encap : fn_encap \in entries)
  (export_decap : fn_decap \in entries)

  (sig_genkey:
    exists pk sk,
      [/\ f_params ufd_genkey = [:: pk; sk ]
        , f_res ufd_genkey = [:: pk; sk ]
        , f_tyout ufd_genkey = [:: aarr U8 pkbytes; aarr U8 skbytes ]
        , wptr_status pk = Some true
        & wptr_status sk = Some true
  ])

  (sig_encap:
    exists pk ct msg,
      [/\ f_params ufd_encap = [:: ct; msg; pk ]
        , f_res ufd_encap = [:: ct; msg ]
        , f_tyout ufd_encap = [:: aarr U8 ctbytes; aarr U8 msgbytes ]
        , wptr_status pk = Some false
        , wptr_status ct = Some true
        & wptr_status msg = Some true
  ])

  (sig_decap:
    exists sk ct msg,
      [/\ f_params ufd_decap = [:: msg; ct; sk ]
        , f_res ufd_decap = [:: msg ]
        , f_tyout ufd_decap = [:: aarr U8 msgbytes ]
        , wptr_status sk = Some false
        , wptr_status ct = Some false
        & wptr_status msg = Some true
  ])

  (* This is only needed in the algorithms where the pointers are not writable,
     since otherwise we have [wf_arg_pointer]. *)
  (ppk_not_rip : disjoint_zrange rip (size_glob sp) ppk pkbytes)
  (pct_not_rip : disjoint_zrange rip (size_glob sp) pct ctbytes)
  (psk_not_rip : disjoint_zrange rip (size_glob sp) psk skbytes)

  (* Only needed in Decap. *)
  (* Really we only need to know that reading from these pointers after writing
     gives us the right values, not that they are disjoint. *)
  (pct_not_psk : disjoint_zrange pct ctbytes psk skbytes)

  (* GenKey is safe on the source memory. *)
  (ok_safe_genkey : safe_uprog up fn_genkey (fsS_GenKey ms))

  (* Encap is safe on the source memory for every public key argument. *)
  (ok_safe_encap : forall pk, safe_uprog up fn_encap (fsS_Encap ms pk))

  (* Decap is safe on the source memory for every ciphertext and secret key
     arguments. *)
  (ok_safe_decap : forall sk ct, safe_uprog up fn_decap (fsS_Decap ms sk ct))

  (* GenKey initializes the entire output arrays. *)
  (ok_defined_genkey : res_defined up fn_genkey (fsS_GenKey ms))

  (* Encap initializes the entire output arrays for any public key
     argument. *)
  (ok_defined_encap : forall pk, res_defined up fn_encap (fsS_Encap ms pk))

  (* Decap initializes the entire output array for every ciphertext and secret
     key arguments. *)
  (ok_defined_decap :
    forall sk ct, res_defined up fn_decap (fsS_Decap ms sk ct))

  (* The target memory coincides with the source one and allocates the global
     data. *)
  (ok_extend_mem : it_extend_mem sp rip ms mt)

  (* GenKey is defined and [ppk] and [psk] are valid pointers. *)
  (ok_genkey :
    let: args := [:: Varr dummyp; Varr dummys ] in
    let: argt := [:: Vword ppk; Vword psk ] in
    ok_fun up sp rip fn_genkey ufd_genkey sfd_genkey ms mt args argt)

  (* Encap is defined and [pct], [pmsg], and [ppk]  are valid pointers. *)
  (ok_encap :
    forall pk : pubkey,
      let: args := [:: Varr dummyc; Varr dummym; Varr pk ] in
      let: argt := [:: Vword pct; Vword pmsg; Vword ppk ] in
      ok_fun up sp rip fn_encap ufd_encap sfd_encap ms mt args argt)

  (* Decap is defined and [pmsg], [pct], and [psk] are valid pointers. *)
  (ok_decap :
    forall (sk : seckey) (ct : ciphert),
      let: args := [:: Varr dummym; Varr ct; Varr sk ] in
      let: argt := [:: Vword pmsg; Vword pct; Vword psk ] in
      ok_fun up sp rip fn_decap ufd_decap sfd_decap ms mt args argt)
.

(* Used to combine the compiler correctness result with safety and the condition
   on defined results. *)
Definition aux_post fn (s t s' t' : fstate) :=
  let: n := get_nb_wptr up fn in
  let: argt := fvals t in
  let: ress := fvals s' in
  [/\ List.Forall2 (value_in_mem (fmem t')) (take n ress) (take n argt)
    , all val_is_def ress
    & forall fd,
        get_fundef (p_funcs up) fn = Some fd ->
        is_finalize (pT := progUnit) (wsw := nosubword) (scP := sCP_unit)
          (dc := indirect_c) fd s'
  ].

Definition REeq {E : Type -> Type} A1 A2 (e1: E A1) (e2: E A2) :=
  exists h : A2 = A1, e1 = eq_rect A2 E e2 A1 h.

Definition RAeq
  {E : Type -> Type} A1 A2 (e1: E A1) (a1: A1) (e2: E A2) (a2: A2) :=
  JMeq a1 a2.

#[local]
Instance _eS : EquivSpec := FrontEndEquiv up sp rip.

Lemma correct_comp {fn fd s t} :
  fn \in entries ->
  get_fundef (p_funcs up) fn = Some fd ->
  safe_uprog up fn s ->
  res_defined up fn s ->
  rpreF fn fn s t ->
  eutt (aux_post fn s t) (isemS up fn s) (isemT sp rip fn t).
Proof.
move=> hfn hfd hsafe hdef hpre.
apply/simple_rutt_eutt/(EPreRel_safe_xrutt_rutt hsafe).
apply: (lutt_xrutt_trans_l'
  (REv := EPreRel_safe (is_error with_Error0) REeq)
  (RAns := RAeq)
  (RR := fun s' t' => all val_is_def (fvals s') /\ rpostF fn fn s t s' t'));
  cycle -2.
- exact: (isem_fun_finalize (wa := withassert) (scP := sCP_unit)) hfd.
- apply: (lutt_xrutt_trans_l'
    (REv := EPreRel (rE0 := HandlerContract))
    (RAns := EPostRel (rE0 := HandlerContract))
    (RR := rpostF fn fn s t)
  ); cycle -2.
  + exact: hdef.
  + exact: it_compiler_front_endP hcomp hfn _ _ hpre.
  + move=> T1 T2 [|[[] n1]]; first by left.
    move=> [//|[[] _]] _ [_ <-]; right; by exists erefl.
  + move=> T1 T2 [//|e1] r1 [//|e2] r2 _ _ [] _.
    destruct e1 as [[] n1]; destruct e2 as [[] n2].
    by move=> /(JMeq_eq (x := r1)) <-.
  done.
- done.
- done.
move=> s' t' hfin [{}hdef [res_in_mem _ _ _ _]].
split=> //; by rewrite hfd => _ [<-].
Qed.

Lemma pre_GenKey :
  rpreF fn_genkey fn_genkey (fsS_GenKey ms) (fsT_GenKey mt ppk psk).
Proof.
have [ok_ufd_genkey ok_sfd_genkey ok_alloc wf_args ok_ra] := ok_genkey.
split=> //.
- move=> fd; rewrite ok_sfd_genkey => -[?]; subst fd.
  rewrite /stack_alloc_proof_2.sf_total_stack ok_ra; by split.
rewrite /get_wptrs ok_ufd_genkey /=.
have [var_pk [var_sk [-> _ _ /= -> ->]]] := sig_genkey.
constructor; last constructor; last by constructor.
- exists ppk; split=> //= i w; by rewrite WArray.get_empty -fun_if.
exists psk; split=> //= i w; by rewrite WArray.get_empty -fun_if.
Qed.

Lemma eutt_GenKey :
  eutt eq
    (semS_GenKey up fn_genkey ms)
    (semT_GenKey sp rip fn_genkey mt ppk psk).
Proof.
have [hfd _ _ _ _] := ok_genkey.
rewrite /semS_GenKey /semT_GenKey.
apply/(eutt_clo_bind eq (UU := exec_rel (aux_post fn_genkey _ _))).
- apply/interp_exec_eutt/(correct_comp _ hfd) => //; exact: pre_GenKey.
move=> [s'|?] [t'|?] => //; last reflexivity.
move=> [] /[swap] hdef /[swap] /(_ _ hfd) [] st.
rewrite /finalize_funcall /get_nb_wptr /get_wptrs /= hfd /=.
have [var_pk [var_sk [-> -> -> /= -> ->]]] /= := sig_genkey.
t_xrbindP=> _ vpk0 hpk0 _ vsk0 hsk0 <- <-.
t_xrbindP=>
  _ vpk1 /truncate_val_typeE [apk ??]
  _ vsk1 /truncate_val_typeE [ask ??]
  _ <- <- <- ?;
  subst vpk0 vpk1 vsk0 vsk1 s'.
move: hdef => /andP /[!andbT] /= -[defpk defsk].
move=> /List_Forall2_inv [] pk_mem /List_Forall2_inv [] sk_mem _.
rewrite /get_res /= /wvec_of_val /= !WArray.castK /wvec_of_arr
  (wseq_in_mem defpk pk_mem) (wseq_in_mem defsk sk_mem).
reflexivity.
Qed.

Lemma pre_Encap pk apk :
  pk_of_w pk = ok apk ->
  rpreF fn_encap fn_encap (fsS_Encap ms apk) (fsT_Encap mt ppk pct pmsg pk).
Proof.
move=> hpk.
have [ok_ufd_encap ok_sfd_encap ok_alloc wf_args ok_ra] := ok_encap apk.
move: (wf_args 2%N); rewrite /= /wf_arg /get_wptrs ok_ufd_encap /=.
have [var_pk [var_ct [var_msg [-> _ _ /= -> -> ->]]]] := sig_encap.
move=> [_ [[<-] [_ hov hv hdisj _ _]]].
split=> //.
- move=> fd; rewrite ok_sfd_encap => -[?]; subst fd.
  rewrite /stack_alloc_proof_2.sf_total_stack ok_ra; split=> //=.
  rewrite /allocatable_stack -(ss_top_stack (a := mt));
    last exact: write_wseq_stack_stable.
  rewrite -(ss_limit (m := mt)) //; exact: write_wseq_stack_stable.
- exact: write_wseq_it_wf_args wf_args.
- constructor; last constructor; last constructor; last by constructor.
  + exists pct; split=> //= i w; by rewrite WArray.get_empty -fun_if.
  + exists pmsg; split=> //= i w; by rewrite WArray.get_empty -fun_if.
  exists ppk; split=> //= i w hw.
  apply: (read_write_wseq (lezP small_pkbytes) _ hpk hw).
  move=> k hk; apply: hv; apply: (between_byte hov); first exact: zbetween_refl.
  exact hk.
apply: write_wseq_extend_mem (ok_extend_mem);
  rewrite -(WArray.fill_size hpk) positive_nat_Z.
- exact: small_pkbytes.
- rewrite -/(size_glob sp); exact/disjoint_zrange_sym/ppk_not_rip.
exact: hdisj.
Qed.

Lemma eutt_Encap {pk} :
  eutt eq
    (semS_Encap up fn_encap ms pk)
    (semT_Encap sp rip fn_encap mt ppk pct pmsg pk).
Proof.
rewrite /semS_Encap /semT_Encap; case hpk: pk_of_w => [apk|]; last reflexivity.
have [hfd _ _ _ _] := ok_encap apk.
apply: (eutt_clo_bind eq (UU := exec_rel (aux_post fn_encap _ _))).
- apply/interp_exec_eutt/(correct_comp _ hfd) => //; exact: pre_Encap hpk.
move=> [s'|?] [t'|?] => //; last reflexivity.
move=> [] /[swap] hdef /[swap] /(_ _ hfd) [] st.
rewrite /finalize_funcall /get_nb_wptr /get_wptrs /= hfd /=.
have [var_pk [var_ct [var_msg [-> -> -> /= -> -> ->]]]] /= := sig_encap.
t_xrbindP=> _ vct0 hct0 _ vmsg0 hmsg0 <- <-.
t_xrbindP=>
  _ vct1 /truncate_val_typeE [act ??]
  _ vmsg1 /truncate_val_typeE [amsg ??]
  _ <- <- <- ?;
  subst vct0 vct1 vmsg0 vmsg1 s'.
move: hdef => /andP /[!andbT] /= -[defct defmsg].
move=> /List_Forall2_inv [] ct_mem /List_Forall2_inv [] msg_mem _.
rewrite /get_res /= /wvec_of_val /= !WArray.castK /wvec_of_arr
  (wseq_in_mem defct ct_mem) (wseq_in_mem defmsg msg_mem).
reflexivity.
Qed.

Lemma pre_Decap sk ct ask act :
  sk_of_w sk = ok ask ->
  ct_of_w ct = ok act ->
  rpreF fn_decap fn_decap
    (fsS_Decap ms ask act) (fsT_Decap mt psk pct pmsg sk ct).
Proof.
move=> hsk hct.
have [ok_ufd_decap ok_sfd_decap ok_alloc wf_args ok_ra] :=
  ok_decap ask act.
move: (wf_args 1%N) (wf_args 2%N);
  rewrite /= /wf_arg /get_wptrs ok_ufd_decap /=.
have [var_sk [var_ct [var_msg [-> _ _ /= -> -> ->]]]] := sig_decap.
move=> [_ [[<-] [_ ct_ov ct_v ct_disj _ _]]]
  [_ [[<-] [_ sk_ov sk_v sk_disj _ _]]].
split=> //.
- move=> fd; rewrite ok_sfd_decap => -[?]; subst fd.
  rewrite /stack_alloc_proof_2.sf_total_stack ok_ra; split=> //=.
  rewrite /allocatable_stack -(ss_top_stack (a := mt)); last first.
  - transitivity (write_wseq mt psk sk); exact: write_wseq_stack_stable.
  rewrite -(ss_limit (m := mt)) //.
  transitivity (write_wseq mt psk sk); exact: write_wseq_stack_stable.
- exact/write_wseq_it_wf_args/(write_wseq_it_wf_args wf_args).
- constructor; last constructor; last constructor; last by constructor.
  + exists pmsg; split=> //= i w; by rewrite WArray.get_empty -fun_if.
  + exists pct; split=> //= i w hw.
    apply: (read_write_wseq (lezP small_ctbytes) _ hct hw).
    move=> k hk; rewrite -(write_wseq_validw_eq); apply: ct_v.
    apply: (between_byte ct_ov); first exact: zbetween_refl.
    exact hk.
  exists psk; split=> //= i w hw.
  rewrite -(write_wseq_disjoint (write_wseq mt _ _)); first last.
  + rewrite -(WArray.fill_size hct) positive_nat_Z.
    apply: (disjoint_zrange_byte pct_not_psk).
    rewrite -(WArray.get8_read _ AAdirect) in hw.
    have [+ + _] := WArray.get_bound hw.
    rewrite /= /wsize_size; lia.
  apply: (read_write_wseq (lezP small_skbytes) _ hsk hw) => k hk.
  apply: sk_v; apply: (between_byte sk_ov); first exact: zbetween_refl.
  exact hk.
apply: write_wseq_extend_mem; rewrite -?(WArray.fill_size hct) ?positive_nat_Z.
- exact: small_ctbytes.
- rewrite -/(size_glob sp); exact/disjoint_zrange_sym/pct_not_rip.
- exact: ct_disj.
apply: write_wseq_extend_mem (ok_extend_mem);
  rewrite -(WArray.fill_size hsk) positive_nat_Z.
- exact: small_skbytes.
- rewrite -/(size_glob sp); exact/disjoint_zrange_sym/psk_not_rip.
exact: sk_disj.
Qed.

Lemma eutt_Decap {sk c} :
  eutt eq
    (semS_Decap up fn_decap ms sk c)
    (semT_Decap sp rip fn_decap mt psk pct pmsg sk c).
Proof.
rewrite /semS_Decap /semT_Decap.
case hsk: sk_of_w => [ask|]; last reflexivity.
case hct: ct_of_w => [act|]; last reflexivity.
have [hfd _ _ _ _] := ok_decap ask act.
apply: (eutt_clo_bind eq (UU := exec_rel (aux_post fn_decap _ _))).
- apply/interp_exec_eutt/(correct_comp _ hfd) => //; exact: pre_Decap hsk hct.
move=> [s'|?] [t'|?] => //; last reflexivity.
move=> [] /[swap] hdef /[swap] /(_ _ hfd) [] st.
rewrite /finalize_funcall /get_nb_wptr /get_wptrs /= hfd /=.
have [var_sk [var_ct [var_msg [-> -> -> /= -> -> ->]]]] /= := sig_decap.
t_xrbindP=> _ vmsg0 hmsg0 <-.
t_xrbindP=> _ vmsg1 /truncate_val_typeE [amsg ??] _ <- <- ?;
  subst vmsg0 vmsg1 s'.
move: hdef => /= /[!andbT] defmsg.
move=> /List_Forall2_inv [] msg_mem _.
rewrite /get_res /= /wvec_of_val /= !WArray.castK /wvec_of_arr
  (wseq_in_mem defmsg msg_mem).
reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Generic *)

Lemma eutt_translateE T (RR : T -> T -> Prop) :
  Proper (eutt RR ==> eutt RR) (translateE (T := T)).
Proof. exact: eutt_interp'. Qed.

Let C_s :=
  Challenger_of_S
    up
    fn_genkey fn_encap fn_decap
    ms.

Let C_t :=
  Challenger_of_T
    sp rip
    fn_genkey fn_encap fn_decap
    mt ppk psk pct pmsg.

Lemma handle_DecP T sk (e : Dec T) :
  eutt eq (handle_Dec C_s sk e) (handle_Dec C_t sk e).
Proof.
move: T e => _ [c] /=; apply/eutt_eq_bind => _.
exact/eutt_translate'/eutt_translateE/eutt_Decap.
Qed.

Lemma interactP T (A : itree _ T) sk :
  eutt eq (interact C_s A sk) (interact C_t A sk).
Proof.
rewrite /indcca.interact; set ds := interp _ _; set dt := interp _ _.
suff -> : eutt eq ds dt by reflexivity.
apply/eutt_interp; last reflexivity.
move=> ??; apply/Proper_Case_Handler; last reflexivity.
move=> *; exact: handle_DecP.
Qed.

Theorem eutt_game {A : KEM_Adversary} :
  eutt eq (game C_s A) (game C_t A).
Proof.
rewrite /game /= (eutt_translateE eutt_GenKey).
apply: eutt_eq_bind => -[pk sk].
rewrite interactP; apply: eutt_eq_bind => -[lq amem].
rewrite (eutt_translateE eutt_Encap); apply: eutt_eq_bind => -[ct m0].
apply: eutt_eq_bind => m1; apply: eutt_eq_bind => b.
rewrite interactP; reflexivity.
Qed.

Corollary deqX_game {A : KEM_Adversary} :
  dgame C_s A =1 dgame C_t A.
Proof. exact/dinterp_eutt/eutt_game. Qed.

Corollary reduction :
  reduction (advmem := advmem) C_s C_t.
Proof. move=> A Q. by rewrite /advantage [in LHS](eq_mu_pr _ deqX_game). Qed.

End THEOREM.

End MAIN.
